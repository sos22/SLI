/* This file is somewhat misnamed, because it also handles store CFGs. */
#include "sli.h"
#include "state_machine.hpp"
#include "cfgnode.hpp"
#include "oracle.hpp"
#include "alloc_mai.hpp"
#include "offline_analysis.hpp"

#include "libvex_guest_offsets.h"

namespace _probeCFGsToMachine {

struct reloc_t {
	StateMachineState **ptr;
	CFGNode *target;
	reloc_t(StateMachineState **_ptr,
		CFGNode *_target)
		: ptr(_ptr), target(_target)
	{}
};

static void
ndChoiceState(StateMachineState **slot,
	      const VexRip &vr,
	      std::vector<reloc_t> &pendingRelocs,
	      std::vector<CFGNode *> &targets,
	      bool storeLike,
	      std::set<CFGNode *> *usedExits)
{
	if (targets.empty()) {
		if (storeLike)
			*slot = StateMachineCrash::get();
		else
			*slot = StateMachineNoCrash::get();
	} else if (targets.size() == 1) {
		if (usedExits)
			usedExits->insert(targets[0]);
		pendingRelocs.push_back(
			reloc_t(slot, targets[0]));
	} else {
		StateMachineNdChoice *nd =
			new StateMachineNdChoice(vr);
		nd->successors.resize(targets.size());
		for (unsigned x = 0; x < targets.size(); x++) {
			if (usedExits)
				usedExits->insert(targets[x]);
			pendingRelocs.push_back(
				reloc_t(&nd->successors[x], targets[x]));
		}
		*slot = nd;
	}
}

static void
getTargets(CFGNode *node, const VexRip &vr, std::vector<CFGNode *> &targets)
{
	if (node->fallThrough.second &&
	    node->fallThrough.first == vr)
		targets.push_back(node->fallThrough.second);
	for (auto it = node->branches.begin(); it != node->branches.end(); it++)
		if (it->second && it->first == vr)
			targets.push_back(it->second);
}

/* State machine builder types to make it a bit easier to define state
 * machines. */
class SMBExpression : public GarbageCollected<SMBExpression, &ir_heap> {
public:
	const IRExpr *what;
	IRExpr *compile() const {
		return (IRExpr *)what;
	}
	bool allowRetyping;
	SMBExpression(const IRExpr *_what)
		: what(_what), allowRetyping(false)
	{}
	explicit SMBExpression(uint8_t k)
		: what(IRExpr_Const(IRConst_U8(k))),
		  allowRetyping(false)
	{
	}
	explicit SMBExpression(int k)
		: what(IRExpr_Const(IRConst_U64(k))),
		  allowRetyping(true)
	{
	}
	explicit SMBExpression(unsigned long k)
		: what(IRExpr_Const(IRConst_U64(k))),
		  allowRetyping(false)
	{
	}
	explicit SMBExpression(const threadAndRegister &tr)
		: what(IRExpr_Get(tr, Ity_I64)),
		  allowRetyping(true)
	{
	}
	const SMBExpression *retype(IRType ty) const {
		if (what->type() == ty)
			return this;
		assert(allowRetyping);
		assert(what->type() == Ity_I64);
		switch (what->tag) {
		case Iex_Const:
			switch (ty) {
			case Ity_I8:
				return new SMBExpression(IRExpr_Const(IRConst_U8( ((IRExprConst *)what)->con->Ico.U64)));
			case Ity_I16:
				return new SMBExpression(IRExpr_Const(IRConst_U8( ((IRExprConst *)what)->con->Ico.U64)));
			case Ity_I32:
				return new SMBExpression(IRExpr_Const(IRConst_U8( ((IRExprConst *)what)->con->Ico.U64)));
			default:
				abort();
			}
		case Iex_Get:
			return new SMBExpression(IRExpr_Get(((IRExprGet *)what)->reg, ty));
		default:
			abort();
		}
	}
	void visit(HeapVisitor &hv) {
		hv(what);
	}
	NAMED_CLASS
};

class SMBStatement : public GarbageCollected<SMBStatement, &ir_heap> {
public:
	virtual StateMachineSideEffect *compile(const ThreadRip &vr) const = 0;
	NAMED_CLASS
};

class SMBStatementCopy;
class SMBRegisterReference : public GarbageCollected<SMBRegisterReference, &ir_heap> {
public:
	threadAndRegister compile() const {
		return tr;
	}
	threadAndRegister tr;
	explicit SMBRegisterReference(const threadAndRegister &_tr)
		: tr(_tr)
	{
	}
	const SMBStatementCopy &operator=(const SMBExpression &value) const;
	void visit(HeapVisitor &) {}
	NAMED_CLASS
};
class SMBStatementCopy : public SMBStatement {
	StateMachineSideEffect *compile(const ThreadRip &) const {
		return new StateMachineSideEffectCopy(
			lvalue->compile(),
			rvalue->compile());
	}
public:
	const SMBRegisterReference *lvalue;
	const SMBExpression *rvalue;
	void visit(HeapVisitor &hv) {
		hv(lvalue);
		hv(rvalue);
	}
	explicit SMBStatementCopy(const SMBRegisterReference *_lvalue, const SMBExpression *_rvalue)
		: lvalue(_lvalue), rvalue(_rvalue)
	{}
};
static const SMBStatementCopy *
Copy(const SMBRegisterReference *addr, const SMBExpression *value)
{
	return new SMBStatementCopy(addr, value);
}
const SMBStatementCopy &
SMBRegisterReference::operator=(const SMBExpression &value) const
{
	return *Copy(this, &value);
}

class SMBStatementStore;
class SMBMemoryReference : public GarbageCollected<SMBMemoryReference, &ir_heap> {
public:
	const SMBExpression *addr;
	IRExpr *compile() const {
		return addr->compile();
	}
	explicit SMBMemoryReference(const SMBExpression *a)
		: addr(a->retype(Ity_I64))
	{
	}
	void visit(HeapVisitor &hv)
	{
		hv(addr);
	}
	const SMBStatementStore &operator=(const SMBExpression &value) const;
	NAMED_CLASS
};
class SMBStatementStore : public SMBStatement {
	StateMachineSideEffect *compile(const ThreadRip &vr) const {
		return new StateMachineSideEffectStore(
			addr->compile(),
			value->compile(),
			MemoryAccessIdentifier(vr,
					       MemoryAccessIdentifier::static_generation));
	}
public:
	const SMBMemoryReference *addr;
	const SMBExpression *value;

	void visit(HeapVisitor &hv) {
		hv(addr);
		hv(value);
	}
	explicit SMBStatementStore(const SMBMemoryReference *_addr, const SMBExpression *_value)
		: addr(_addr), value(_value)
	{
		assert(!value->allowRetyping);
	}
};
static const SMBStatementStore *
Store(const SMBMemoryReference *addr, const SMBExpression *value)
{
	return new SMBStatementStore(addr, value);
}
const SMBStatementStore &
SMBMemoryReference::operator=(const SMBExpression &value) const
{
	return *Store(this, &value);
}

class SMBStatementLoad : public SMBStatement {
	StateMachineSideEffect *compile(const ThreadRip &vr) const {
		return new StateMachineSideEffectLoad(
			target->compile(),
			addr->compile(),
			MemoryAccessIdentifier(vr,
					       MemoryAccessIdentifier::static_generation),
			type);
	}
public:
	const SMBRegisterReference *target;
	const SMBMemoryReference *addr;
	IRType type;

	void visit(HeapVisitor &hv) {
		hv(target);
		hv(addr);
	}
	explicit SMBStatementLoad(const SMBRegisterReference *_target,
				  const SMBMemoryReference *_addr,
				  IRType _type)
		: target(_target), addr(_addr), type(_type)
	{
	}
};
static const SMBStatementLoad *
Load(const SMBRegisterReference *target, const SMBMemoryReference *addr, IRType ty)
{
	return new SMBStatementLoad(target, addr, ty);
}

static const SMBExpression &operator+(const SMBExpression &a, const SMBExpression &b)
{
	if (a.what->type() != b.what->type()) {
		if (a.allowRetyping && !b.allowRetyping)
			return *a.retype(b.what->type()) + b;
		assert(!a.allowRetyping && b.allowRetyping);
		return *b.retype(a.what->type()) + a;
	}
	IROp op;
	switch (a.what->type()) {
	case Ity_I1:
		op = Iop_Xor1;
		break;
	case Ity_I8:
		op = Iop_Add8;
		break;
	case Ity_I16:
		op = Iop_Add16;
		break;
	case Ity_I32:
		op = Iop_Add32;
		break;
	case Ity_I64:
		op = Iop_Add64;
		break;
	case Ity_I128:
		abort();
	case Ity_F32:
		abort();
	case Ity_F64:
		op = Iop_AddF64;
		break;
	case Ity_V128:
		abort();
	case Ity_INVALID:
		abort();
	}
	SMBExpression *res = new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.what, (IRExpr *)b.what));
	if (a.allowRetyping && b.allowRetyping)
		res->allowRetyping = true;
	return *res;
				     
}
static const SMBExpression &operator==(const SMBExpression &a, const SMBExpression &b)
{
	if (a.what->type() != b.what->type()) {
		if (a.allowRetyping && !b.allowRetyping)
			return *a.retype(b.what->type()) == b;
		assert(!a.allowRetyping && b.allowRetyping);
		return *b.retype(a.what->type()) == a;
	}
	IROp op;
	switch (a.what->type()) {
	case Ity_I1:
		op = Iop_CmpEQ1;
		break;
	case Ity_I8:
		op = Iop_CmpEQ8;
		break;
	case Ity_I16:
		op = Iop_CmpEQ16;
		break;
	case Ity_I32:
		op = Iop_CmpEQ32;
		break;
	case Ity_I64:
		op = Iop_CmpEQ64;
		break;
	case Ity_I128:
		op = Iop_CmpEQI128;
		break;
	case Ity_V128:
		op = Iop_CmpEQV128;
		break;
	case Ity_F32:
		op = Iop_CmpEQF32;
		break;
	case Ity_F64:
		op = Iop_CmpEQF64;
		break;
	case Ity_INVALID:
		abort();
	}
	return *(new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.what, (IRExpr *)b.what)));
}
static const SMBExpression &operator<=(const SMBExpression &a, const SMBExpression &b)
{
	if (a.what->type() != b.what->type()) {
		if (a.allowRetyping && !b.allowRetyping)
			return *a.retype(b.what->type()) == b;
		assert(!a.allowRetyping && b.allowRetyping);
		return *b.retype(a.what->type()) == a;
	}
	IROp op;
	switch (a.what->type()) {
	case Ity_I1:
		abort();
	case Ity_I8:
		abort();
	case Ity_I16:
		abort();
	case Ity_I32:
		op = Iop_CmpLE32U;
		break;
	case Ity_I64:
		op = Iop_CmpLE64U;
		break;
	case Ity_I128:
	case Ity_V128:
	case Ity_F32:
	case Ity_F64:
		abort();
	case Ity_INVALID:
		abort();
	}
	return *(new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.what, (IRExpr *)b.what)));
}

static const SMBMemoryReference &operator*(const SMBExpression &a)
{
	return *(new SMBMemoryReference(&a));
}

class SMBState : public GarbageCollected<SMBState, &ir_heap> {
protected:
	struct reloc2 {
		const SMBState *target;
		StateMachineState **t;
		reloc2(const SMBState *_target, StateMachineState **_t)
			: target(_target), t(_t)
		{}
	};
	virtual StateMachineState *_compile(const ThreadRip &vr,
					    std::vector<reloc_t> &relocs,
					    std::vector<reloc2> &relocs2) const = 0;
private:
	StateMachineState *compile(const ThreadRip &vr,
				   std::map<const SMBState *, StateMachineState *> &m,
				   std::vector<reloc_t> &relocs,
				   std::vector<reloc2> &relocs2) const {
		auto it_did_insert = m.insert(std::pair<const SMBState *, StateMachineState *>(this, (StateMachineState *)NULL));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert)
			it->second = _compile(vr, relocs, relocs2);
		return it->second;
	}
public:
	StateMachineState *compile(const ThreadRip &vr, std::vector<reloc_t> &relocs) const {
		std::map<const SMBState *, StateMachineState *> m;
		std::vector<reloc2> relocs2;
		StateMachineState *res;
		res = NULL;
		relocs2.push_back(reloc2(this, &res));
		while (!relocs2.empty()) {
			reloc2 r2(relocs2.back());
			relocs2.pop_back();
			assert(!*r2.t);
			*r2.t = r2.target->compile(vr, m, relocs, relocs2);
			assert(*r2.t);
		}
		assert(res);
		return res;
	}
	NAMED_CLASS
};
class SMBStateStatement : public SMBState {
	StateMachineState *_compile(const ThreadRip &vr,
				    std::vector<reloc_t> &,
				    std::vector<reloc2> &relocs2) const {
		StateMachineSideEffecting *smse =
			new StateMachineSideEffecting(
				vr.rip,
				first->compile(vr),
				NULL);
		relocs2.push_back(reloc2(second, &smse->target));
		return smse;
	}
public:
	const SMBStatement *first;
	const SMBState *second;
	explicit SMBStateStatement(const SMBStatement *_first, const SMBState *_second)
		: first(_first), second(_second)
	{}
	void visit(HeapVisitor &hv)
	{
		hv(first);
		hv(second);
	}
};
static const SMBState &operator>>(const SMBStatement &a, const SMBState &b)
{
	return *(new SMBStateStatement(&a, &b));
}
class SMBStateIf : public SMBState {
	StateMachineState *_compile(const ThreadRip &tr,
				    std::vector<reloc_t> &,
				    std::vector<reloc2> &relocs2) const {
		StateMachineBifurcate *smb =
			new StateMachineBifurcate(tr.rip,
						  cond->compile(),
						  NULL,
						  NULL);
		relocs2.push_back(reloc2(trueTarg, &smb->trueTarget));
		relocs2.push_back(reloc2(falseTarg, &smb->falseTarget));
		return smb;
	}
public:
	const SMBExpression *cond;
	const SMBState *trueTarg;
	const SMBState *falseTarg;
	explicit SMBStateIf(const SMBExpression *_cond, const SMBState *_trueTarg, const SMBState *_falseTarg)
		: cond(_cond), trueTarg(_trueTarg), falseTarg(_falseTarg)
	{}
	void visit(HeapVisitor &hv)
	{
		hv(cond);
		hv(trueTarg);
		hv(falseTarg);
	}	
};
static SMBState &If(const SMBExpression &a, const SMBState &trueTarg, const SMBState &falseTarg)
{
	return *(new SMBStateIf(&a, &trueTarg, &falseTarg));
}
class SMBStateProxy : public SMBState {
	StateMachineState *_compile(const ThreadRip &tr,
				    std::vector<reloc_t> &relocs,
				    std::vector<reloc2> &) const {
		StateMachineSideEffecting *smse =
			new StateMachineSideEffecting(tr.rip, NULL, NULL);
		relocs.push_back(reloc_t(&smse->target, target));
		return smse;
	}
public:
	CFGNode *target;
	explicit SMBStateProxy(CFGNode *_target)
		: target(_target)
	{
		assert(target);
	}
	void visit(HeapVisitor &hv)
	{
		hv(target);
	}
};

static StateMachineState *
getLibraryStateMachine(CFGNode *cfgnode, unsigned tid,
		       std::vector<reloc_t> &pendingRelocs)
{
	assert(cfgnode->fallThrough.second);
	assert(cfgnode->branches.empty());
	threadAndRegister rax(threadAndRegister::reg(tid, OFFSET_amd64_RAX, 0));
	threadAndRegister arg1(threadAndRegister::reg(tid, OFFSET_amd64_RDI, 0));
	threadAndRegister arg2(threadAndRegister::reg(tid, OFFSET_amd64_RSI, 0));
	const SMBState *end = new SMBStateProxy(cfgnode->fallThrough.second);;
	const SMBState *acc;
	switch (cfgnode->libraryFunction) {
	case LibraryFunctionTemplate::__cxa_atexit: {
		acc = &( (*(new SMBRegisterReference(rax)) = *(new SMBExpression((uint64_t)0))) >> *end);
		break;
	}
	case LibraryFunctionTemplate::bzero: {
		int i, j;
		acc = end;
		const SMBExpression *zero_word = new SMBExpression((uint64_t)0);
		const SMBExpression *arg1_expr = new SMBExpression(arg1);
		const SMBExpression *arg2_expr = new SMBExpression(arg2);
		for (j = 0; j < 64; j += 8) {
			const SMBExpression *j_expr = new SMBExpression(j);
			const SMBState *acc2 = new SMBStateProxy(cfgnode->fallThrough.second);
			for (i = j - 8; i >= 0; i -= 8)
				acc2 = &((*(*arg1_expr + *(new SMBExpression(i))) = *zero_word) >> *acc2);
			acc = &If(j == 56 ? *j_expr <= *arg2_expr : *arg2_expr == *j_expr,
				  *acc2,
				  *acc);
		}
		break;
	}
	case LibraryFunctionTemplate::strlen: {
		int i;
		threadAndRegister tmp1(threadAndRegister::temp(tid, 0, 0));
		const SMBExpression *arg1_expr = new SMBExpression(arg1);
		const SMBRegisterReference *rax_ref = new SMBRegisterReference(rax);
		const SMBRegisterReference *tmp1_ref = new SMBRegisterReference(tmp1);
		const SMBExpression *tmp1_expr = new SMBExpression(tmp1);
		const SMBExpression *zero_byte = new SMBExpression((uint8_t)0);
		acc = &( (*rax_ref = *(new SMBExpression((uint64_t)64))) >> *end);
		for (i = 63; i >= 0; i--) {
			const SMBExpression *i_expr = new SMBExpression((uint64_t)i);
			acc = &(*Load(tmp1_ref,
				      &*(*arg1_expr + *i_expr),
				      Ity_I8) >>
				If(*tmp1_expr == *zero_byte,
				   (*rax_ref = *i_expr) >> *end,
				   *acc));
		}
		break;
	}
	case LibraryFunctionTemplate::none:
		abort();
	}
	return acc->compile(ThreadRip(tid, cfgnode->my_rip), pendingRelocs);
}

static StateMachineState *
cfgNodeToState(Oracle *oracle,
	       unsigned tid,
	       CFGNode *target,
	       bool storeLike,
	       MemoryAccessIdentifierAllocator &mai,
	       std::vector<reloc_t> &pendingRelocs)
{
	ThreadRip tr(tid, target->my_rip);

	if (target->libraryFunction)
		return getLibraryStateMachine(target, tid, pendingRelocs);

	IRSB *irsb;
	try {
		irsb = oracle->ms->addressSpace->getIRSBForAddress(tr);
	} catch (BadMemoryException &e) {
		return StateMachineUnreached::get();
	}
	std::set<CFGNode *> usedExits;
	StateMachineState *root = NULL;
	StateMachineState **cursor = &root;
	int i;
	for (i = 1; i < irsb->stmts_used && irsb->stmts[i]->tag != Ist_IMark; i++) {
		IRStmt *stmt = irsb->stmts[i];
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			abort();
			break;
		case Ist_AbiHint:
			break;
		case Ist_Put: {
			IRStmtPut *isp = (IRStmtPut *)stmt;
			StateMachineSideEffect *se =
				new StateMachineSideEffectCopy(
					isp->target,
					isp->data);
			StateMachineSideEffecting *smse =
				new StateMachineSideEffecting(
					target->my_rip,
					se,
					NULL);
			*cursor = smse;
			cursor = &smse->target;
			break;
		}
		case Ist_PutI:
			/* These can't really be represented in the
			 * state machine model. */
			abort();
			break;
		case Ist_Store: {
			IRStmtStore *ist = (IRStmtStore *)stmt;
			StateMachineSideEffect *se =
				new StateMachineSideEffectStore(
					ist->addr,
					ist->data,
					mai(tr));
			StateMachineSideEffecting *smse =
				new StateMachineSideEffecting(
					target->my_rip,
					se,
					NULL);
			*cursor = smse;
			cursor = &smse->target;
			break;
		}
		case Ist_CAS: {
			IRCAS *cas = ((IRStmtCAS *)stmt)->details;
			/* This is a bit tricky.  We take a

			   CAS *x : expd -> b

			   and we turn it into

			   l1: t <- *x then l2
			   l2: if (t == expd) then l3 else l4
			   l3: *x <- data
			   l4: old <- t
			*/
#warning This breaks the atomicity of the CAS
			/* Breaking the atomicity of the CAS like that
			   means that we'll sometimes report a crash
			   which can't happen, but we'll never miss a
			   crash which can. */
			IRTemp t = newIRTemp(irsb->tyenv);
			threadAndRegister tempreg = threadAndRegister::temp(tid, t, 0);
			IRType ty = cas->expdLo->type();
			IRExpr *t_expr = IRExpr_Get(tempreg, ty);
			StateMachineSideEffecting *l4 =
				new StateMachineSideEffecting(
					target->my_rip,
					new StateMachineSideEffectCopy(
						cas->oldLo,
						t_expr),
					NULL);
			StateMachineState *l3 =
				new StateMachineSideEffecting(
					target->my_rip,
					new StateMachineSideEffectStore(
						cas->addr,
						cas->dataLo,
						mai(tr)),
					l4);
			StateMachineState *l2 =
				new StateMachineBifurcate(
					target->my_rip,
					expr_eq(t_expr, cas->expdLo),
					l3,
					l4);
			StateMachineState *l1 =
				new StateMachineSideEffecting(
					target->my_rip,
					new StateMachineSideEffectLoad(
						tempreg,
						cas->addr,
						mai(tr),
						ty),
					l2);
			*cursor = l1;
			cursor = &l4->target;
			break;
		}
		case Ist_Dirty: {
			IRDirty *dirty = ((IRStmtDirty *)stmt)->details;
			IRType ity = Ity_INVALID;
			StateMachineSideEffect *se;
			if (!strncmp(dirty->cee->name, "helper_load_", strlen("helper_load_"))) {
				if (!strcmp(dirty->cee->name, "helper_load_8"))
					ity = Ity_I8;
				else if (!strcmp(dirty->cee->name, "helper_load_16"))
					ity = Ity_I16;
				else if (!strcmp(dirty->cee->name, "helper_load_32"))
					ity = Ity_I32;
				else if (!strcmp(dirty->cee->name, "helper_load_64"))
					ity = Ity_I64;
				else
					abort();
				assert(ity != Ity_INVALID);
				se = new StateMachineSideEffectLoad(
					dirty->tmp,
					dirty->args[0],
					mai(tr),
					ity);
			} else if (!strcmp(dirty->cee->name, "amd64g_dirtyhelper_RDTSC")) {
				se = new StateMachineSideEffectCopy(
					dirty->tmp,
					mai.freeVariable(Ity_I64, tr));
			} else {
				abort();
			}
			StateMachineSideEffecting *smse =
				new StateMachineSideEffecting(
					target->my_rip,
					se,
					NULL);
			*cursor = smse;
			cursor = &smse->target;
			break;
		}
		case Ist_MBE:
			break;
		case Ist_Exit: {
			IRStmtExit *stmt = (IRStmtExit *)irsb->stmts[i];
			std::vector<CFGNode *> targets;
			getTargets(target, stmt->dst.rip, targets);
			StateMachineBifurcate *smb;
			smb = new StateMachineBifurcate(
				target->my_rip,
				stmt->guard,
				NULL,
				NULL);
			ndChoiceState(&smb->trueTarget, target->my_rip,
				      pendingRelocs, targets, storeLike, &usedExits);
			*cursor = smb;
			cursor = &smb->falseTarget;
			break;
		}
		}
	}

	if (root == NULL) {
		/* This can happen when you're looking at jmp
		   instructions, because they get encoded as empty
		   IRSBs by just setting the next field at the end.
		   Unfortunately, we need to have *something* to
		   return (can't return a relocation), so we need to
		   create a proxy state here. */
		StateMachineSideEffecting *smp =
			new StateMachineSideEffecting(
				target->my_rip,
				NULL,
				NULL);
		root = smp;
		cursor = &smp->target;
	}

	assert(*cursor == NULL);

	std::vector<CFGNode *> targets;
	if (i == irsb->stmts_used) {
		if (irsb->next_is_const) {
			getTargets(target, irsb->next_const.rip, targets);
		} else {
			if (target->fallThrough.second &&
			    !usedExits.count(target->fallThrough.second))
				targets.push_back(target->fallThrough.second);
			for (auto it = target->branches.begin();
			     it != target->branches.end();
			     it++)
				if (it->second &&
				    !usedExits.count(it->second))
					targets.push_back(it->second);
		}
	} else {
		IRStmtIMark *mark = (IRStmtIMark *)irsb->stmts[i];
		getTargets(target, mark->addr.rip, targets);
	}
	ndChoiceState(cursor, target->my_rip, pendingRelocs, targets, storeLike, NULL);

	return root;
}

struct cfg_translator {
	virtual StateMachineState *operator()(CFGNode *src,
					      Oracle *oracle,
					      unsigned tid,
					      std::vector<reloc_t> &pendingRelocations) = 0;
};

static StateMachineState *
performTranslation(std::map<CFGNode *, StateMachineState *> &results,
		   CFGNode *rootCfg,
		   Oracle *oracle,
		   unsigned tid,
		   cfg_translator &node_translator)
{
	std::vector<reloc_t> pendingRelocations;
	StateMachineState *root = NULL;
	pendingRelocations.push_back(
		reloc_t(&root, rootCfg));
	while (!pendingRelocations.empty()) {
		reloc_t r(pendingRelocations.back());
		pendingRelocations.pop_back();
		assert(r.target);
		assert(r.ptr);
		assert(!*r.ptr);
		std::pair<CFGNode *, StateMachineState *> thingToInsert(r.target, (StateMachineState *)NULL);
		auto slot_and_inserted = results.insert(thingToInsert);
		auto slot = slot_and_inserted.first;
		auto inserted = slot_and_inserted.second;
		if (!inserted)
			assert(slot->second);
		else 
			slot->second = node_translator(r.target, oracle, tid, pendingRelocations);
		*r.ptr = slot->second;
	}
	return root;
}

/* The rest of the analysis can't use any more than four slots of RIP
   context, so there's not really much point in maintaining them. */
static StateMachine *
truncateRips(StateMachine *sm)
{
	struct : public StateMachineTransformer {
		bool truncateVexRip(const VexRip &in, VexRip *out) {
			if (in.stack.size() <= (unsigned)DynAnalysisRip::DATABASE_RIP_DEPTH)
				return false;
			std::vector<unsigned long> c;
			c.reserve(DynAnalysisRip::DATABASE_RIP_DEPTH);
			for (auto it = in.stack.rbegin(); it != in.stack.rend(); it++)
				c.push_back(*it);
			*out= VexRip(c);
			return true;
		}
		StateMachineSideEffectLoad *transformOneSideEffect(
			StateMachineSideEffectLoad *smsel, bool *done_something)
		{
			VexRip t;
			if (truncateVexRip(smsel->rip.rip.rip, &t)) {
				*done_something = true;
				return new StateMachineSideEffectLoad(
					smsel->target,
					smsel->addr,
					MemoryAccessIdentifier(
						ThreadRip(smsel->rip.rip.thread, t),
						smsel->rip.generation),
					smsel->type);
			} else {
				return NULL;
			}
		}
		StateMachineSideEffectStore *transformOneSideEffect(
			StateMachineSideEffectStore *smses, bool *done_something)
		{
			VexRip t;
			if (truncateVexRip(smses->rip.rip.rip, &t)) {
				*done_something = true;
				return new StateMachineSideEffectStore(
					smses->addr,
					smses->data,
					MemoryAccessIdentifier(ThreadRip(smses->rip.rip.thread, t), smses->rip.generation));
			} else {
				return NULL;
			}
		}
	} doit;
	return doit.transform(sm);
}

static void
probeCFGsToMachine(Oracle *oracle, unsigned tid, std::set<CFGNode *> &roots,
		   const DynAnalysisRip &proximalRip,
		   StateMachineState *proximal,
		   MemoryAccessIdentifierAllocator &mai,
		   std::set<StateMachine *> &out)
{
	struct _ : public cfg_translator {
		const DynAnalysisRip &proximalRip;
		MemoryAccessIdentifierAllocator &mai;		
		StateMachineState *proximal;
		StateMachineState *operator()(CFGNode *e,
					      Oracle *oracle,
					      unsigned tid,
					      std::vector<reloc_t> &pendingRelocations) {
			if (DynAnalysisRip(e->my_rip) == proximalRip) {
				return proximal;
			} else {
				return cfgNodeToState(oracle, tid, e, false, mai, pendingRelocations);
			}
		}
		_(const DynAnalysisRip &_proximalRip,
		  MemoryAccessIdentifierAllocator &_mai,
		  StateMachineState *_proximal)
			: proximalRip(_proximalRip), mai(_mai), proximal(_proximal)
		{}
	} doOne(proximalRip, mai, proximal);

	std::map<CFGNode *, StateMachineState *> results;
	for (auto it = roots.begin(); it != roots.end(); it++)
		performTranslation(results, *it, oracle, tid, doOne);

	for (auto it = roots.begin(); it != roots.end(); it++) {
		StateMachineState *root = results[*it];
		assert(root);
		std::vector<std::pair<unsigned, VexRip> > origin;
		origin.push_back(std::pair<unsigned, VexRip>(tid, root->origin));
		StateMachine *sm = new StateMachine(root, origin);
		sm->sanityCheck();
		out.insert(truncateRips(sm));
	}
}

static StateMachine *
storeCFGsToMachine(Oracle *oracle, unsigned tid, CFGNode *root, MemoryAccessIdentifierAllocator &mai)
{
	struct _ : public cfg_translator {
		MemoryAccessIdentifierAllocator *mai;
		StateMachineState *operator()(CFGNode *e,
					      Oracle *oracle,
					      unsigned tid,
					      std::vector<reloc_t> &pendingRelocations)
		{
			return cfgNodeToState(oracle, tid, e, true, *mai, pendingRelocations);
		}
	} doOne;
	doOne.mai = &mai;
	std::map<CFGNode *, StateMachineState *> results;
	std::vector<std::pair<unsigned, VexRip> > origin;
	origin.push_back(std::pair<unsigned, VexRip>(tid, root->my_rip));
	StateMachine *sm = new StateMachine(performTranslation(results, root, oracle, tid, doOne),
					    origin);
	return truncateRips(sm);
}

/* End of namespace */
};

void
probeCFGsToMachine(Oracle *oracle, unsigned tid,
		   std::set<CFGNode *> &roots,
		   const DynAnalysisRip &targetRip,
		   StateMachineState *proximal,
		   MemoryAccessIdentifierAllocator &mai,
		   std::set<StateMachine *> &out)
{
	return _probeCFGsToMachine::probeCFGsToMachine(oracle, tid, roots, targetRip, proximal, mai, out);
}

StateMachine *
storeCFGToMachine(Oracle *oracle,
		  unsigned tid,
		  CFGNode *root,
		  MemoryAccessIdentifierAllocator &mai)
{
	return _probeCFGsToMachine::storeCFGsToMachine(oracle, tid, root, mai);
}
