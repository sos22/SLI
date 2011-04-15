/* Simple thing for experimenting with various forms of static
   analysis. */
#include <ctype.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include "libvex_alloc.h"
#include "libvex_ir.h"
#include "libvex_guest_offsets.h"
#include "sli.h"
#include "map.h"

#include <map>

class Function;
class Oracle;

/* Liveness and aliasing only consder the first @NR_REGS registers. */
#define NR_REGS 16

class LivenessSet : public Named {
public:
	unsigned long mask;

	LivenessSet() : mask(0) {}

	LivenessSet use(Int offset);
	LivenessSet define(Int offset);

	void operator |=(const LivenessSet x) { mask |= x.mask; }
	bool operator !=(const LivenessSet x) { return mask != x.mask; }
	LivenessSet operator &(const LivenessSet x) { return LivenessSet(mask & x.mask); }
	static LivenessSet everything;
	static LivenessSet argRegisters;
private:
	LivenessSet(unsigned long _m) : mask(_m) {}
	char *mkName() const {
		int i;
		char *acc;
		char *acc2;
		bool first = true;
		acc = strdup("<");
		for (i = 0; i < NR_REGS; i++) {
			if (!(mask & (1ul << i)))
				continue;
			if (!first) {
				acc2 = my_asprintf("%s|", acc);
				free(acc);
				acc = acc2;
			}
			first = false;
			switch (i * 8) {
#define do_reg(name) case OFFSET_amd64_ ## name : acc2 = my_asprintf("%s" #name , acc); break
				do_reg(RAX);
				do_reg(RDX);
				do_reg(RCX);
				do_reg(RBX);
				do_reg(RSP);
				do_reg(RBP);
				do_reg(RSI);
				do_reg(RDI);
				do_reg(R8);
				do_reg(R9);
				do_reg(R10);
				do_reg(R11);
				do_reg(R12);
				do_reg(R13);
				do_reg(R14);
				do_reg(R15);
			default:
				abort();
			}
			free(acc);
			acc = acc2;
		}
		acc2 = my_asprintf("%s>", acc);
		free(acc);
		return acc2;
	}
};

LivenessSet LivenessSet::everything(~0ul);
LivenessSet LivenessSet::argRegisters(
	0x01 | /* rax -- not strictly an arg register, but treated
	       as one for variadic functions. */
	0x02 | /* rcx */
	0x04 | /* rdx */
     /* 0x08 |    rbx */
	0x10 | /* rsp -- not an argument register, but almost certainly
		truly live on function entry */
     /* 0x20 |    rbp */
	0x40 | /* rsi */
	0x80 | /* rdi */
       0x100 | /* r8 */
       0x200 | /* r9 */
       0x400   /* r10 -- technically static chain rather than a true
		  argument, but they're the same thing for our
		  purposes. */
    /* 0x800 |   r11 */
	);

LivenessSet
LivenessSet::use(Int offset)
{
	if (offset >= 8 * NR_REGS)
		return *this;
	else
		return LivenessSet(mask | (1ul << (offset / 8)));
}

LivenessSet
LivenessSet::define(Int offset)
{
	if (offset >= 8 * NR_REGS)
		return *this;
	else
		return LivenessSet(mask & ~(1ul << (offset / 8)));
}

/* Pointer aliasing stuff.  Note that ``stack'' in this context means
   the *current* stack frame: a pointer without the stack bit set
   could still point into a *calling* functions' stack frame, and that
   wouldn't be a bug. */
class PointerAliasingSet : public Named {
	int v;
	char *mkName() const {
		const char *r;
		switch (v) {
		case 0:
			r = "()";
			break;
		case 1:
			r = "not-a-pointer";
			break;
		case 2:
			r = "stack-pointer";
			break;
		case 3:
			r = "not-a-pointer|stack-pointer";
			break;
		case 4:
			r = "non-stack-pointer";
			break;
		case 5:
			r = "not-a-pointer|non-stack-pointer";
			break;
		case 6:
			r = "stack-pointer|non-stack-pointer";
			break;
		case 7:
			r = "*";
			break;
		default:
			abort();
		}
		return strdup(r);
	}
	PointerAliasingSet(int _v) : v(_v) {}
public:

	PointerAliasingSet() : v(0) {}
	static const PointerAliasingSet notAPointer;
	static const PointerAliasingSet stackPointer;
	static const PointerAliasingSet nonStackPointer;
	static const PointerAliasingSet anything;

	PointerAliasingSet operator |(PointerAliasingSet o) const { return PointerAliasingSet(v | o.v); }
	PointerAliasingSet operator &(PointerAliasingSet o) const { return PointerAliasingSet(v & o.v); }
	bool operator !=(PointerAliasingSet o) const { return v != o.v; }
	operator bool() const { return v != 0; }
};

const PointerAliasingSet PointerAliasingSet::notAPointer(1);
const PointerAliasingSet PointerAliasingSet::stackPointer(2);
const PointerAliasingSet PointerAliasingSet::nonStackPointer(4);
const PointerAliasingSet PointerAliasingSet::anything(7);

class RegisterAliasingConfiguration {
	RegisterAliasingConfiguration(float x); /* initialise as function entry configuration */
public:
	RegisterAliasingConfiguration() : stackHasLeaked(false) {}
	PointerAliasingSet v[NR_REGS];
	bool stackHasLeaked;

	void operator|=(const RegisterAliasingConfiguration &src) {
		stackHasLeaked |= src.stackHasLeaked;
		for (int i = 0; i < NR_REGS; i++)
			v[i] = v[i] | src.v[i];
	}
	bool operator != (const RegisterAliasingConfiguration &x) const {
		if (stackHasLeaked != x.stackHasLeaked)
			return true;
		for (int i = 0; i < NR_REGS; i++)
			if (v[i] != x.v[i])
				return true;
		return false;
	}
	/* This should be const, but C++ can't quite manage the
	 * initialisation in that case, poor thing. */
	static RegisterAliasingConfiguration functionEntryConfiguration;

	void prettyPrint(FILE *) const;
};
RegisterAliasingConfiguration RegisterAliasingConfiguration::functionEntryConfiguration(5.3f);
RegisterAliasingConfiguration::RegisterAliasingConfiguration(float f)
{
	stackHasLeaked = false;
	v[1] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer; /* rcx */
	v[2] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer; /* rdx */
	v[4] = PointerAliasingSet::stackPointer; /* rsp */
	v[6] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer; /* rsi */
	v[7] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer; /* rdi */
	v[8] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer; /* r8 */
	v[9] = PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer; /* r9 */
}

void
RegisterAliasingConfiguration::prettyPrint(FILE *f) const
{
	for (int i = 0; i < NR_REGS; i++)
		fprintf(f, "\t%8d: %s\n", i, v[i].name());
}

class Instruction : public GarbageCollected<Instruction, &ir_heap>, public Named {
	IRStmt **statements;
	IRTypeEnv *tyenv;
	int nr_statements;
public:
	unsigned long rip;
	unsigned long _fallThroughRip;
	unsigned long _branchRip;
	unsigned long _calleeRip;
	Instruction *branch;
	Instruction *fallThrough;
	Function *callee;

	LivenessSet liveOnEntry;
	RegisterAliasingConfiguration aliasOnEntry;

protected:
	char *mkName() const { return my_asprintf("%lx", rip); }
public:
	Instruction(unsigned long rip, IRStmt **content, int nr_statements,
		    IRTypeEnv *_tyenv);
	void resolveSuccessors(Function *f);
	void resolveCallGraph(Oracle *oracle);

	void updateLiveOnEntry(bool *changed);
	void updateSuccessorInstructionsAliasing(std::vector<Instruction *> *changed);

	void visit(HeapVisitor &hv) { hv(statements); hv(branch); hv(fallThrough); hv(callee); hv(tyenv); }
	NAMED_CLASS
};

class Function : public GarbageCollected<Function>, public Named {
public:
	typedef gc_heap_map<unsigned long, Instruction, &ir_heap>::type instr_map_t;

	unsigned long rip;
	VexPtr<instr_map_t, &ir_heap> instructions;

protected:
	char *mkName() const { return my_asprintf("%lx", rip); }
public:
	Function(unsigned long _rip) :
		rip(_rip),
		instructions(new instr_map_t())
	{}

	void resolveCallGraph(Oracle *oracle);
	bool hasInstruction(unsigned long rip) const { return instructions->hasKey(rip); }
	void addInstruction(Instruction *i) { instructions->set(i->rip, i); }
	Instruction *ripToInstruction(unsigned long rip) { return instructions->get(rip); }
	void calculateRegisterLiveness(bool *done_something);
	void calculateAliasing(bool *done_something);

	void visit(HeapVisitor &hv) { }
	NAMED_CLASS
};

class Oracle : public GarbageCollected<Oracle> {
	std::vector<unsigned long> unprocessedRoots;

	gc_heap_map<unsigned long, Function>::type *addrToFunctions;

	void processRoot(unsigned long x);
	void calculateRegisterLiveness(void);
	void calculateAliasing(void);
public:
	MachineState *ms;

	Oracle(MachineState *_ms)
		: addrToFunctions(new gc_heap_map<unsigned long, Function>::type()),
		  ms(_ms)
	{
	}

	Function *get_function(unsigned long rip) { return addrToFunctions->get(rip); }
	void add_root(unsigned long root);
	void calculate(void);
	void list_functions(std::vector<Function *> *heads) {
		heads->clear();
		for (gc_heap_map<unsigned long, Function>::type::iterator i = addrToFunctions->begin();
		     i != addrToFunctions->end();
		     i++)
			heads->push_back(i.value());
	}
	void visit(HeapVisitor &hv) { hv(ms); hv(addrToFunctions); }
	NAMED_CLASS
};

void
Oracle::add_root(unsigned long root)
{
	unprocessedRoots.push_back(root);
}

void
Oracle::calculate(void)
{
	while (!unprocessedRoots.empty()) {
		unsigned long x = unprocessedRoots.back();
		unprocessedRoots.pop_back();
		processRoot(x);
	}
	for (gc_heap_map<unsigned long, Function>::type::iterator it = addrToFunctions->begin();
	     it != addrToFunctions->end();
	     it++)
		it.value()->resolveCallGraph(this);
	calculateRegisterLiveness();
	calculateAliasing();
}

void
Oracle::processRoot(unsigned long x)
{
	if (addrToFunctions->hasKey(x)) {
		/* Already done */
		return;
	}

	printf("Discovered function at %lx\n", x);

	Function *work = new Function(x);

	/* Start by building a CFG of the function's instructions. */
	std::vector<unsigned long> unexplored;
	unexplored.push_back(x);
	while (!unexplored.empty()) {
		unsigned long rip = unexplored.back();
		unexplored.pop_back();

		if (work->hasInstruction(rip))
			continue;
		IRSB *irsb = ms->addressSpace->getIRSBForAddress(99, rip);
		if (!irsb) {
			printf("WARNING: No IRSB for %lx!\n", rip);
			continue;
		}
		assert(irsb->stmts[0]->tag == Ist_IMark);
		int end_of_instruction;
		for (end_of_instruction = 1;
		     end_of_instruction < irsb->stmts_used && irsb->stmts[end_of_instruction]->tag != Ist_IMark;
		     end_of_instruction++)
			;
		Instruction *i = new Instruction(rip, irsb->stmts + 1, end_of_instruction - 1, irsb->tyenv);
		if (end_of_instruction == irsb->stmts_used) {
			if (irsb->jumpkind == Ijk_Call) {
				i->_fallThroughRip = extract_call_follower(irsb);
				if (irsb->next->tag == Iex_Const)
					i->_calleeRip = irsb->next->Iex.Const.con->Ico.U64;
			} else {
				if (irsb->next->tag == Iex_Const)
					i->_fallThroughRip = irsb->next->Iex.Const.con->Ico.U64;
			}
		} else {
			i->_fallThroughRip = irsb->stmts[end_of_instruction]->Ist.IMark.addr;
		}
		work->addInstruction(i);
		if (i->_fallThroughRip)
			unexplored.push_back(i->_fallThroughRip);
		if (i->_branchRip)
			unexplored.push_back(i->_branchRip);
		if (i->_calleeRip)
			unprocessedRoots.push_back(i->_calleeRip);
	}

	/* Now go through and set successor pointers etc. */
	for (Function::instr_map_t::iterator it = work->instructions->begin();
	     it != work->instructions->end();
	     it++) {
		Instruction *i = it.value();
		i->resolveSuccessors(work);
	}
	addrToFunctions->set(work->rip, work);
}

void
Oracle::calculateRegisterLiveness(void)
{
	bool done_something;

	do {
		done_something = false;
		for (gc_heap_map<unsigned long, Function>::type::iterator it = addrToFunctions->begin();
		     it != addrToFunctions->end();
		     it++)
			it.value()->calculateRegisterLiveness(&done_something);
	} while (done_something);
}

void
Oracle::calculateAliasing(void)
{
	bool done_something;

	for (gc_heap_map<unsigned long, Function>::type::iterator it = addrToFunctions->begin();
	     it != addrToFunctions->end();
	     it++) {
		do {
			done_something = false;
			it.value()->calculateAliasing(&done_something);
		} while (done_something);
	}
}

void
Function::resolveCallGraph(Oracle *oracle)
{
	for (instr_map_t::iterator it = instructions->begin();
	     it != instructions->end();
	     it++)
		it.value()->resolveCallGraph(oracle);
}

void
Function::calculateRegisterLiveness(bool *done_something)
{
	for (instr_map_t::iterator it = instructions->begin();
	     it != instructions->end();
	     it++)
		it.value()->updateLiveOnEntry(done_something);
}

void
Function::calculateAliasing(bool *done_something)
{
	Instruction *head = instructions->get(rip);
	RegisterAliasingConfiguration a(head->aliasOnEntry);
	a |= RegisterAliasingConfiguration::functionEntryConfiguration;
	if (head->aliasOnEntry != a) {
		*done_something = true;
		head->aliasOnEntry = a;
	}

	std::vector<Instruction *> needsUpdating;
	for (instr_map_t::iterator it = instructions->begin();
	     it != instructions->end();
	     it++)
		it.value()->updateSuccessorInstructionsAliasing(&needsUpdating);
	while (!needsUpdating.empty()) {
		*done_something = true;
		Instruction *i = needsUpdating.back();
		needsUpdating.pop_back();
		i->updateSuccessorInstructionsAliasing(&needsUpdating);
	}
}

Instruction::Instruction(unsigned long _rip, IRStmt **stmts, int nr_stmts, IRTypeEnv *_tyenv)
	: statements((IRStmt **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_stmts)),
	  tyenv(_tyenv),
	  nr_statements(nr_stmts),
	  rip(_rip)
{
	for (int i = 0; i < nr_statements; i++) {
		statements[i] = stmts[i];
		if (statements[i]->tag == Ist_Exit)
			_branchRip = statements[i]->Ist.Exit.dst->Ico.U64;
	}
}

void
Instruction::resolveSuccessors(Function *f)
{
	if (_fallThroughRip) {
		fallThrough = f->ripToInstruction(_fallThroughRip);
		assert(fallThrough);
	}
	if (_branchRip) {
		branch = f->ripToInstruction(_branchRip);
		assert(branch);
	}
}

void
Instruction::resolveCallGraph(Oracle *oracle)
{
	if (_calleeRip) {
		callee = oracle->get_function(_calleeRip);
		assert(callee);
	}
}

static LivenessSet
irexprUsedValues(LivenessSet old, IRExpr *w)
{
	if (!w)
		return old;
	switch (w->tag) {
	case Iex_Binder:
		return old;
	case Iex_Get:
		return old.use(w->Iex.Get.offset);
	case Iex_GetI:
		return LivenessSet::everything;
	case Iex_RdTmp:
		return old;
	case Iex_Qop:
		old = irexprUsedValues(old, w->Iex.Qop.arg4);
	case Iex_Triop:
		old = irexprUsedValues(old, w->Iex.Qop.arg3);
	case Iex_Binop:
		old = irexprUsedValues(old, w->Iex.Qop.arg2);
	case Iex_Unop:
		return irexprUsedValues(old, w->Iex.Qop.arg1);
	case Iex_Load:
		return irexprUsedValues(old, w->Iex.Load.addr);
	case Iex_Const:
		return old;
	case Iex_CCall:
		for (int i = 0; w->Iex.CCall.args[i]; i++)
			old = irexprUsedValues(old, w->Iex.CCall.args[i]);
		return old;
	case Iex_Mux0X:
		old = irexprUsedValues(old, w->Iex.Mux0X.cond);
		old = irexprUsedValues(old, w->Iex.Mux0X.expr0);
		old = irexprUsedValues(old, w->Iex.Mux0X.exprX);
		return old;
	case Iex_Associative:
		for (int i = 0; i < w->Iex.Associative.nr_arguments; i++)
			old = irexprUsedValues(old, w->Iex.Associative.contents[i]);
		return old;
	}
	abort();
}

void
Instruction::updateLiveOnEntry(bool *changed)
{
	LivenessSet res;

	if (callee) {
		res = callee->instructions->get(callee->rip)->liveOnEntry & LivenessSet::argRegisters;
		if (fallThrough)
			res |= fallThrough->liveOnEntry;
	} else if (fallThrough)
		res = fallThrough->liveOnEntry;
	for (int i = nr_statements - 1; i >= 0; i--) {
		switch (statements[i]->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			abort();
		case Ist_AbiHint:
			break;
		case Ist_Put:
			res = res.define(statements[i]->Ist.Put.offset);
			res = irexprUsedValues(res, statements[i]->Ist.Put.data);
			break;
		case Ist_PutI:
			res = irexprUsedValues(res, statements[i]->Ist.PutI.data);
			res = irexprUsedValues(res, statements[i]->Ist.PutI.ix);
			break;
		case Ist_WrTmp:
			res = irexprUsedValues(res, statements[i]->Ist.WrTmp.data);
			break;
		case Ist_Store:
			res = irexprUsedValues(res, statements[i]->Ist.Store.data);
			res = irexprUsedValues(res, statements[i]->Ist.Store.addr);
			break;
		case Ist_CAS:
			res = irexprUsedValues(res, statements[i]->Ist.CAS.details->addr);
			res = irexprUsedValues(res, statements[i]->Ist.CAS.details->expdHi);
			res = irexprUsedValues(res, statements[i]->Ist.CAS.details->expdLo);
			res = irexprUsedValues(res, statements[i]->Ist.CAS.details->dataHi);
			res = irexprUsedValues(res, statements[i]->Ist.CAS.details->dataLo);
			break;
		case Ist_Dirty:
			res = irexprUsedValues(res, statements[i]->Ist.Dirty.details->guard);
			for (int j = 0; statements[i]->Ist.Dirty.details->args[j]; j++)
				res = irexprUsedValues(res, statements[i]->Ist.Dirty.details->args[j]);
			res = irexprUsedValues(res, statements[i]->Ist.Dirty.details->mAddr);
			break;
		case Ist_MBE:
			abort();
		case Ist_Exit:
			if (branch)
				res |= branch->liveOnEntry;
			res = irexprUsedValues(res, statements[i]->Ist.Exit.guard);
			break;
		default:
			abort();
		}
	}
	if (res != liveOnEntry)
		*changed = true;
	liveOnEntry = res;
}

static PointerAliasingSet
irexprAliasingClass(IRExpr *expr,
		    IRTypeEnv *tyenv,
		    const RegisterAliasingConfiguration &config,
		    std::map<IRTemp, PointerAliasingSet> &temps)
{
	if (typeOfIRExpr(tyenv, expr) != Ity_I64)
		/* Not a 64 bit value -> not a pointer */
		return PointerAliasingSet::notAPointer;

	switch (expr->tag) {
	case Iex_Get:
		if (expr->Iex.Get.offset < NR_REGS * 8)
			return config.v[expr->Iex.Get.offset / 8];
		else {
			/* Assume that those are the only pointer registers */
			return PointerAliasingSet::notAPointer;
		}
	case Iex_RdTmp:
		return temps[expr->Iex.RdTmp.tmp];
	case Iex_Const:
		return PointerAliasingSet::notAPointer | PointerAliasingSet::nonStackPointer;
	case Iex_Unop:
		switch (expr->Iex.Unop.op) {
		case Iop_8Uto64:
		case Iop_8Sto64:
		case Iop_16Uto64:
		case Iop_16Sto64:
		case Iop_32Uto64:
		case Iop_32Sto64:
		case Iop_128to64:
		case Iop_128HIto64:
		case Iop_V128to64:
		case Iop_V128HIto64:
		case Iop_Not64:
			return PointerAliasingSet::notAPointer;
		default:
			break;
		}
		break;
	case Iex_Binop: {
		PointerAliasingSet a1 = irexprAliasingClass(expr->Iex.Binop.arg1,
							    tyenv,
							    config,
							    temps);
		PointerAliasingSet a2 = irexprAliasingClass(expr->Iex.Binop.arg2,
							    tyenv,
							    config,
							    temps);
		switch (expr->Iex.Binop.op) {
		case Iop_Sub64:
			/* x - y is a pointer to zone A if x is a
			 * pointer to zone A and y is not a pointer of
			 * any sort.  Otherwise, it's just not a
			 * pointer. */ {
			PointerAliasingSet res;
			if (a2 & PointerAliasingSet::notAPointer) {
				res = a1;
				if (a2 & (PointerAliasingSet::stackPointer |
					  PointerAliasingSet::nonStackPointer))
					res = res | PointerAliasingSet::notAPointer;
			} else {
				res = PointerAliasingSet::notAPointer;
			}
			return res;
		}
		case Iop_Add64:
		case Iop_And64:
		case Iop_Xor64:
		case Iop_Or64:
			return a1 | a2;
		case Iop_Shl64:
		case Iop_Shr64:
		case Iop_Sar64:
		case Iop_Mul64:
		case Iop_MullU32:
		case Iop_MullS32:
		case Iop_F64toI64:
		case Iop_32HLto64:
		case Iop_DivModU64to32:
			return PointerAliasingSet::notAPointer;
		default:
			break;
		}
		break;
	}
	case Iex_Mux0X:
		return irexprAliasingClass(expr->Iex.Mux0X.expr0,
					   tyenv,
					   config,
					   temps) |
			irexprAliasingClass(expr->Iex.Mux0X.exprX,
					    tyenv,
					    config,
					    temps);
	case Iex_Associative:
		switch (expr->Iex.Associative.op) {
		case Iop_Add64: {
			PointerAliasingSet res;
			for (int i = 0; i < expr->Iex.Associative.nr_arguments; i++) {
				if (expr->Iex.Associative.contents[i]->tag != Iex_Const)
					res = res | irexprAliasingClass(expr->Iex.Associative.contents[i],
									tyenv,
									config,
									temps);
			}
			if (!(res & PointerAliasingSet::anything))
				res = PointerAliasingSet::notAPointer;
			return res;
		}
		default:
			break;
		}
		break;

	case Iex_CCall:
		if (!strcmp(expr->Iex.CCall.cee->name, "amd64g_calculate_rflags_c") ||
		    !strcmp(expr->Iex.CCall.cee->name, "amd64g_calculate_rflags_all"))
			return PointerAliasingSet::notAPointer;
		break;

	default:
		break;
	}
	printf("Don't know how to compute aliasing sets for ");
	ppIRExpr(expr, stdout);
	printf("\n");
	return PointerAliasingSet::anything;
}

void
Instruction::updateSuccessorInstructionsAliasing(std::vector<Instruction *> *changed)
{
	RegisterAliasingConfiguration config(aliasOnEntry);
	std::map<IRTemp, PointerAliasingSet> temporaryAliases;
	IRStmt *st;

	for (int i = 0; i < nr_statements; i++) {
		st = statements[i];
		switch (st->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			abort();
		case Ist_AbiHint:
			break;
		case Ist_Put:
			if (st->Ist.Put.offset < NR_REGS * 8 &&
			    st->Ist.Put.offset != OFFSET_amd64_RSP) {
				config.v[st->Ist.Put.offset / 8] =
					irexprAliasingClass(st->Ist.Put.data,
							    tyenv,
							    config, temporaryAliases);
			}
			break;
		case Ist_PutI:
			/* Assume that PutIs never target the NR_REGS registers */
			break;
		case Ist_WrTmp:
			temporaryAliases[st->Ist.WrTmp.tmp] =
				irexprAliasingClass(st->Ist.WrTmp.data,
						    tyenv,
						    config,
						    temporaryAliases);
			break;
		case Ist_Store:
			if (!config.stackHasLeaked) {
				PointerAliasingSet addr, data;
				addr = irexprAliasingClass(st->Ist.Store.data,
							   tyenv,
							   config,
							   temporaryAliases);
				data = irexprAliasingClass(st->Ist.Store.data,
							   tyenv,
							   config,
							   temporaryAliases);
				if ((addr & PointerAliasingSet::nonStackPointer) &&
				    (data & PointerAliasingSet::stackPointer))
					config.stackHasLeaked = true;
			}
			break;
		case Ist_CAS:
			temporaryAliases[st->Ist.CAS.details->oldLo] =
				PointerAliasingSet::anything;
			break;
		case Ist_Dirty: {
			PointerAliasingSet res;
			if (tyenv->types[st->Ist.Dirty.details->tmp] == Ity_I64) {
				if (!strcmp(st->Ist.Dirty.details->cee->name,
					    "helper_load_64")) {
					if (config.stackHasLeaked)
						res = PointerAliasingSet::anything;
					else
						res = PointerAliasingSet::notAPointer |
							PointerAliasingSet::nonStackPointer;
				} else {
					res = PointerAliasingSet::anything;
				}
			} else {
				res = PointerAliasingSet::notAPointer;
			}
			temporaryAliases[st->Ist.Dirty.details->tmp] = res;
			break;
		}
		case Ist_MBE:
			abort();
		case Ist_Exit: {
			if (branch) {
				RegisterAliasingConfiguration newExitConfig(branch->aliasOnEntry);
				newExitConfig |= config;
				if (newExitConfig != branch->aliasOnEntry) {
					changed->push_back(branch);
					branch->aliasOnEntry = newExitConfig;
				}
			}
			break;
		}
		default:
			abort();
		}
	}
	if (fallThrough) {
		if (callee) {
			LivenessSet ls = callee->instructions->get(callee->rip)->liveOnEntry;
			/* If any of the argument registers contain
			   stack pointers on entry, the return value
			   can potentially also contain stack
			   pointers. */
			/* This isn't perfectly accurate, but it's a
			   pretty close approximation. */
			bool stackEscapes = false;
			/* rcx = 2, rdx = 4, rsi = 0x40, rdi = 0x80,
			 * r8 = 0x100, r9 = 0x200 */
#define ARG_REGISTERS 0x3c6
			for (int i = 0; !stackEscapes && i < NR_REGS; i++) {
				if (!(ARG_REGISTERS & (1 << i)))
					continue;
				if (!(ls.mask & (1 << i)))
					continue;
				if (config.v[i] & PointerAliasingSet::stackPointer)
					stackEscapes = true;
			}
#undef ARG_REGISTERS
			config.v[0] = PointerAliasingSet::notAPointer;
			if (stackEscapes)
				config.v[0] = config.v[0] | PointerAliasingSet::stackPointer;
			config.v[0] = config.v[0] | PointerAliasingSet::nonStackPointer;
		}
		config |= fallThrough->aliasOnEntry;
		if (config != fallThrough->aliasOnEntry) {
			changed->push_back(fallThrough);
			fallThrough->aliasOnEntry = config;
		}
	}
}

/* Read a whole line into the GC heap */
static char *
read_line(FILE *f)
{
	size_t acc_size;
	size_t used;
	char *acc;
	int c;

	acc_size = 128;
	acc = (char *)LibVEX_Alloc_Bytes(acc_size);
	used = 0;
	while (1) {
		c = fgetc(f);
		if (c == '\n' || c == EOF)
			break;
		acc[used] = c;
		used++;
		if (used == acc_size) {
			acc_size *= 2;
			acc = (char *)LibVEX_realloc(&main_heap, acc, acc_size);
		}
	}
	if (c == EOF) {
		if (used == 0 || ferror(f))
			return NULL;
	}
	acc[used] = 0;
	return acc;
}

class BadParseException {
};

class Word : public GarbageCollected<Word>, public Named {
protected:
	char *mkName() const { return strdup(content); }
public:
	char *content;
	Word(const char *c, int len) {
		content = (char *)LibVEX_Alloc_Bytes(len + 1);
		memcpy(content, c, len);
		content[len] = 0;
	}
	bool operator==(const char *p) const {
		return strcmp(content, p) == 0;
	}
	operator unsigned long() const {
		if (!this) {
			printf("Not enough arguments\n");
			throw BadParseException();
		}
		errno = 0;
		char *end;
		unsigned long r = strtol(content, &end, 0);
		if (errno != 0 || *end != 0) {
			printf("Expected number; got %s\n", content);
			throw BadParseException();
		}
		return r;
	}
	void visit(HeapVisitor &hv) { hv(content); }
	NAMED_CLASS
};

static Word **
find_words(char *command)
{
	int i;
	int nr_words;
	int j;

	nr_words = 0;
	i = 0;
	while (1) {
		/* Find the start of the current word. */
		while (isspace(command[i]))
			i++;
		if (command[i] == 0)
			break;
		/* We have another word. */
		nr_words++;
		/* And now find its end */
		while (!isspace(command[i]) && command[i])
			i++;
	}

	Word **res;
	res = (Word **)__LibVEX_Alloc_Ptr_Array(&main_heap, nr_words + 1);
	j = 0;
	i = 0;
	nr_words = 0;
	while (1) {
		/* Find the start of the word */
		while (isspace(command[i]))
			i++;
		if (command[i] == 0)
			break;
		/* Now find the end. */
		j = i;
		while (!isspace(command[j]) && command[j])
			j++;
		res[nr_words] = new Word(command + i, j - i);
		nr_words++;
		i = j;
	}
	res[nr_words] = NULL;
	return res;
}

static void
list_heads(Oracle *oracle)
{
	std::vector<Function *> f;

	oracle->list_functions(&f);
	for (std::vector<Function *>::iterator it = f.begin();
	     it != f.end();
	     it++)
		printf("%s\n", (*it)->name());
}

static void
run_command(Oracle *oracle)
{
	printf("\n> ");
	fflush(stdout);
	char *command = read_line(stdin);
	if (!command)
		exit(0);
	Word **words = find_words(command);	

	if (*words[0] == "add_root") {
		oracle->add_root(*words[1]);
	} else if (*words[0] == "doit") {
		oracle->calculate();
	} else if (*words[0] == "list_heads") {
		list_heads(oracle);
	} else if (*words[0] == "liveness") {
		Function *f = oracle->get_function(*words[1]);
		if (!f) {
			printf("No function at %s\n", words[1]->name());
		} else {
			printf("%s\n", f->instructions->get(f->rip)->liveOnEntry.name());
		}
	} else if (*words[0] == "alias") {
		Function *f = oracle->get_function(*words[1]);
		if (!f) {
			printf("No function at %s\n", words[1]->name());
		} else {
			Instruction *i = f->instructions->get(*words[2]);
			printf("Alias table for %lx:%lx:\n", (unsigned long)*words[1],
			       (unsigned long)*words[2]);
			i->aliasOnEntry.prettyPrint(stdout);
		}
	} else {
		printf("Unknown command %s\n", words[0]->content);
	}
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readCoredump(argv[1]));
	VexPtr<Oracle> oracle(new Oracle(ms));

	while (1) {
		LibVEX_maybe_gc(ALLOW_GC);
		try {
			run_command(oracle);
		} catch (BadParseException e) {
		}
	}
}
