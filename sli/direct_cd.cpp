/* Re-implementation of direct which tries to work off of just a core
   dump, rather than needing the full trace. */
#include <err.h>

#include <queue>
#include <map>
#include <set>

#include "sli.h"

class PrettyPrintable {
public:
	void prettyPrint(void) const { prettyPrint(stdout); }
	virtual void prettyPrint(FILE *f) const = 0;
};

/* Perform simple peephole optimisation on the IRExpr.  The resulting
   expression is guaranteed to be equivalent to the old one in any
   context.  We may mutate the expression in-place, which is okay
   because there are no semantic changes. */
static IRExpr *optimiseIRExpr(IRExpr *e);

class StateMachine : public GarbageCollected<StateMachine>, public PrettyPrintable {
public:
	/* Another peephole optimiser.  Again, must be
	   context-independent and result in no changes to the
	   semantic value of the machine, and can mutate in-place. */
	virtual StateMachine *optimise() = 0;
	NAMED_CLASS
};

class StateMachineSideEffect : public PrettyPrintable {
	StateMachineSideEffect(IRExpr *_addr, IRExpr *_data)
		: addr(_addr), data(_data)
	{
	}
public:
	StateMachineSideEffect() : addr(NULL), data(NULL) {}
	IRExpr *addr;
	IRExpr *data;
	void prettyPrint(FILE *f) const {
		fprintf(f, "*(");
		ppIRExpr(addr, f);
		fprintf(f, ") <- ");
		ppIRExpr(data, f);
	}
	static StateMachineSideEffect store(IRExpr *addr, IRExpr *data) {
		return StateMachineSideEffect(addr, data);
	}
	void visit(HeapVisitor &hv) {
		hv(addr);
		hv(data);
	}
	void optimise() {
		addr = optimiseIRExpr(addr);
		data = optimiseIRExpr(data);
	}
};

class StateMachineEdge : public GarbageCollected<StateMachineEdge>, public PrettyPrintable {
public:
	StateMachineEdge(StateMachine *t) : target(t) {}
	StateMachine *target;
	std::vector<StateMachineSideEffect> sideEffects;

	void prependSideEffect(const StateMachineSideEffect &k) {
		std::vector<StateMachineSideEffect> n;
		n.reserve(sideEffects.size() + 1);
		n.push_back(k);
		for (std::vector<StateMachineSideEffect>::iterator it = sideEffects.begin();
		     it != sideEffects.end();
		     it++)
			n.push_back(*it);
		sideEffects = n;
	}

	void prettyPrint(FILE *f) const {
		if (sideEffects.size() != 0) {
			fprintf(f, "{");
			bool b = true;
			for (std::vector<StateMachineSideEffect>::const_iterator it = sideEffects.begin();
			     it != sideEffects.end();
			     it++) {
				if (!b)
					fprintf(f, "; ");
				b = false;
				it->prettyPrint(f);
			}
			fprintf(f, "} ");
		}
		fprintf(f, "%p", target);
	}
	void visit(HeapVisitor &hv) {
		hv(target);
		for (std::vector<StateMachineSideEffect>::iterator it = sideEffects.begin();
		     it != sideEffects.end();
		     it++)
			it->visit(hv);
	}
	StateMachineEdge *optimise();
	NAMED_CLASS
};

class StateMachineCrash : public StateMachine {
	StateMachineCrash() {}
	static VexPtr<StateMachineCrash> _this;
public:
	static StateMachineCrash *get() {
		if (!_this) _this = new StateMachineCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<crash>"); }
	StateMachine *optimise() { return this; }
	void visit(HeapVisitor &hv) {}
};
VexPtr<StateMachineCrash> StateMachineCrash::_this;

class StateMachineNoCrash : public StateMachine {
	StateMachineNoCrash() {}
	static VexPtr<StateMachineNoCrash> _this;
public:
	static StateMachineNoCrash *get() {
		if (!_this) _this = new StateMachineNoCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<survive>"); }
	StateMachine *optimise() { return this; }
	void visit(HeapVisitor &hv) {}
};
VexPtr<StateMachineNoCrash> StateMachineNoCrash::_this;

class StateMachineBifurcate : public StateMachine {
public:
	StateMachineBifurcate(IRExpr *_condition,
			      StateMachineEdge *t,
			      StateMachineEdge *f)
		: condition(_condition),
		  trueTarget(t),
		  falseTarget(f)
	{
	}	
	StateMachineBifurcate(IRExpr *_condition,
			      StateMachine *t,
			      StateMachine *f)
		: condition(_condition),
		  trueTarget(new StateMachineEdge(t)),
		  falseTarget(new StateMachineEdge(f))
	{
	}

	IRExpr *condition; /* Should be typed Ity_I1.  If zero, we go
			      to the false target.  Otherwise, we go
			      to the true one. */
	StateMachineEdge *trueTarget;
	StateMachineEdge *falseTarget;

	void prettyPrint(FILE *f) const {
		fprintf(f, "if (");
		ppIRExpr(condition, f);
		fprintf(f, ") then {");
		trueTarget->prettyPrint(f);
		fprintf(f, "} else {");
		falseTarget->prettyPrint(f);
		fprintf(f, "}");
	}
	void visit(HeapVisitor &hv)
	{
		hv(trueTarget);
		hv(falseTarget);
		hv(condition);
	}
	StateMachine *optimise()
	{
		condition = optimiseIRExpr(condition);
		trueTarget = trueTarget->optimise();
		falseTarget = falseTarget->optimise();
		return this;
	}
};

/* A state machine node which always advances to another one.  These
   can be safely eliminated, but they're sometimes kind of handy when
   you're building the machine. */
class StateMachineProxy : public StateMachine {
public:
	StateMachineEdge *target;

	StateMachineProxy(StateMachine *t)
		: target(new StateMachineEdge(t))
	{
	}
	StateMachineProxy(StateMachineEdge *t)
		: target(t)
	{
	}
	void prettyPrint(FILE *f) const
	{
		target->prettyPrint(f);
	}
	void visit(HeapVisitor &hv)
	{
		hv(target);
	}
	StateMachine *optimise()
	{
		if (target->sideEffects.size() == 0)
			return target->target->optimise();
		target = target->optimise();
		return this;
	}
};

/* A node in the state machine representing a bit of code which we
   haven't explored yet. */
class StateMachineStub : public StateMachine {
public:
	IRExpr *target;

	StateMachineStub(IRExpr *t) : target(t) {}

	void prettyPrint(FILE *f) const
	{
		fprintf(f, "<jmp ");
		ppIRExpr(target, f);
		fprintf(f, ">");
	}
	void visit(HeapVisitor &hv) { hv(target); }
	StateMachine *optimise() { return this; }
};

StateMachineEdge *
StateMachineEdge::optimise()
{
	if (StateMachineProxy *smp =
	    dynamic_cast<StateMachineProxy *>(target)) {
		StateMachineEdge *sme =
			new StateMachineEdge(smp->target->target);
		sme->sideEffects = sideEffects;
		for (std::vector<StateMachineSideEffect>::iterator it =
			     smp->target->sideEffects.begin();
		     it != smp->target->sideEffects.end();
		     it++)
			sme->sideEffects.push_back(*it);
		return sme->optimise();
	}
	target = target->optimise();
	for (std::vector<StateMachineSideEffect>::iterator it = sideEffects.begin();
	     it != sideEffects.end();
	     it++)
		it->optimise();
	return this;
}

/* A VEX RIP combines an ordinary machine code RIP with an offset into
   a VEX IRSB.  An idx of 0 corresponds to just before the start of
   the block, and stmts_used corresponds to just after the end. */
class VexRip : public Named {
protected:
	char *mkName() const { return my_asprintf("%lx:%x", rip, idx); }
public:
	VexRip(unsigned long _rip, unsigned _idx) : rip(_rip), idx(_idx) {}
	unsigned long rip;
	unsigned idx;	
	void changedIdx() { clearName(); }
	bool operator<(const VexRip &a) const {
		return rip < a.rip || (rip == a.rip && idx < a.idx);
	}
	bool operator==(const VexRip &a) const {
		return rip == a.rip && idx == a.idx;
	}
};

class CrashReason : public GarbageCollected<CrashReason>,
		    public PrettyPrintable {
public:
	/* A crash reason represents a summary of information which is
	   believed to be relevant in explaining a crash.  It consists
	   of state machine and a rip, such that the state machine
	   will evaluate to 0 if we're likely to crash and 1 if we're
	   not. */	   
	VexRip rip;
	StateMachine *sm;

	CrashReason(const VexRip &_rip, StateMachine *_sm)
		: rip(_rip), sm(_sm)
	{}

	void visit(HeapVisitor &hv) { hv(sm); }
	void prettyPrint(FILE *f) const
	{
		fprintf(f, "%s: ", rip.name());
		sm->prettyPrint(f);
	}

	/* Don't really understand why this is necessary... */
	void prettyPrint() const { PrettyPrintable::prettyPrint(); }

	NAMED_CLASS
};

/* A bunch of heuristics for figuring out why we crashed.  Returns
 * NULL on failure.  Pretty stupid. */
static CrashReason *
getProximalCause(MachineState *ms, Thread *thr)
{
	unsigned long rip = thr->regs.rip();
	IRSB *irsb;
	int x;
	int nr_marks;

	if (rip == 0) {
		/* Probably caused by calling a bad function pointer.
		 * Look at the call site. */
		rip = ms->addressSpace->fetch<unsigned long>(thr->regs.rsp(), NULL) - 2;
		irsb = ms->addressSpace->getIRSBForAddress(rip);
		if (!irsb) {
			/* I guess that wasn't it.  Give up. */
			return NULL;
		}
		/* That should be a call instruction, in which case
		   we'll have a single mark, a jumpkind of Call, and a
		   next pointer of some expression. */
		if (irsb->jumpkind != Ijk_Call)
			return NULL;
		nr_marks = 0;
		for (x = 0; x < irsb->stmts_used; x++) {
			if (irsb->stmts[x]->tag == Ist_IMark)
				nr_marks++;
		}
		if (nr_marks != 1)
			return NULL;

		/* We now guess that we crashed because the function
		   pointer called turned out to be NULL. */
		return new CrashReason(VexRip(rip, irsb->stmts_used),
				       new StateMachineBifurcate(
					       IRExpr_Binop(
						       Iop_CmpEQ64,
						       irsb->next,
						       IRExpr_Const(IRConst_U64(0))),
					       StateMachineCrash::get(),
					       StateMachineNoCrash::get()));
	} else {
		return NULL;
	}
}

class StateMachineTransformer {
private:
	/* Transformations are memoised.  This is important, because
	   it means that we preserve the state machine structure
	   rather than unrolling it. */
	std::map<const StateMachine *, StateMachine *> memoTable;
	StateMachine *doit(StateMachine *inp);
	StateMachineEdge *doit(StateMachineEdge *inp);

protected:
	virtual StateMachine *transformedCrash()
	{
		return StateMachineCrash::get();
	}
	virtual StateMachine *transformedNoCrash()
	{
		return StateMachineNoCrash::get();
	}
	virtual IRExpr *transformIRExpr(IRExpr *e);

	virtual IRExpr *transformIexGet(IRExpr *e) { return e; }
	virtual IRExpr *transformIexGetI(IRExpr *e)
	{
		return IRExpr_GetI(e->Iex.GetI.descr,
				   transformIRExpr(e->Iex.GetI.ix),
				   e->Iex.GetI.bias);
	}
	virtual IRExpr *transformIexRdTmp(IRExpr *e) { return e; }
	virtual IRExpr *transformIexQop(IRExpr *e)
	{
		return IRExpr_Qop(e->Iex.Qop.op,
				  transformIRExpr(e->Iex.Qop.arg1),
				  transformIRExpr(e->Iex.Qop.arg2),
				  transformIRExpr(e->Iex.Qop.arg3),
				  transformIRExpr(e->Iex.Qop.arg4));
	}
	virtual IRExpr *transformIexTriop(IRExpr *e)
	{
		return IRExpr_Triop(e->Iex.Triop.op,
				    transformIRExpr(e->Iex.Triop.arg1),
				    transformIRExpr(e->Iex.Triop.arg2),
				    transformIRExpr(e->Iex.Triop.arg3));
	}
	virtual IRExpr *transformIexBinop(IRExpr *e)
	{
		return IRExpr_Binop(e->Iex.Binop.op,
				    transformIRExpr(e->Iex.Binop.arg1),
				    transformIRExpr(e->Iex.Binop.arg2));
	}
	virtual IRExpr *transformIexUnop(IRExpr *e)
	{
		return IRExpr_Unop(e->Iex.Unop.op,
				   transformIRExpr(e->Iex.Unop.arg));
	}
	virtual IRExpr *transformIexLoad(IRExpr *e)
	{
		return IRExpr_Load(e->Iex.Load.isLL,
				   e->Iex.Load.end,
				   e->Iex.Load.ty,
				   transformIRExpr(e->Iex.Load.addr));
	}
	virtual IRExpr *transformIexSLILoad(IRExpr *e)
	{
		return IRExpr_SLI_Load(transformIRExpr(e->Iex.SLI_Load.addr),
				       e->Iex.SLI_Load.rip);
	}
	virtual IRExpr *transformIexConst(IRExpr *e)
	{
		return e;
	}
	virtual IRExpr *transformIexMux0X(IRExpr *e)
	{
		return IRExpr_Mux0X(
			transformIRExpr(e->Iex.Mux0X.cond),
			transformIRExpr(e->Iex.Mux0X.expr0),
			transformIRExpr(e->Iex.Mux0X.exprX));
	}
	virtual IRExpr *transformIexCCall(IRExpr *);
public:
	StateMachine *transform(StateMachine *start);
};

StateMachine *
StateMachineTransformer::doit(StateMachine *inp)
{
	if (memoTable.count(inp))
		return memoTable[inp];
	StateMachine *out;
	if (inp == StateMachineCrash::get()) {
		out = transformedCrash();
	} else if (inp == StateMachineNoCrash::get()) {
		out = transformedNoCrash();
	} else if (StateMachineBifurcate *smb =
		   dynamic_cast<StateMachineBifurcate *>(inp)) {
		StateMachineEdge *t = doit(smb->trueTarget);
		StateMachineEdge *f = doit(smb->falseTarget);
		IRExpr *cond = transformIRExpr(smb->condition);
		out = new StateMachineBifurcate(cond, t, f);
	} else if (StateMachineProxy *smp =
		   dynamic_cast<StateMachineProxy *>(inp)) {
		StateMachineEdge *t = doit(smp->target);
		out = new StateMachineProxy(t);
	} else if (StateMachineStub *sms =
		   dynamic_cast<StateMachineStub *>(inp)) {
		IRExpr *target = transformIRExpr(sms->target);
		out = new StateMachineStub(target);
	} else {
		abort();
	}
	memoTable[inp] = out;
	return out;
}

StateMachineEdge *
StateMachineTransformer::doit(StateMachineEdge *inp)
{
	StateMachine *t = doit(inp->target);
	StateMachineEdge *res = new StateMachineEdge(t);
	for (std::vector<StateMachineSideEffect>::iterator it = inp->sideEffects.begin();
	     it != inp->sideEffects.end();
	     it++) {
		res->sideEffects.push_back(
			StateMachineSideEffect::store(
				transformIRExpr(it->addr),
				transformIRExpr(it->data)));
	}
	return res;
}

StateMachine *
StateMachineTransformer::transform(StateMachine *inp)
{
	StateMachine *transformed = doit(inp);

	/* Now eliminate redundant states.  The algorithm for doing so
	   is essentially a Tarski iteration: we start by assuming
	   that all states are equivalent, and then look for
	   contradictions.  When we find one, we weaken the
	   assumption.  Iterate until there are no more
	   contradictions, and then collapse the machine by
	   eliminating redundancies. */

	/* Leave that alone for now so that I can look at other
	 * bits. */
#warning Write me

	return transformed;
}

IRExpr *
StateMachineTransformer::transformIRExpr(IRExpr *e)
{
	switch (e->tag) {
	case Iex_Binder:
		return e;
	case Iex_Get:
		return transformIexGet(e);
	case Iex_GetI:
		return transformIexGetI(e);
	case Iex_RdTmp:
		return transformIexRdTmp(e);
	case Iex_Qop:
		return transformIexQop(e);
	case Iex_Triop:
		return transformIexTriop(e);
	case Iex_Binop:
		return transformIexBinop(e);
	case Iex_Unop:
		return transformIexUnop(e);
	case Iex_Load:
		return transformIexLoad(e);
	case Iex_SLI_Load:
		return transformIexSLILoad(e);
	case Iex_Const:
		return transformIexConst(e);
	case Iex_CCall:
		return transformIexCCall(e);
	case Iex_Mux0X:
		return transformIexMux0X(e);
	default:
		abort();
	}
}

IRExpr *
StateMachineTransformer::transformIexCCall(IRExpr *e)
{
	IRExpr **newArgs;
	int nr_args;
	int x;

	for (nr_args = 0; e->Iex.CCall.args[nr_args]; nr_args++)
		;
	newArgs = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_args + 1);
	for (x = 0; x < nr_args; x++)
		newArgs[x] = transformIRExpr(e->Iex.CCall.args[x]);
	newArgs[nr_args] = NULL;
	return IRExpr_CCall(e->Iex.CCall.cee,
			    e->Iex.CCall.retty,
			    newArgs);
}

class RewriteRegister : public StateMachineTransformer {
	unsigned idx;
	IRExpr *to;
protected:
	IRExpr *transformIexGet(IRExpr *what);
public:
	RewriteRegister(unsigned _idx, IRExpr *_to)
		: idx(_idx), to(_to)
	{
	}
};

IRExpr *
RewriteRegister::transformIexGet(IRExpr *what)
{
	if (what->Iex.Get.offset == (int)idx)
		return to;
	else
		return what;
}

static StateMachine *
rewriteRegister(StateMachine *sm,
		unsigned reg_idx,
		IRExpr *newval)
{
	RewriteRegister rr(reg_idx, newval);
	return rr.transform(sm);
}

class RewriteTemporary : public StateMachineTransformer {
	IRTemp tmp;
	IRExpr *to;
protected:
	IRExpr *transformIexRdTmp(IRExpr *what)
	{
		if (what->Iex.RdTmp.tmp == tmp)
			return to;
		else
			return what;
	}
public:
	RewriteTemporary(IRTemp _tmp, IRExpr *_to)
		: tmp(_tmp), to(_to)
	{
	}
};

static StateMachine *
rewriteTemporary(StateMachine *sm,
		 IRTemp tmp,
		 IRExpr *newval)
{
	RewriteTemporary rt(tmp, newval);
	return rt.transform(sm);
}

static CrashReason *
backtrackOneStatement(CrashReason *cr, IRStmt *stmt)
{
	StateMachine *sm = cr->sm;

	VexRip newRip(cr->rip);
	assert(newRip.idx > 0);
	newRip.idx--;
	newRip.changedIdx();
	switch (stmt->tag) {
	case Ist_NoOp:
	case Ist_IMark:
	case Ist_AbiHint:
		break;
	case Ist_Put:
		sm = rewriteRegister(sm,
				     stmt->Ist.Put.offset,
				     stmt->Ist.Put.data);
		break;
	case Ist_PutI:
		/* We can't handle these correctly. */
		abort();
		return NULL;
	case Ist_WrTmp:
		sm = rewriteTemporary(sm,
				      stmt->Ist.WrTmp.tmp,
				      stmt->Ist.WrTmp.data);
		break;
	case Ist_Store: {
		StateMachineProxy *smp = new StateMachineProxy(sm);
		smp->target->prependSideEffect(
			StateMachineSideEffect::store(
				stmt->Ist.Store.addr,
				stmt->Ist.Store.data));
		return new CrashReason(newRip, smp);
	}

	case Ist_Dirty:
		if (!strcmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_64") ||
		    !strcmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_32")) {
			sm = rewriteTemporary(
				sm,
				stmt->Ist.Dirty.details->tmp,
				IRExpr_SLI_Load(
					stmt->Ist.Dirty.details->args[0],
					cr->rip.rip));
		}  else {
			abort();
		}
		break;

	case Ist_CAS:
		/* Can't backtrack across these */
		abort();
		return NULL;
	case Ist_MBE:
		return cr;
	case Ist_Exit:
		sm = new StateMachineBifurcate(
			stmt->Ist.Exit.guard,
			new StateMachineStub(
				IRExpr_Const(stmt->Ist.Exit.dst)),
			sm);
		break;
	default:
		abort();
	}

	return new CrashReason(newRip, sm);
}

static CrashReason *
backtrackToStartOfInstruction(CrashReason *cr, AddressSpace *as)
{
	IRSB *irsb = as->getIRSBForAddress(cr->rip.rip);
	assert((int)cr->rip.idx <= irsb->stmts_used);
	while (cr->rip.idx != 0)
		cr = backtrackOneStatement(cr, irsb->stmts[cr->rip.idx-1]);
	return cr;
}

static void
printStateMachine(const StateMachine *sm, FILE *f)
{
	std::set<const StateMachine *> emitted;
	std::vector<const StateMachine *> toEmit;

	toEmit.push_back(sm);
	while (!toEmit.empty()) {
		sm = toEmit.back();
		toEmit.pop_back();
		if (emitted.count(sm))
			continue;
		emitted.insert(sm);
		fprintf(f, "%p: ", sm);
		sm->prettyPrint(f);
		fprintf(f, "\n");
		if (const StateMachineBifurcate *smb =
		    dynamic_cast<const StateMachineBifurcate *>(sm)) {
			toEmit.push_back(smb->trueTarget->target);
			toEmit.push_back(smb->falseTarget->target);
		} else if (const StateMachineProxy *smp =
			   dynamic_cast<const StateMachineProxy *>(sm)) {
			toEmit.push_back(smp->target->target);
		}
	}
}

/* All of the information from sources other than the main crash dump.
 * Information from the oracle will be true of some executions but not
 * necessarily all of them, so should only really be used where static
 * analysis is insufficient. */
class Oracle : public GarbageCollected<Oracle> {
public:
	MachineState *ms;
	Thread *crashedThread;

	void findPreviousInstructions(std::vector<unsigned long> &output);

	Oracle(MachineState *_ms, Thread *_thr)
		: ms(_ms), crashedThread(_thr)
	{
	}
	void visit(HeapVisitor &hv) {
		hv(ms);
		hv(crashedThread);
	}
	NAMED_CLASS
};

class CFGNode : public GarbageCollected<CFGNode>, public PrettyPrintable {
public:
	unsigned long fallThroughRip;
	unsigned long branchRip;
	CFGNode *fallThrough;
	CFGNode *branch;

	unsigned long my_rip;

	CFGNode(unsigned long rip) : my_rip(rip) {}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%#lx: %#lx(%p), %#lx(%p)",
			my_rip, fallThroughRip, fallThrough,
			branchRip, branch);
	}
	void visit(HeapVisitor &hv) {
		hv(fallThrough);
		hv(branch);
	}
	NAMED_CLASS
};

/* All the various bits and pieces which we've discovered so far, in one
 * convenient place. */
class InferredInformation : public GarbageCollected<InferredInformation> {
public:
	Oracle *oracle;
	std::map<VexRip, CrashReason *> crashReasons;

	InferredInformation(Oracle *_oracle) : oracle(_oracle) {}
	void addCrashReason(CrashReason *cr) { crashReasons[cr->rip] = cr; }
	CFGNode *CFGFromRip(unsigned long rip);
	CrashReason *CFGtoCrashReason(CFGNode *cfg);

	void visit(HeapVisitor &hv) {
		hv(oracle);
		for (std::map<VexRip, CrashReason *>::iterator it =
			     crashReasons.begin();
		     it != crashReasons.end();
		     it++)
			hv(it->second);
	}
	NAMED_CLASS
};

CFGNode *
InferredInformation::CFGFromRip(unsigned long start)
{
	std::map<unsigned long, CFGNode *> builtSoFar;
	std::vector<unsigned long> needed;
	unsigned long rip;

	/* Mild hack to make some corned cases easier. */
	builtSoFar[0] = NULL;

	/* Step one: discover all of the instructions which we're
	 * going to need. */
	needed.push_back(start);
	while (!needed.empty()) {
		rip = needed.back();
		needed.pop_back();
		if (builtSoFar.count(rip))
			continue;
		IRSB *irsb = oracle->ms->addressSpace->getIRSBForAddress(rip);
		CFGNode *work = new CFGNode(rip);
		int x;
		for (x = 1; x < irsb->stmts_used; x++) {
			if (irsb->stmts[x]->tag == Ist_IMark) {
				work->fallThroughRip = irsb->stmts[x]->Ist.IMark.addr;
				needed.push_back(work->fallThroughRip);
				break;
			}
			if (irsb->stmts[x]->tag == Ist_Exit) {
				assert(work->branch == 0);
				work->branchRip = irsb->stmts[x]->Ist.Exit.dst->Ico.U64;
				needed.push_back(work->branchRip);
			}
		}
		if (x == irsb->stmts_used) {
			if (irsb->jumpkind == Ijk_Call) {
				work->fallThroughRip = extract_call_follower(irsb);
				needed.push_back(work->fallThroughRip);
			} else {
				/* Don't currently try to trace across indirect branches. */
				if (irsb->next->tag == Iex_Const) {
					work->fallThroughRip = irsb->next->Iex.Const.con->Ico.U64;
					needed.push_back(work->fallThroughRip);
				}
			}
		}
		builtSoFar[rip] = work;
	}

	/* Now we have a CFG node for every needed instruction.  Go
	   through and resolve exit branches. */
	for (std::map<unsigned long, CFGNode *>::iterator it = builtSoFar.begin();
	     it != builtSoFar.end();
	     it++) {
		if (it->second) {
			it->second->fallThrough = builtSoFar[it->second->fallThroughRip];
			it->second->branch = builtSoFar[it->second->branchRip];
		}
	}

	/* That should do it */
	return builtSoFar[start];
}

CrashReason *
InferredInformation::CFGtoCrashReason(CFGNode *cfg)
{
	VexRip finalRip(cfg->my_rip, 0);
	if (crashReasons.count(finalRip)) {
		assert(crashReasons[finalRip]);
		return crashReasons[finalRip];
	}
	CrashReason *res;
	if (!cfg->branch && !cfg->fallThrough) {
		res = new CrashReason(finalRip, StateMachineNoCrash::get());
	} else {
		IRSB *irsb = oracle->ms->addressSpace->getIRSBForAddress(finalRip.rip);
		int x;
		for (x = 1; x < irsb->stmts_used; x++)
			if (irsb->stmts[x]->tag == Ist_IMark)
				break;
		if (cfg->fallThrough) {
			CrashReason *ft = CFGtoCrashReason(cfg->fallThrough);

			ft = new CrashReason(VexRip(finalRip.rip, x), ft->sm);
			while (ft->rip.idx != 0) {
				IRStmt *stmt = irsb->stmts[ft->rip.idx-1];
				if (stmt->tag == Ist_Exit) {
					VexRip newRip(ft->rip);
					newRip.idx--;
					newRip.changedIdx();
					if (cfg->branch) {
						ft = new CrashReason(
							newRip,
							new StateMachineBifurcate(
								stmt->Ist.Exit.guard,
								CFGtoCrashReason(cfg->branch)->sm,
								ft->sm));
					} else {
						ft = new CrashReason(
							newRip,
							ft->sm);
					}
				} else {
					ft = backtrackOneStatement(ft, stmt);
				}
			}
			res = ft;
		} else {
			assert(cfg->branch);
			CrashReason *b = CFGtoCrashReason(cfg->branch);
			for (; x >= 0; x--)
				if (irsb->stmts[x]->tag == Ist_Exit)
					break;
			assert(x > 0);
			b = new CrashReason(VexRip(finalRip.rip, x), b->sm);
			while (b->rip.idx != 0) {
				IRStmt *stmt = irsb->stmts[b->rip.idx-1];
				b = backtrackOneStatement(b, stmt);
			}
			res = b;
		}
	}
	assert(finalRip == res->rip);
	assert(res);
	crashReasons[finalRip] = res;
	return res;
}

static void
printCFG(const CFGNode *cfg)
{
	std::vector<const CFGNode *> pending;
	std::set<const CFGNode *> done;

	pending.push_back(cfg);
	while (!pending.empty()) {
		cfg = pending.back();
		pending.pop_back();
		if (done.count(cfg))
			continue;
		printf("%p: ", cfg);
		cfg->prettyPrint(stdout);
		printf("\n");
		if (cfg->fallThrough)
			pending.push_back(cfg->fallThrough);
		if (cfg->branch)
			pending.push_back(cfg->branch);
		done.insert(cfg);
	}
}

void
Oracle::findPreviousInstructions(std::vector<unsigned long> &out)
{
	getDominators(crashedThread, ms, out);
}

static void
enumerateCFG(CFGNode *root, std::map<unsigned long, CFGNode *> &rips)
{
	if (!root)
		return;
	if (rips.count(root->my_rip))
		return;
	rips[root->my_rip] = root;
	enumerateCFG(root->branch, rips);
	enumerateCFG(root->fallThrough, rips);
}

/* Remove all of the nodes which appear to be uninteresting.  A node
   is uninteresting if it is not in the initial interesting set and
   there are no paths from it to an interesting node. */
static void
trimCFG(CFGNode *root, std::set<unsigned long> interestingAddresses)
{
	std::map<unsigned long, CFGNode *> uninteresting;
	std::map<unsigned long, CFGNode *> interesting;
	/* Start on the assumption that everything is uninteresting. */
	enumerateCFG(root, uninteresting);
	/* addresses which are explicitly flagged as interesting are
	   not uninteresting. */
	for (std::set<unsigned long>::iterator it = interestingAddresses.begin();
	     it != interestingAddresses.end();
	     it++) {
		interesting[*it] = uninteresting[*it];
		uninteresting.erase(*it);
	}

	/* Tarski iteration */
	bool progress;
	do {
		progress = false;
		for (std::map<unsigned long, CFGNode *>::iterator it = uninteresting.begin();
		     it != uninteresting.end();
			) {
			CFGNode *n = it->second;
			bool shouldBeUninteresting = true;
			if (n->branch &&
			    !uninteresting.count(n->branch->my_rip))
				shouldBeUninteresting = false;
			if (n->fallThrough &&
			    !uninteresting.count(n->fallThrough->my_rip))
				shouldBeUninteresting = false;
			if (shouldBeUninteresting) {
				it++;
			} else {
				progress = true;
				interesting[it->first] = it->second;
				uninteresting.erase(it++);
			}
		}
	} while (progress);

	/* The uninteresting set should now be correct.  Eliminate any
	   edges which go to an uninteresting target. */
	for (std::map<unsigned long, CFGNode *>::iterator it = interesting.begin();
	     it != interesting.end();
	     it++) {
		CFGNode *n = it->second;
		if (n->branch && uninteresting.count(n->branch->my_rip))
			n->branch = NULL;
		if (n->fallThrough && uninteresting.count(n->fallThrough->my_rip))
			n->fallThrough = NULL;
	}

	/* All done. */
}

/* Break cycles using a simple depth-first iteration.  @cfg is the
   current node in the iteration and @onPath is the set of nodes on
   the path from the root to the current node.  We will always try to
   break the cycle on a back edge, defined to be one where the value
   in @numbering decreases.  *@lastBackEdge should be the last back
   pointer which we followed on this path, and it is where we will
   break the cycle.  Returns false if we broke a cycle, in which case
   the whole thing needs to be re-run, or true otherwise. */
static bool
breakCycles(CFGNode *cfg, std::map<CFGNode *, unsigned> &numbering,
	    CFGNode **lastBackEdge, std::set<CFGNode *> &onPath)
{
	if (onPath.count(cfg)) {
		/* We have a cycle.  Break it. */
		assert(lastBackEdge);
		lastBackEdge = NULL;
		return false;
	}

	onPath.insert(cfg);
	if (cfg->branch) {
		CFGNode **p = lastBackEdge;
		if (numbering[cfg->branch] < numbering[cfg])
			p = &cfg->branch;
		if (!breakCycles(cfg->branch, numbering, p, onPath))
			return false;
	}
	if (cfg->fallThrough) {
		CFGNode **p = lastBackEdge;
		if (numbering[cfg->fallThrough] < numbering[cfg])
			p = &cfg->fallThrough;
		if (!breakCycles(cfg->fallThrough, numbering, p, onPath))
			return false;
	}

	onPath.erase(cfg);

	return true;
}

/* We use a breadth first search to number the nodes and then use a
   variant of Tarjan's algorithm to detect cycles.  When we detect a
   cycle, we use the numbering scheme to identify a back edge and
   eliminate it. */
static void
breakCycles(CFGNode *cfg)
{
	std::map<CFGNode *, unsigned> numbering;
	std::queue<CFGNode *> queue;
	CFGNode *t;

	/* Assign numbering */
	unsigned idx;
	idx = 0;
	queue.push(cfg);
	while (!queue.empty()) {
		t = queue.front();
		queue.pop();
		if (numbering.count(t))
			continue;
		numbering[t] = idx;
		idx++;
		if (t->branch)
			queue.push(t->branch);
		if (t->fallThrough)
			queue.push(t->fallThrough);
	}

	std::set<CFGNode *> visited;
	while (!breakCycles(cfg, numbering, NULL, visited))
		visited.clear();
}

/* Returns true if the operation definitely commutes, or false if
 * we're not sure. */
static bool
operationCommutes(IROp op)
{
	return op >= Iop_Add8 && op <= Iop_Add64;
}

static IRExpr *
optimiseIRExpr(IRExpr *src)
{
	/* First, recursively optimise our arguments. */
	switch (src->tag) {
	case Iex_Qop:
		src->Iex.Qop.arg4 = optimiseIRExpr(src->Iex.Qop.arg4);
	case Iex_Triop:
		src->Iex.Triop.arg3 = optimiseIRExpr(src->Iex.Triop.arg3);
	case Iex_Binop:
		src->Iex.Binop.arg2 = optimiseIRExpr(src->Iex.Binop.arg2);
	case Iex_Unop:
		src->Iex.Unop.arg = optimiseIRExpr(src->Iex.Unop.arg);
		break;
	case Iex_Load:
		src->Iex.Load.addr = optimiseIRExpr(src->Iex.Load.addr);
		break;
	case Iex_Mux0X:
		src->Iex.Mux0X.cond = optimiseIRExpr(src->Iex.Mux0X.cond);
		src->Iex.Mux0X.expr0 = optimiseIRExpr(src->Iex.Mux0X.expr0);
		src->Iex.Mux0X.exprX = optimiseIRExpr(src->Iex.Mux0X.exprX);
		break;
	case Iex_SLI_Load:
		src->Iex.SLI_Load.addr = optimiseIRExpr(src->Iex.SLI_Load.addr);
		break;
	default:
		break;
	}

	/* Now use some special rules to simplify a few classes of binops. */
	if (src->tag == Iex_Binop) {
		if (src->Iex.Binop.op >= Iop_Sub8 &&
		    src->Iex.Binop.op <= Iop_Sub64) {
			/* Replace a - b with a + (-b), so as to
			   eliminate binary -. */
			src->Iex.Binop.op = (IROp)(src->Iex.Binop.op - Iop_Sub8 + Iop_Add8);
			src->Iex.Binop.arg2 =
				optimiseIRExpr(
					IRExpr_Unop( (IROp)((src->Iex.Binop.op - Iop_Add8) + Iop_Neg8),
						     src->Iex.Binop.arg2 ) );
		}
		/* If a op b commutes, and b is a constant and a
		   isn't, rewrite to b op a. */
		if (operationCommutes(src->Iex.Binop.op) &&
		    src->Iex.Binop.arg1->tag == Iex_Const &&
		    src->Iex.Binop.arg2->tag != Iex_Const) {
			IRExpr *a = src->Iex.Binop.arg1;
			src->Iex.Binop.arg1 = src->Iex.Binop.arg2;
			src->Iex.Binop.arg2 = a;
		}
		/* If both arguments are constant, try to constant
		 * fold everything away. */
		if (src->Iex.Binop.arg1->tag == Iex_Const &&
		    src->Iex.Binop.arg2->tag == Iex_Const) {
			switch (src->Iex.Binop.op) {
			case Iop_Add8:
				return IRExpr_Const(
					IRConst_U8(
						(src->Iex.Binop.arg1->Iex.Const.con->Ico.U8 +
						 src->Iex.Binop.arg2->Iex.Const.con->Ico.U8) & 0xff));
			case Iop_Add16:
				return IRExpr_Const(
					IRConst_U16(
						(src->Iex.Binop.arg1->Iex.Const.con->Ico.U16 +
						 src->Iex.Binop.arg2->Iex.Const.con->Ico.U16) & 0xffff));
			case Iop_Add32:
				return IRExpr_Const(
					IRConst_U32(
						(src->Iex.Binop.arg1->Iex.Const.con->Ico.U32 +
						 src->Iex.Binop.arg2->Iex.Const.con->Ico.U32) & 0xffffffff));
			case Iop_Add64:
				return IRExpr_Const(
					IRConst_U64(
						src->Iex.Binop.arg1->Iex.Const.con->Ico.U64 +
						src->Iex.Binop.arg2->Iex.Const.con->Ico.U64));
			default:
				break;
			}
		}
	}
				      
	return src;
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readCoredump(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(CRASHED_THREAD)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr));

	CrashReason *proximal = getProximalCause(ms, thr);
	if (!proximal)
		errx(1, "cannot get proximal cause of crash");
	printf("Immediate proximal cause:\n");
	printStateMachine(proximal->sm, stdout);

	proximal = backtrackToStartOfInstruction(proximal, ms->addressSpace);
	printf("Cause at start of this instruction:\n");
	printStateMachine(proximal->sm, stdout);

	VexPtr<InferredInformation> ii(new InferredInformation(oracle));
	ii->addCrashReason(proximal);

	std::vector<unsigned long> previousInstructions;
	oracle->findPreviousInstructions(previousInstructions);
	for (std::vector<unsigned long>::iterator it = previousInstructions.begin();
	     it != previousInstructions.end();
	     it++) {
		CFGNode *cfg = ii->CFGFromRip(*it);
		std::set<unsigned long> interesting;
		interesting.insert(proximal->rip.rip);
		trimCFG(cfg, interesting);
		breakCycles(cfg);

		CrashReason *cr = ii->CFGtoCrashReason(cfg);
		printf("Crash reason %s:\n", cr->rip.name());
		printStateMachine(cr->sm, stdout);
		cr->sm = cr->sm->optimise();
		printf("After optimisation:\n");
		printStateMachine(cr->sm, stdout);
	}

	return 0;
}
