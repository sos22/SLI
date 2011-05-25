/* Re-implementation of direct which tries to work off of just a core
   dump, rather than needing the full trace. */
#include <err.h>
#include <limits.h>
#include <time.h>

#include <algorithm>
#include <queue>
#include <map>
#include <set>

#include "sli.h"
#include "nd_chooser.h"
#include "range_tree.h"
#include "pickle.hpp"
#include "state_machine.hpp"
#include "oracle.hpp"

static void assertUnoptimisable(IRExpr *e, const AllowableOptimisations &);

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
	unsigned long hash(void) const {
		return rip ^ (idx * 13);
	}
	bool operator<(const VexRip &a) const {
		return rip < a.rip || (rip == a.rip && idx < a.idx);
	}
	bool operator==(const VexRip &a) const {
		return rip == a.rip && idx == a.idx;
	}
};

class CrashReason : public GarbageCollected<CrashReason, &ir_heap> {
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
		irsb = ms->addressSpace->getIRSBForAddress(thr->tid._tid(), rip);
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
					       rip,
					       IRExpr_Binop(
						       Iop_CmpEQ64,
						       irsb->next,
						       IRExpr_Const(IRConst_U64(0))),
					       StateMachineCrash::get(),
					       StateMachineNoCrash::get()));
	}

	/* Next guess: it's caused by dereferencing a bad pointer.
	   Grab the crashing instruction and try emulating it.  If it
	   results in a crash, we can be pretty confident that we've
	   found the problem. */
	irsb = ms->addressSpace->getIRSBForAddress(thr->tid._tid(), rip);
	thr->temporaries.setSize(irsb->tyenv->types_used);
	for (int x = 1 /* Skip the initial IMark */;
	     x < irsb->stmts_used;
	     x++) {
		IRStmt *stmt = irsb->stmts[x];
		ThreadEvent *evt;
		{
			ReplayEngineTimer ret;
			evt = interpretStatement(stmt,
						 thr,
						 NULL,
						 ms,
						 irsb,
						 ret);
		}
		if (evt == NULL)
			continue;
		if (evt == DUMMY_EVENT || evt == FINISHED_BLOCK) {
			/* Okay, so re-interpreting this instruction
			   didn't give us any clues as to why we're
			   crashing.  Give up. */
			break;
		}

		SignalEvent *se = dynamic_cast<SignalEvent *>(evt);
		if (se && se->signr == 11) {
			/* Program tripped over a segfault -> almost
			   certainly the cause of the crash.  It'll be
			   from either a load or a store, and we
			   special case the two cases here. */
			IRExpr *addr = NULL;
			if (stmt->tag == Ist_Dirty &&
			    (!strcmp(stmt->Ist.Dirty.details->cee->name,
				     "helper_load_8") ||
			     !strcmp(stmt->Ist.Dirty.details->cee->name,
				     "helper_load_16") ||
			     !strcmp(stmt->Ist.Dirty.details->cee->name,
				     "helper_load_32") ||			     
			     !strcmp(stmt->Ist.Dirty.details->cee->name,
				     "helper_load_64"))) {
				/* It's a load; the address loaded is
				   in the first argument. */
				addr = stmt->Ist.Dirty.details->args[0];
			} else if (stmt->tag == Ist_Store) {
				addr = stmt->Ist.Store.addr;
			} else {
				/* Neither a load nor a store.  That
				   shouldn't be generating a segfault,
				   then. */
				abort();
			}
			assert(addr != NULL);
			return new CrashReason(VexRip(rip, x),
					       new StateMachineBifurcate(
						       rip,
						       IRExpr_Binop(
							       Iop_CmpEQ64,
							       addr,
							       IRExpr_Const(IRConst_U64(se->virtaddr))),
						       StateMachineCrash::get(),
						       StateMachineNoCrash::get()));
		}
		printf("Generated event %s\n", evt->name());
	}

	printf("Hit end of block without any events -> no idea why we crashed.\n");
	return NULL;
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
	virtual StateMachine *transformedUnreached()
	{
		return StateMachineUnreached::get();
	}
	virtual IRExpr *transformIRExpr(IRExpr *e);

	virtual IRExpr *transformIexGet(IRExpr *e) { return e; }
	virtual IRExpr *transformIexGetI(IRExpr *e)
	{
		IRExpr *e2 = transformIRExpr(e->Iex.GetI.ix);
		if (e2 == e)
			return e;
		else
			return IRExpr_GetI(e->Iex.GetI.descr,
					   e2,
					   e->Iex.GetI.bias,
					   e->Iex.GetI.tid);
	}
	virtual IRExpr *transformIexRdTmp(IRExpr *e) { return e; }
	virtual IRExpr *transformIexQop(IRExpr *e)
	{
		IRExpr *a1 = transformIRExpr(e->Iex.Qop.arg1);
		IRExpr *a2 = transformIRExpr(e->Iex.Qop.arg2);
		IRExpr *a3 = transformIRExpr(e->Iex.Qop.arg3);
		IRExpr *a4 = transformIRExpr(e->Iex.Qop.arg4);
		if (a1 == e->Iex.Qop.arg1 &&
		    a2 == e->Iex.Qop.arg2 &&
		    a3 == e->Iex.Qop.arg3 &&
		    a4 == e->Iex.Qop.arg4)
			return e;
		else
			return IRExpr_Qop(e->Iex.Qop.op,
					  a1,
					  a2,
					  a3,
					  a4);
	}
	virtual IRExpr *transformIexTriop(IRExpr *e)
	{
		IRExpr *a1 = transformIRExpr(e->Iex.Qop.arg1);
		IRExpr *a2 = transformIRExpr(e->Iex.Qop.arg2);
		IRExpr *a3 = transformIRExpr(e->Iex.Qop.arg3);
		if (a1 == e->Iex.Qop.arg1 &&
		    a2 == e->Iex.Qop.arg2 &&
		    a3 == e->Iex.Qop.arg3)
			return e;
		else
			return IRExpr_Triop(e->Iex.Qop.op,
					    a1,
					    a2,
					    a3);
	}
	virtual IRExpr *transformIexBinop(IRExpr *e)
	{
		IRExpr *a1 = transformIRExpr(e->Iex.Qop.arg1);
		IRExpr *a2 = transformIRExpr(e->Iex.Qop.arg2);
		if (a1 == e->Iex.Qop.arg1 &&
		    a2 == e->Iex.Qop.arg2)
			return e;
		else
			return IRExpr_Binop(e->Iex.Qop.op,
					    a1,
					    a2);
	}
	virtual IRExpr *transformIexUnop(IRExpr *e)
	{
		IRExpr *a1 = transformIRExpr(e->Iex.Qop.arg1);
		if (a1 == e->Iex.Qop.arg1)
			return e;
		else
			return IRExpr_Unop(e->Iex.Qop.op,
					    a1);
	}
	virtual IRExpr *transformIexLoad(IRExpr *e)
	{
		IRExpr *addr = transformIRExpr(e->Iex.Load.addr);
		if (addr == e->Iex.Load.addr)
			return e;
		else
			return IRExpr_Load(e->Iex.Load.isLL,
					   e->Iex.Load.end,
					   e->Iex.Load.ty,
					   addr);
	}
	virtual IRExpr *transformIexConst(IRExpr *e)
	{
		return e;
	}
	virtual IRExpr *transformIexMux0X(IRExpr *e)
	{
		IRExpr *c = transformIRExpr(e->Iex.Mux0X.cond);
		IRExpr *z = transformIRExpr(e->Iex.Mux0X.expr0);
		IRExpr *x = transformIRExpr(e->Iex.Mux0X.exprX);
		if (c == e->Iex.Mux0X.cond &&
		    z == e->Iex.Mux0X.expr0 &&
		    x == e->Iex.Mux0X.exprX)
			return e;
		else
			return IRExpr_Mux0X(c, z, x);
	}
	virtual IRExpr *transformIexCCall(IRExpr *);
	virtual IRExpr *transformIexAssociative(IRExpr *);
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
	} else if (inp == StateMachineUnreached::get()) {
		out = transformedUnreached();
	} else if (StateMachineBifurcate *smb =
		   dynamic_cast<StateMachineBifurcate *>(inp)) {
		StateMachineEdge *t = doit(smb->trueTarget);
		StateMachineEdge *f = doit(smb->falseTarget);
		IRExpr *cond = transformIRExpr(smb->condition);
		if (t == smb->trueTarget && f == smb->falseTarget && cond == smb->condition)
			out = inp;
		else
			out = new StateMachineBifurcate(inp->origin, cond, t, f);
	} else if (StateMachineProxy *smp =
		   dynamic_cast<StateMachineProxy *>(inp)) {
		StateMachineEdge *t = doit(smp->target);
		if (t == smp->target)
			out = inp;
		else
			out = new StateMachineProxy(inp->origin, t);
	} else if (StateMachineStub *sms =
		   dynamic_cast<StateMachineStub *>(inp)) {
		IRExpr *target = transformIRExpr(sms->target);
		if (target == sms->target)
			out = inp;
		else
			out = new StateMachineStub(inp->origin, target);
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
	bool changedSideEffect = false;
	for (std::vector<StateMachineSideEffect *>::iterator it = inp->sideEffects.begin();
	     it != inp->sideEffects.end();
	     it++) {
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(*it)) {
			IRExpr *a, *d;
			a = transformIRExpr(smses->addr);
			d = transformIRExpr(smses->data);
			if (a != smses->addr || d != smses->data)
				changedSideEffect = true;
			res->sideEffects.push_back(
				new StateMachineSideEffectStore(
					a,
					d,
					smses->rip));
		} else if (StateMachineSideEffectLoad *smsel =
			   dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			IRExpr *a = transformIRExpr(smsel->smsel_addr);
			if (a != smsel->smsel_addr)
				changedSideEffect = true;
			res->sideEffects.push_back(
				new StateMachineSideEffectLoad(
					smsel->key,
					a,
					smsel->rip));
		} else if (StateMachineSideEffectCopy *smsec =
			   dynamic_cast<StateMachineSideEffectCopy *>(*it)) {
			IRExpr *v = transformIRExpr(smsec->value);
			if (v != smsec->value)
				changedSideEffect = true;
			res->sideEffects.push_back(
				new StateMachineSideEffectCopy(
					smsec->key,
					v));
		} else if (dynamic_cast<StateMachineSideEffectUnreached *>(*it)) {
			res->sideEffects.push_back(*it);
		} else {
			abort();
		}
	}
	if (!changedSideEffect && t == inp->target)
		return inp;
	else
		return res;
}

StateMachine *
StateMachineTransformer::transform(StateMachine *inp)
{
	return doit(inp);
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
	case Iex_Const:
		return transformIexConst(e);
	case Iex_CCall:
		return transformIexCCall(e);
	case Iex_Mux0X:
		return transformIexMux0X(e);
	case Iex_Associative:
		return transformIexAssociative(e);
	}
	abort();
}

IRExpr *
StateMachineTransformer::transformIexCCall(IRExpr *e)
{
	IRExpr **newArgs;
	int nr_args;
	int x;
	bool changedSomething;

	for (nr_args = 0; e->Iex.CCall.args[nr_args]; nr_args++)
		;
	newArgs = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_args + 1);
	changedSomething = false;
	for (x = 0; x < nr_args; x++) {
		newArgs[x] = transformIRExpr(e->Iex.CCall.args[x]);
		if (newArgs[x] != e->Iex.CCall.args[x])
			changedSomething = true;
	}
	newArgs[nr_args] = NULL;
	if (!changedSomething)
		return e;
	else
		return IRExpr_CCall(e->Iex.CCall.cee,
				    e->Iex.CCall.retty,
				    newArgs);
}

IRExpr *
StateMachineTransformer::transformIexAssociative(IRExpr *e)
{
	IRExpr *r = IRExpr_Associative(e);
	bool changedSomething = false;
	for (int x = 0; x < r->Iex.Associative.nr_arguments; x++) {
		r->Iex.Associative.contents[x] =
			transformIRExpr(r->Iex.Associative.contents[x]);
		if (e->Iex.Associative.contents[x] !=
		    r->Iex.Associative.contents[x])
			changedSomething = true;
	}
	if (!changedSomething)
		return e;
	else
		return r;
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

static StateMachine *
backtrackStateMachineOneStatement(StateMachine *sm, IRStmt *stmt, unsigned long rip)
{
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
		StateMachineProxy *smp = new StateMachineProxy(sm->origin, sm);
		smp->target->prependSideEffect(
			new StateMachineSideEffectStore(
				stmt->Ist.Store.addr,
				stmt->Ist.Store.data,
				rip));
		sm = smp;
		break;
	}

	case Ist_Dirty:
		if (!strcmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_8") ||
		    !strcmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_64") ||
		    !strcmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_32")) {
			StateMachineSideEffectLoad *smsel =
				new StateMachineSideEffectLoad(
					stmt->Ist.Dirty.details->args[0],
					rip);
			sm = rewriteTemporary(
				sm,
				stmt->Ist.Dirty.details->tmp,
				IRExpr_Binder(smsel->key));
			StateMachineProxy *smp = new StateMachineProxy(sm->origin, sm);
			smp->target->prependSideEffect(smsel);
			sm = smp;
		}  else {
			abort();
		}
		break;

	case Ist_CAS:
		/* Can't backtrack across these */
		abort();
		sm = NULL;
		break;

	case Ist_MBE:
		break;
	case Ist_Exit:
		sm = new StateMachineBifurcate(
			rip,
			stmt->Ist.Exit.guard,
			new StateMachineStub(
				rip,
				IRExpr_Const(stmt->Ist.Exit.dst)),
			sm);
		break;
	default:
		abort();
	}
	return sm;
}

static CrashReason *
backtrackOneStatement(CrashReason *cr, IRStmt *stmt)
{
	StateMachine *sm = cr->sm;

	VexRip newRip(cr->rip);
	assert(newRip.idx > 0);
	newRip.idx--;
	newRip.changedIdx();
	sm = backtrackStateMachineOneStatement(sm, stmt, cr->rip.rip);
	return new CrashReason(newRip, sm);
}

static CrashReason *
backtrackToStartOfInstruction(unsigned tid, CrashReason *cr, AddressSpace *as)
{
	IRSB *irsb = as->getIRSBForAddress(tid, cr->rip.rip);
	assert((int)cr->rip.idx <= irsb->stmts_used);
	while (cr->rip.idx != 0)
		cr = backtrackOneStatement(cr, irsb->stmts[cr->rip.idx-1]);
	return cr;
}

template <typename t>
class CFGNode : public GarbageCollected<CFGNode<t>, &ir_heap>, public PrettyPrintable {
public:
	t fallThroughRip;
	t branchRip;
	CFGNode<t> *fallThrough;
	CFGNode<t> *branch;

	t my_rip;

	bool accepting;

	CFGNode(t rip) : my_rip(rip), accepting(false) {}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%#lx: %#lx(%p), %#lx(%p)",
			wrappedRipToRip(my_rip),
			wrappedRipToRip(fallThroughRip),
			fallThrough,
			wrappedRipToRip(branchRip),
			branch);
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
	VexPtr<gc_heap_map<VexRip, CrashReason, &ir_heap>::type, &ir_heap> crashReasons;

	InferredInformation(Oracle *_oracle) :
		oracle(_oracle),
		crashReasons(new gc_heap_map<VexRip, CrashReason, &ir_heap>::type())
	{}
	void addCrashReason(CrashReason *cr) { crashReasons->set(cr->rip, cr); }
	CFGNode<unsigned long> *CFGFromRip(unsigned long rip, const std::set<unsigned long> &terminalFunctions);
	CrashReason *CFGtoCrashReason(unsigned tid, CFGNode<unsigned long> *cfg);

	void visit(HeapVisitor &hv) {
		hv(oracle);
	}
	void relocate(InferredInformation *to, size_t s) {
		crashReasons.relocate(&to->crashReasons);
	}
	NAMED_CLASS
};

static void
enumerateReachableStates(CFGNode<unsigned long> *from, std::set<CFGNode<unsigned long> *> &out)
{
	if (!from || out.count(from))
		return;
	out.insert(from);
	enumerateReachableStates(from->fallThrough, out);
	enumerateReachableStates(from->branch, out);
}

/* Build a control flow graph which covers all of the RIPs in @rips.
 * @output is filled in with pointers to all of the possible start
 * nodes.
 */
/* This only really makes sense if @rips are similar enough that the
 * CFGs are likely to overlap. */
static void
buildCFGForRipSet(AddressSpace *as,
		  const std::set<unsigned long> &rips,
		  const std::set<unsigned long> &terminalFunctions,
		  std::set<CFGNode<unsigned long> *> &output,
		  Oracle *oracle)
{
	std::map<unsigned long, CFGNode<unsigned long> *> builtSoFar;
	std::vector<unsigned long> needed;
	unsigned long rip;

	/* Mild hack to make some corned cases easier. */
	builtSoFar[0] = NULL;

	/* Step one: discover all of the instructions which we're
	 * going to need. */
	for (std::set<unsigned long>::const_iterator it = rips.begin();
	     it != rips.end();
	     it++)
		needed.push_back(*it);
	while (!needed.empty()) {
		rip = needed.back();
		needed.pop_back();
		if (builtSoFar.count(rip))
			continue;
		IRSB *irsb = as->getIRSBForAddress(-1, rip);
		CFGNode<unsigned long> *work = new CFGNode<unsigned long>(rip);
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
				if (irsb->next->tag == Iex_Const) {
					if (terminalFunctions.count(irsb->next->Iex.Const.con->Ico.U64))
						work->fallThroughRip = irsb->next->Iex.Const.con->Ico.U64;
					else if (!oracle->functionCanReturn(irsb->next->Iex.Const.con->Ico.U64))
						work->fallThroughRip = 0;
				}
				if (work->fallThroughRip)
					needed.push_back(work->fallThroughRip);
			} else if (irsb->jumpkind == Ijk_Ret) {
				work->accepting = true;
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
	for (std::map<unsigned long, CFGNode<unsigned long> *>::iterator it = builtSoFar.begin();
	     it != builtSoFar.end();
	     it++) {
		if (it->second) {
			it->second->fallThrough = builtSoFar[it->second->fallThroughRip];
			it->second->branch = builtSoFar[it->second->branchRip];
		}
	}

	/* Extract the start states.  These will be some subset of the
	   input root nodes. */
	std::set<CFGNode<unsigned long> *> outputSoFar;
	for (std::set<unsigned long>::const_iterator it = rips.begin();
	     it != rips.end();
	     it++) {
		CFGNode<unsigned long> *startnode = builtSoFar[*it];
		if (outputSoFar.count(startnode))
			continue;
		output.insert(startnode);

		enumerateReachableStates(startnode, outputSoFar);
	}
}

/* Special case of buildCFGForRipSet() when you only have one entry
 * RIP */
CFGNode<unsigned long> *
InferredInformation::CFGFromRip(unsigned long start, const std::set<unsigned long> &terminalFunctions)
{
	std::set<unsigned long> rips;
	std::set<CFGNode<unsigned long> *> out;
	rips.insert(start);
	buildCFGForRipSet(oracle->ms->addressSpace, rips, terminalFunctions, out, oracle);
	if (out.size() == 0)
		return NULL;
	assert(out.size() == 1);
	return *out.begin();
}

CrashReason *
InferredInformation::CFGtoCrashReason(unsigned tid, CFGNode<unsigned long> *cfg)
{
	VexRip finalRip(cfg->my_rip, 0);
	if (crashReasons->hasKey(finalRip)) {
		assert(crashReasons->get(finalRip));
		return crashReasons->get(finalRip);
	}
	CrashReason *res;
	if (!cfg->branch && !cfg->fallThrough) {
		res = new CrashReason(finalRip, StateMachineNoCrash::get());
	} else {
		IRSB *irsb = oracle->ms->addressSpace->getIRSBForAddress(tid, finalRip.rip);
		int x;
		for (x = 1; x < irsb->stmts_used; x++)
			if (irsb->stmts[x]->tag == Ist_IMark)
				break;
		if (cfg->fallThrough) {
			CrashReason *ft;
			ft = CFGtoCrashReason(tid, cfg->fallThrough);
			if (x == irsb->stmts_used &&
			    irsb->jumpkind == Ijk_Call &&
			    cfg->fallThroughRip == extract_call_follower(irsb)) {
				/* This call is suppressed -> ignore
				   it, rather than doing the
				   backtracking thing. */
				ft = new CrashReason(finalRip, ft->sm);
			} else {
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
									ft->rip.rip,
									stmt->Ist.Exit.guard,
									CFGtoCrashReason(tid, cfg->branch)->sm,
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
			}
			res = ft;
		} else {
			assert(cfg->branch);
			CrashReason *b = CFGtoCrashReason(tid, cfg->branch);
			for (x--; x >= 0; x--)
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
	crashReasons->set(finalRip, res);
	return res;
}

template <typename t> void
printCFG(const CFGNode<t> *cfg)
{
	std::vector<const CFGNode<t> *> pending;
	std::set<const CFGNode<t> *> done;

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

template <typename t> void
enumerateCFG(CFGNode<t> *root, std::map<t, CFGNode<t> *> &rips)
{
	if (!root)
		return;
	if (rips.count(root->my_rip))
		return;
	rips[root->my_rip] = root;
	enumerateCFG(root->branch, rips);
	enumerateCFG(root->fallThrough, rips);
}

static bool
instructionIsInteresting(const InstructionSet &i, unsigned long r)
{
	return i.rips.count(r) != 0;
}

/* Remove all of the nodes which appear to be uninteresting.  A node
   is uninteresting if it is not in the initial interesting set and
   there are no paths from it to an interesting node. */
template <typename t> void
trimCFG(CFGNode<t> *root, const InstructionSet &interestingAddresses, int max_path_length)
{
	std::map<t, CFGNode<t> *> uninteresting;
	std::map<t, std::pair<CFGNode<t> *, int> > interesting;
	/* Start on the assumption that everything is uninteresting. */
	enumerateCFG<t>(root, uninteresting);
	/* addresses which are explicitly flagged as interesting are
	   not uninteresting. */
	for (typename std::map<t, CFGNode<t> *>::iterator it = uninteresting.begin();
	     it != uninteresting.end();
		) {
		if (it->second->accepting ||
		    instructionIsInteresting(interestingAddresses, it->first)) {
			interesting[it->first] = std::pair<CFGNode<t> *, int>(it->second, max_path_length);
			uninteresting.erase(it++);
		} else {
			it++;
		}
	}

	/* Tarski iteration */
	bool progress;
	do {
		progress = false;
		for (typename std::map<t, CFGNode<t> *>::iterator it = uninteresting.begin();
		     it != uninteresting.end();
			) {
			CFGNode<t> *n = it->second;
			int path_length = -1;
			if (n->branch &&
			    interesting.count(n->branch->my_rip))
				path_length = interesting[n->branch->my_rip].second - 1;
			if (n->fallThrough &&
			    interesting.count(n->fallThrough->my_rip) &&
			    interesting[n->fallThrough->my_rip].second > path_length)
				path_length = interesting[n->fallThrough->my_rip].second - 1;
			if (path_length < 0) {
				it++;
			} else {
				progress = true;
				interesting[it->first] = std::pair<CFGNode<t> *, int>(
					it->second, path_length);
				uninteresting.erase(it++);
			}
		}
	} while (progress);

	/* The uninteresting set should now be correct.  Eliminate any
	   edges which go to an uninteresting target. */
	for (typename std::map<t, std::pair<CFGNode<t> *, int> >::iterator it = interesting.begin();
	     it != interesting.end();
	     it++) {
		CFGNode<t> *n = it->second.first;
		assert(n);
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
template <typename t> bool
breakCycles(CFGNode<t> *cfg, std::map<CFGNode<t> *, unsigned> &numbering,
	    CFGNode<t> **lastBackEdge, std::set<CFGNode<t> *> &onPath,
	    std::set<CFGNode<t> *> &clean)
{
	if (clean.count(cfg))
		return true;

	if (onPath.count(cfg)) {
		/* We have a cycle.  Break it. */
		assert(lastBackEdge);
		*lastBackEdge = NULL;
		return false;
	}

	onPath.insert(cfg);
	if (cfg->branch) {
		CFGNode<t> **p = lastBackEdge;
		if (numbering[cfg->branch] < numbering[cfg])
			p = &cfg->branch;
		if (!breakCycles(cfg->branch, numbering, p, onPath, clean))
			return false;
	}
	if (cfg->fallThrough) {
		CFGNode<t> **p = lastBackEdge;
		if (numbering[cfg->fallThrough] < numbering[cfg])
			p = &cfg->fallThrough;
		if (!breakCycles(cfg->fallThrough, numbering, p, onPath, clean))
			return false;
	}

	onPath.erase(cfg);

        clean.insert(cfg);
	return true;
}

/* We use a breadth first search to number the nodes and then use a
   variant of Tarjan's algorithm to detect cycles.  When we detect a
   cycle, we use the numbering scheme to identify a back edge and
   eliminate it. */
template <typename t> void
breakCycles(CFGNode<t> *cfg)
{
	std::map<CFGNode<t> *, unsigned> numbering;
	std::queue<CFGNode<t> *> queue;
	CFGNode<t> *tmp;

	/* Assign numbering */
	unsigned idx;
	idx = 0;
	queue.push(cfg);
	while (!queue.empty()) {
		tmp = queue.front();
		queue.pop();
		if (numbering.count(tmp))
			continue;
		numbering[tmp] = idx;
		idx++;
		if (tmp->branch)
			queue.push(tmp->branch);
		if (tmp->fallThrough)
			queue.push(tmp->fallThrough);
	}

	std::set<CFGNode<t> *> visited;
	std::set<CFGNode<t> *> clean;
	while (!breakCycles<t>(cfg, numbering, NULL, visited, clean)) {
		visited.clear();
		clean.clear();
	}
}
static void
assertUnoptimisable(IRExpr *e, const AllowableOptimisations &opt)
{
	bool progress = false;
	optimiseIRExpr(e, opt, &progress);
	assert(!progress);
}

class StateMachineWalker {
	void doit(StateMachine *s, std::set<StateMachine *> &visited);
	void doit(StateMachineEdge *s, std::set<StateMachine *> &visited);
public:
	virtual void visitEdge(StateMachineEdge *e) {}
	virtual void visitState(StateMachine *s) {}
	virtual void visitSideEffect(StateMachineSideEffect *smse) {}
	void doit(StateMachine *s);
};

void
StateMachineWalker::doit(StateMachine *sm, std::set<StateMachine *> &visited)
{
	if (visited.count(sm))
		return;
	visited.insert(sm);

	visitState(sm);
	if (dynamic_cast<StateMachineCrash *>(sm) ||
	    dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm) ||
	    dynamic_cast<StateMachineUnreached *>(sm))
		return;
	if (StateMachineBifurcate *smb =
	    dynamic_cast<StateMachineBifurcate *>(sm)) {
		doit(smb->trueTarget, visited);
		doit(smb->falseTarget, visited);
	} else if (StateMachineProxy *smp =
		   dynamic_cast<StateMachineProxy *>(sm)) {
		doit(smp->target, visited);
	} else {
		abort();
	}
}
void
StateMachineWalker::doit(StateMachineEdge *se, std::set<StateMachine *> &visited)
{
	visitEdge(se);
	for (std::vector<StateMachineSideEffect *>::iterator it = se->sideEffects.begin();
	     it != se->sideEffects.end();
	     it++)
		visitSideEffect(*it);
	doit(se->target, visited);
}
void
StateMachineWalker::doit(StateMachine *s)
{
	std::set<StateMachine *> visited;
	doit(s, visited);
}

class findAllStoresVisitor : public StateMachineWalker {
public:
	std::set<StateMachineSideEffectStore *> &out;
	findAllStoresVisitor(std::set<StateMachineSideEffectStore *> &o)
		: out(o)
	{}
	void visitSideEffect(StateMachineSideEffect *smse)
	{
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(smse))
			out.insert(smses);
	}
};
static void
findAllStores(StateMachine *sm, std::set<StateMachineSideEffectStore *> &out)
{
	findAllStoresVisitor v(out);
	v.doit(sm);
}

class findAllLoadsVisitor : public StateMachineWalker {
public:
	std::set<StateMachineSideEffectLoad *> &out;
	findAllLoadsVisitor(std::set<StateMachineSideEffectLoad *> &o)
		: out(o)
	{}
	void visitSideEffect(StateMachineSideEffect *smse)
	{
		if (StateMachineSideEffectLoad *smsel =
		    dynamic_cast<StateMachineSideEffectLoad *>(smse))
			out.insert(smsel);
	}
};
static void
findAllLoads(StateMachine *sm, std::set<StateMachineSideEffectLoad *> &out)
{
	findAllLoadsVisitor v(out);
	v.doit(sm);
}

class findAllEdgesVisitor : public StateMachineWalker {
public:
	std::set<StateMachineEdge *> &out;
	findAllEdgesVisitor(std::set<StateMachineEdge *> &o)
		: out(o)
	{}
	void visitEdge(StateMachineEdge *sme)
	{
		out.insert(sme);
	}
};
static void
findAllEdges(StateMachine *sm, std::set<StateMachineEdge *> &out)
{
	findAllEdgesVisitor v(out);
	v.doit(sm);
}

class findAllStatesVisitor : public StateMachineWalker {
public:
	std::set<StateMachine *> &out;
	findAllStatesVisitor(std::set<StateMachine *> &o)
		: out(o)
	{}
	void visitState(StateMachine *sm)
	{
		out.insert(sm);
	}
};
static void
findAllStates(StateMachine *sm, std::set<StateMachine *> &out)
{
	findAllStatesVisitor v(out);
	v.doit(sm);
}

static StateMachine *buildNewStateMachineWithLoadsEliminated(
	StateMachine *sm,
	std::map<StateMachine *,
	               std::set<StateMachineSideEffectStore *> > &availMap,
	std::map<StateMachine *, StateMachine *> &memo,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration &aliasing,
	Oracle *oracle);

static StateMachineEdge *
buildNewStateMachineWithLoadsEliminated(
	StateMachineEdge *sme,
	std::set<StateMachineSideEffectStore *> &initialAvail,
	std::map<StateMachine *,
	               std::set<StateMachineSideEffectStore *> > &availMap,
	std::map<StateMachine *, StateMachine *> &memo,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration &aliasing,
	Oracle *oracle)
{
	StateMachineEdge *res =
		new StateMachineEdge(buildNewStateMachineWithLoadsEliminated(sme->target, availMap, memo, opt, aliasing, oracle));

	std::set<StateMachineSideEffectStore *> currentlyAvailable(initialAvail);

	for (std::vector<StateMachineSideEffect *>::const_iterator it =
		     sme->sideEffects.begin();
	     it != sme->sideEffects.end();
	     it++) {
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(*it)) {
			for (std::set<StateMachineSideEffectStore *>::iterator it2 =
				     currentlyAvailable.begin();
			     it2 != currentlyAvailable.end();
				) {
				if ( aliasing.mightAlias((*it2)->addr, smses->addr) &&
				     !definitelyNotEqual((*it2)->addr, smses->addr, opt) ) {
					currentlyAvailable.erase(it2++);
				} else {
					it2++;
				}
			}
			if (opt.assumeExecutesAtomically || oracle->storeIsThreadLocal(smses))
				currentlyAvailable.insert(smses);
			res->sideEffects.push_back(*it);
		} else if (StateMachineSideEffectLoad *smsel =
			   dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			bool done = false;
			for (std::set<StateMachineSideEffectStore *>::iterator it2 =
				     currentlyAvailable.begin();
			     !done && it2 != currentlyAvailable.end();
			     it2++) {
				if ( aliasing.mightAlias((*it2)->addr, smsel->smsel_addr) &&
				     definitelyEqual((*it2)->addr, smsel->smsel_addr, opt) ) {
					res->sideEffects.push_back(
						new StateMachineSideEffectCopy(
							smsel->key,
							(*it2)->data));
					done = true;
				}
			}
			if (!done)
				res->sideEffects.push_back(*it);
		} else {
			assert(dynamic_cast<StateMachineSideEffectCopy *>(*it) ||
			       dynamic_cast<StateMachineSideEffectUnreached *>(*it));
			res->sideEffects.push_back(*it);
		}
	}
	return res;
}

static StateMachine *
buildNewStateMachineWithLoadsEliminated(
	StateMachine *sm,
	std::map<StateMachine *,
	               std::set<StateMachineSideEffectStore *> > &availMap,
	std::map<StateMachine *, StateMachine *> &memo,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration &alias,
	Oracle *oracle)
{
	if (dynamic_cast<StateMachineCrash *>(sm) ||
	    dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm) ||
	    dynamic_cast<StateMachineUnreached *>(sm))
		return sm;
	if (memo.count(sm))
		return memo[sm];
	if (StateMachineBifurcate *smb =
	    dynamic_cast<StateMachineBifurcate *>(sm)) {
		StateMachineBifurcate *res;
		res = new StateMachineBifurcate(sm->origin, smb->condition, (StateMachineEdge *)NULL, NULL);
		memo[sm] = res;
		res->trueTarget = buildNewStateMachineWithLoadsEliminated(
			smb->trueTarget, availMap[sm], availMap, memo, opt, alias, oracle);
		res->falseTarget = buildNewStateMachineWithLoadsEliminated(
			smb->falseTarget, availMap[sm], availMap, memo, opt, alias, oracle);
		return res;
	} if (StateMachineProxy *smp =
	      dynamic_cast<StateMachineProxy *>(sm)) {
		StateMachineProxy *res;
		res = new StateMachineProxy(sm->origin, (StateMachineEdge *)NULL);
		memo[sm] = res;
		res->target = buildNewStateMachineWithLoadsEliminated(
			smp->target, availMap[sm], availMap, memo, opt, alias, oracle);
		return res;
	} else {
		abort();
	}
}

static StateMachine *
buildNewStateMachineWithLoadsEliminated(
	StateMachine *sm,
	std::map<StateMachine *,
	         std::set<StateMachineSideEffectStore *> > &availMap,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration &alias,
	Oracle *oracle)
{
	std::map<StateMachine *, StateMachine *> memo;
	return buildNewStateMachineWithLoadsEliminated(sm, availMap, memo, opt, alias, oracle);
}

/* Available expression analysis on memory locations.  This isn't
   included in the normal optimise() operation because it's
   context-sensitive, and therefore isn't allowed to mutate nodes
   in-place. */
static StateMachine *
availExpressionAnalysis(StateMachine *sm, const AllowableOptimisations &opt,
			const Oracle::RegisterAliasingConfiguration &alias, Oracle *oracle)
{
	/* Fairly standard available expression analysis.  Each edge
	   in the state machine has two sets of
	   StateMachineSideEffectStores representing the set of things
	   which are available at the start and end of the edge.  We
	   start off with everything available everywhere except at
	   the start node (which has nothing) and then do a Tarski
	   iteration to remove all of the contradictions.  Once we
	   know what's available, it's easy enough to go through and
	   forward all of the remaining stores. */
	/* Minor tweak: the onEntry map is keyed on states rather than
	   edges, since every edge starting at a given state will have
	   the same entry map. */
	typedef std::set<StateMachineSideEffectStore *> avail_t;

	/* build the set of potentially-available expressions. */
	avail_t potentiallyAvailable;
	findAllStores(sm, potentiallyAvailable);

	/* If we're not executing atomically, stores to
	   non-thread-local memory locations are never considered to
	   be available. */
	if (!opt.assumeExecutesAtomically) {
		for (avail_t::iterator it = potentiallyAvailable.begin();
		     it != potentiallyAvailable.end();
			) {
			if (oracle->storeIsThreadLocal(*it)) {
				it++;
			} else {
				potentiallyAvailable.erase(it++);
			}
		}
	}

	/* build the initial availability map. */
	std::set<StateMachineEdge *> allEdges;
	std::set<StateMachine *> allStates;
	findAllEdges(sm, allEdges);
	findAllStates(sm, allStates);
	std::map<StateMachine *, avail_t> availOnEntry;
	std::map<StateMachineEdge *, avail_t> availOnExit;
	for (std::set<StateMachineEdge *>::iterator it = allEdges.begin();
	     it != allEdges.end();
	     it++)
		availOnExit[*it] = potentiallyAvailable;
	for (std::set<StateMachine *>::iterator it = allStates.begin();
	     it != allStates.end();
	     it++)
		availOnEntry[*it] = potentiallyAvailable;
	availOnEntry[sm].clear();

	std::set<StateMachine *> statesNeedingRefresh(allStates);

	/* Tarski iteration.  */
	bool progress;
	do {
		progress = false;

		/* Update the set of things which are available on
		   entry.  This means walking the set of edges and
		   looking at the targets.  If there's something which
		   is available at the start of the target, but not at
		   the end of this edge, remove it from the target. */
		for (std::set<StateMachineEdge *>::iterator it = allEdges.begin();
		     it != allEdges.end();
		     it++) {
			StateMachineEdge *edge = *it;
			StateMachine *target = edge->target;
			avail_t &avail_at_end_of_edge(availOnExit[edge]);
			avail_t &avail_at_start_of_target(availOnEntry[target]);
			for (avail_t::iterator it2 = avail_at_start_of_target.begin();
			     it2 != avail_at_start_of_target.end();
				) {
				if (avail_at_end_of_edge.count(*it2) == 0) {
					statesNeedingRefresh.insert(target);
					avail_at_start_of_target.erase(it2++); 
					progress = true;
				} else {
					it2++;
				}
			}
		}

		/* Now go through and update the avail-on-exit set.
		   Use a slightly weird-looking iteration over states
		   instead of over edges because that makes things a
		   bit easier. */
		for (std::set<StateMachine *>::iterator it = statesNeedingRefresh.begin();
		     it != statesNeedingRefresh.end();
		     it++) {
			if (dynamic_cast<StateMachineCrash *>(*it) ||
			    dynamic_cast<StateMachineNoCrash *>(*it) ||
			    dynamic_cast<StateMachineStub *>(*it) ||
			    dynamic_cast<StateMachineUnreached *>(*it))
				continue;
			StateMachineEdge *edges[2];
			int nr_edges;
			if (StateMachineBifurcate *smb =
			    dynamic_cast<StateMachineBifurcate *>(*it)) {
				edges[0] = smb->trueTarget;
				edges[1] = smb->falseTarget;
				nr_edges = 2;
			} else if (StateMachineProxy *smp =
				   dynamic_cast<StateMachineProxy *>(*it)) {
				edges[0] = smp->target;
				nr_edges = 1;
			} else {
				abort();
			}
			for (int x = 0; x < nr_edges; x++) {
				StateMachineEdge *edge = edges[x];
				assert(availOnEntry.count(*it));
				avail_t outputAvail(availOnEntry[*it]);

				/* Build the output set. */
				for (std::vector<StateMachineSideEffect *>::const_iterator it2 =
					     edge->sideEffects.begin();
				     it2 != edge->sideEffects.end();
				     it2++) {
					StateMachineSideEffectStore *smses =
						dynamic_cast<StateMachineSideEffectStore *>(*it2);
					if (!smses)
						continue;
					/* Eliminate anything which is killed */
					for (avail_t::iterator it3 = outputAvail.begin();
					     it3 != outputAvail.end();
						) {
						if ( alias.mightAlias((*it3)->addr,
								      smses->addr) &&
						     !definitelyNotEqual( (*it3)->addr,
									  smses->addr,
									  opt) )
							outputAvail.erase(it3++);
						else
							it3++;
					}
					/* Introduce the store which was generated. */
					if (opt.assumeExecutesAtomically ||
					    oracle->storeIsThreadLocal(smses))
						outputAvail.insert(smses);
				}
				/* Now check whether we actually did anything. */
				avail_t &currentAvail(availOnExit[edge]);
				for (avail_t::iterator it2 = currentAvail.begin();
				     it2 != currentAvail.end();
				     it2++) {
					if (!outputAvail.count(*it2))
						progress = true;
				}
				currentAvail = outputAvail;
			}
		}
		statesNeedingRefresh.clear();
	} while (progress);

	/* So after all that we now have a complete map of what's
	   available where.  Given that, we should be able to
	   construct a new state machine with redundant loads replaced
	   with copy side effects. */
	return buildNewStateMachineWithLoadsEliminated(
		sm,
		availOnEntry,
		opt,
		alias,
		oracle);
}

typedef std::pair<StateMachine *, StateMachine *> st_pair_t;
typedef std::pair<StateMachineEdge *, StateMachineEdge *> st_edge_pair_t;

static bool
hasDisallowedSideEffects(StateMachineEdge *sme,
			 const AllowableOptimisations &opt)
{
	if (opt.ignoreSideEffects)
		return false;
	for (std::vector<StateMachineSideEffect *>::iterator sideEffect =
		     sme->sideEffects.begin();
	     sideEffect != sme->sideEffects.end();
	     sideEffect++) {
		if (dynamic_cast<StateMachineSideEffectStore *>(*sideEffect))
			return true;
	}
	return false;
}

static bool
edgesLocallyBisimilar(StateMachineEdge *sme1,
		      StateMachineEdge *sme2,
		      const std::set<st_pair_t> &states,
		      const std::set<st_edge_pair_t> &edges,
		      const AllowableOptimisations &opt)
{
	if (sme1->sideEffects.size() !=
	    sme2->sideEffects.size())
		return false;
	for (unsigned x = 0; x < sme1->sideEffects.size(); x++) {
		if (!sideEffectsBisimilar(sme1->sideEffects[x],
					  sme2->sideEffects[x],
					  opt))
			return false;
	}
	if (states.count(st_pair_t(sme1->target, sme2->target)))
		return true;
	else
		return false;
}

static bool
statesLocallyBisimilar(StateMachine *sm1,
		       StateMachine *sm2,
		       const std::set<st_edge_pair_t> &edges,
		       const std::set<st_pair_t> &others,
		       const AllowableOptimisations &opt)
{
	/* Sort our arguments by type.  Ordering is:

	   Crash
	   NoCrash
	   Stub
	   Unreached
	   Proxy
	   Bifurcation
	*/
	bool swapArgs = false;
	if (!dynamic_cast<StateMachineCrash *>(sm1)) {
		if (dynamic_cast<StateMachineCrash *>(sm2)) {
			swapArgs = true;
		} else if (!dynamic_cast<StateMachineNoCrash *>(sm1)) {
			if (dynamic_cast<StateMachineNoCrash *>(sm2)) {
				swapArgs = true;
			} else if (!dynamic_cast<StateMachineStub *>(sm1)) {
				if (dynamic_cast<StateMachineStub *>(sm2)) {
					swapArgs = true;
				} else if (!dynamic_cast<StateMachineUnreached *>(sm1)) {
					if (dynamic_cast<StateMachineUnreached *>(sm2)) {
						swapArgs = true;
					} else if (!dynamic_cast<StateMachineProxy *>(sm1)) {
						assert(dynamic_cast<StateMachineBifurcate *>(sm1));
						if (dynamic_cast<StateMachineProxy *>(sm2)) {
							swapArgs = true;
						}
					}
				}
			}
		}
	}
	if (swapArgs)
		return statesLocallyBisimilar(sm2, sm1, edges, others, opt);

	if (dynamic_cast<StateMachineCrash *>(sm1)) {
		if (dynamic_cast<StateMachineCrash *>(sm2)) {
			return true;
		} else if (dynamic_cast<StateMachineNoCrash *>(sm2)) {
			return false;
		} else if (dynamic_cast<StateMachineUnreached *>(sm2)) {
			return false;
		} else if (StateMachineProxy *smp =
			   dynamic_cast<StateMachineProxy *>(sm2)) {
			/* We're locally bisimilar to a proxy if the
			   proxy's target is bisimilar to us and the
			   proxy has no disallowed side effects. */
			if (!hasDisallowedSideEffects(smp->target, opt) &&
			    others.count(st_pair_t(sm1, smp->target->target)))
				return true;
			else
				return false;
		} else if (StateMachineBifurcate *smb =
			   dynamic_cast<StateMachineBifurcate *>(sm2)) {
			/* Likewise, we're similar to a proxy if it
			   has no disallowed side-effects and both
			   targets are crash nodes. */
			if (!hasDisallowedSideEffects(smb->trueTarget, opt) &&
			    others.count(st_pair_t(sm1, smb->trueTarget->target)) &&
			    !hasDisallowedSideEffects(smb->falseTarget, opt) &&
			    others.count(st_pair_t(sm1, smb->falseTarget->target)))
				return true;
			else
				return false;
		} else {
			assert(dynamic_cast<StateMachineStub *>(sm2));
			return false;
		}
	}

	if (dynamic_cast<StateMachineNoCrash *>(sm1)) {
		if (dynamic_cast<StateMachineNoCrash *>(sm2)) {
			return true;
		} else if (dynamic_cast<StateMachineUnreached *>(sm2)) {
			return false;
		} else if (StateMachineProxy *smp =
			   dynamic_cast<StateMachineProxy *>(sm2)) {
			if (!hasDisallowedSideEffects(smp->target, opt) &&
			    others.count(st_pair_t(sm1, smp->target->target)))
				return true;
			else
				return false;
		} else if (StateMachineBifurcate *smb =
			   dynamic_cast<StateMachineBifurcate *>(sm2)) {
			if (!hasDisallowedSideEffects(smb->trueTarget, opt) &&
			    others.count(st_pair_t(sm1, smb->trueTarget->target)) &&
			    !hasDisallowedSideEffects(smb->falseTarget, opt) &&
			    others.count(st_pair_t(sm1, smb->falseTarget->target)))
				return true;
			else
				return false;
		} else {
			assert(dynamic_cast<StateMachineStub *>(sm2));
			return false;
		}
	}

	if (dynamic_cast<StateMachineUnreached *>(sm1)) {
		/* We ignore side effects for unreached states: since
		   we never go down here, any side effects are
		   completely irrelevant. */
		if (dynamic_cast<StateMachineUnreached *>(sm2)) {
			return true;
		} else if (StateMachineProxy *smp =
			   dynamic_cast<StateMachineProxy *>(sm2)) {
			if (others.count(st_pair_t(sm1, smp->target->target)))
				return true;
			else
				return false;
		} else if (StateMachineBifurcate *smb =
			   dynamic_cast<StateMachineBifurcate *>(sm2)) {
			if (others.count(st_pair_t(sm1, smb->trueTarget->target)) &&
			    others.count(st_pair_t(sm1, smb->falseTarget->target)))
				return true;
			else
				return false;
		} else {
			assert(dynamic_cast<StateMachineStub *>(sm2));
			return false;
		}
	}
	if (StateMachineStub *sms1 =
	    dynamic_cast<StateMachineStub *>(sm1)) {
		if (StateMachineStub *sms2 = dynamic_cast<StateMachineStub *>(sm2))
			return definitelyEqual(sms1->target, sms2->target, opt);
		else
			return false;
	}

	if (StateMachineProxy *smp1 =
	    dynamic_cast<StateMachineProxy *>(sm1)) {
		if (StateMachineProxy *smp2 =
		    dynamic_cast<StateMachineProxy *>(sm2)) {
			return edges.count(st_edge_pair_t(smp1->target, smp2->target)) ||
				edgesLocallyBisimilar(smp1->target,
						      smp2->target,
						      others,
						      edges,
						      opt);
		} else if (StateMachineBifurcate *smb2 =
			   dynamic_cast<StateMachineBifurcate *>(sm2)) {
			return (edges.count(st_edge_pair_t(smp1->target,
							   smb2->trueTarget)) ||
				edgesLocallyBisimilar(smp1->target,
						      smb2->trueTarget,
						      others,
						      edges,
						      opt)) &&
				(edges.count(st_edge_pair_t(smp1->target,
							    smb2->falseTarget)) ||
				 edgesLocallyBisimilar(smp1->target,
						       smb2->falseTarget,
						       others,
						       edges,
						       opt));
		} else {
			abort();
		}
	}

	StateMachineBifurcate *smb1 =
		dynamic_cast<StateMachineBifurcate *>(sm1);
	StateMachineBifurcate *smb2 =
		dynamic_cast<StateMachineBifurcate *>(sm2);
	assert(smb1);
	assert(smb2);
	return
		(edges.count(st_edge_pair_t(smb1->trueTarget, smb2->trueTarget)) ||
		 edgesLocallyBisimilar(smb1->trueTarget, smb2->trueTarget, others, edges, opt)) &&
		(edges.count(st_edge_pair_t(smb1->falseTarget, smb2->falseTarget)) ||
		 edgesLocallyBisimilar(smb1->falseTarget, smb2->falseTarget, others, edges, opt)) &&
		definitelyEqual(smb1->condition, smb2->condition, opt);
}

static StateMachine *
rewriteStateMachine(StateMachine *sm,
		    std::map<StateMachine *, StateMachine *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules,
		    std::set<StateMachine *> &memo,
		    std::set<StateMachineEdge *> &edgeMemo);

static StateMachineEdge *
rewriteStateMachineEdge(StateMachineEdge *sme,
			std::map<StateMachine *, StateMachine *> &rules,
			std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules,
			std::set<StateMachine *> &memo,
			std::set<StateMachineEdge *> &edgeMemo)
{
	if (edgeRules.count(sme)) {
		edgeMemo.insert(edgeRules[sme]);
		return rewriteStateMachineEdge(edgeRules[sme], rules, edgeRules, memo, edgeMemo);
	}
	edgeMemo.insert(sme);
	sme->target = rewriteStateMachine(sme->target,
					  rules,
					  edgeRules,
					  memo,
					  edgeMemo);
	return sme;
}

static StateMachine *
rewriteStateMachine(StateMachine *sm,
		    std::map<StateMachine *, StateMachine *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules,
		    std::set<StateMachine *> &memo,
		    std::set<StateMachineEdge *> &edgeMemo)
{
	if (rules.count(sm) && rules[sm] != sm) {
		memo.insert(rules[sm]);
		return rewriteStateMachine(rules[sm], rules, edgeRules, memo, edgeMemo);
	}
	memo.insert(sm);
	if (dynamic_cast<StateMachineCrash *>(sm) ||
	    dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm) ||
	    dynamic_cast<StateMachineUnreached *>(sm)) {
		return sm;
	} else if (StateMachineBifurcate *smb =
		   dynamic_cast<StateMachineBifurcate *>(sm)) {
		smb->trueTarget = rewriteStateMachineEdge(
			smb->trueTarget,
			rules,
			edgeRules,
			memo,
			edgeMemo);
		smb->falseTarget = rewriteStateMachineEdge(
			smb->falseTarget,
			rules,
			edgeRules,
			memo,
			edgeMemo);
		return sm;
	} else if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
		smp->target = rewriteStateMachineEdge(
			smp->target,
			rules,
			edgeRules,
			memo,
			edgeMemo);
		return sm;
	} else {
		abort();
	}
}

static StateMachine *
rewriteStateMachine(StateMachine *sm, std::map<StateMachine *, StateMachine *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules)
{
	std::set<StateMachine *> memo;
	std::set<StateMachineEdge *> edgeMemo;
	return rewriteStateMachine(sm, rules, edgeRules, memo, edgeMemo);
}

static void
buildStateMachineBisimilarityMap(StateMachine *sm, std::set<st_pair_t> &bisimilarStates,
				 std::set<st_edge_pair_t> &bisimilarEdges,
				 const std::set<StateMachine *> *allStates,
				 const AllowableOptimisations &opt)
{
	/* We start by assuming that all states are bisimilar to each
	   other, and then use Tarski iteration to eliminate the
	   contradictions.  That allows us to build up maximal sets of
	   states such that the states in the sets are bisimilar to
	   each other.  Once we've got that, we pick one of the states
	   as being representative of the set, and then use it in
	   place of the other states. */
	std::set<StateMachine *> _allStates;
	if (!allStates) {
		allStates = &_allStates;
		findAllStates(sm, _allStates);
	}

	std::set<StateMachineEdge *> allEdges;
	findAllEdges(sm, allEdges);	

	/* Initially, everything is bisimilar to everything else. */
	for (std::set<StateMachine *>::const_iterator it = allStates->begin();
	     it != allStates->end();
	     it++)
		for (std::set<StateMachine *>::const_iterator it2 = allStates->begin();
		     it2 != allStates->end();
		     it2++)
			bisimilarStates.insert(st_pair_t(*it, *it2));
	for (std::set<StateMachineEdge *>::iterator it = allEdges.begin();
	     it != allEdges.end();
	     it++)
		for (std::set<StateMachineEdge *>::iterator it2 = allEdges.begin();
		     it2 != allEdges.end();
		     it2++)
			bisimilarEdges.insert(st_edge_pair_t(*it, *it2));

	bool progress;
	do {
		progress = false;

		/* Iterate over every suspected bisimilarity pair and
		   check for ``local bisimilarity''.  Once we're
		   consistent with the local bisimilarity
		   relationship, we will also be consistent with
		   global bismilarity. */
		for (std::set<st_pair_t>::iterator it = bisimilarStates.begin();
		     it != bisimilarStates.end();
			) {
			if (statesLocallyBisimilar(it->first, it->second, bisimilarEdges, bisimilarStates, opt)) {
				it++;
			} else {
				bisimilarStates.erase(it++);
				progress = true;
			}
		}
		for (std::set<st_edge_pair_t>::iterator it = bisimilarEdges.begin();
		     it != bisimilarEdges.end();
			) {
			if (edgesLocallyBisimilar(it->first, it->second, bisimilarStates, bisimilarEdges, opt)) {
				it++;
			} else {
				bisimilarEdges.erase(it++);
				progress = true;
			}
		}
	} while (progress);

}

/* Try to identify states which are bisimilar, and then go and merge
 * them.  This is in-place, so should really be part of ::optimise();
 * nevermind. */
static StateMachine *
bisimilarityReduction(StateMachine *sm, const AllowableOptimisations &opt)
{
	std::set<st_edge_pair_t> bisimilarEdges;
	std::set<st_pair_t> bisimilarStates;
	std::set<StateMachine *> allStates;

	findAllStates(sm, allStates);
	buildStateMachineBisimilarityMap(sm, bisimilarStates, bisimilarEdges, &allStates, opt);

	std::map<StateMachine *, StateMachine *> canonMap;
	/* While we're here, iterate over every bifurcation node, and
	   if the branches are bisimilar to each other then replace it
	   with a proxy. */

	for (std::set<StateMachine *>::iterator it = allStates.begin();
	     it != allStates.end();
	     it++) {
		StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(*it);
		if (smb && bisimilarEdges.count(st_edge_pair_t(smb->trueTarget, smb->falseTarget)))
			canonMap[*it] = new StateMachineProxy((*it)->origin, smb->trueTarget);
	}

	/* Now build a mapping from states to canonical states, using
	   the bisimilarity information, such that two states map to
	   the same canonical state iff they are bisimilar. */
	/* The canonMap effectively forms an inverted forest.  Each
	   tree in the forest represents some set of bisimilar nodes,
	   and each node's entry points at its parent in the tree, if
	   it has one.  The canonical representation of each set is
	   the root of its corresponding tree.  We advance by merging
	   sets, by inserting one as a child of the root of the other,
	   in response to bisimilar state entries. */

	for (std::set<st_pair_t>::iterator it = bisimilarStates.begin();
	     it != bisimilarStates.end();
	     it++) {
		StateMachine *s1 = it->first;
		StateMachine *s2 = it->second;

		/* Map the two nodes to their canonicalisations, if
		 * they have them. */
		while (canonMap.count(s1))
			s1 = canonMap[s1];
		while (canonMap.count(s2))
			s2 = canonMap[s2];
		/* This is more subtle than it looks.  It might appear
		   that we should be able to pick pretty much
		   arbitrarily which way round we perform the mapping
		   (s2 -> s1 or s1 -> s2).  Not so: the mapping we
		   build has to respect a depth-first ordering of the
		   graph, or you risk introducing loops.  This way
		   around does respect that ordering, whereas the
		   other way around wouldn't. */
		/* XXX I'm not entirely convinced I believe that
		 * explanation. */
		if (s1 != s2)
			canonMap[s2] = s1;
	}

	/* Do the same thing for edges */
	std::map<StateMachineEdge *, StateMachineEdge *> canonEdgeMap;
	for (std::set<st_edge_pair_t>::iterator it = bisimilarEdges.begin();
	     it != bisimilarEdges.end();
	     it++) {
		StateMachineEdge *s1 = it->first;
		StateMachineEdge *s2 = it->second;
		while (canonEdgeMap.count(s1))
			s1 = canonEdgeMap[s1];
		while (canonEdgeMap.count(s2))
			s2 = canonEdgeMap[s2];
		if (s1 != s2)
			canonEdgeMap[s2] = s1;
	}

	/* Perform the rewrite.  We do this in-place, because it's not
	   context-dependent. */
	return rewriteStateMachine(sm, canonMap, canonEdgeMap);
}

static unsigned long
wrappedRipToRip(unsigned long r)
{
	return r;
}

template <typename t> StateMachine *
CFGtoStoreMachine(unsigned tid, AddressSpace *as, CFGNode<t> *cfg, std::map<CFGNode<t> *, StateMachine *> &memo)
{
	if (!cfg)
		return StateMachineNoCrash::get();
	if (memo.count(cfg))
		return memo[cfg];
	StateMachine *res;
	IRSB *irsb = as->getIRSBForAddress(tid, wrappedRipToRip(cfg->my_rip));
	int endOfInstr;
	for (endOfInstr = 1; endOfInstr < irsb->stmts_used; endOfInstr++)
		if (irsb->stmts[endOfInstr]->tag == Ist_IMark)
			break;
	if (cfg->fallThrough || !cfg->branch) {
		res = CFGtoStoreMachine(tid, as, cfg->fallThrough, memo);
		int idx = endOfInstr;
		while (idx != 0) {
			IRStmt *stmt = irsb->stmts[idx-1];
			if (stmt->tag == Ist_Exit) {
				if (cfg->branch) {
					res = new StateMachineBifurcate(
						wrappedRipToRip(cfg->my_rip),
						stmt->Ist.Exit.guard,
						CFGtoStoreMachine(tid, as, cfg->branch, memo),
						res);
				}
			} else {
				res = backtrackStateMachineOneStatement(res, stmt, wrappedRipToRip(cfg->my_rip));
			}
			idx--;
		}
	} else {
		assert(cfg->branch);
		res = CFGtoStoreMachine(tid, as, cfg->branch, memo);
		int idx;
		for (idx = endOfInstr - 1; idx >= 0; idx--)
			if (irsb->stmts[idx]->tag == Ist_Exit)
				break;
		assert(idx > 0);
		while (idx != 0) {
			IRStmt *stmt = irsb->stmts[idx-1];
			res = backtrackStateMachineOneStatement(res, stmt, wrappedRipToRip(cfg->my_rip));
			idx--;
		}
	}
	memo[cfg] = res;
	return res;		
}

template <typename t> StateMachine *
CFGtoStoreMachine(unsigned tid, AddressSpace *as, CFGNode<t> *cfg)
{
	std::map<CFGNode<t> *, StateMachine *> memo;
	return CFGtoStoreMachine(tid, as, cfg, memo);
}

class StateMachineEvalContext {
public:
	StateMachineEvalContext() : justPathConstraint(NULL) {}
	std::vector<StateMachineSideEffectStore *> stores;
	std::map<Int, IRExpr *> binders;
	/* justPathConstraint contains all of the assumptions we've
	   made using the ND chooser.  pathConstraint is that plus the
	   initial assumption. */
	IRExpr *pathConstraint;
	IRExpr *justPathConstraint;
};

static IRExpr *
specialiseIRExpr(IRExpr *iex, std::map<Int,IRExpr *> &binders)
{
	switch (iex->tag) {
	case Iex_Binder:
		assert(binders[iex->Iex.Binder.binder]);
		return binders[iex->Iex.Binder.binder];
	case Iex_Get:
		return iex;
	case Iex_GetI:
		return IRExpr_GetI(
			iex->Iex.GetI.descr,
			specialiseIRExpr(iex->Iex.GetI.ix, binders),
			iex->Iex.GetI.bias,
			iex->Iex.GetI.tid);
	case Iex_RdTmp:
		return iex;
	case Iex_Qop:
		return IRExpr_Qop(
			iex->Iex.Qop.op,
			specialiseIRExpr(iex->Iex.Qop.arg1, binders),
			specialiseIRExpr(iex->Iex.Qop.arg2, binders),
			specialiseIRExpr(iex->Iex.Qop.arg3, binders),
			specialiseIRExpr(iex->Iex.Qop.arg4, binders));
	case Iex_Triop:
		return IRExpr_Triop(
			iex->Iex.Triop.op,
			specialiseIRExpr(iex->Iex.Triop.arg1, binders),
			specialiseIRExpr(iex->Iex.Triop.arg2, binders),
			specialiseIRExpr(iex->Iex.Triop.arg3, binders));
	case Iex_Binop:
		return IRExpr_Binop(
			iex->Iex.Binop.op,
			specialiseIRExpr(iex->Iex.Binop.arg1, binders),
			specialiseIRExpr(iex->Iex.Binop.arg2, binders));
	case Iex_Unop:
		return IRExpr_Unop(
			iex->Iex.Unop.op,
			specialiseIRExpr(iex->Iex.Unop.arg, binders));
	case Iex_Load:
		return IRExpr_Load(
			iex->Iex.Load.isLL,
			iex->Iex.Load.end,
			iex->Iex.Load.ty,
			specialiseIRExpr(iex->Iex.Load.addr, binders));
	case Iex_Const:
		return iex;
	case Iex_CCall: {
		IRExpr **args;
		int n;
		for (n = 0; iex->Iex.CCall.args[n]; n++)
			;
		args = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, n + 1);
		for (n = 0; iex->Iex.CCall.args[n]; n++)
			args[n] = specialiseIRExpr(iex->Iex.CCall.args[n], binders);
		return IRExpr_CCall(
			iex->Iex.CCall.cee,
			iex->Iex.CCall.retty,
			args);
	}
	case Iex_Mux0X:
		return IRExpr_Mux0X(
			specialiseIRExpr(iex->Iex.Mux0X.cond, binders),
			specialiseIRExpr(iex->Iex.Mux0X.expr0, binders),
			specialiseIRExpr(iex->Iex.Mux0X.exprX, binders));
	case Iex_Associative: {
		IRExpr *res = IRExpr_Associative(iex);
		for (int it = 0;
		     it < res->Iex.Associative.nr_arguments;
		     it++)
			res->Iex.Associative.contents[it] =
				specialiseIRExpr(res->Iex.Associative.contents[it],
						 binders);
		return res;
	}
	}
	abort();
}

static bool
expressionIsTrue(IRExpr *exp, NdChooser &chooser, std::map<Int, IRExpr *> &binders, IRExpr **assumption,
		 IRExpr **accumulatedAssumptions)
{
	exp = optimiseIRExpr(
		specialiseIRExpr(exp, binders),
		AllowableOptimisations::defaultOptimisations);

	/* Combine the path constraint with the new expression and see
	   if that produces a contradiction.  If it does then we know
	   for sure that the new expression is false. */
	IRExpr *e =
		optimiseIRExpr(
			IRExpr_Binop(
				Iop_And1,
				*assumption,
				exp),
			AllowableOptimisations::defaultOptimisations);
	if (e->tag == Iex_Const) {
		/* That shouldn't produce the constant 1 very often.
		   If it does, it indicates that the path constraint
		   is definitely true, and the new expression is
		   definitely true, but for some reason we weren't
		   able to simplify the path constraint down to 1
		   earlier.  Consider that a lucky break and simplify
		   it now. */
		if (e->Iex.Const.con->Ico.U1) {
			assertUnoptimisable(e, AllowableOptimisations::defaultOptimisations);
			*assumption = e;
			return true;
		} else {
			return false;
		}
	}

	/* Now try it the other way around, by combining the path
	   constraint with ¬exp.  If we had a perfect theorem prover
	   this would be redundant with the previous version, but we
	   don't, so it isn't. */
	IRExpr *e2 =
		optimiseIRExpr(
			IRExpr_Binop(
				Iop_And1,
				*assumption,
				IRExpr_Unop(
					Iop_Not1,
					exp)),
			AllowableOptimisations::defaultOptimisations);
	if (e2->tag == Iex_Const) {
		/* If X & ¬Y is definitely true, Y is definitely
		 * false and X is definitely true. */
		if (e2->Iex.Const.con->Ico.U1) {
			*assumption = IRExpr_Const(IRConst_U1(1));
			return false;
		}

		/* So now we know that X & ¬Y is definitely false, and
		 * we assume that X is true.  Therefore ¬Y is false
		 * and Y is true. */
		return true;
	}

	/* Can't prove it one way or another.  Use the
	   non-deterministic chooser to guess. */
	int res;
	bool isNewChoice;
	res = chooser.nd_choice(2, &isNewChoice);

#if 0
	if (isNewChoice) {
		printf("Having to use state split to check whether ");
		ppIRExpr(exp, stdout);
		printf(" is true under assumption ");
		ppIRExpr(*assumption, stdout);
		printf("\n");
	}
#endif

	if (res == 0) {
		assertUnoptimisable(e, AllowableOptimisations::defaultOptimisations);
		*assumption = e;
		if (accumulatedAssumptions && *accumulatedAssumptions)
			*accumulatedAssumptions =
				optimiseIRExpr(
					IRExpr_Binop(
						Iop_And1,
						*accumulatedAssumptions,
						exp),
					AllowableOptimisations::defaultOptimisations);
		return true;
	} else {
		assertUnoptimisable(e2, AllowableOptimisations::defaultOptimisations);
		*assumption = e2;
		if (accumulatedAssumptions && *accumulatedAssumptions)
			*accumulatedAssumptions =
				optimiseIRExpr(
					IRExpr_Binop(
						Iop_And1,
						*accumulatedAssumptions,
						IRExpr_Unop(
							Iop_Not1,
							exp)),
					AllowableOptimisations::defaultOptimisations);
		return false;
	}
}

static bool
evalExpressionsEqual(IRExpr *exp1, IRExpr *exp2, NdChooser &chooser, std::map<Int, IRExpr *> &binders,
		     IRExpr **assumption, IRExpr **accAssumptions)
{
	return expressionIsTrue(IRExpr_Binop(
					Iop_CmpEQ64,
					exp1,
					exp2),
				chooser,
				binders,
				assumption,
				accAssumptions);
}

static void evalStateMachine(StateMachine *sm,
			     bool *crashes,
			     NdChooser &chooser,
			     Oracle *oracle,
			     StateMachineEvalContext &ctxt);

static void
evalStateMachineSideEffect(StateMachineSideEffect *smse,
			   NdChooser &chooser,
			   Oracle *oracle,
			   std::map<Int, IRExpr *> &binders,
			   std::vector<StateMachineSideEffectStore *> &stores,
			   IRExpr **assumption,
			   IRExpr **accumulatedAssumptions)
{
	if (StateMachineSideEffectStore *smses =
	    dynamic_cast<StateMachineSideEffectStore *>(smse)) {
		stores.push_back(
			new StateMachineSideEffectStore(
				specialiseIRExpr(smses->addr, binders),
				specialiseIRExpr(smses->data, binders),
				smses->rip
				)
				);
	} else if (StateMachineSideEffectLoad *smsel =
		   dynamic_cast<StateMachineSideEffectLoad *>(smse)) {
		IRExpr *val;
		val = NULL;
		for (std::vector<StateMachineSideEffectStore *>::reverse_iterator it = stores.rbegin();
		     !val && it != stores.rend();
		     it++) {
			StateMachineSideEffectStore *smses = *it;
			if (!oracle->memoryAccessesMightAlias(smsel, smses))
				continue;
			if (evalExpressionsEqual(smses->addr, smsel->smsel_addr, chooser, binders, assumption, accumulatedAssumptions))
				val = smses->data;
		}
		if (!val)
			val = IRExpr_Load(False, Iend_LE, Ity_I64, smsel->smsel_addr);
		binders[smsel->key] = val;
	} else if (StateMachineSideEffectCopy *smsec =
		   dynamic_cast<StateMachineSideEffectCopy *>(smse)) {
		binders[smsec->key] =
			specialiseIRExpr(smsec->value, binders);
	} else {
		abort();
	}
}

static void
evalStateMachineEdge(StateMachineEdge *sme,
		     bool *crashes,
		     NdChooser &chooser,
		     Oracle *oracle,
		     StateMachineEvalContext &ctxt)
{
	for (std::vector<StateMachineSideEffect *>::iterator it = sme->sideEffects.begin();
	     it != sme->sideEffects.end();
	     it++)
		evalStateMachineSideEffect(*it, chooser, oracle, ctxt.binders,
					   ctxt.stores, &ctxt.pathConstraint,
					   &ctxt.justPathConstraint);
	evalStateMachine(sme->target, crashes, chooser, oracle, ctxt);
}

/* Walk the state machine and figure out whether it's going to crash.
   If we hit something which we can't solve statically or via the
   oracle, ask the chooser which way we should go, and then emit a
   path constraint saying which way we went.  Stubs are assumed to
   never crash. */
static void
evalStateMachine(StateMachine *sm,
		 bool *crashes,
		 NdChooser &chooser,
		 Oracle *oracle,
		 StateMachineEvalContext &ctxt)
{
	if (dynamic_cast<StateMachineCrash *>(sm)) {
		*crashes = true;
		return;
	}
	if (dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm)) {
		*crashes = false;
		return;
	}
	if (StateMachineProxy *smp =
	    dynamic_cast<StateMachineProxy *>(sm)) {
		evalStateMachineEdge(smp->target, crashes, chooser, oracle, ctxt);
		return;
	}
	if (StateMachineBifurcate *smb =
	    dynamic_cast<StateMachineBifurcate *>(sm)) {
		if (expressionIsTrue(smb->condition, chooser, ctxt.binders, &ctxt.pathConstraint, &ctxt.justPathConstraint)) {
			evalStateMachineEdge(smb->trueTarget, crashes, chooser, oracle, ctxt);
		} else {
			evalStateMachineEdge(smb->falseTarget, crashes, chooser, oracle, ctxt);
		}
		return;
	}
	abort();
}

/* Assume that @sm executes atomically.  Figure out a constraint on
   the initial state which will lead to it not crashing. */
static IRExpr *
survivalConstraintIfExecutedAtomically(VexPtr<StateMachine, &ir_heap> &sm,
				       VexPtr<Oracle> &oracle,
				       GarbageCollectionToken token)
{
	NdChooser chooser;
	VexPtr<IRExpr, &ir_heap> currentConstraint(IRExpr_Const(IRConst_U1(1)));
	bool crashes;

	do {
		LibVEX_maybe_gc(token);
		StateMachineEvalContext ctxt;
		ctxt.pathConstraint = IRExpr_Const(IRConst_U1(1));
		evalStateMachine(sm, &crashes, chooser, oracle, ctxt);
		if (crashes) {
			/* This path leads to a crash, so the
			   constraint should include something to make
			   sure that we don't go down here. */
			IRExpr *newConstraint =
				IRExpr_Binop(
					Iop_And1,
					currentConstraint,
					IRExpr_Unop(
						Iop_Not1,
						ctxt.pathConstraint));
			ctxt.pathConstraint =
				optimiseIRExpr(
					IRExpr_Unop(Iop_Not1, ctxt.pathConstraint),
					AllowableOptimisations::defaultOptimisations);
			newConstraint = optimiseIRExpr(newConstraint,
						       AllowableOptimisations::defaultOptimisations);
			currentConstraint = newConstraint;
		}
	} while (chooser.advance());

	return currentConstraint;
}

static IROp
random_irop(void)
{
	return (IROp)((unsigned long)Iop_Add8 + random() % (Iop_Perm8x16 - Iop_Add8 + 1));
}

static IRType
random_irtype(void)
{
	return (IRType)((unsigned long)Ity_I8 + random() % 7);
}

static IRConst *
random_irconst(void)
{
	switch (random_irtype()) {
	case Ity_I8:
		return IRConst_U8(random() % 256);
	case Ity_I16:
		return IRConst_U16(random() % 65536);
	case Ity_I32:
		return IRConst_U32(random());
	case Ity_I64:
		return IRConst_U64(random());
	case Ity_F32:
	case Ity_I128:
		return random_irconst();
	case Ity_F64:
		return IRConst_F64(random() / (double)random());
	case Ity_V128:
		return IRConst_V128(random());
	default:
		abort();
	}
}

static IRRegArray *
random_irregarray(void)
{
	return mkIRRegArray( (random() % 10) * 8,
			     random_irtype(),
			     random() % 16 );
}

static IRExpr *
random_irexpr(unsigned depth)
{
	if (!depth)
		return IRExpr_Const(random_irconst());
	switch (random() % 8) {
	case 0:
		return IRExpr_Binder(random() % 30);
	case 1:
		return IRExpr_Get((random() % 40) * 8,
				  random_irtype(),
				  73);
	case 2:
		return IRExpr_RdTmp(random() % 5, 73);
	case 3:
		switch (random() % 5) {
		case 0:
			return IRExpr_Unop(random_irop(), random_irexpr(depth - 1));
		case 1:
			return IRExpr_Binop(
				random_irop(),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1));
		case 2:
			return IRExpr_Triop(
				random_irop(),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1));
		case 3:
			return IRExpr_Qop(
				random_irop(),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1));
		case 4: {
			IRExpr *e = IRExpr_Associative(
				random_irop(),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1),
				NULL);
			while (random() % 2)
				addArgumentToAssoc(e, random_irexpr(depth - 1));
			return e;
		}
		default:
			abort();
		}
	case 4:
		return IRExpr_Load(
			False,
			Iend_LE,
			random_irtype(),
			random_irexpr(depth - 1));
	case 5:
		return IRExpr_Const(random_irconst());
	case 6: {
		IRExpr **args;
		switch (random() % 4) {
		case 0:
			args = mkIRExprVec_0();
			break;
		case 1:
			args = mkIRExprVec_1(random_irexpr(depth - 1));
			break;
		case 2:
			args = mkIRExprVec_2(random_irexpr(depth - 1), random_irexpr(depth - 1));
			break;
		case 3:
			args = mkIRExprVec_3(random_irexpr(depth - 1), random_irexpr(depth - 1), random_irexpr(depth - 1));
			break;
		default:
			abort();
		}
		return IRExpr_CCall(mkIRCallee(0, "random_ccall", (void *)0x52),
				    random_irtype(),
				    args);
	}
	case 7:
		return IRExpr_Mux0X(random_irexpr(depth - 1), random_irexpr(depth - 1), random_irexpr(depth - 1));
	case 8:
		return IRExpr_GetI(random_irregarray(), random_irexpr(depth - 1), (random() % 20) * 8, 98);
	default:
		abort();
	}		
}

/* Check that sortIRExprs() produces vaguely sane results. */
static void
sanity_check_irexpr_sorter(void)
{
	srandom(time(NULL));
#define NR_EXPRS 10000
	IRExpr *exprs[NR_EXPRS];
	int x;
	int y;

	printf("Generating %d random expressions\n", NR_EXPRS);
	for (x = 0; x < NR_EXPRS; x++)
		exprs[x] = random_irexpr(3);

	printf("Ordering should be anti-reflexive.\n");
	for (x = 0; x < NR_EXPRS; x++)
		assert(!sortIRExprs(exprs[x], exprs[x]));

	printf("Ordering should be anti-symmetric.\n");
	for (x = 0; x < NR_EXPRS; x++) {
		for (y = x + 1; y < NR_EXPRS; y++) {
			if (sortIRExprs(exprs[x], exprs[y]))
				assert(!sortIRExprs(exprs[y], exprs[x]));
		}
	}

	/* Ordering must be transitive and total.  We check this by
	 * performing a naive topological sort on the expressions and
	 * then checking that whenever x < y exprs[x] < exprs[y]. */
	IRExpr *exprs2[NR_EXPRS];

	int nr_exprs2 = 0;
	int candidate;
	int probe;
	bool progress = true;
	printf("Toposorting...\n");
	while (nr_exprs2 < NR_EXPRS) {
		/* Try to find an ordering-minimal entry in the
		 * array.  */
		assert(progress);
		progress = false;
		for (candidate = 0; candidate < NR_EXPRS; candidate++) {
			if (!exprs[candidate])
				continue;
			for (probe = 0; probe < NR_EXPRS; probe++) {
				if (!exprs[probe])
					continue;
				if (sortIRExprs(exprs[probe], exprs[candidate])) {
					/* probe is less than
					   candidate, so candidate
					   fails. */
					break;
				}
			}
			if (probe == NR_EXPRS) {
				/* This candidate passes.  Add it to
				   the list. */
				exprs2[nr_exprs2] = exprs[candidate];
				exprs[candidate] = NULL;
				nr_exprs2++;
				progress = true;
			}
		}
	}

	/* Okay, have a topo sort.  The ordering is supposed to be
	   total, so that should have just been an O(n^3) selection
	   sort, and the array should now be totally sorted.  check
	   it. */
	printf("Check toposort is total...\n");
	for (x = 0; x < NR_EXPRS; x++)
		for (y = x + 1; y < NR_EXPRS; y++)
			assert(!sortIRExprs(exprs2[y], exprs2[x]));
#undef NR_EXPRS
}

static void
sanity_check_optimiser(void)
{
	/* x + -x -> 0 */
	IRExpr *start =
		IRExpr_Associative(
			Iop_Add64,
			IRExpr_Get(0, Ity_I64, 0),
			IRExpr_Unop(
				Iop_Neg64,
				IRExpr_Get(0, Ity_I64, 0)),
			NULL);
	IRExpr *end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	assert(physicallyEqual(end, IRExpr_Const(IRConst_U64(0))));
	/* x & ~x -> 0 */
	start = IRExpr_Associative(
		Iop_And1,
		IRExpr_Unop(
			Iop_Not1,
			IRExpr_Get(0, Ity_I64, 0)),
		IRExpr_Get(0, Ity_I64, 0),
		NULL);
	end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	assert(physicallyEqual(end, IRExpr_Const(IRConst_U1(0))));
}

static void
evalMachineUnderAssumption(VexPtr<StateMachine, &ir_heap> &sm, VexPtr<Oracle> &oracle,
			   VexPtr<IRExpr, &ir_heap> assumption,
			   bool *mightSurvive, bool *mightCrash,
			   GarbageCollectionToken token)
{
	NdChooser chooser;
	bool crashes;

	assertUnoptimisable(assumption, AllowableOptimisations::defaultOptimisations);
	*mightSurvive = false;
	*mightCrash = false;
	while (!*mightCrash || !*mightSurvive) {
		LibVEX_maybe_gc(token);
		StateMachineEvalContext ctxt;
		assertUnoptimisable(assumption, AllowableOptimisations::defaultOptimisations);
		ctxt.pathConstraint = assumption;
		evalStateMachine(sm, &crashes, chooser, oracle, ctxt);
		assertUnoptimisable(assumption, AllowableOptimisations::defaultOptimisations);
		if (crashes)
			*mightCrash = true;
		else
			*mightSurvive = true;
		if (!chooser.advance())
			break;
	}
}

class CrossEvalState {
public:
	StateMachineEdge *currentEdge;
	unsigned nextEdgeSideEffectIdx;
	bool finished;
	bool crashed;
	std::map<Int, IRExpr *> binders;
	CrossEvalState(StateMachineEdge *_e, int _i)
		: currentEdge(_e), nextEdgeSideEffectIdx(_i), finished(false),
		  crashed(false)
	{}
};

class CrossMachineEvalContext {
public:
	IRExpr *pathConstraint;
	std::vector<StateMachineSideEffectStore *> stores;
	CrossEvalState *states[2];
	std::vector<StateMachineSideEffect *> history;
	void advanceMachine(unsigned tid, NdChooser &chooser, Oracle *oracle);
	void advanceToSideEffect(unsigned tid, NdChooser &chooser, Oracle *oracle);
	void dumpHistory(void) const;
};

void
CrossMachineEvalContext::dumpHistory(void) const
{
	for (std::vector<StateMachineSideEffect *>::const_iterator it = history.begin();
	     it != history.end();
	     it++) {
		printf("\t");
		(*it)->prettyPrint(stdout);
		printf("\n");
	}
}

void
CrossMachineEvalContext::advanceToSideEffect(unsigned tid,
					     NdChooser &chooser,
					     Oracle *oracle)
{
	CrossEvalState *machine = states[tid];
	StateMachine *s;

top:
	while (machine->nextEdgeSideEffectIdx == machine->currentEdge->sideEffects.size()) {
		/* We've hit the end of the edge.  Move to the next
		 * state. */
		s = machine->currentEdge->target;
		assert(!dynamic_cast<StateMachineUnreached *>(s));
		if (dynamic_cast<StateMachineCrash *>(s)) {
			machine->finished = true;
			machine->crashed = true;
			return;
		}
		if (dynamic_cast<StateMachineNoCrash *>(s) ||
		    dynamic_cast<StateMachineStub *>(s)) {
			machine->finished = true;
			return;
		}
		if (StateMachineProxy *smp =
		    dynamic_cast<StateMachineProxy *>(s)) {
			machine->currentEdge = smp->target;
			machine->nextEdgeSideEffectIdx = 0;
			continue;
		}
		if (StateMachineBifurcate *smb =
		    dynamic_cast<StateMachineBifurcate *>(s)) {
			if (expressionIsTrue(smb->condition, chooser, machine->binders, &pathConstraint, NULL))
				machine->currentEdge = smb->trueTarget;
			else
				machine->currentEdge = smb->falseTarget;
			machine->nextEdgeSideEffectIdx = 0;
			continue;
		}
		abort();
	}

	/* You don't need to context switch after a copy, because
	   they're purely local. */
	StateMachineSideEffect *se;
	se = machine->currentEdge->sideEffects[machine->nextEdgeSideEffectIdx];
	if (dynamic_cast<StateMachineSideEffectCopy *>(se)) {
		evalStateMachineSideEffect(se, chooser, oracle, machine->binders, stores, &pathConstraint, NULL);
		history.push_back(se);
		machine->nextEdgeSideEffectIdx++;
		goto top;
	}
}

void
CrossMachineEvalContext::advanceMachine(unsigned tid,
					NdChooser &chooser,
					Oracle *oracle)
{
	CrossEvalState *machine = states[tid];

top:
	advanceToSideEffect(tid, chooser, oracle);
	if (machine->finished || machine->crashed)
		return;

	StateMachineSideEffect *se;
	se = machine->currentEdge->sideEffects[machine->nextEdgeSideEffectIdx];	
	assert(!dynamic_cast<StateMachineSideEffectCopy *>(se));
	assert(!dynamic_cast<StateMachineSideEffectUnreached *>(se));
	evalStateMachineSideEffect(se, chooser, oracle, machine->binders, stores, &pathConstraint, NULL);
	history.push_back(se);
	machine->nextEdgeSideEffectIdx++;

	advanceToSideEffect(tid, chooser, oracle);

	/* Now look at what the other machine is doing, and decide
	   whether the side effect we just issued might conceivably
	   race with the other machine's current side effect. */
	CrossEvalState *other = states[1-tid];
	if (other->finished) {
		/* If the other machine has finished then there really
		   is no point in continuing to explore alternative
		   interleavings. */
		goto top;
	}

	assert(other->nextEdgeSideEffectIdx < other->currentEdge->sideEffects.size());
	StateMachineSideEffect *otherSe = other->currentEdge->sideEffects[other->nextEdgeSideEffectIdx];
	if (StateMachineSideEffectLoad *otherLoad =
	    dynamic_cast<StateMachineSideEffectLoad *>(otherSe)) {
		if (StateMachineSideEffectStore *localStore =
		    dynamic_cast<StateMachineSideEffectStore *>(se)) {
			if (!oracle->memoryAccessesMightAlias(otherLoad, localStore) ||
			    definitelyNotEqual(otherLoad->smsel_addr, localStore->addr, 
					       AllowableOptimisations::defaultOptimisations)) {
				goto top;
			}
		} else {
			assert(dynamic_cast<StateMachineSideEffectLoad *>(se));
			/* Two loads can never alias */
			goto top;
		}
	} else {
		StateMachineSideEffectStore *otherStore =
			dynamic_cast<StateMachineSideEffectStore *>(otherSe);
		assert(otherStore);

		if (StateMachineSideEffectStore *localStore =
		    dynamic_cast<StateMachineSideEffectStore *>(se)) {
			if (!oracle->memoryAccessesMightAlias(otherStore, localStore) ||
			    definitelyNotEqual(otherStore->addr, localStore->addr, 
					       AllowableOptimisations::defaultOptimisations))
				goto top;
		} else {
			StateMachineSideEffectLoad *localLoad =
				dynamic_cast<StateMachineSideEffectLoad *>(se);
			if (!oracle->memoryAccessesMightAlias(localLoad, otherStore) ||
			    definitelyNotEqual(otherStore->addr, localLoad->smsel_addr, 
					       AllowableOptimisations::defaultOptimisations))
				goto top;
		}
	}			
}

/* Run sm1 and sm2 in parallel, ***stopping as soon as sm1
 * terminates***.  Consider every possible interleaving of the
 * machines, and every possible aliasing pattern.  Set *mightSurvive
 * to true if any run caused sm1 to reach a NoCrash state, otherwise
 * set it to false; likewise *mightCrash for Crash states. */
static void
evalCrossProductMachine(VexPtr<StateMachine, &ir_heap> &sm1,
			VexPtr<StateMachine, &ir_heap> &sm2,
			VexPtr<Oracle> &oracle,
			VexPtr<IRExpr, &ir_heap> &initialStateCondition,
			bool *mightSurvive,
			bool *mightCrash,
			GarbageCollectionToken token)
{
	NdChooser chooser;

	*mightSurvive = false;
	*mightCrash = false;

	VexPtr<StateMachineEdge, &ir_heap> sme1(new StateMachineEdge(sm1));
	VexPtr<StateMachineEdge, &ir_heap> sme2(new StateMachineEdge(sm2));
	while (!*mightCrash || !*mightSurvive) {
		LibVEX_maybe_gc(token);

		CrossMachineEvalContext ctxt;
		assert(ctxt.stores.size() == 0);
		ctxt.pathConstraint = initialStateCondition;
		CrossEvalState s1(sme1, 0);
		CrossEvalState s2(sme2, 0);
		ctxt.states[0] = &s1;
		ctxt.states[1] = &s2;
		ctxt.advanceToSideEffect(0, chooser, oracle);
		ctxt.advanceToSideEffect(1, chooser, oracle);
		while (!s1.finished && !s2.finished)
			ctxt.advanceMachine(chooser.nd_choice(2),
					    chooser,
					    oracle);
		while (!s1.finished)
			ctxt.advanceMachine(0, chooser, oracle);
		if (s1.crashed) {
#if 0
			if (!*mightCrash) {
				printf("First crashing history:\n");
				ctxt.dumpHistory();
			}
#endif
			*mightCrash = true;
		} else {
#if 0
			if (!*mightSurvive) {
				printf("First surviving history:\n");
				ctxt.dumpHistory();
			}
#endif
			*mightSurvive = true;
		}
		if (!chooser.advance())
			break;
	}
}

/* Running the store machine atomically and then runing the probe
   machine atomically shouldn't ever crash.  Tweak the initial
   assumption so that it doesn't.  Returns NULL if that's not
   possible. */
static IRExpr *
writeMachineSuitabilityConstraint(
	StateMachine *readMachine,
	StateMachine *writeMachine,
	IRExpr *assumption,
	Oracle *oracle)
{
	printf("\t\tBuilding write machine suitability constraint.\n");
	IRExpr *rewrittenAssumption = assumption;
	NdChooser chooser;
	StateMachineEdge *writeStartEdge = new StateMachineEdge(writeMachine);
	do {
		std::vector<StateMachineSideEffectStore *> storesIssuedByWriter;
		std::map<Int, IRExpr *> writerBinders;
		StateMachineEdge *writerEdge;
		IRExpr *pathConstraint;
		IRExpr *thisTimeConstraint;

		pathConstraint = assumption;
		writerEdge = writeStartEdge;
		thisTimeConstraint = IRExpr_Const(IRConst_U1(1));
		while (1) {
			for (unsigned i = 0; i < writerEdge->sideEffects.size(); i++) {
				evalStateMachineSideEffect(writerEdge->sideEffects[i],
							   chooser,
							   oracle,
							   writerBinders,
							   storesIssuedByWriter,
							   &pathConstraint,
							   &thisTimeConstraint);
			}

			StateMachine *s = writerEdge->target;
			if (dynamic_cast<StateMachineCrash *>(s) ||
			    dynamic_cast<StateMachineNoCrash *>(s) ||
			    dynamic_cast<StateMachineStub *>(s)) {
				/* Hit end of writer */
				break;
			} else if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(s)) {
				writerEdge = smp->target;
			} else {
				StateMachineBifurcate *smb =
					dynamic_cast<StateMachineBifurcate *>(s);
				assert(smb);
				if (expressionIsTrue(smb->condition, chooser, writerBinders, &pathConstraint, &thisTimeConstraint))
					writerEdge = smb->trueTarget;
				else
					writerEdge = smb->falseTarget;
			}
		}

		StateMachineEvalContext readEvalCtxt;
		readEvalCtxt.pathConstraint = pathConstraint;
		readEvalCtxt.stores = storesIssuedByWriter;
		readEvalCtxt.justPathConstraint = thisTimeConstraint;
		bool crashes;
		evalStateMachine(readMachine, &crashes, chooser, oracle, readEvalCtxt);
		if (crashes) {
			/* We get a crash if we evaluate the read
			   machine after running the store machine to
			   completion -> this is a poor choice of
			   store machines. */
			printf("Bad assumptions:\n");
			ppIRExpr(readEvalCtxt.justPathConstraint, stdout);
			printf("\n");

			/* If we evaluate the read machine to
			   completion after running the write
			   machine to completion under these
			   assumptions then we get a crash ->
			   these assumptions must be false. */
			rewrittenAssumption = optimiseIRExpr(
				IRExpr_Binop(
					Iop_And1,
					rewrittenAssumption,
					IRExpr_Unop(
						Iop_Not1,
						readEvalCtxt.justPathConstraint)),
				AllowableOptimisations::defaultOptimisations);
		}
	} while (chooser.advance());
	
	if (rewrittenAssumption->tag == Iex_Const &&
	    rewrittenAssumption->Iex.Const.con->Ico.U64 == 0) {
		printf("\t\tBad choice of machines\n");
		return NULL;
	}
	return rewrittenAssumption;
}

/* Run the write machine, covering every possible schedule and
 * aliasing pattern.  After every store, run the read machine
 * atomically.  Find ranges of the store machine where the read
 * machine predicts a crash; these ranges are the remote macro
 * sections (as opposed to remote micro sections, which are just the
 * individual stores).  We assume that @assumption holds before
 * either machine starts running. */
/* Returns false if we discover something which suggests that this is
 * a bad choice of write machine, or true otherwise. */
static bool
findRemoteMacroSections(StateMachine *readMachine,
			StateMachine *writeMachine,
			IRExpr *assumption,
			Oracle *oracle,
			std::set<std::pair<StateMachineSideEffectStore *,
			                   StateMachineSideEffectStore *> > &output)
{
	NdChooser chooser;

	StateMachineEdge *writeStartEdge = new StateMachineEdge(writeMachine);
	do {
		std::vector<StateMachineSideEffectStore *> storesIssuedByWriter;
		std::map<Int, IRExpr *> writerBinders;
		StateMachineEdge *writerEdge;
		unsigned writeEdgeIdx;
		IRExpr *pathConstraint;
		StateMachineSideEffectStore *sectionStart;

		writeEdgeIdx = 0;
		pathConstraint = assumption;
		writerEdge = writeStartEdge;
		sectionStart = NULL;
		while (1) {
			/* Have we hit the end of the current writer edge? */
			if (writeEdgeIdx == writerEdge->sideEffects.size()) {
				/* Yes, move to the next state. */
				StateMachine *s = writerEdge->target;
				assert(!dynamic_cast<StateMachineUnreached *>(s));
				if (dynamic_cast<StateMachineCrash *>(s) ||
				    dynamic_cast<StateMachineNoCrash *>(s) ||
				    dynamic_cast<StateMachineStub *>(s)) {
					/* Hit the end of the writer
					 * -> we're done. */
					break;
				}
				if (StateMachineProxy *smp =
				    dynamic_cast<StateMachineProxy *>(s)) {
					writerEdge = smp->target;
					writeEdgeIdx = 0;
					continue;
				}
				StateMachineBifurcate *smb =
					dynamic_cast<StateMachineBifurcate *>(s);
				assert(smb);
				if (expressionIsTrue(smb->condition, chooser, writerBinders, &pathConstraint, NULL))
					writerEdge = smb->trueTarget;
				else
					writerEdge = smb->falseTarget;
				writeEdgeIdx = 0;
				continue;				
			}

			/* Advance the writer by one state.  Note that
			   we *don't* consider running the read before
			   any write states, as that's already been
			   handled and is known to lead to
			   no-crash. */
			StateMachineSideEffect *se;
			se = writerEdge->sideEffects[writeEdgeIdx];
			evalStateMachineSideEffect(se, chooser, oracle, writerBinders, storesIssuedByWriter, &pathConstraint, NULL);
			writeEdgeIdx++;

			/* Advance to a store */
			StateMachineSideEffectStore *smses =
				dynamic_cast<StateMachineSideEffectStore *>(se);
			if (!smses)
				continue;

			/* The writer just issued a store, so we
			   should now try running the reader
			   atomically.  We discard any stores issued
			   by the reader once it's finished, but we
			   need to track them while it's running, so
			   need a fresh eval ctxt and a fresh copy of
			   the stores list every time around the
			   loop. */
			StateMachineEvalContext readEvalCtxt;
			readEvalCtxt.pathConstraint = pathConstraint;
			readEvalCtxt.stores = storesIssuedByWriter;
			bool crashes;
			evalStateMachine(readMachine, &crashes, chooser, oracle, readEvalCtxt);
			if (crashes) {
				if (!sectionStart) {
					/* The previous attempt at
					   evaluating the read machine
					   didn't lead to a crash, so
					   this is the start of a
					   critical section. */
					sectionStart = smses;
				} else {
					/* Critical section
					 * continues. */
				}
			} else {
				if (sectionStart) {
					/* Previous attempt did crash
					   -> this is the end of the
					   section. */
					output.insert(std::pair<StateMachineSideEffectStore *,
						                StateMachineSideEffectStore *>(sectionStart, smses));
					sectionStart = NULL;
				}
			}
		}

		/* This is enforced by the suitability check at the
		 * top of this function. */
		assert(sectionStart == NULL);
	} while (chooser.advance());
	return true;
}

/* Build up a static call graph which covers, at a minimum, all of the
 * RIPs included in the input set.  Functions in the graph are
 * represented by a combination of the set of RIPs in the function,
 * plus a set of functions which are statically called from that
 * function. */
/* Tail calls are a fairly major complication here.  If you see a call
 * to X, and another call to Y where Y tail calls into X, it would
 * naturally look like X and Y overlap, which confuses things.  In
 * that case, we have to split Y so that they no longer overlap.  If X
 * is discovered first then that's actually trivial (you just stop
 * exploring Y when you hit X's head), but if Y is discovered first
 * then it's quite messy.  We give up at that point, removing Y from
 * the known set, exploring X, and then re-exploring Y.
 */
/* There's also a bit of a bootstrapping problem.  We're given a bunch
 * of RIPs, but function heads to start from.  We start by picking a
 * RIP pretty much at random and assuming that it's a function head.
 * That mostly works reasonably well, even if it isn't, because we
 * effectively just cut off the part of the function before that
 * instruction.  The problem comes if there's another root instruction
 * in the same ``real'' function from which the speculative head is
 * reachable.  In that case, we'll insert a function boundary where
 * there isn't one (due to the tail-call elimination heuristic
 * discussed above), which can in turn lead to the introduction of
 * bogus recursion, which screws with the cycle breaking heuristic.
 * The fix for that is to purge the function which we derived from the
 * assumed head and continue.
 *
 * Note that this is pretty much the opposite to what we do if we
 * suspect a tail call, so we need to track whether a head is real
 * (obtained from following a call instruction) or assumed (obtained
 * directly from a root).  Note also that we *don't* purge the
 * functions which were obtained by tracing from the assumed head, as
 * the new subsuming head is guaranteed to find them again, and
 * this makes things a little bit quicker.
 */
class CallGraphEntry : public GarbageCollected<CallGraphEntry, &ir_heap> {
public:
	CallGraphEntry(unsigned long r, int _depth)
		: headRip(r),
		  callees(new gc_pair_ulong_set_t()),
		  instructions(new RangeSet()),
		  calls(new gc_heap_map<unsigned long, CallGraphEntry, &ir_heap>::type()),
		  depth(_depth)
	{}
	unsigned long headRip;
	bool isRealHead; /* Head is derived from a call instruction,
			    as opposed to one of the exploration
			    roots. */

	/* Pair of call instruction and callee address */
	gc_pair_ulong_set_t *callees;
	RangeSet *instructions;

	/* The same information as callees in a slightly different
	   format. */
	typedef gc_heap_map<unsigned long, CallGraphEntry, &ir_heap>::type calls_t;
	calls_t *calls;

	int depth;

	void visit(HeapVisitor &hv) {
		hv(instructions);
		hv(calls);
		hv(callees);
	}
	NAMED_CLASS
};
static unsigned long
getInstrLength(AddressSpace *as, unsigned long a)
{
	IRSB *irsb;
	try {
		irsb = as->getIRSBForAddress(0xabcde, a);
	} catch (BadMemoryException &e) {
		return 0;
	}
	assert(irsb != NULL);
	assert(irsb->stmts_used > 0);
	assert(irsb->stmts[0]->tag == Ist_IMark);
	return irsb->stmts[0]->Ist.IMark.len;
}
static CallGraphEntry *
exploreOneFunctionForCallGraph(unsigned long head,
			       int depth,
			       bool isRealHead,
			       RangeTree<CallGraphEntry> *instrsToCGEntries,
			       AddressSpace *as,
			       std::set<unsigned long> &realFunctionHeads)
{
	CallGraphEntry *cge;

	cge = new CallGraphEntry(head, depth);
	cge->isRealHead = isRealHead;

	std::vector<unsigned long> unexploredInstrsThisFunction;
	unexploredInstrsThisFunction.push_back(head);
	unsigned long prev = head;
	while (!unexploredInstrsThisFunction.empty()) {
		unsigned long i = unexploredInstrsThisFunction.back();
		unexploredInstrsThisFunction.pop_back();

		if (cge->instructions->test(i)) {
			/* Done this instruction already -> move
			 * on. */
			continue;
		}
		if (i != head && realFunctionHeads.count(i)) {
			/* This is a tail call. */
			cge->callees->set(std::pair<unsigned long, unsigned long>(prev, i), true);
			continue;
		}
		CallGraphEntry *old = instrsToCGEntries->get(i);
		if (old) {
			assert(old != cge);
			assert(old->headRip != cge->headRip);
			if (old->isRealHead) {
				/* This is a tail call. */
				cge->callees->set(std::pair<unsigned long, unsigned long>(prev, i), true);
				continue;
			} else {
				/* We have a branch from the current
				   function to a previous assumed
				   function head.  That means that the
				   assumed function head wasn't
				   actually a function head at all.
				   Kill it. */
				instrsToCGEntries->purgeByValue(old);
				printf("Purge %lx for %lx\n", old->headRip, i);
			}
		}

		unsigned long end = i + getInstrLength(as, i);
		if (end == i) {
			/* Valgrind occasionally gets confused and
			   returns empty instructions.  Treat them as
			   single-byte ones for these purposes. */
			end = i + 1;
		}

		/* Add this instruction to the current function. */
		cge->instructions->set(i, end);
		instrsToCGEntries->set(i, end, cge);

		/* Where are we going next? */
		findInstrSuccessorsAndCallees(as, i, unexploredInstrsThisFunction,
					      cge->callees);
		prev = i;
	}
	return cge;
}
static unsigned
countReachableCGEs(CallGraphEntry *s)
{
	std::set<CallGraphEntry *> reachable;
	std::queue<CallGraphEntry *> toExplore;
	toExplore.push(s);
	while (!toExplore.empty()) {
		s = toExplore.front();
		toExplore.pop();
		if (reachable.count(s))
			continue;
		reachable.insert(s);
		for (gc_heap_map<unsigned long,CallGraphEntry,&ir_heap>::type::iterator it = s->calls->begin();
		     it != s->calls->end();
		     it++)
			toExplore.push(it.value());
	}
	return reachable.size();
}
static void
purgeCGFromCGESet(std::set<CallGraphEntry *> &s, CallGraphEntry *root)
{
	if (!s.count(root))
		return;
	s.erase(root);
	for (gc_heap_map<unsigned long, CallGraphEntry, &ir_heap>::type::iterator it = root->calls->begin();
	     it != root->calls->end();
	     it++)
		purgeCGFromCGESet(s, it.value());
}
static CallGraphEntry **
buildCallGraphForRipSet(AddressSpace *as, const std::set<unsigned long> &rips,
			int *nr_roots)
{
	if (rips.size() == 1) {
		CallGraphEntry *cge = new CallGraphEntry(*rips.begin(), 0);
		cge->isRealHead = true;
		cge->instructions->set(*rips.begin(), *rips.begin() + 1);

		*nr_roots = 1;
		CallGraphEntry **res = (CallGraphEntry **)__LibVEX_Alloc_Ptr_Array(&ir_heap, 1);
		res[0] = cge;
		return res;
	}
	std::set<std::pair<unsigned long, int> > unexploredRips;
	for (std::set<unsigned long>::iterator it = rips.begin();
	     it != rips.end();
	     it++) {
		unexploredRips.insert(std::pair<unsigned long, int>(*it, 0));
	}
	RangeTree<CallGraphEntry> *instrsToCGEntries = new RangeTree<CallGraphEntry>();
	std::set<unsigned long> realFunctionHeads;

	while (!unexploredRips.empty()) {
		std::set<std::pair<unsigned long, int> >::iterator it = unexploredRips.begin();
		unsigned long head = it->first;
		int depth = it->second;
		unexploredRips.erase(it);

		if (depth >= 10)
			continue;

		CallGraphEntry *cge;
		cge = instrsToCGEntries->get(head);
		if (cge) {
			/* We already have a function which contains
			   this instruction, so we're finished. */
			continue;			
		}

		/* Explore the current function, starting from this
		 * instruction. */
		cge = exploreOneFunctionForCallGraph(head, depth, false, instrsToCGEntries, as, realFunctionHeads);
		assert(instrsToCGEntries->get(head) == cge);

		/* Now explore the functions which were called by that
		 * root. */
		std::set<std::pair<unsigned long, int> > unexploredRealHeads;
		for (gc_pair_ulong_set_t::iterator it = cge->callees->begin();
		     it != cge->callees->end();
		     it++) {
			unexploredRealHeads.insert(std::pair<unsigned long, int>(it.key().second,
										 depth + 1));
		}
		while (!unexploredRealHeads.empty()) {
			std::set<std::pair<unsigned long, int> >::const_iterator it = unexploredRealHeads.begin();
			unsigned long h = it->first;
			int depth_h = it->second;
			unexploredRealHeads.erase(it);

			if (depth_h >= 10)
				continue;

			realFunctionHeads.insert(h);

			CallGraphEntry *old = instrsToCGEntries->get(h);
			if (old) {
				/* Already have a CG node for this
				   instruction.  What kind of node? */
				if (!old->isRealHead) {
					/* It was an inferred head
					   from an earlier pass, so we
					   need to get rid of it. */
					printf("%lx was a pseudo-root; purge.\n", h);
					instrsToCGEntries->purgeByValue(old);
				} else if (old->headRip == h && old->depth <= depth_h) {
					/* It's the head of an
					   existing function ->
					   everything is fine and we
					   don't need to do
					   anything. */
					continue;
				} else {
					/* Urk.  We previously saw a
					   tail call to this location,
					   and now we're seeing a real
					   call.  The result is that
					   we need to purge the old
					   call and introduce a new
					   one. */
					instrsToCGEntries->purgeByValue(old);
					/* Need to re-explore whatever
					   it was that tail-called
					   into this function. */
					unexploredRealHeads.insert(std::pair<unsigned long, int>(h, depth_h + 1));
				}
			}

			/* Now explore that function */
			cge = exploreOneFunctionForCallGraph(h,
							     depth_h,
							     true,
							     instrsToCGEntries,
							     as,
							     realFunctionHeads);
			for (gc_pair_ulong_set_t::iterator it = cge->callees->begin();
			     it != cge->callees->end();
			     it++)
				unexploredRealHeads.insert(std::pair<unsigned long, int>(it.key().second, depth_h + 1));
			assert(instrsToCGEntries->get(h) == cge);
		}
	}

	/* Build a set of all of the CGEs which still exist */
	std::set<CallGraphEntry *> allCGEs;
	for (RangeTree<CallGraphEntry>::iterator it = instrsToCGEntries->begin();
	     it != instrsToCGEntries->end();
	     it++) {
		assert(it->value);
		allCGEs.insert(it->value);
	}

	/* Figure out which call graph entries are actually
	 * interesting. */
	std::set<CallGraphEntry *> interesting;

	/* Anything which contains one of the root RIPs is
	 * automatically interesting. */
	for (std::set<unsigned long>::iterator it = rips.begin();
	     it != rips.end();
	     it++) {
		CallGraphEntry *i = instrsToCGEntries->get(*it);
		assert(i != NULL);
		interesting.insert(i);
	}
	/* Tarski iteration: anything which calls an interesting
	   function is itself interesting. */
	bool done_something;
	do {
		done_something = false;
		for (std::set<CallGraphEntry *>::iterator it = allCGEs.begin();
		     it != allCGEs.end();
		     it++) {
			if (interesting.count(*it))
				continue;
			for (gc_pair_ulong_set_t::iterator it2 = (*it)->callees->begin();
			     it2 != (*it)->callees->end();
			     it2++) {
				CallGraphEntry *callee = instrsToCGEntries->get(it2.key().second);
				if (interesting.count(callee)) {
					/* Uninteresting function
					   calling an interesting ->
					   not allowed.  Fix it. */
					interesting.insert(*it);
					done_something = true;
					break;
				}
			}
		}
	} while (done_something);

	/* Now strip anything which isn't interesting. */
	/* Strip the uninteresting entries from the allCGEs set.  At
	   the same time, remove them from the callee lists. */
	for (std::set<CallGraphEntry *>::iterator it = allCGEs.begin();
	     it != allCGEs.end();
		) {
		CallGraphEntry *cge = *it;
		if (!interesting.count(cge)) {
			allCGEs.erase(it++);
		} else {
			for (gc_pair_ulong_set_t::iterator it2 = cge->callees->begin();
			     it2 != cge->callees->end();
				) {
				if (!interesting.count(instrsToCGEntries->get(it2.key().second))) {
					it2 = cge->callees->erase(it2);
				} else {
					it2++;
				}
			}
			it++;
		}
	}
	/* And now drop them from the instructions map */
	for (RangeTree<CallGraphEntry>::iterator it = instrsToCGEntries->begin();
	     it != instrsToCGEntries->end();
		) {
		if (!interesting.count(it->value))
			it = instrsToCGEntries->erase(it);
		else
			it++;
	}

	/* Resolve any remaining edges into pointers. */
	for (std::set<CallGraphEntry *>::iterator it = allCGEs.begin();
	     it != allCGEs.end();
	     it++) {
		for (gc_pair_ulong_set_t::iterator it2 = (*it)->callees->begin();
		     it2 != (*it)->callees->end();
		     it2++) {
			CallGraphEntry *cge = instrsToCGEntries->get(it2.key().second);
			assert(cge != NULL);
			(*it)->calls->set(it2.key().first, cge);
		}
	}

	std::vector<CallGraphEntry *> roots;
	/* Build the root set. */
	while (!allCGEs.empty()) {
		/* Pick a new root.  If there's anything with no
		   parents, we make that our root. */
		CallGraphEntry *res = NULL;
		for (std::set<CallGraphEntry *>::iterator it = allCGEs.begin();
		     !res && it != allCGEs.end();
		     it++) {
			bool hasParent = false;
			for (std::set<CallGraphEntry *>::iterator it2 = allCGEs.begin();
			     !hasParent && it2 != allCGEs.end();
			     it2++) {
				if ( (*it2)->calls->hasKey( (*it)->headRip) )
					hasParent = true;
			}
			if (!hasParent)
				res = *it;
		}
		if (!res) {
			/* Okay, every node we have left has a parent.
			   That means that they're either in a cycle
			   or reachable from a cycle.  In that case,
			   we pick whichever node has the most
			   reachable nodes. */
			std::map<CallGraphEntry *, int> nrReachable;
			std::set<CallGraphEntry *> unexaminedCGEs(allCGEs);
			while (!unexaminedCGEs.empty()) {
				CallGraphEntry *t = *unexaminedCGEs.begin();
				unexaminedCGEs.erase(unexaminedCGEs.begin());
				nrReachable[t] = countReachableCGEs(t);
			}
			CallGraphEntry *best = NULL;
			for (std::map<CallGraphEntry *, int>::iterator it = nrReachable.begin();
			     it != nrReachable.end();
			     it++) {
				if (!best || it->second > nrReachable[best])
					best = it->first;
			}
			assert(best != NULL);
			res = best;
		}

		roots.push_back(res);

		purgeCGFromCGESet(allCGEs, res);
	}

	CallGraphEntry **res;
	*nr_roots = roots.size();
	res = (CallGraphEntry **)__LibVEX_Alloc_Ptr_Array(&ir_heap, roots.size());
	for (unsigned i = 0; i < roots.size(); i++)
		res[i] = roots[i];
	return res;
}

static void
printCallGraph(CallGraphEntry *root, FILE *f, std::set<CallGraphEntry *> &memo)
{
	if (memo.count(root))
		return;
	memo.insert(root);
	fprintf(f, "%p: %#lx%s {", root, root->headRip, root->isRealHead ? "" : " (fake)");
	for (RangeSet::iterator it = root->instructions->begin();
	     it != root->instructions->end();
	     it++)
		fprintf(f, "%#lx-%#lx, ", it->start, it->end1);
	fprintf(f, "} (");
	for (gc_heap_map<unsigned long, CallGraphEntry, &ir_heap>::type::iterator it = root->calls->begin();
	     it != root->calls->end();
	     it++)
		fprintf(f, "%#lx:%p; ", it.key(), it.value());
	fprintf(f, ")\n");
	for (gc_heap_map<unsigned long, CallGraphEntry, &ir_heap>::type::iterator it = root->calls->begin();
	     it != root->calls->end();
	     it++)
		printCallGraph(it.value(), f, memo);
}
static void
printCallGraph(CallGraphEntry *root, FILE *f)
{
	std::set<CallGraphEntry *> alreadyDone;
	printCallGraph(root, f, alreadyDone);
}

class StackRip {
public:
	unsigned long rip;
	std::vector<unsigned long> callStack;
	bool valid;
	StackRip(unsigned long _rip) : rip(_rip), valid(true) {}
	StackRip() : valid(false) {}

	StackRip jump(unsigned long r) {
		StackRip w(*this);
		w.rip = r;
		return w;
	}
	StackRip call(unsigned long target, unsigned long rtrn) {
		StackRip w(*this);
		w.callStack.push_back(rtrn);
		w.rip = target;
		return w;
	}
	StackRip rtrn(void) {
		StackRip w(*this);
		w.rip = w.callStack.back();
		w.callStack.pop_back();
		return w;
	}
};

template <> void printCFG(const CFGNode<StackRip> *cfg);

static unsigned long
wrappedRipToRip(const StackRip &r)
{
	return r.rip;
}

static bool
instructionIsInteresting(const InstructionSet &i, const StackRip &r)
{
	return i.rips.count(r.rip) != 0;
}

static bool
operator<(const StackRip &a, const StackRip &b)
{
	if (!b.valid)
		return false;
	if (!a.valid)
		return true;
	if (a.rip < b.rip)
		return true;
	else if (a.rip > b.rip)
		return false;
	if (a.callStack.size() < b.callStack.size())
		return true;
	else if (a.callStack.size() > b.callStack.size())
		return false;
	for (unsigned x = 0; x < a.callStack.size(); x++)
		if (a.callStack[x] < b.callStack[x])
			return true;
		else if (a.callStack[x] > b.callStack[x])
			return false;
	return false;
}

static CFGNode<StackRip> *
buildCFGForCallGraph(AddressSpace *as,
		     CallGraphEntry *root)
{
	/* Build a map from instruction RIPs to CGEs. */
	std::set<CallGraphEntry *> explored;
	std::queue<CallGraphEntry *> toExplore;
	RangeTree<CallGraphEntry> *ripToCFGNode = new RangeTree<CallGraphEntry>();
	toExplore.push(root);
	while (!toExplore.empty()) {
		CallGraphEntry *cge = toExplore.front();
		toExplore.pop();
		if (explored.count(cge))
			continue;
		explored.insert(cge);
		for (RangeSet::iterator it = cge->instructions->begin();
		     it != cge->instructions->end();
		     it++) {
			ripToCFGNode->set(it->start, it->end1, cge);
		}
		for (CallGraphEntry::calls_t::iterator it = cge->calls->begin();
		     it != cge->calls->end();
		     it++)
			toExplore.push(it.value());
	}

	/* Now, starting from the head of the root node, work our way
	 * forwards and build up the state machine.  We identify
	 * instructions by a combination of the RIP and call stack,
	 * encapsulated as a StackRip; this effectively allows us to
	 * inline chosen functions. */
	std::map<StackRip, CFGNode<StackRip> *> builtSoFar;
	std::queue<StackRip> needed;

	needed.push(StackRip(root->headRip));
	while (!needed.empty()) {
		StackRip &r(needed.front());
		if (builtSoFar.count(r) || ripToCFGNode->get(r.rip) == NULL) {
			needed.pop();
			continue;
		}
		CFGNode<StackRip> *work = new CFGNode<StackRip>(r);
		builtSoFar[r] = work;
		IRSB *irsb = as->getIRSBForAddress(-1, r.rip);
		int x;
		for (x = 1; x < irsb->stmts_used; x++) {
			if (irsb->stmts[x]->tag == Ist_IMark) {
				work->fallThroughRip = r.jump(irsb->stmts[x]->Ist.IMark.addr);
				break;
			}
			if (irsb->stmts[x]->tag == Ist_Exit) {
				assert(!work->branchRip.valid);
				work->branchRip = r.jump(irsb->stmts[x]->Ist.Exit.dst->Ico.U64);
				assert(work->branchRip.valid);
				needed.push(work->branchRip);
			}
		}
		if (x == irsb->stmts_used) {
			if (irsb->jumpkind == Ijk_Call) {
				if (ripToCFGNode->get(r.rip)->calls->hasKey(r.rip)) {
					/* We should inline this call. */
					work->fallThroughRip = r.call(
						ripToCFGNode->get(r.rip)->calls->get(r.rip)->headRip,
						extract_call_follower(irsb));
				} else {
					/* Skip over this call. */
					work->fallThroughRip = r.jump(extract_call_follower(irsb));
				}
			} else if (irsb->jumpkind == Ijk_Ret) {
				if (r.callStack.size() == 0) {
					/* End of the line. */
					work->accepting = true;
				} else {
					/* Return to calling function. */
					work->fallThroughRip = r.rtrn();
				}
			} else if (irsb->next->tag == Iex_Const) {
				work->fallThroughRip = r.jump(irsb->next->Iex.Const.con->Ico.U64);
			} else {
				/* Don't currently try to trace across indirect branches. */
			}
		}
		needed.pop();
		if (work->fallThroughRip.valid)
			needed.push(work->fallThroughRip);
	}

	/* We have now built all of the needed CFG nodes.  Resolve
	 * references. */
	for (std::map<StackRip, CFGNode<StackRip> *>::iterator it = builtSoFar.begin();
	     it != builtSoFar.end();
	     it++) {
		assert(it->second);
		if (it->second->fallThroughRip.valid && builtSoFar.count(it->second->fallThroughRip))
			it->second->fallThrough = builtSoFar[it->second->fallThroughRip];
		if (it->second->branchRip.valid && builtSoFar.count(it->second->branchRip))
			it->second->branch = builtSoFar[it->second->branchRip];
	}

	/* All done */
	CFGNode<StackRip> *res = builtSoFar[StackRip(root->headRip)];
	assert(res != NULL);
	return res;
}

typedef std::set<std::pair<StateMachineSideEffectStore *,
			   StateMachineSideEffectStore *> > remoteMacroSectionsT;

static bool
fixSufficient(StateMachine *writeMachine,
	      StateMachine *probeMachine,
	      IRExpr *assumption,
	      Oracle *oracle,
	      const remoteMacroSectionsT &sections)
{
	NdChooser chooser;
	StateMachineEdge *writeStartEdge = new StateMachineEdge(writeMachine);

	do {
		std::vector<StateMachineSideEffectStore *> storesIssuedByWriter;
		std::map<Int, IRExpr *> writerBinders;
		StateMachineEdge *writerEdge;
		unsigned writeEdgeIdx;
		IRExpr *pathConstraint;
		std::set<StateMachineSideEffectStore *> incompleteSections;

		writeEdgeIdx = 0;
		pathConstraint = assumption;
		writerEdge = writeStartEdge;
		while (1) {
			/* Have we hit the end of the current writer edge? */
			if (writeEdgeIdx == writerEdge->sideEffects.size()) {
				/* Yes, move to the next state. */
				StateMachine *s = writerEdge->target;
				assert(!dynamic_cast<StateMachineUnreached *>(s));
				if (dynamic_cast<StateMachineCrash *>(s) ||
				    dynamic_cast<StateMachineNoCrash *>(s) ||
				    dynamic_cast<StateMachineStub *>(s)) {
					/* Hit the end of the writer
					 * -> we're done. */
					break;
				}
				if (StateMachineProxy *smp =
				    dynamic_cast<StateMachineProxy *>(s)) {
					writerEdge = smp->target;
					writeEdgeIdx = 0;
					continue;
				}
				StateMachineBifurcate *smb =
					dynamic_cast<StateMachineBifurcate *>(s);
				assert(smb);
				if (expressionIsTrue(smb->condition, chooser, writerBinders, &pathConstraint, NULL))
					writerEdge = smb->trueTarget;
				else
					writerEdge = smb->falseTarget;
				writeEdgeIdx = 0;
				continue;				
			}

			/* Advance the writer by one state.  Note that
			   we *don't* consider running the read before
			   any write states, as that's already been
			   handled and is known to lead to
			   no-crash. */
			StateMachineSideEffect *se;
			se = writerEdge->sideEffects[writeEdgeIdx];
			evalStateMachineSideEffect(se, chooser, oracle, writerBinders, storesIssuedByWriter, &pathConstraint, NULL);
			writeEdgeIdx++;

			/* Only consider running the probe machine if
			 * we just executed a store. */
			StateMachineSideEffectStore *smses =
				dynamic_cast<StateMachineSideEffectStore *>(se);
			if (!smses)
				continue;

			/* Did we just leave a critical section? */
			if (incompleteSections.count(smses))
				incompleteSections.erase(smses);
			/* Did we just enter a critical section? */
			for (remoteMacroSectionsT::const_iterator it = sections.begin();
			     it != sections.end();
			     it++) {
				if (it->first == smses)
					incompleteSections.insert(it->second);
			}
			/* If we have incomplete critical sections, we
			 * can't run the probe machine. */
			if (incompleteSections.size() != 0)
				continue;

			/* The writer just issued a store and is not
			   in a critical section, so we should now try
			   running the reader atomically.  */
			StateMachineEvalContext readEvalCtxt;
			readEvalCtxt.pathConstraint = pathConstraint;
			readEvalCtxt.stores = storesIssuedByWriter;
			bool crashes;
			evalStateMachine(probeMachine, &crashes, chooser, oracle, readEvalCtxt);
			if (crashes) {
				printf("Fix is insufficient, witness: ");
				ppIRExpr(readEvalCtxt.pathConstraint, stdout);
				printf("\n");
				dbg_break("Failed...\n");
				return false; 
			}
		}
	} while (chooser.advance());

	/* If we get here then there's no way of crashing the probe
	   machine by running it in parallel with the store machine,
	   provided the proposed fix is applied.  That means that the
	   proposed fix is good. */

	return true;
}

#define CRASHING_THREAD 73
#define STORING_THREAD 97

static void
considerStoreCFG(VexPtr<CFGNode<StackRip>, &ir_heap> cfg,
		 VexPtr<AddressSpace> &as,
		 VexPtr<Oracle> &oracle,
		 VexPtr<IRExpr, &ir_heap> &assumption,
		 VexPtr<StateMachine, &ir_heap> &probeMachine,
		 GarbageCollectionToken token)
{
	VexPtr<StateMachine, &ir_heap> sm(CFGtoStoreMachine(STORING_THREAD, as.get(), cfg.get()));

	AllowableOptimisations opt2 =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack();
	bool done_something;
	do {
		done_something = false;
		sm = sm->optimise(opt2, oracle, &done_something);
	} while (done_something);
	const Oracle::RegisterAliasingConfiguration &alias(oracle->getAliasingConfigurationForRip(cfg->my_rip.rip));
	sm = availExpressionAnalysis(sm, opt2, alias, oracle);
	sm = bisimilarityReduction(sm, opt2);
	do {
		done_something = false;
		sm = sm->optimise(opt2, oracle, &done_something);
	} while (done_something);

	assumption = writeMachineSuitabilityConstraint(probeMachine, sm, assumption, oracle);
	if (!assumption)
		return;

	/* Now try running that in parallel with the probe machine,
	   and see if it might lead to a crash. */
	bool mightSurvive;
	bool mightCrash;
	evalCrossProductMachine(probeMachine,
				sm,
				oracle,
				assumption,
				&mightSurvive,
				&mightCrash,
				token);
	printf("\t\tRun in parallel with the probe machine, might survive %d, might crash %d\n",
	       mightSurvive, mightCrash);
	
	/* We know that mightSurvive is true when the load machine is
	 * run atomically, so if mightSurvive is now false then that
	 * means that evalCrossProductMachine didn't consider that
	 * case, which is a bug. */
	assert(mightSurvive);

	if (!mightCrash) {
		/* Executing in parallel with this machine cannot lead
		 * to a crash, so there's no point in doing any more
		 * work with it. */
		return;
	}

	remoteMacroSectionsT remoteMacroSections;
	if (!findRemoteMacroSections(probeMachine, sm, assumption, oracle, remoteMacroSections)) {
		printf("\t\tChose a bad write machine...\n");
		return;
	}
	if (!fixSufficient(probeMachine, sm, assumption, oracle, remoteMacroSections)) {
		printf("\t\tHave a fix, but it was insufficient...\n");
		dbg_break("Failed!\n");
		return;
	}
	dbg_break("Have remote critical sections");
	for (std::set<std::pair<StateMachineSideEffectStore *,
		     StateMachineSideEffectStore *> >::iterator it =
		     remoteMacroSections.begin();
	     it != remoteMacroSections.end();
	     it++) {
		printf("\t\tRemote macro section ");
		it->first->prettyPrint(stdout);
		printf(" -> ");
		it->second->prettyPrint(stdout);
		printf("\n");
	}
}

static FILE *
fopenf(const char *mode, const char *fmt, ...)
{
	va_list args;
	char *path;
	FILE *res;

	va_start(args, fmt);
	vasprintf(&path, fmt, args);
	va_end(args);

	res = fopen(path, mode);
	free(path);
	return res;
}

unsigned long
__hash_state_machine(StateMachine *const &s)
{
	return s->hashval();
}

bool
__eq_state_machine(StateMachine *const &a, StateMachine *const &b)
{
	return stateMachinesBisimilar((StateMachine *)a, (StateMachine *)b);
}

void
__visit_state_machine_set_entry(StateMachine *&a, bool &b, HeapVisitor &hv)
{
	hv(a);
}

typedef class gc_map<StateMachine *, bool, __hash_state_machine,
		     __eq_state_machine, __visit_state_machine_set_entry> StateMachineSet;

static bool storeMightBeLoadedByState(StateMachine *sm, StateMachineSideEffectStore *smses, Oracle *oracle);
static bool
storeMightBeLoadedByStateEdge(StateMachineEdge *sme, StateMachineSideEffectStore *smses, Oracle *oracle)
{
	for (unsigned y = 0; y < sme->sideEffects.size(); y++) {
		if (StateMachineSideEffectLoad *smsel =
		    dynamic_cast<StateMachineSideEffectLoad *>(sme->sideEffects[y])) {
			if (oracle->memoryAccessesMightAlias(smsel, smses))
				return true;
		}
	}
	return storeMightBeLoadedByState(sme->target, smses, oracle);
}
static bool
storeMightBeLoadedByState(StateMachine *sm, StateMachineSideEffectStore *smses, Oracle *oracle)
{
	if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm))
		return storeMightBeLoadedByStateEdge(smp->target, smses, oracle);
	if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm))
		return storeMightBeLoadedByStateEdge(smb->trueTarget, smses, oracle) ||
			storeMightBeLoadedByStateEdge(smb->falseTarget, smses, oracle);
	return false;
}
static bool
storeMightBeLoadedFollowingSideEffect(StateMachineEdge *sme, unsigned idx,
				      StateMachineSideEffectStore *smses,
				      Oracle *oracle)
{
	for (unsigned y = idx + 1; y < sme->sideEffects.size(); y++) {
		if (StateMachineSideEffectLoad *smsel =
		    dynamic_cast<StateMachineSideEffectLoad *>(sme->sideEffects[y])) {
			if (oracle->memoryAccessesMightAlias(smsel, smses))
				return true;
		}
	}
	return storeMightBeLoadedByState(sme->target, smses, oracle);
}

/* Look at the state machine, compare it to the tags table, and remove
   any stores which are definitely never loaded (assuming that the
   tags table is correct). */
static void removeRedundantStores(StateMachine *sm, Oracle *oracle, bool *done_something,
				  std::set<StateMachine *> &visited);
static void
removeRedundantStores(StateMachineEdge *sme, Oracle *oracle, bool *done_something,
		      std::set<StateMachine *> &visited)
{
	for (unsigned x = 0; x < sme->sideEffects.size(); x++) {
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(sme->sideEffects[x])) {
			if (!storeMightBeLoadedFollowingSideEffect(sme, x, smses, oracle)) {
				sme->sideEffects.erase(
					sme->sideEffects.begin() + x);
				x--;
				*done_something = true;
			}
		}
	}
	removeRedundantStores(sme->target, oracle, done_something, visited);
}
static void
removeRedundantStores(StateMachine *sm, Oracle *oracle, bool *done_something,
		      std::set<StateMachine *> &visited)
{
	if (visited.count(sm))
		return;
	visited.insert(sm);
	if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
		removeRedundantStores(smp->target, oracle, done_something, visited);
		return;
	}
	if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm)) {
		removeRedundantStores(smb->trueTarget, oracle, done_something, visited);
		removeRedundantStores(smb->falseTarget, oracle, done_something, visited);
		return;
	}
	assert(dynamic_cast<StateMachineUnreached *>(sm) ||
	       dynamic_cast<StateMachineCrash *>(sm) ||
	       dynamic_cast<StateMachineNoCrash *>(sm) ||
	       dynamic_cast<StateMachineStub *>(sm));
}
static void
removeRedundantStores(StateMachine *sm, Oracle *oracle, bool *done_something)
{
	std::set<StateMachine *> visited;

	removeRedundantStores(sm, oracle, done_something, visited);
}

static StateMachine *
optimiseStateMachine(StateMachine *sm, const Oracle::RegisterAliasingConfiguration &alias,
		     const AllowableOptimisations &opt, Oracle *oracle)
{
	bool done_something;
	do {
		done_something = false;
		sm = sm->optimise(opt, oracle, &done_something);
		removeRedundantStores(sm, oracle, &done_something);
		sm = availExpressionAnalysis(sm, opt, alias, oracle);
		sm = bisimilarityReduction(sm, opt);
		sm = sm->optimise(opt, oracle, &done_something);
	} while (done_something);
	return sm;
}

int
main(int argc, char *argv[])
{
	if (argc <= 1)
		errx(1, "need at least one argument");

	init_sli();

	if (!strcmp(argv[1], "--check-sorter")) {
		sanity_check_irexpr_sorter();
		return 0;
	}
	if (!strcmp(argv[1], "--check-optimiser")) {
		sanity_check_optimiser();
		return 0;
	}

	VexPtr<MachineState> ms(MachineState::readCoredump(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(CRASHED_THREAD)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));

	VexPtr<CrashReason, &ir_heap> proximal(getProximalCause(ms, thr));
	if (!proximal)
		errx(1, "cannot get proximal cause of crash");
	proximal = backtrackToStartOfInstruction(CRASHING_THREAD, proximal, ms->addressSpace);

	VexPtr<InferredInformation> ii(new InferredInformation(oracle));
	ii->addCrashReason(proximal);

	VexPtr<StateMachineSet> readMachinesChecked(new StateMachineSet());

	std::vector<unsigned long> previousInstructions;
	oracle->findPreviousInstructions(previousInstructions);
	for (std::vector<unsigned long>::iterator it = previousInstructions.begin();
	     it != previousInstructions.end();
	     it++) {
		printf("Investigating %lx...\n", *it);
		LibVEX_maybe_gc(ALLOW_GC);

		std::set<unsigned long> terminalFunctions;
		terminalFunctions.insert(0x757bf0);
		VexPtr<CFGNode<unsigned long>, &ir_heap> cfg(
			ii->CFGFromRip(*it, terminalFunctions));
		InstructionSet interesting;
		interesting.rips.insert(proximal->rip.rip);
		trimCFG(cfg.get(), interesting, INT_MAX);
		breakCycles(cfg.get());

		VexPtr<CrashReason, &ir_heap> cr(
			ii->CFGtoCrashReason(CRASHING_THREAD, cfg));
		AllowableOptimisations opt =
			AllowableOptimisations::defaultOptimisations
			.enableassumePrivateStack()
			.enableignoreSideEffects();

		cr->sm = optimiseStateMachine(cr->sm,
					      oracle->getAliasingConfigurationForRip(*it),
					      opt,
					      oracle);

		printf("\tComputed state machine.\n");

		{
			FILE *f = fopenf("w", "machines/%s", cr->rip.name());
			pickleStateMachine(cr->sm, f);
			fclose(f);
		}

		if (readMachinesChecked->hasKey(cr->sm)) {
			printf("\tAlready investigated that one...\n");
			continue;
		}
		readMachinesChecked->set(cr->sm, true);

		cr->sm = cr->sm->selectSingleCrashingPath();
		cr->sm = optimiseStateMachine(cr->sm,
					      oracle->getAliasingConfigurationForRip(*it),
					      opt,
					      oracle);

		VexPtr<IRExpr, &ir_heap> survive;
		{
			VexPtr<StateMachine, &ir_heap> crSm(cr->sm);
			survive =
				optimiseIRExpr(
					survivalConstraintIfExecutedAtomically(crSm, oracle, ALLOW_GC),
					opt);
		}

		survive = internIRExpr(survive);
		survive = simplifyIRExprAsBoolean(survive);
		survive = optimiseIRExpr(survive, opt);

		printf("\tComputed survival constraint\n");
		{
			FILE *f = fopenf("w", "machines/%s.survival_constraint", cr->rip.name());
			pickleIRExpr(survive, f);
			fclose(f);
		}

		/* Quick check that that vaguely worked.  If this
		   reports mightCrash == true then that probably means
		   that the theorem prover bits need more work.  If it
		   reports mightSurvive == false then the program is
		   doomed and it's not possible to fix it from this
		   point. */
		bool mightSurvive, mightCrash;
		{
			VexPtr<StateMachine, &ir_heap> crSm(cr->sm);
			evalMachineUnderAssumption(crSm, oracle, survive, &mightSurvive, &mightCrash, ALLOW_GC);
		}

		if (!mightSurvive) {
			printf("\tCan never survive...\n");
			continue;
		}
		if (mightCrash) {
			printf("WARNING: Cannot determine any condition which will definitely ensure that we don't crash, even when executed atomically -> probably won't be able to fix this\n");
			dbg_break("whoops");
		}

		std::set<unsigned long> potentiallyConflictingStores;
		{
			std::set<StateMachineSideEffectLoad *> allLoads;
			findAllLoads(cr->sm, allLoads);
			for (std::set<StateMachineSideEffectLoad *>::iterator it = allLoads.begin();
			     it != allLoads.end();
			     it++) {
				oracle->findConflictingStores(*it, potentiallyConflictingStores);
			}
		}
		printf("\tConflicting stores: ");
		for (std::set<unsigned long>::iterator it = potentiallyConflictingStores.begin();
		     it != potentiallyConflictingStores.end();
		     it++)
			printf("%lx ", *it);
		printf("\n");

		std::set<InstructionSet> conflictClusters;
		oracle->clusterRips(potentiallyConflictingStores, conflictClusters);
		if (conflictClusters.size() == 0)
			assert(potentiallyConflictingStores.size() == 0);
		for (std::set<InstructionSet>::iterator it = conflictClusters.begin();
		     it != conflictClusters.end();
		     it++) {
			printf("\t\tCluster:");
			for (std::set<unsigned long>::iterator it2 = it->rips.begin();
			     it2 != it->rips.end();
			     it2++)
				printf(" %lx", *it2);
			printf("\n");
		}

		for (std::set<InstructionSet>::iterator it = conflictClusters.begin();
		     it != conflictClusters.end();
		     it++) {
			printf("\t\tCluster:");
			for (std::set<unsigned long>::iterator it2 = it->rips.begin();
			     it2 != it->rips.end();
			     it2++)
				printf(" %lx", *it2);
			printf("\n");
			LibVEX_maybe_gc(ALLOW_GC);
			VexPtr<CallGraphEntry *, &ir_heap> cgRoots;
			int nr_roots;
			cgRoots = buildCallGraphForRipSet(ms->addressSpace, it->rips, &nr_roots);
			for (int i = 0; i < nr_roots; i++) {
				VexPtr<CFGNode<StackRip>, &ir_heap> storeCFG;
				storeCFG = buildCFGForCallGraph(ms->addressSpace, cgRoots[i]);
				trimCFG(storeCFG.get(), *it, 20);
				breakCycles(storeCFG.get());

				VexPtr<AddressSpace> as(ms->addressSpace);
				VexPtr<StateMachine, &ir_heap> sm(cr->sm);
				considerStoreCFG(storeCFG, as, oracle,
						 survive, sm, ALLOW_GC);
			}
		}
	}

	return 0;
}
