/* A load of random stuff which doesn't really belong anywhere. */
#include <limits.h>
#include <queue>

#include "sli.h"
#include "range_tree.h"
#include "state_machine.hpp"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "eval_state_machine.hpp"
#include "offline_analysis.hpp"
#include "intern.hpp"
#include "libvex_prof.hpp"

/* We allow at most 5 assertions to be available at any given point in
 * the state machines, so as to reduce the risk of dependency
 * explosion.  If we go over that then we keep the ones which are
 * earlier in the machine, for two reasons:
 *
 * 1) It's often most useful, as the earlier assumptions are generally
 * ones which have been recently introduced, while later ones have
 * been there a while so have probably already been used as we move
 * backwards through the program.
 * 2) It's much easier to implement.
 */
#define MAX_LIVE_ASSERTIONS 5

template <typename t> void printCFG(const CFGNode<t> *cfg);
template <typename k, typename v>
class abstract_map {
public:
	virtual bool hasKey(const k &) = 0;
	virtual v get(const k &) = 0;
	virtual void set(const k &, const v &) = 0;
};
template <typename t> StateMachine *CFGtoCrashReason(unsigned tid, CFGNode<t> *cfg,
						     abstract_map<t, StateMachineState *> &crashReasons,
						     StateMachineState *escapeState,
						     Oracle *oracle);

typedef std::pair<StateMachineState *, StateMachineState *> st_pair_t;
typedef std::pair<StateMachineEdge *, StateMachineEdge *> st_edge_pair_t;

class iiCrashReasons : public abstract_map<unsigned long, StateMachineState *> {
public:
	InferredInformation *ii;
	iiCrashReasons(InferredInformation *_ii)
		: ii(_ii)
	{}
	bool hasKey(const unsigned long &x) { return ii->hasKey(x); }
	StateMachineState *get(const unsigned long &x) {
		return ii->get(x);
	}
	void set(const unsigned long &x, StateMachineState *const &v) {
		ii->set(x, v);
	}
};
static CFGNode<unsigned long> *buildCFGForRipSet(AddressSpace *as,
						 unsigned long start,
						 const std::set<unsigned long> &terminalFunctions,
						 Oracle *oracle,
						 unsigned max_depth);

/* A bunch of heuristics for figuring out why we crashed.  Returns
 * NULL on failure.  Pretty stupid. */
static StateMachineEdge *
_getProximalCause(MachineState *ms, unsigned long rip, Thread *thr, unsigned *idx)
{
	__set_profiling(getProximalCause);
	FreeVariableMap fv;

	IRSB *irsb;
	int x;
	int nr_marks;

	*idx = 9999999;
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
		*idx = irsb->stmts_used;
		return new StateMachineEdge(
			new StateMachineBifurcate(
				rip,
				IRExpr_Unop(
					Iop_BadPtr,
					irsb->next),
				StateMachineCrash::get(),
				StateMachineNoCrash::get()));
	}

	/* Next guess: it's caused by dereferencing a bad pointer.
	   Grab the crashing instruction and try emulating it.  If it
	   results in a crash, we can be pretty confident that we've
	   found the problem. */
	try {
		irsb = ms->addressSpace->getIRSBForAddress(thr->tid._tid(), rip);
	} catch (BadMemoryException &e) {
		return NULL;
	}

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
			*idx = x;
			return new StateMachineEdge(
				new StateMachineBifurcate(
					rip,
					IRExpr_Unop(
						Iop_BadPtr,
						addr),
					StateMachineCrash::get(),
					StateMachineNoCrash::get()));
		}
		fprintf(_logfile, "Generated event %s\n", evt->name());
	}

	fprintf(_logfile, "Hit end of block without any events -> no idea why we crashed.\n");
	return NULL;
}

StateMachineState *
StateMachineTransformer::doit(StateMachineState *inp, bool *done_something)
{
	if (TIMEOUT)
		return inp;
	if (memoTable.count(inp)) {
		/* We rely on whoever set memoTable having also set
		   *done_something if necessary. */
		return memoTable[inp];
	}
	StateMachineState *out;
	if (inp == StateMachineCrash::get()) {
		out = transformedCrash(done_something);
	} else if (inp == StateMachineNoCrash::get()) {
		out = transformedNoCrash(done_something);
	} else if (inp == StateMachineUnreached::get()) {
		out = transformedUnreached(done_something);
	} else if (StateMachineBifurcate *smb =
		   dynamic_cast<StateMachineBifurcate *>(inp)) {
		bool done = false;
		StateMachineEdge *t = doit(smb->trueTarget, &done);
		StateMachineEdge *f = doit(smb->falseTarget, &done);
		IRExpr *cond = transformIRExpr(smb->condition, &done);
		if (done) {
			*done_something = true;
			out = new StateMachineBifurcate(inp->origin, cond, t, f);
		} else {
			out = inp;
		}
	} else if (StateMachineProxy *smp =
		   dynamic_cast<StateMachineProxy *>(inp)) {
		bool d = false;
		StateMachineEdge *t = doit(smp->target, &d);
		if (d) {
			*done_something = true;
			out = new StateMachineProxy(inp->origin, t);
		} else {
			out = inp;
		}
	} else if (StateMachineStub *sms =
		   dynamic_cast<StateMachineStub *>(inp)) {
		bool d = false;
		IRExpr *target = transformIRExpr(sms->target, &d);
		if (d) {
			*done_something = true;
			out = new StateMachineStub(inp->origin, target);
		} else {
			out = inp;
		}
	} else {
		abort();
	}
	memoTable[inp] = out;
	return out;
}

StateMachineSideEffect *
StateMachineTransformer::transform(StateMachineSideEffect *se, bool *done_something)
{
	bool b;
	if (!done_something)
		done_something = &b;
	switch (se->type) {
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectStore *smses =
			dynamic_cast<StateMachineSideEffectStore *>(se);
		assert(smses);
		IRExpr *a, *d;
		a = transformIRExpr(smses->addr, done_something);
		d = transformIRExpr(smses->data, done_something);
		return new StateMachineSideEffectStore(
			a,
			d,
			smses->rip);
	}
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel =
			dynamic_cast<StateMachineSideEffectLoad *>(se);
		IRExpr *a = transformIRExpr(smsel->addr, done_something);
		return new StateMachineSideEffectLoad(
			smsel->key,
			a,
			smsel->rip);
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec =
			dynamic_cast<StateMachineSideEffectCopy *>(se);
		IRExpr *v = transformIRExpr(smsec->value, done_something);
		return new StateMachineSideEffectCopy(
			smsec->key,
			v);
	}
	case StateMachineSideEffect::Unreached:
		return se;
	case StateMachineSideEffect::Put: {
		StateMachineSideEffectPut *smsep =
			dynamic_cast<StateMachineSideEffectPut *>(se);
		IRExpr *v = transformIRExpr(smsep->value, done_something);
		return new StateMachineSideEffectPut(
			smsep->offset,
			v,
			smsep->rip);
	}
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(se);
		IRExpr *v = transformIRExpr(smseaf->value, done_something);
		return new StateMachineSideEffectAssertFalse(v);
	}
	}
	abort();
}

StateMachineEdge *
StateMachineTransformer::doit(StateMachineEdge *inp, bool *done_something)
{
	bool done = false;
	StateMachineState *t = doit(inp->target, &done);
	StateMachineEdge *res = new StateMachineEdge(t);
	for (std::vector<StateMachineSideEffect *>::iterator it = inp->sideEffects.begin();
	     it != inp->sideEffects.end();
	     it++)
		res->sideEffects.push_back(transform(*it, &done));
	if (done) {
		*done_something = true;
		return res;
	} else {
		return inp;
	}
}

StateMachineState *
StateMachineTransformer::transform(StateMachineState *inp, bool *done_something)
{
	return doit(inp, done_something);
}

IRExpr *
IRExprTransformer::transformIRExpr(IRExpr *e, bool *done_something)
{
	if (TIMEOUT)
		return e;
	IRExpr *oldCurrent = _currentIRExpr;
	_currentIRExpr = e;
	IRExpr *res = NULL;
	switch (e->tag) {
	case Iex_Binder:
		res = transformIex(&e->Iex.Binder);
		break;
	case Iex_Get:
		res = transformIex(&e->Iex.Get);
		break;
	case Iex_GetI:
		res = transformIex(&e->Iex.GetI);
		break;
	case Iex_RdTmp:
		res = transformIex(&e->Iex.RdTmp);
		break;
	case Iex_Qop:
		res = transformIex(&e->Iex.Qop);
		break;
	case Iex_Triop:
		res = transformIex(&e->Iex.Triop);
		break;
	case Iex_Binop:
		res = transformIex(&e->Iex.Binop);
		break;
	case Iex_Unop:
		res = transformIex(&e->Iex.Unop);
		break;
	case Iex_Load:
		res = transformIex(&e->Iex.Load);
		break;
	case Iex_Const:
		res = transformIex(&e->Iex.Const);
		break;
	case Iex_CCall:
		res = transformIex(&e->Iex.CCall);
		break;
	case Iex_Mux0X:
		res = transformIex(&e->Iex.Mux0X);
		break;
	case Iex_Associative:
		res = transformIex(&e->Iex.Associative);
		break;
	case Iex_FreeVariable:
		res = transformIex(&e->Iex.FreeVariable);
		break;
	case Iex_ClientCall:
		res = transformIex(&e->Iex.ClientCall);
		break;
	case Iex_ClientCallFailed:
		res = transformIex(&e->Iex.ClientCallFailed);
		break;
	case Iex_HappensBefore:
		res = transformIex(&e->Iex.HappensBefore);
		break;
	}
	/* res == e shouldn't really happen, but it's just about
	   possible that expression internment could make it happen in
	   otherwise correct code, so handle it correctly. */
	if (res && res != e) {
		*done_something = true;
	} else {
		res = e;
	}
	_currentIRExpr = oldCurrent;
	return res;
}

IRExpr *
IRExprTransformer::transformIex(IRExpr::CCall *e)
{
	IRExpr **newArgs;
	int nr_args;
	int x;
	bool t = false;

	for (nr_args = 0; e->args[nr_args]; nr_args++)
		;
	newArgs = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_args + 1);
	for (x = 0; x < nr_args; x++)
		newArgs[x] = transformIRExpr(e->args[x], &t);
	newArgs[nr_args] = NULL;
	if (!t)
		return NULL;
	else
		return IRExpr_CCall(e->cee,
				    e->retty,
				    newArgs);
}

IRExpr *
IRExprTransformer::transformIex(IRExpr::ClientCall *e)
{
	IRExpr **newArgs;
	int nr_args;
	int x;
	bool t = false;

	for (nr_args = 0; e->args[nr_args]; nr_args++)
		;
	newArgs = alloc_irexpr_array(nr_args + 1);
	for (x = 0; x < nr_args; x++)
		newArgs[x] = transformIRExpr(e->args[x], &t);
	newArgs[nr_args] = NULL;
	if (!t)
		return NULL;
	else
		return IRExpr_ClientCall(e->calledRip, e->callSite, newArgs);
}

IRExpr *
IRExprTransformer::transformIex(IRExpr::Associative *e)
{
	bool t = false;
	IRExpr *r = IRExpr_Associative(e);
	for (int x = 0; x < e->nr_arguments; x++)
		r->Iex.Associative.contents[x] = transformIRExpr(e->contents[x], &t);
	if (!t)
		return NULL;
	else
		return r;
}

static IRExpr *
rewriteTemporary(IRExpr *sm,
		 IRTemp tmp,
		 IRExpr *newval)
{
	class _ : public IRExprTransformer {
		IRTemp tmp;
		IRExpr *to;
	protected:
		IRExpr *transformIex(IRExpr::RdTmp *what)
		{
			if (what->tmp == tmp)
				return to;
			else
				return NULL;
		}
	public:
		_(IRTemp _tmp, IRExpr *_to)
			: tmp(_tmp), to(_to)
		{
		}
	} rt(tmp, newval);
	return rt.transformIRExpr(sm);
}

static StateMachineEdge *
backtrackOneStatement(StateMachineEdge *sm, IRStmt *stmt, ThreadRip site)
{
	switch (stmt->tag) {
	case Ist_NoOp:
	case Ist_IMark:
	case Ist_AbiHint:
		break;
	case Ist_Put:
		sm->prependSideEffect(
			new StateMachineSideEffectPut(
				stmt->Ist.Put.offset,
				stmt->Ist.Put.data,
				site));
		break;
	case Ist_PutI:
		/* We can't handle these correctly. */
		abort();
		return NULL;
	case Ist_WrTmp:
		sm->prependSideEffect(
			new StateMachineSideEffectPut(
				-stmt->Ist.WrTmp.tmp - 1,
				stmt->Ist.WrTmp.data,
				site));
		break;
	case Ist_Store:
		sm->prependSideEffect(
			new StateMachineSideEffectStore(
				stmt->Ist.Store.addr,
				stmt->Ist.Store.data,
				site));
		break;

	case Ist_Dirty:
		if (!strcmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_8") ||
		    !strcmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_16") ||
		    !strcmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_64") ||
		    !strcmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_32")) {
			StateMachineSideEffectLoad *smsel =
				new StateMachineSideEffectLoad(
					stmt->Ist.Dirty.details->args[0],
					site);
			sm->prependSideEffect(
				new StateMachineSideEffectPut(
					-stmt->Ist.Dirty.details->tmp - 1,
					IRExpr_Binder(smsel->key),
					site));
			sm->prependSideEffect(smsel);
		}  else {
			abort();
		}
		break;

	case Ist_CAS:
		/* Can't backtrack across these */
		fprintf(_logfile, "Don't know how to backtrack across CAS statements?\n");
		sm = NULL;
		break;

	case Ist_MBE:
		break;
	case Ist_Exit:
		sm = new StateMachineEdge(
			new StateMachineBifurcate(
				site.rip,
				stmt->Ist.Exit.guard,
				new StateMachineEdge(
					new StateMachineStub(
						site.rip,
						IRExpr_Const(stmt->Ist.Exit.dst))),
				sm));
		break;
	}
	return sm;
}

StateMachineEdge *
getProximalCause(MachineState *ms, unsigned long rip, Thread *thr)
{
	unsigned idx;
	StateMachineEdge *sm = _getProximalCause(ms, rip, thr, &idx);
	if (!sm)
		return NULL;
	IRSB *irsb = ms->addressSpace->getIRSBForAddress(thr->tid._tid(), rip);
	while (idx != 0) {
		idx--;
		sm = backtrackOneStatement(sm, irsb->stmts[idx], ThreadRip::mk(thr->tid._tid(), rip));
		if (!sm)
			return NULL;
	}
	return sm;
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

/* Remove all of the nodes which appear to be uninteresting.  A node
   is uninteresting if it is not in the initial interesting set and
   there are no paths from it to an interesting node. */
template <typename t> void
trimCFG(CFGNode<t> *root, const InstructionSet &interestingAddresses, int max_path_length, bool acceptingAreInteresting)
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
		if ((acceptingAreInteresting && it->second->accepting) ||
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
		if (cfg->branch == cfg)
			cfg->branch = NULL;
		else if (!breakCycles(cfg->branch, numbering, p, onPath, clean))
			return false;
	}
	if (cfg->fallThrough) {
		CFGNode<t> **p = lastBackEdge;
		if (numbering[cfg->fallThrough] < numbering[cfg])
			p = &cfg->fallThrough;
		if (cfg->fallThrough == cfg)
			cfg->fallThrough = NULL;
		else if (!breakCycles(cfg->fallThrough, numbering, p, onPath, clean))
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

static bool storeMightBeLoadedByState(StateMachineState *sm, StateMachineSideEffectStore *smses, OracleInterface *oracle,
				      std::set<StateMachineEdge *> &memo);
static bool
storeMightBeLoadedByStateEdge(StateMachineEdge *sme, StateMachineSideEffectStore *smses, OracleInterface *oracle,
			      std::set<StateMachineEdge *> &memo)
{
	if (TIMEOUT)
		return true;
	if (memo.count(sme))
		return false;
	memo.insert(sme);
	for (unsigned y = 0; y < sme->sideEffects.size(); y++) {
		if (sme->sideEffects[y] == smses) {
			/* We've reached a cycle without hitting a
			   load of this store, so this path, at least,
			   is clear. */
			return false;
		}
		if (sme->sideEffects[y]->type == StateMachineSideEffect::Load) {
			StateMachineSideEffectLoad *smsel =
				dynamic_cast<StateMachineSideEffectLoad *>(sme->sideEffects[y]);
			assert(smsel);
			if (oracle->memoryAccessesMightAlias(smsel, smses))
				return true;
		}
	}
	return storeMightBeLoadedByState(sme->target, smses, oracle, memo);
}
static bool
storeMightBeLoadedByState(StateMachineState *sm, StateMachineSideEffectStore *smses, OracleInterface *oracle,
			  std::set<StateMachineEdge *> &memo)
{
	if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm))
		return storeMightBeLoadedByStateEdge(smp->target, smses, oracle, memo);
	if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm))
		return storeMightBeLoadedByStateEdge(smb->trueTarget, smses, oracle, memo) ||
			storeMightBeLoadedByStateEdge(smb->falseTarget, smses, oracle, memo);
	return false;
}
static bool
storeMightBeLoadedFollowingSideEffect(StateMachineEdge *sme, unsigned idx,
				      StateMachineSideEffectStore *smses,
				      OracleInterface *oracle)
{
	for (unsigned y = idx + 1; y < sme->sideEffects.size(); y++) {
		if (sme->sideEffects[y]->type == StateMachineSideEffect::Load) {
			StateMachineSideEffectLoad *smsel =
				dynamic_cast<StateMachineSideEffectLoad *>(sme->sideEffects[y]);
			assert(smsel);
			if (oracle->memoryAccessesMightAlias(smsel, smses))
				return true;
		}
	}
	std::set<StateMachineEdge *> memo;
	return storeMightBeLoadedByState(sme->target, smses, oracle, memo);
}

/* Look at the state machine, compare it to the tags table, and remove
   any stores which are definitely never loaded (assuming that the
   tags table is correct). */
static void removeRedundantStores(StateMachineState *sm, OracleInterface *oracle, bool *done_something,
				  std::set<StateMachineState *> &visited,
				  const AllowableOptimisations &opt);
static void
removeRedundantStores(StateMachineEdge *sme, OracleInterface *oracle, bool *done_something,
		      std::set<StateMachineState *> &visited,
		      const AllowableOptimisations &opt)
{
	if (TIMEOUT)
		return;
	for (unsigned x = 0; x < sme->sideEffects.size(); x++) {
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(sme->sideEffects[x])) {
			if (opt.ignoreStore(smses->rip.rip) &&
			    !storeMightBeLoadedFollowingSideEffect(sme, x, smses, oracle)) {
				sme->sideEffects[x] =
					new StateMachineSideEffectAssertFalse(
						IRExpr_Unop(
							Iop_BadPtr,
							smses->addr));
				sme->sideEffects.erase(
					sme->sideEffects.begin() + x);
				x--;
				*done_something = true;
			}
		}
	}
	removeRedundantStores(sme->target, oracle, done_something, visited, opt);
}
static void
removeRedundantStores(StateMachineState *sm, OracleInterface *oracle, bool *done_something,
		      std::set<StateMachineState *> &visited,
		      const AllowableOptimisations &opt)
{
	if (visited.count(sm))
		return;
	visited.insert(sm);
	if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
		removeRedundantStores(smp->target, oracle, done_something, visited, opt);
		return;
	}
	if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm)) {
		removeRedundantStores(smb->trueTarget, oracle, done_something, visited, opt);
		removeRedundantStores(smb->falseTarget, oracle, done_something, visited, opt);
		return;
	}
	assert(dynamic_cast<StateMachineUnreached *>(sm) ||
	       dynamic_cast<StateMachineCrash *>(sm) ||
	       dynamic_cast<StateMachineNoCrash *>(sm) ||
	       dynamic_cast<StateMachineStub *>(sm));
}
static void
removeRedundantStores(StateMachine *sm, OracleInterface *oracle, bool *done_something,
		      const AllowableOptimisations &opt)
{
	__set_profiling(removeRedundantStores);
	std::set<StateMachineState *> visited;

	removeRedundantStores(sm->root, oracle, done_something, visited, opt);
}

class StateMachineWalker {
	void doit(StateMachineState *s, std::set<StateMachineState *> &visited);
	void doit(StateMachineEdge *s, std::set<StateMachineState *> &visited);
public:
	virtual void visitEdge(StateMachineEdge *e) {}
	virtual void visitState(StateMachineState *s) {}
	virtual void visitSideEffect(StateMachineSideEffect *smse) {}
	void doit(StateMachineState *s);
};

void
StateMachineWalker::doit(StateMachineState *sm, std::set<StateMachineState *> &visited)
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
StateMachineWalker::doit(StateMachineEdge *se, std::set<StateMachineState *> &visited)
{
	visitEdge(se);
	for (std::vector<StateMachineSideEffect *>::iterator it = se->sideEffects.begin();
	     it != se->sideEffects.end();
	     it++)
		visitSideEffect(*it);
	doit(se->target, visited);
}
void
StateMachineWalker::doit(StateMachineState *s)
{
	std::set<StateMachineState *> visited;
	doit(s, visited);
}

class findAllSideEffectsVisitor : public StateMachineWalker {
public:
	std::set<StateMachineSideEffect *> &out;
	findAllSideEffectsVisitor(std::set<StateMachineSideEffect *> &o)
		: out(o)
	{}
	void visitSideEffect(StateMachineSideEffect *smse)
	{
		out.insert(smse);
	}
};
static void
findAllSideEffects(StateMachine *sm, std::set<StateMachineSideEffect *> &out)
{
	findAllSideEffectsVisitor v(out);
	v.doit(sm->root);
}

class findAllLoadsVisitor : public StateMachineWalker {
public:
	std::set<StateMachineSideEffectLoad *> &out;
	findAllLoadsVisitor(std::set<StateMachineSideEffectLoad *> &o)
		: out(o)
	{}
	void visitSideEffect(StateMachineSideEffect *smse)
	{
		if (smse->type == StateMachineSideEffect::Load)
			out.insert(dynamic_cast<StateMachineSideEffectLoad *>(smse));
	}
};
void
findAllLoads(StateMachine *sm, std::set<StateMachineSideEffectLoad *> &out)
{
	findAllLoadsVisitor v(out);
	v.doit(sm->root);
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
	v.doit(sm->root);
}

class findAllStatesVisitor : public StateMachineWalker {
public:
	std::set<StateMachineState *> &out;
	findAllStatesVisitor(std::set<StateMachineState *> &o)
		: out(o)
	{}
	void visitState(StateMachineState *sm)
	{
		out.insert(sm);
	}
};
static void
findAllStates(StateMachine *sm, std::set<StateMachineState *> &out)
{
	findAllStatesVisitor v(out);
	v.doit(sm->root);
}

class avail_t {
	class StateMachineClassifier : public StateMachineTransformer {
	protected:
		bool res;
	public:
		bool operator()(StateMachineSideEffect *se) {
			res = false;
			transform(se);
			return res;
		}
		bool operator()(IRExpr *e) {
			res = false;
			transformIRExpr(e);
			return res;
		}
	};
	void purge(StateMachineClassifier &);
public:
	std::set<StateMachineSideEffect *> sideEffects;
	std::set<IRExpr *> assertFalse;
	std::map<threadAndRegister, IRExpr *> registers;

	void clear() { sideEffects.clear(); assertFalse.clear(); registers.clear(); }
	void makeFalse(IRExpr *expr);
	void dereference(IRExpr *ptr);
	/* Go through and remove anything which isn't also present in
	   other.  Returns true if we did anything, and false
	   otherwise. */
	bool intersect(const avail_t &other);

	bool operator !=(const avail_t &other) const;

	void calcRegisterMap();

	void invalidateBinder(Int key, StateMachineSideEffect *preserve);
	void invalidateRegister(threadAndRegister reg, StateMachineSideEffect *preserve);

	int nr_asserts() const {
		int cntr = 0;
		for (auto it = sideEffects.begin(); it != sideEffects.end(); it++)
			if ((*it)->type == StateMachineSideEffect::AssertFalse)
				cntr++;
		return cntr;
	}
	void print(FILE *f);
};

void
avail_t::print(FILE *f)
{
	fprintf(f, "Available side effects:\n");
	for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
		fprintf(f, "\t");
		(*it)->prettyPrint(f);
		fprintf(f, "\n");
	}
	fprintf(f, "Asserted false:\n");
	for (auto it = assertFalse.begin(); it != assertFalse.end(); it++) {
		fprintf(f, "\t");
		ppIRExpr(*it, f);
		fprintf(f, "\n");
	}
}

void
avail_t::makeFalse(IRExpr *expr)
{
	if (expr->tag == Iex_Const)
		return;
	for (auto it = assertFalse.begin();
	     it != assertFalse.end();
	     it++)
		if (definitelyEqual(*it, expr, AllowableOptimisations::defaultOptimisations))
			return;
	assertFalse.insert(expr);
}

void
avail_t::dereference(IRExpr *addr)
{
	if (TIMEOUT)
		return;
	IRExpr *badPtr = IRExpr_Unop(Iop_BadPtr, addr);
	badPtr = simplifyIRExpr(badPtr, AllowableOptimisations::defaultOptimisations);
	makeFalse(badPtr);
}

bool
avail_t::intersect(const avail_t &other)
{
	bool res = false;
	for (std::set<StateMachineSideEffect *>::iterator it = sideEffects.begin();
	     it != sideEffects.end();
		) {
		if (other.sideEffects.count(*it) == 0) {
			res = true;
			sideEffects.erase(it++); 
		} else {
			it++;
		}
	}
	for (auto it = assertFalse.begin();
	     it != assertFalse.end();
		) {
		bool purge = true;
		for (auto it2 = other.assertFalse.begin();
		     purge && it2 != other.assertFalse.end();
		     it2++) {
			if (definitelyEqual(*it, *it2, AllowableOptimisations::defaultOptimisations))
				purge = false;
		}
		if (purge) {
			res = true;
			assertFalse.erase(it++);
		} else {
			it++;
		}
	}
	return res;
}

void
avail_t::purge(StateMachineClassifier &o)
{
	for (auto it = sideEffects.begin(); it != sideEffects.end(); ) {
		if (o(*it)) {
			sideEffects.erase(it++);
		} else {
			it++;
		}
	}
	for (auto it = assertFalse.begin(); it != assertFalse.end(); ) {
		if (o(*it))
			assertFalse.erase(it++);
		else
			it++;
	}
	for (auto it = registers.begin(); it != registers.end(); ) {
		if (o(it->second))
			registers.erase(it++);
		else
			it++;
	}
}
void
avail_t::invalidateRegister(threadAndRegister reg, StateMachineSideEffect *preserve)
{
	class _ : public StateMachineClassifier {
		threadAndRegister reg;
		StateMachineSideEffect *preserve;
		IRExpr *transformIex(IRExpr::Get *e) {
			if (threadAndRegister(*e) == reg)
				res = true;
			return NULL;
		}
		IRExpr *transformIex(IRExpr::RdTmp *e) {
			if (threadAndRegister(*e) == reg)
				res = true;
			return NULL;
		}
		StateMachineSideEffect *transform(StateMachineSideEffect *se, bool *done_something)
		{
			if (se != preserve &&
			    se->type == StateMachineSideEffect::Put &&
			    threadAndRegister(*(StateMachineSideEffectPut *)se) == reg)
				res = true;
			return StateMachineClassifier::transform(se, done_something);
		}
	public:
		_(threadAndRegister _reg, StateMachineSideEffect *_preserve)
			: reg(_reg), preserve(_preserve)
		{}
	} checkIfPresent(reg, preserve);
	purge(checkIfPresent);
}
void
avail_t::invalidateBinder(Int key, StateMachineSideEffect *preserve)
{
	class _ : public StateMachineClassifier {
		Int k;
		StateMachineSideEffect *preserve;
		IRExpr *transformIex(IRExpr::Binder *e) {
			if (e->binder == k)
				res = true;
			return NULL;
		}
		StateMachineSideEffect *transform(StateMachineSideEffect *se, bool *done_something)
		{
			if (se != preserve &&
			    ( (se->type == StateMachineSideEffect::Load &&
			       ((StateMachineSideEffectLoad *)se)->key == k) ||
			      (se->type == StateMachineSideEffect::Copy &&
			       ((StateMachineSideEffectCopy *)se)->key == k) ))
				res = true;
			return StateMachineClassifier::transform(se, done_something);
		}
	public:
		_(unsigned _k, StateMachineSideEffect *_preserve)
			: k(_k), preserve(_preserve)
		{}
	} checkIfPresent(key, preserve);
	purge(checkIfPresent);
}

bool
avail_t::operator!=(const avail_t &other) const
{
	return sideEffects != other.sideEffects || assertFalse != other.assertFalse;
}

void
avail_t::calcRegisterMap()
{
	registers.clear();
	for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
		StateMachineSideEffect *se = *it;
		if (se->type == StateMachineSideEffect::Put) {
			StateMachineSideEffectPut *sep = (StateMachineSideEffectPut *)se;
			registers[threadAndRegister(*sep)] = sep->value;
		} else if (se->type == StateMachineSideEffect::AssertFalse) {
			StateMachineSideEffectAssertFalse *seaf = (StateMachineSideEffectAssertFalse *)se;
			makeFalse(seaf->value);
		}
	}
}

static void
updateAvailSetForSideEffect(avail_t &outputAvail, StateMachineSideEffect *smse,
			    const AllowableOptimisations &opt,
			    const Oracle::RegisterAliasingConfiguration &alias,
			    OracleInterface *oracle)
{
	if (TIMEOUT)
		return;
	switch (smse->type) {
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectStore *smses =
			dynamic_cast<StateMachineSideEffectStore *>(smse);
		assert(smses);
		/* Eliminate anything which is killed */
		for (std::set<StateMachineSideEffect *>::iterator it = outputAvail.sideEffects.begin();
		     it != outputAvail.sideEffects.end();
			) {
			StateMachineSideEffectStore *smses2 =
				dynamic_cast<StateMachineSideEffectStore *>(*it);
			StateMachineSideEffectLoad *smsel2 =
				dynamic_cast<StateMachineSideEffectLoad *>(*it);
			IRExpr *addr;
			if (smses2)
				addr = smses2->addr;
			else if (smsel2)
				addr = smsel2->addr;
			else
				addr = NULL;

			if ( addr &&
			     alias.ptrsMightAlias(addr, smses->addr, opt.freeVariablesMightAccessStack) &&
			     ((smses2 && oracle->memoryAccessesMightAlias(smses2, smses)) ||
			      (smsel2 && oracle->memoryAccessesMightAlias(smsel2, smses))) &&
			     !definitelyNotEqual( addr,
						  smses->addr,
						  opt) )
				outputAvail.sideEffects.erase(it++);
			else
				it++;
		}
		/* Introduce the store which was generated. */
		if (opt.assumeNoInterferingStores ||
		    oracle->storeIsThreadLocal(smses))
			outputAvail.sideEffects.insert(smses);
		outputAvail.dereference(smses->addr);
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec =
			dynamic_cast<StateMachineSideEffectCopy *>(smse);
		assert(smsec);
		outputAvail.sideEffects.insert(smsec);
		outputAvail.invalidateBinder(smsec->key, smsec);
		break;
	}
	case StateMachineSideEffect::Put: {
		StateMachineSideEffectPut *smsep =
			dynamic_cast<StateMachineSideEffectPut *>(smse);
		assert(smsep);
		outputAvail.sideEffects.insert(smsep);
		outputAvail.invalidateRegister(threadAndRegister(*smsep), smsep);
		break;
	}
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel =
			dynamic_cast<StateMachineSideEffectLoad *>(smse);
		outputAvail.sideEffects.insert(smsel);
		outputAvail.dereference(smsel->addr);
		outputAvail.invalidateBinder(smsel->key, smsel);
		break;
	}
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(smse);
		outputAvail.makeFalse(smseaf->value);
		break;
	}
	case StateMachineSideEffect::Unreached:
		abort();
	}
	outputAvail.calcRegisterMap();
}

class applyAvailTransformer : public IRExprTransformer {
public:
	const avail_t &avail;
	const bool use_assumptions;
	IRExpr *transformIex(IRExpr::Binder *e) {
		for (std::set<StateMachineSideEffect *>::const_iterator it = avail.sideEffects.begin();
		     it != avail.sideEffects.end();
		     it++) {
			if ( (*it)->type != StateMachineSideEffect::Copy)
				continue;
			StateMachineSideEffectCopy *smsec = dynamic_cast<StateMachineSideEffectCopy *>(*it);
			assert(smsec);
			if (smsec->key == e->binder)
				return smsec->value;
		}
		return IRExprTransformer::transformIex(e);
	}
	IRExpr *transformIex(IRExpr::Get *e) {
		auto it = avail.registers.find(threadAndRegister(*e));
		if (it != avail.registers.end())
			return it->second;
		return IRExprTransformer::transformIex(e);
	}
	IRExpr *transformIex(IRExpr::RdTmp *e) {
		auto it = avail.registers.find(threadAndRegister(*e));
		if (it != avail.registers.end())
			return it->second;
		return IRExprTransformer::transformIex(e);
	}
	IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
		if (use_assumptions) {
			for (std::set<IRExpr *>::iterator it = avail.assertFalse.begin();
			     it != avail.assertFalse.end();
			     it++) {
				if (definitelyEqual(*it, e,  AllowableOptimisations::defaultOptimisations)) {
					*done_something = true;
					return IRExpr_Const(IRConst_U1(0));
				}
			}
		}
		return IRExprTransformer::transformIRExpr(e, done_something);
	}
	applyAvailTransformer(const avail_t &_avail, bool _use_assumptions)
		: avail(_avail), use_assumptions(_use_assumptions)
	{}
};
static IRExpr *
applyAvailSet(const avail_t &avail, IRExpr *expr, bool use_assumptions, bool *done_something)
{
	applyAvailTransformer aat(avail, use_assumptions);
	return aat.transformIRExpr(expr, done_something);
}

/* Slightly misnamed: this also propagates copy operations.  Also, it
   doesn't so much eliminate loads are replace them with copies of
   already-loaded values. */
static StateMachineState *buildNewStateMachineWithLoadsEliminated(
	StateMachineState *sm,
	std::map<StateMachineState *, avail_t> &availMap,
	std::map<StateMachineState *, StateMachineState *> &memo,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration &aliasing,
	OracleInterface *oracle,
	bool *done_something);
static StateMachineEdge *
buildNewStateMachineWithLoadsEliminated(
	StateMachineEdge *sme,
	const avail_t &initialAvail,
	std::map<StateMachineState *, avail_t> &availMap,
	std::map<StateMachineState *, StateMachineState *> &memo,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration &aliasing,
	OracleInterface *oracle,
	bool *done_something)
{
	if (TIMEOUT)
		return sme;
	StateMachineEdge *res =
		new StateMachineEdge(buildNewStateMachineWithLoadsEliminated(sme->target, availMap, memo, opt, aliasing, oracle,
									     done_something));

	avail_t currentlyAvailable(initialAvail);
	
	for (std::vector<StateMachineSideEffect *>::const_iterator it =
		     sme->sideEffects.begin();
	     !TIMEOUT && it != sme->sideEffects.end();
	     it++) {
		StateMachineSideEffect *newEffect;

		newEffect = NULL;

		switch ((*it)->type) {
		case StateMachineSideEffect::Store: {
			StateMachineSideEffectStore *smses =
				dynamic_cast<StateMachineSideEffectStore *>(*it);
			IRExpr *newAddr, *newData;
			bool doit = false;
			newAddr = applyAvailSet(currentlyAvailable, smses->addr, false, &doit);
			newData = applyAvailSet(currentlyAvailable, smses->data, false, &doit);
			if (doit) {
				newEffect = new StateMachineSideEffectStore(
					newAddr, newData, smses->rip);
				*done_something = true;
			} else {
				newEffect = smses;
			}
			break;
		}
		case StateMachineSideEffect::Load: {
			StateMachineSideEffectLoad *smsel =
				dynamic_cast<StateMachineSideEffectLoad *>(*it);
			IRExpr *newAddr;
			bool doit = false;
			newAddr = applyAvailSet(currentlyAvailable, smsel->addr, false, &doit);
			for (std::set<StateMachineSideEffect *>::iterator it2 = currentlyAvailable.sideEffects.begin();
			     !newEffect && it2 != currentlyAvailable.sideEffects.end();
			     it2++) {
				StateMachineSideEffectStore *smses2 =
					dynamic_cast<StateMachineSideEffectStore *>(*it2);
				StateMachineSideEffectLoad *smsel2 =
					dynamic_cast<StateMachineSideEffectLoad *>(*it2);
				if ( smses2 &&
				     aliasing.ptrsMightAlias(smses2->addr, newAddr, opt.freeVariablesMightAccessStack) &&
				     definitelyEqual(smses2->addr, newAddr, opt) ) {
					newEffect =
						new StateMachineSideEffectCopy(
							smsel->key,
							smses2->data);
				} else if ( smsel2 &&
					    aliasing.ptrsMightAlias(smsel2->addr, newAddr, opt.freeVariablesMightAccessStack) &&
					    definitelyEqual(smsel2->addr, newAddr, opt) ) {
					newEffect =
						new StateMachineSideEffectCopy(
							smsel->key,
							IRExpr_Binder(smsel2->key));
				}
			}
			if (!newEffect && doit)
				newEffect = new StateMachineSideEffectLoad(
					smsel->key, newAddr, smsel->rip);
			if (!newEffect)
				newEffect = *it;
			if (newEffect != *it)
				*done_something = true;
			break;
		}
		case StateMachineSideEffect::Copy: {
			StateMachineSideEffectCopy *smsec =
				dynamic_cast<StateMachineSideEffectCopy *>(*it);
			IRExpr *newValue;
			bool doit = false;
			newValue = applyAvailSet(currentlyAvailable, smsec->value, false, &doit);
			if (doit)
				newEffect = new StateMachineSideEffectCopy(
					smsec->key, newValue);
			else
				newEffect = *it;
			break;
		}
		case StateMachineSideEffect::Unreached:
			newEffect = *it;
			break;
		case StateMachineSideEffect::Put: {
			StateMachineSideEffectPut *smsep =
				dynamic_cast<StateMachineSideEffectPut *>(*it);
			IRExpr *newVal;
			bool doit = false;
			newVal = applyAvailSet(currentlyAvailable, smsep->value, false, &doit);
			if (doit)
				newEffect = new StateMachineSideEffectPut(
					smsep->offset, newVal, smsep->rip);
			else
				newEffect = *it;
			break;
		}
		case StateMachineSideEffect::AssertFalse: {
			StateMachineSideEffectAssertFalse *smseaf =
				dynamic_cast<StateMachineSideEffectAssertFalse *>(*it);
			IRExpr *newVal;
			bool doit = false;
			if (currentlyAvailable.nr_asserts() < MAX_LIVE_ASSERTIONS) {
				newVal = applyAvailSet(currentlyAvailable, smseaf->value, true, &doit);
			} else {
				/* We have too many live assertions.
				   That can lead to them holding
				   enormous number of variables live,
				   which isn't much use, so turn this
				   one into a no-op.  It'll get
				   optimised out again later. */
				newVal = IRExpr_Const(IRConst_U1(0));
				doit = true;
			}
			if (doit)
				newEffect = new StateMachineSideEffectAssertFalse(newVal);
			else
				newEffect = *it;
			break;
		}
		}
		assert(newEffect);
		updateAvailSetForSideEffect(currentlyAvailable, newEffect, opt, aliasing, oracle);
		res->sideEffects.push_back(newEffect);
	}
	return res;
}
static StateMachineState *
buildNewStateMachineWithLoadsEliminated(
	StateMachineState *sm,
	std::map<StateMachineState *, avail_t> &availMap,
	std::map<StateMachineState *, StateMachineState *> &memo,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration &alias,
	OracleInterface *oracle,
	bool *done_something)
{
	if (dynamic_cast<StateMachineCrash *>(sm) ||
	    dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm) ||
	    dynamic_cast<StateMachineUnreached *>(sm))
		return sm;
	if (memo.count(sm)) {
		/* We rely on whoever it was that set memo[sm] having
		 * also set *done_something if appropriate. */
		return memo[sm];
	}
	avail_t avail(availMap[sm]);
	avail.calcRegisterMap();

	if (StateMachineBifurcate *smb =
	    dynamic_cast<StateMachineBifurcate *>(sm)) {
		StateMachineBifurcate *res;
		bool doit = false;
		res = new StateMachineBifurcate(
			sm->origin,
			applyAvailSet(avail, smb->condition, true, &doit),
			(StateMachineEdge *)NULL, NULL);
		*done_something |= doit;
		memo[sm] = res;
		res->trueTarget = buildNewStateMachineWithLoadsEliminated(
			smb->trueTarget, avail, availMap, memo, opt, alias, oracle,
			done_something);
		res->falseTarget = buildNewStateMachineWithLoadsEliminated(
			smb->falseTarget, avail, availMap, memo, opt, alias, oracle,
			done_something);
		return res;
	} if (StateMachineProxy *smp =
	      dynamic_cast<StateMachineProxy *>(sm)) {
		StateMachineProxy *res;
		res = new StateMachineProxy(sm->origin, (StateMachineEdge *)NULL);
		memo[sm] = res;
		res->target = buildNewStateMachineWithLoadsEliminated(
			smp->target, avail, availMap, memo, opt, alias, oracle,
			done_something);
		return res;
	} else {
		abort();
	}
}

static StateMachine *
buildNewStateMachineWithLoadsEliminated(
	StateMachine *sm,
	std::map<StateMachineState *, avail_t> &availMap,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration &alias,
	OracleInterface *oracle,
	bool *done_something)
{
	std::map<StateMachineState *, StateMachineState *> memo;
	bool d = false;
	StateMachineState *new_root = buildNewStateMachineWithLoadsEliminated(sm->root, availMap, memo, opt, alias, oracle,
									      &d);
	if (d) {
		*done_something = true;
		return new StateMachine(sm, sm->origin, new_root);
	} else {
		return sm;
	}
}

/* Available expression analysis on memory locations.  This isn't
   included in the normal optimise() operation because it's
   context-sensitive, and therefore isn't allowed to mutate nodes
   in-place. */
static StateMachine *
availExpressionAnalysis(StateMachine *sm, const AllowableOptimisations &opt,
			const Oracle::RegisterAliasingConfiguration &alias, OracleInterface *oracle,
			bool *done_something)
{
	__set_profiling(availExpressionAnalysis);
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

	/* build the set of potentially-available expressions. */
	avail_t potentiallyAvailable;
	findAllSideEffects(sm, potentiallyAvailable.sideEffects);
	for (std::set<StateMachineSideEffect *>::iterator it = potentiallyAvailable.sideEffects.begin();
	     !TIMEOUT && it != potentiallyAvailable.sideEffects.end();
	     it++) {
		StateMachineSideEffect *smse = *it;
		if (StateMachineSideEffectMemoryAccess *smsema =
		    dynamic_cast<StateMachineSideEffectMemoryAccess *>(smse)) {
			potentiallyAvailable.dereference(smsema->addr);
		} else if (StateMachineSideEffectAssertFalse *smseaf =
			   dynamic_cast<StateMachineSideEffectAssertFalse *>(smse)) {
			potentiallyAvailable.makeFalse(smseaf->value);
		}
	}

	/* If we're not executing atomically, stores to
	   non-thread-local memory locations are never considered to
	   be available. */
	if (!opt.assumeNoInterferingStores) {
		for (std::set<StateMachineSideEffect *>::iterator it = potentiallyAvailable.sideEffects.begin();
		     !TIMEOUT && it != potentiallyAvailable.sideEffects.end();
			) {
			StateMachineSideEffectStore *smses =
				dynamic_cast<StateMachineSideEffectStore *>(*it);
			StateMachineSideEffectLoad *smsel =
				dynamic_cast<StateMachineSideEffectLoad *>(*it);
			if ( (smses && !oracle->storeIsThreadLocal(smses)) ||
			     (smsel && !oracle->loadIsThreadLocal(smsel)) ) {
				potentiallyAvailable.sideEffects.erase(it++);
			} else {
				it++;
			}
		}
	}

	/* build the initial availability map.  We start by assuming
	 * that everything is available everywhere, except that at the
	 * start of the very first state nothing is available, and
	 * then use a Tarski iteration to make everything
	 * consistent. */
	std::set<StateMachineEdge *> allEdges;
	std::set<StateMachineState *> allStates;
	findAllEdges(sm, allEdges);
	findAllStates(sm, allStates);
	std::map<StateMachineState *, avail_t> availOnEntry;
	std::map<StateMachineEdge *, avail_t> availOnExit;
	for (std::set<StateMachineEdge *>::iterator it = allEdges.begin();
	     !TIMEOUT && it != allEdges.end();
	     it++)
		availOnExit[*it] = potentiallyAvailable;
	for (std::set<StateMachineState *>::iterator it = allStates.begin();
	     !TIMEOUT && it != allStates.end();
	     it++)
		availOnEntry[*it] = potentiallyAvailable;
	availOnEntry[sm->root].clear();

	std::set<StateMachineState *> statesNeedingRefresh(allStates);

	/* Tarski iteration.  */
	bool progress;
	do {
		progress = false;

		if (TIMEOUT)
			return sm;

		/* Update the set of things which are available on
		   entry.  This means walking the set of edges and
		   looking at the targets.  If there's something which
		   is available at the start of the target, but not at
		   the end of this edge, remove it from the target. */
		for (std::set<StateMachineEdge *>::iterator it = allEdges.begin();
		     it != allEdges.end();
		     it++) {
			StateMachineEdge *edge = *it;
			StateMachineState *target = edge->target;
			avail_t &avail_at_end_of_edge(availOnExit[edge]);
			avail_t &avail_at_start_of_target(availOnEntry[target]);
			if (avail_at_start_of_target.intersect(avail_at_end_of_edge)) {
				progress = true;
				statesNeedingRefresh.insert(target);
			}
		}

		/* Now go through and update the avail-on-exit set.
		   Use a slightly weird-looking iteration over states
		   instead of over edges because that makes things a
		   bit easier. */
		for (std::set<StateMachineState *>::iterator it = statesNeedingRefresh.begin();
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
				     !TIMEOUT && it2 != edge->sideEffects.end();
				     it2++)
					updateAvailSetForSideEffect(outputAvail, *it2,
								    opt, alias, oracle);
				avail_t &currentAvail(availOnExit[edge]);
				if (!progress && currentAvail != outputAvail)
					progress = true;
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
		oracle,
		done_something);
}

static StateMachineState *
rewriteStateMachine(StateMachineState *sm,
		    std::map<StateMachineState *, StateMachineState *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules,
		    std::set<StateMachineState *> &memo,
		    std::set<StateMachineEdge *> &edgeMemo);

static StateMachineEdge *
rewriteStateMachineEdge(StateMachineEdge *sme,
			std::map<StateMachineState *, StateMachineState *> &rules,
			std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules,
			std::set<StateMachineState *> &memo,
			std::set<StateMachineEdge *> &edgeMemo)
{
	if (edgeMemo.count(sme))
		return sme;

	if (edgeRules.count(sme)) {
		edgeMemo.insert(edgeRules[sme]);
		return rewriteStateMachineEdge(edgeRules[sme], rules, edgeRules, memo, edgeMemo);
	}
	if (TIMEOUT)
		return sme;
	edgeMemo.insert(sme);
	sme->target = rewriteStateMachine(sme->target,
					  rules,
					  edgeRules,
					  memo,
					  edgeMemo);
	return sme;
}

static StateMachineState *
rewriteStateMachine(StateMachineState *sm,
		    std::map<StateMachineState *, StateMachineState *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules,
		    std::set<StateMachineState *> &memo,
		    std::set<StateMachineEdge *> &edgeMemo)
{
	if (memo.count(sm))
		return sm;

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

template <typename t> void
assert_mapping_acyclic(std::map<t, t> &m)
{
	std::set<t> clean;

	for (typename std::map<t, t>::const_iterator it = m.begin();
	     it != m.end();
	     it++) {
		if (clean.count(it->first))
			continue;
		t fastIterator;
		t slowIterator;
		bool cycle;
		slowIterator = fastIterator = it->first;
		while (1) {
			clean.insert(fastIterator);
			fastIterator = m[fastIterator];
			if (fastIterator == slowIterator) {
				cycle = true;
				break;
			}
			if (!m.count(fastIterator)) {
				cycle = false;
				break;
			}

			clean.insert(fastIterator);
			fastIterator = m[fastIterator];
			if (fastIterator == slowIterator) {
				cycle = true;
				break;
			}
			if (!m.count(fastIterator)) {
				cycle = false;
				break;
			}

			assert(m.count(slowIterator));
			slowIterator = m[slowIterator];
		}
		assert(!cycle);
	}
}

static StateMachineState *
rewriteStateMachine(StateMachineState *sm, std::map<StateMachineState *, StateMachineState *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules)
{
	/* Cyclies make this work badly. */
	assert_mapping_acyclic(rules);
	assert_mapping_acyclic(edgeRules);

	std::set<StateMachineState *> memo;
	std::set<StateMachineEdge *> edgeMemo;

	return rewriteStateMachine(sm, rules, edgeRules, memo, edgeMemo);
}

static StateMachine *
rewriteStateMachine(StateMachine *sm, std::map<StateMachineState *, StateMachineState *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules)
{
	sm->root = rewriteStateMachine(sm->root, rules, edgeRules);
	return sm;
}


static bool
edgesLocallyBisimilar(StateMachineEdge *sme1,
		      StateMachineEdge *sme2,
		      const std::set<st_pair_t> &states,
		      const AllowableOptimisations &opt)
{
	if (sme1->sideEffects.size() !=
	    sme2->sideEffects.size())
		return false;
	if (!states.count(st_pair_t(sme1->target, sme2->target)))
		return false;
	for (unsigned x = 0; x < sme1->sideEffects.size(); x++) {
		if (!sideEffectsBisimilar(sme1->sideEffects[x],
					  sme2->sideEffects[x],
					  opt))
			return false;
	}
	return true;
}

static bool
statesLocallyBisimilar(StateMachineState *sm1,
		       StateMachineState *sm2,
		       const std::set<st_edge_pair_t> &edges,
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
		return statesLocallyBisimilar(sm2, sm1, edges, opt);

	if (dynamic_cast<StateMachineCrash *>(sm1)) {
		if (dynamic_cast<StateMachineCrash *>(sm2)) {
			return true;
		} else {
			return false;
		}
	}

	if (dynamic_cast<StateMachineNoCrash *>(sm1)) {
		if (dynamic_cast<StateMachineNoCrash *>(sm2)) {
			return true;
		} else {
			return false;
		}
	}

	if (dynamic_cast<StateMachineUnreached *>(sm1)) {
		if (dynamic_cast<StateMachineUnreached *>(sm2)) {
			return true;
		} else {
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
			return edges.count(st_edge_pair_t(smp1->target, smp2->target));
		} else {
			return false;
		}
	}

	StateMachineBifurcate *smb1 =
		dynamic_cast<StateMachineBifurcate *>(sm1);
	StateMachineBifurcate *smb2 =
		dynamic_cast<StateMachineBifurcate *>(sm2);
	assert(smb1);
	assert(smb2);
	return edges.count(st_edge_pair_t(smb1->trueTarget, smb2->trueTarget)) &&
		edges.count(st_edge_pair_t(smb1->falseTarget, smb2->falseTarget)) &&
		definitelyEqual(smb1->condition, smb2->condition, opt);
}

static void
buildStateMachineBisimilarityMap(StateMachine *sm, std::set<st_pair_t> &bisimilarStates,
				 std::set<st_edge_pair_t> &bisimilarEdges,
				 const std::set<StateMachineState *> *allStates,
				 const AllowableOptimisations &opt)
{
	/* We start by assuming that all states are bisimilar to each
	   other, and then use Tarski iteration to eliminate the
	   contradictions.  That allows us to build up maximal sets of
	   states such that the states in the sets are bisimilar to
	   each other.  Once we've got that, we pick one of the states
	   as being representative of the set, and then use it in
	   place of the other states. */
	std::set<StateMachineState *> _allStates;
	if (!allStates) {
		allStates = &_allStates;
		findAllStates(sm, _allStates);
	}

	std::set<StateMachineEdge *> allEdges;
	findAllEdges(sm, allEdges);	

	/* Initially, everything is bisimilar to everything else. */
	for (std::set<StateMachineState *>::const_iterator it = allStates->begin();
	     !TIMEOUT && it != allStates->end();
	     it++)
		for (std::set<StateMachineState *>::const_iterator it2 = allStates->begin();
		     !TIMEOUT && it2 != allStates->end();
		     it2++)
			bisimilarStates.insert(st_pair_t(*it, *it2));
	for (std::set<StateMachineEdge *>::iterator it = allEdges.begin();
	     !TIMEOUT && it != allEdges.end();
	     it++)
		for (std::set<StateMachineEdge *>::iterator it2 = allEdges.begin();
		     !TIMEOUT && it2 != allEdges.end();
		     it2++)
			bisimilarEdges.insert(st_edge_pair_t(*it, *it2));

	bool progress;
	do {
		progress = false;

		if (TIMEOUT)
			return;
		/* Iterate over every suspected bisimilarity pair and
		   check for ``local bisimilarity''.  Once we're
		   consistent with the local bisimilarity
		   relationship, we will also be consistent with
		   global bismilarity. */
		for (std::set<st_pair_t>::iterator it = bisimilarStates.begin();
		     it != bisimilarStates.end();
			) {
			if (statesLocallyBisimilar(it->first, it->second, bisimilarEdges, opt)) {
				it++;
			} else {
				bisimilarStates.erase(it++);
				progress = true;
			}
		}
		for (std::set<st_edge_pair_t>::iterator it = bisimilarEdges.begin();
		     it != bisimilarEdges.end();
			) {
			if (edgesLocallyBisimilar(it->first, it->second, bisimilarStates, opt)) {
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
	__set_profiling(bisimilarityReduction);
	std::set<st_edge_pair_t> bisimilarEdges;
	std::set<st_pair_t> bisimilarStates;
	std::set<StateMachineState *> allStates;

	findAllStates(sm, allStates);
	buildStateMachineBisimilarityMap(sm, bisimilarStates, bisimilarEdges, &allStates, opt);

	if (TIMEOUT)
		return sm;

	std::map<StateMachineState *, StateMachineState *> canonMap;
	/* While we're here, iterate over every bifurcation node, and
	   if the branches are bisimilar to each other then replace it
	   with a proxy. */

	for (std::set<StateMachineState *>::iterator it = allStates.begin();
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
		StateMachineState *s1 = it->first;
		StateMachineState *s2 = it->second;

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

/* Turn references to RBP into RSP+k, if we know that RBP=RSP+k. */
class CanonicaliseRbp : public StateMachineTransformer {
	IRExpr *delta;
	IRExpr *transformIex(IRExpr::Get *orig) {
		if (orig->offset == OFFSET_amd64_RBP && orig->ty == Ity_I64) {
			return IRExpr_Associative(
				Iop_Add64,
				delta,
				IRExpr_Get(
					OFFSET_amd64_RSP,
					Ity_I64,
					orig->tid),
				NULL);
		}
		return StateMachineTransformer::transformIex(orig);
	}
public:
	CanonicaliseRbp(long _delta)
		: delta(IRExpr_Const(IRConst_U64(_delta)))
	{
	}
};
static StateMachine *
canonicaliseRbp(StateMachine *sm, OracleInterface *oracle,
		bool *done_something)
{
	long delta;

	if (!oracle->getRbpToRspDelta(sm->origin, &delta)) {
		/* Can't do anything if we don't know the delta */
		return sm;
	}
	/* Got RBP->RSP delta, want RSP->RBP */
	delta = -delta;

	CanonicaliseRbp canon(delta);
	return canon.transform(sm, done_something);
}

class BuildFreeVariableMapTransformer : public StateMachineTransformer {
public:
	std::set<threadAndRegister> accessedRegisters;
	std::set<threadAndRegister> puttedRegisters;
	FreeVariableMap &freeVariables;

	std::map<threadAndRegister, IRExpr *> map;

	StateMachineSideEffect *transform(StateMachineSideEffect *se, bool *done_something)
	{
		if (se->type == StateMachineSideEffect::Put)
			puttedRegisters.insert(threadAndRegister(*(StateMachineSideEffectPut *)se));
		return se;
	}
	IRExpr *transformIex(IRExpr::Get *what) {
		accessedRegisters.insert(threadAndRegister(*what));
		return StateMachineTransformer::transformIex(what);
	}
	BuildFreeVariableMapTransformer(FreeVariableMap &_freeVariables)
		: freeVariables(_freeVariables)
	{}
	/* It's not really a good idea to introduce more free
	   variables on behalf of an expression which is only used in
	   the free variable map. */
	void transform(FreeVariableMap *fvm, bool *done_something)
	{}
	void finalise()
	{
		for (auto it = accessedRegisters.begin();
		     it != accessedRegisters.end();
		     it++)
			if (!puttedRegisters.count(*it))
				map[*it] = IRExpr_FreeVariable();
	}
};

class IntroduceFreeVariablesRegisterTransformer : public StateMachineTransformer {
public:
	std::map<threadAndRegister, IRExpr *> &map;
	IntroduceFreeVariablesRegisterTransformer(
		std::map<threadAndRegister, IRExpr *> &_map)
		: map(_map)
	{}
	IRExpr *transformIex(IRExpr::Get *what) {
		threadAndRegister k(*what);
		if (map.count(k)) {
			IRExpr *res = map[k];
			fvDelta.push_back(std::pair<FreeVariableKey, IRExpr *>(res->Iex.FreeVariable.key, currentIRExpr()));
			return res;
		} else {
			return NULL;
		}
	}
};

static StateMachine *
introduceFreeVariablesForRegisters(StateMachine *sm, bool *done_something)
{
	__set_profiling(introduceFreeVariablesForRegisters);
	BuildFreeVariableMapTransformer t(sm->freeVariables);
	t.StateMachineTransformer::transform(sm);
	t.finalise();
	IntroduceFreeVariablesRegisterTransformer s(t.map);
	return s.transform(sm, done_something);
}

/* For some reason C++ doesn't allow you to instantiate a template at
   a function-local type.  Work around this language limitation with a
   silly dummy namespace. */
namespace __offline_analysis_dead_code {
	class LivenessEntry : public std::pair<std::set<Int>, std::set<threadAndRegister> > {
		void killBinder(Int binder)
		{
			first.erase(binder);
		}

		void killRegister(threadAndRegister r)
		{
			second.erase(r);
		}
	public:
		void useExpression(IRExpr *e)
		{
			class _ : public IRExprTransformer {
				LivenessEntry &out;
				IRExpr *transformIex(IRExpr::Get *g) {
					out.second.insert(threadAndRegister(*g));
					return IRExprTransformer::transformIex(g);
				}
				IRExpr *transformIex(IRExpr::RdTmp *g) {
					out.second.insert(threadAndRegister(*g));
					return IRExprTransformer::transformIex(g);
				}
				IRExpr *transformIex(IRExpr::Binder *b) {
					out.first.insert(b->binder);
					return IRExprTransformer::transformIex(b);
				}
			public:
				_(LivenessEntry &_out) : out(_out) {}
			} t(*this);
			t.transformIRExpr(e);
		}

		void useSideEffect(StateMachineSideEffect *smse)
		{
			switch (smse->type) {
			case StateMachineSideEffect::Load: {
				StateMachineSideEffectLoad *smsel =
					(StateMachineSideEffectLoad *)smse;
				killBinder(smsel->key);
				useExpression(smsel->addr);
				return;
			}
			case StateMachineSideEffect::Copy: {
				StateMachineSideEffectCopy *smsec =
					(StateMachineSideEffectCopy *)smse;
				killBinder(smsec->key);
				useExpression(smsec->value);
				return;
			}
			case StateMachineSideEffect::Store: {
				StateMachineSideEffectStore *smses =
					(StateMachineSideEffectStore *)smse;
				useExpression(smses->addr);
				useExpression(smses->data);
				return;
			}
			case StateMachineSideEffect::Put: {
				StateMachineSideEffectPut *smsep =
					(StateMachineSideEffectPut *)smse;
				killRegister(threadAndRegister(*smsep));
				useExpression(smsep->value);
				return;
			}
			case StateMachineSideEffect::Unreached:
				return;
			case StateMachineSideEffect::AssertFalse: {
				StateMachineSideEffectAssertFalse *smseaf =
					(StateMachineSideEffectAssertFalse *)smse;
				useExpression(smseaf->value);
				return;
			}
			}
			abort();
		}

		void merge(const LivenessEntry &other) {
			for (auto it = other.first.begin();
			     it != other.first.end();
			     it++)
				first.insert(*it);
			for (auto it = other.second.begin();
			     it != other.second.end();
			     it++)
				second.insert(*it);
		}

		bool binderLive(Int key) { return first.count(key); }
		bool registerLive(threadAndRegister reg) { return second.count(reg); }
		bool assertionLive(IRExpr *assertion) {
			class _ : public IRExprTransformer {
				LivenessEntry *_this;

				IRExpr *transformIex(IRExpr::Get *g) {
					if (_this->registerLive(threadAndRegister(*g)))
						res = true;
					return IRExprTransformer::transformIex(g);
				}
				IRExpr *transformIex(IRExpr::RdTmp *g) {
					if (_this->registerLive(threadAndRegister(*g)))
						res = true;
					return IRExprTransformer::transformIex(g);
				}
				IRExpr *transformIex(IRExpr::Binder *g) {
					if (_this->binderLive(g->binder))
						res = true;
					return IRExprTransformer::transformIex(g);
				}
			public:
				bool res;
				_(LivenessEntry *__this)
					: _this(__this), res(false)
				{}
			} t(this);
			t.transformIRExpr(assertion);
			return t.res;
		}
	};
};

class RewriteBindersTransformer : public IRExprTransformer {
public:
	int key;
	IRExpr *val;
	RewriteBindersTransformer(int _key, IRExpr *_val)
		: key(_key), val(_val)
	{}
	IRExpr *transformIex(IRExpr::Binder *e) {
		if (e->binder == key)
			return val;
		return IRExprTransformer::transformIex(e);
	}
};
class RewriteBinderToLoadTransformer : public IRExprTransformer {
public:
	int key;
	ThreadRip rip;
	IRExpr *addr;
	IRExpr *val;
	RewriteBinderToLoadTransformer(int _key, ThreadRip _rip, IRExpr *_addr)
		: key(_key), rip(_rip), addr(_addr), val(NULL)
	{}
	IRExpr *transformIex(IRExpr::Binder *e) {
		if (e->binder == key) {
			if (!val)
				val = IRExpr_Load(false, Iend_LE, Ity_I64, addr, rip);
			return val;
		}
		return IRExprTransformer::transformIex(e);
	}
};
void
applySideEffectToFreeVariables(FreeVariableMap &fvm, StateMachineSideEffect *e, bool *done_something)
{
	bool b;
	if (!done_something) done_something = &b;
	switch (e->type) {
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *c = (StateMachineSideEffectLoad *)e;
		RewriteBinderToLoadTransformer t(c->key, c->rip, c->addr);
		fvm.applyTransformation(t, done_something);
		return;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *c = (StateMachineSideEffectCopy *)e;
		RewriteBindersTransformer t(c->key, c->value);
		fvm.applyTransformation(t, done_something);
		return;
	}
	case StateMachineSideEffect::Store:
	case StateMachineSideEffect::Unreached:
	case StateMachineSideEffect::AssertFalse:
		return;
	case StateMachineSideEffect::Put:
		/* It might appear that we should
		   rewrite the free variables here as
		   well.  We don't, though, because
		   there will always be a free
		   variable for any mentioned
		   register, with any other free
		   variable expressed in terms of that
		   one, and rewriting that one free
		   variable is just a bad idea. */
		return;
	}
	abort();
}

/* Simple dead code elimination: find binders and registers which are
   never accessed after being set and eliminate them. */
static StateMachine *
deadCodeElimination(StateMachine *sm, bool *done_something)
{
	typedef __offline_analysis_dead_code::LivenessEntry LivenessEntry;

	std::set<StateMachineState *> allStates;
	findAllStates(sm, allStates);

	class LivenessMap : public std::map<StateMachineState *, LivenessEntry> {
		void buildResForEdge(LivenessEntry &out, StateMachineEdge *edge)
		{
			out = (*this)[edge->target];
			for (auto it = edge->sideEffects.rbegin();
			     it != edge->sideEffects.rend();
			     it++)
				out.useSideEffect(*it);
		}

		void updateState(StateMachineState *sm, bool *progress)
		{
			LivenessEntry &outputSlot( (*this)[sm] );
			LivenessEntry res;
			if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
				buildResForEdge(res, smp->target);
			} else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm)) {
				buildResForEdge(res, smb->trueTarget);
				LivenessEntry res_false;
				buildResForEdge(res_false, smb->falseTarget);
				res.merge(res_false);
				res.useExpression(smb->condition);
			} else if (StateMachineStub *sms = dynamic_cast<StateMachineStub *>(sm)) {
				res.useExpression(sms->target);
			} else if (dynamic_cast<StateMachineTerminal *>(sm)) {
				/* Nothing needed */
			} else {
				abort();
			}
			if (outputSlot != res) {
				*progress = true;
				outputSlot = res;
			}
		}

	public:
		LivenessMap(StateMachine *sm, std::set<StateMachineState *> &allStates) {
			bool progress;
			do {
				progress = false;
				for (auto it = allStates.begin();
				     it != allStates.end();
				     it++)
					updateState(*it, &progress);
			} while (progress);
		}
	} livenessMap(sm, allStates);

	class _ {
		LivenessMap &livenessMap;
		bool *done_something;
		FreeVariableMap &fvm;

		void doit(StateMachineEdge *edge, FreeVariableMap &fvm) {
			LivenessEntry alive = livenessMap[edge->target];
			/* Surprise! vector::erase doesn't work with a
			   reverse_iterator, so use a raw index. */
			for (int x = edge->sideEffects.size() - 1;
			     x >= 0;
			     x--) {
				StateMachineSideEffect *newEffect = NULL;
				StateMachineSideEffect *e = edge->sideEffects[x];
				bool dead = false;
				switch (e->type) {
				case StateMachineSideEffect::Load: {
					StateMachineSideEffectLoad *smsel =
						(StateMachineSideEffectLoad *)e;
					if (!alive.binderLive(smsel->key))
						newEffect = new StateMachineSideEffectAssertFalse(
							IRExpr_Unop(Iop_BadPtr, smsel->addr));
					break;
				}
				case StateMachineSideEffect::Store:
				case StateMachineSideEffect::Unreached:
					break;
				case StateMachineSideEffect::AssertFalse: {
					StateMachineSideEffectAssertFalse *a =
						(StateMachineSideEffectAssertFalse *)e;
					if (dynamic_cast<StateMachineTerminal *>(edge->target) ||
					    !alive.assertionLive(a->value))
						dead = true;
					break;
				}
				case StateMachineSideEffect::Put: {
					StateMachineSideEffectPut *smsep =
						(StateMachineSideEffectPut *)e;
					dead = !alive.registerLive(threadAndRegister(*smsep));
					break;
				}
				case StateMachineSideEffect::Copy: {
					StateMachineSideEffectCopy *smsec =
						(StateMachineSideEffectCopy *)e;
					dead = !alive.binderLive(smsec->key);
					break;
				}
				}

				if (dead) {
					*done_something = true;
					applySideEffectToFreeVariables(fvm, e);
					edge->sideEffects.erase(edge->sideEffects.begin() + x);
				} else if (newEffect) {
					*done_something = true;
					applySideEffectToFreeVariables(fvm, e);
					edge->sideEffects[x] = newEffect;
					alive.useSideEffect(newEffect);
				} else {
					alive.useSideEffect(e);
				}
			}
		}
	public:
		void operator()(StateMachineState *state) {
			if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(state)) {
				doit(smp->target, fvm);
			} else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(state)) {
				doit(smb->trueTarget, fvm);
				doit(smb->falseTarget, fvm);
			} else if (dynamic_cast<StateMachineTerminal *>(state)) {
				/* Nothing needed */
			} else {
				abort();
			}			
		}

		_(LivenessMap &_livenessMap, bool *_done_something, FreeVariableMap &_fvm)
			: livenessMap(_livenessMap), done_something(_done_something), fvm(_fvm)
		{}
	} eliminateDeadCode(livenessMap, done_something, sm->freeVariables);

	for (auto it = allStates.begin();
	     it != allStates.end();
	     it++)
		eliminateDeadCode(*it);

	return sm;
}

StateMachine *
optimiseStateMachine(StateMachine *sm,
		     const AllowableOptimisations &opt,
		     Oracle *oracle,
		     bool noExtendContext)
{
	__set_profiling(optimiseStateMachine);
	const Oracle::RegisterAliasingConfiguration &alias(oracle->getAliasingConfigurationForRip(sm->origin));
	bool done_something;
	do {
		if (TIMEOUT)
			return sm;
		done_something = false;
		sm = internStateMachine(sm);
		sm = sm->optimise(opt, oracle, &done_something);
		removeRedundantStores(sm, oracle, &done_something, opt);
		sm = availExpressionAnalysis(sm, opt, alias, oracle, &done_something);
		sm = deadCodeElimination(sm, &done_something);
		sm = sm->optimise(opt, oracle, &done_something);
		sm = bisimilarityReduction(sm, opt);
		if (noExtendContext) {
			sm->root->assertAcyclic();
			sm = introduceFreeVariables(sm, alias, opt, oracle, &done_something);
			sm = introduceFreeVariablesForRegisters(sm, &done_something);
			sm = optimiseFreeVariables(sm, &done_something);
			sm = canonicaliseRbp(sm, oracle, &done_something);
			sm->root->assertAcyclic();
		}
		sm = sm->optimise(opt, oracle, &done_something);
	} while (done_something);
	return sm;
}

static void
getConflictingStoreClusters(StateMachine *sm, Oracle *oracle, std::set<InstructionSet> &conflictClusters)
{
	std::set<unsigned long> potentiallyConflictingStores;
	std::set<StateMachineSideEffectLoad *> allLoads;
	findAllLoads(sm, allLoads);
	if (allLoads.size() == 0) {
		fprintf(_logfile, "\t\tNo loads left in store machine?\n");
		return;
	}
	for (std::set<StateMachineSideEffectLoad *>::iterator it = allLoads.begin();
	     it != allLoads.end();
	     it++) {
		oracle->findConflictingStores(*it, potentiallyConflictingStores);
	}

	oracle->clusterRips(potentiallyConflictingStores, conflictClusters);
	if (conflictClusters.size() == 0)
		assert(potentiallyConflictingStores.size() == 0);
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
		  instructions(new RangeSet<&ir_heap>()),
		  calls(new gc_heap_map<unsigned long, CallGraphEntry, &ir_heap>::type()),
		  depth(_depth)
	{}
	unsigned long headRip;
	bool isRealHead; /* Head is derived from a call instruction,
			    as opposed to one of the exploration
			    roots. */

	/* Pair of call instruction and callee address */
	gc_pair_ulong_set_t *callees;
	RangeSet<&ir_heap> *instructions;

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
			       RangeTree<CallGraphEntry, &ir_heap> *instrsToCGEntries,
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

		if (TIMEOUT)
			return NULL;

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
	RangeTree<CallGraphEntry, &ir_heap> *instrsToCGEntries = new RangeTree<CallGraphEntry, &ir_heap>();
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
		if (!cge) {
			fprintf(_logfile, "%s failed\n", __func__);
			return NULL;
		}
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
					fprintf(_logfile, "%lx was a pseudo-root; purge.\n", h);
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
			if (!cge) {
				fprintf(_logfile, "%s failed on line %d\n", __func__, __LINE__);
				return NULL;
			}
			for (gc_pair_ulong_set_t::iterator it = cge->callees->begin();
			     it != cge->callees->end();
			     it++)
				unexploredRealHeads.insert(std::pair<unsigned long, int>(it.key().second, depth_h + 1));
			assert(instrsToCGEntries->get(h) == cge);
		}
	}

	/* Build a set of all of the CGEs which still exist */
	std::set<CallGraphEntry *> allCGEs;
	for (RangeTree<CallGraphEntry, &ir_heap>::iterator it = instrsToCGEntries->begin();
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
		if (!i) {
			fprintf(_logfile, "Failed to build CG entries for every instruction in %s\n", __func__);
			return NULL;
		}
		interesting.insert(i);
	}
	/* Tarski iteration: anything which calls an interesting
	   function is itself interesting. */
	bool done_something;
	do {
		done_something = false;
		if (TIMEOUT)
			return NULL;
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
	for (RangeTree<CallGraphEntry, &ir_heap>::iterator it = instrsToCGEntries->begin();
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
	for (RangeSet<&ir_heap>::iterator it = root->instructions->begin();
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
	bool on_stack(unsigned long rtrn) {
		for (unsigned x = 0; x < callStack.size(); x++)
			if (rtrn == callStack[x])
				return true;
		return false;
	}
	bool operator==(const StackRip &r) const {
		if (valid) {
			return r.valid && rip == r.rip && callStack == r.callStack;
		} else {
			return !r.valid;
		}
	}
};

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
	RangeTree<CallGraphEntry, &ir_heap> *ripToCFGNode = new RangeTree<CallGraphEntry, &ir_heap>();
	toExplore.push(root);
	while (!toExplore.empty()) {
		CallGraphEntry *cge = toExplore.front();
		toExplore.pop();
		if (explored.count(cge))
			continue;
		explored.insert(cge);
		for (RangeSet<&ir_heap>::iterator it = cge->instructions->begin();
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
	std::map<StackRip, std::pair<CFGNode<StackRip> *, int> > builtSoFar;
	std::queue<std::pair<StackRip, int> > needed;

	needed.push(std::pair<StackRip, int>(StackRip(root->headRip), 100));
	while (!needed.empty()) {
		StackRip &r(needed.front().first);
		int depth = needed.front().second;
		if (depth == 0 ||
		    (builtSoFar.count(r) && builtSoFar[r].second >= depth) ||
		    ripToCFGNode->get(r.rip) == NULL) {
			needed.pop();
			continue;
		}
		CFGNode<StackRip> *work = new CFGNode<StackRip>(r);
		builtSoFar[r] = std::pair<CFGNode<StackRip> *, int>(work, depth);
		IRSB *irsb;
		try {
			irsb = as->getIRSBForAddress(-1, r.rip);
		} catch (BadMemoryException &e) {
			irsb = NULL;
		}
		if (!irsb)
			continue; /* Just give up on this bit */

		int x;
		for (x = 1; x < irsb->stmts_used; x++) {
			if (irsb->stmts[x]->tag == Ist_IMark) {
				work->fallThroughRip = r.jump(irsb->stmts[x]->Ist.IMark.addr);
				break;
			}
			if (irsb->stmts[x]->tag == Ist_Exit) {
				if (work->branchRip.valid) {
					assert(work->branchRip == r.jump(irsb->stmts[x]->Ist.Exit.dst->Ico.U64));
				} else {
					work->branchRip = r.jump(irsb->stmts[x]->Ist.Exit.dst->Ico.U64);
				}
				assert(work->branchRip.valid);
				needed.push(std::pair<StackRip, int>(work->branchRip, depth - 1));
			}
		}
		if (x == irsb->stmts_used) {
			if (irsb->jumpkind == Ijk_Call) {
				unsigned long follower = extract_call_follower(irsb);
				if (ripToCFGNode->get(r.rip)->calls->hasKey(r.rip) &&
				    !r.on_stack(follower)) {
					/* We should inline this call. */
					work->fallThroughRip = r.call(
						ripToCFGNode->get(r.rip)->calls->get(r.rip)->headRip,
						follower);
				} else {
					/* Skip over this call. */
					work->fallThroughRip = r.jump(follower);
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
			needed.push(std::pair<StackRip, int>(work->fallThroughRip, depth - 1));
	}

	/* We have now built all of the needed CFG nodes.  Resolve
	 * references. */
	for (std::map<StackRip, std::pair<CFGNode<StackRip> *, int> >::iterator it = builtSoFar.begin();
	     it != builtSoFar.end();
	     it++) {
		assert(it->second.first);
		if (it->second.first->fallThroughRip.valid && builtSoFar.count(it->second.first->fallThroughRip))
			it->second.first->fallThrough = builtSoFar[it->second.first->fallThroughRip].first;
		if (it->second.first->branchRip.valid && builtSoFar.count(it->second.first->branchRip))
			it->second.first->branch = builtSoFar[it->second.first->branchRip].first;
	}

	/* All done */
	CFGNode<StackRip> *res = builtSoFar[StackRip(root->headRip)].first;
	assert(res != NULL);
	return res;
}

static StateMachine *
CFGtoStoreMachine(unsigned tid, Oracle *oracle, CFGNode<StackRip> *cfg)
{
	class : public abstract_map<StackRip, StateMachineState *> {
	public:
		std::map<StackRip, StateMachineState *> impl;
		bool hasKey(const StackRip &k) {
			return impl.count(k) != 0;
		}
		StateMachineState *get(const StackRip &k) {
			return impl[k];
		}
		void set(const StackRip &k, StateMachineState *const &v) {
			impl[k] = v;
		}
	} state;
	return CFGtoCrashReason<StackRip>(tid, cfg, state, StateMachineCrash::get(), oracle);
}

static bool
determineWhetherStoreMachineCanCrash(VexPtr<StateMachine, &ir_heap> &storeMachine,
				     VexPtr<StateMachine, &ir_heap> &probeMachine,
				     VexPtr<Oracle> &oracle,
				     VexPtr<IRExpr, &ir_heap> assumption,
				     const AllowableOptimisations &opt,
				     GarbageCollectionToken token,
				     IRExpr **assumptionOut,
				     StateMachine **newStoreMachine)
{
	__set_profiling(determineWhetherStoreMachineCanCrash);
	/* Specialise the state machine down so that we only consider
	   the interesting stores, and introduce free variables as
	   appropriate. */
	VexPtr<StateMachine, &ir_heap> sm;
	sm = optimiseStateMachine(storeMachine, opt, oracle, true);

	if (dynamic_cast<StateMachineUnreached *>(sm->root)) {
		/* This store machine is unusable, probably because we
		 * don't have the machine code for the relevant
		 * library */
		fprintf(_logfile, "\t\tStore machine is unusable\n");
		return false;
	}

	fprintf(_logfile, "\t\tStore machine:\n");
	printStateMachine(sm, _logfile);

	assumption = writeMachineCrashConstraint(sm, assumption, oracle, opt, token);
	if (!assumption) {
		fprintf(_logfile, "\t\tCannot derive write machine survival constraint\n");
		return false;
	}
	fprintf(_logfile, "\t\tWrite machine survival constraint: ");
	ppIRExpr(assumption, _logfile);
	fprintf(_logfile, "\n");

	assumption = writeMachineSuitabilityConstraint(probeMachine, sm, assumption, oracle, opt, token);
	if (!assumption) {
		fprintf(_logfile, "\t\tCannot derive suitability constraint\n");
		return false;
	}
	fprintf(_logfile, "\t\tSuitability constraint: ");
	ppIRExpr(assumption, _logfile);
	fprintf(_logfile, "\n");

	/* Now try running that in parallel with the probe machine,
	   and see if it might lead to a crash. */
	bool mightSurvive;
	bool mightCrash;
	if (!evalCrossProductMachine(probeMachine,
				     sm,
				     oracle,
				     assumption,
				     opt,
				     &mightSurvive,
				     &mightCrash,
				     token)) {
		fprintf(_logfile, "Failed to run cross product machine\n");
		return false;
	}
	fprintf(_logfile,
		"\t\tRun in parallel with the probe machine, might survive %d, might crash %d\n",
		mightSurvive, mightCrash);
	
	/* We know that mightSurvive is true when the load machine is
	 * run atomically, so if mightSurvive is now false then that
	 * means that evalCrossProductMachine didn't consider that
	 * case, which is a bug. */
	if (!mightSurvive) {
		assert(_timed_out);
		return false;
	}

	if (!mightCrash) {
		fprintf(_logfile,
			"\t\tDefinitely cannot crash\n");
		return false;
	}

	if (assumptionOut)
		*assumptionOut = assumption;
	if (newStoreMachine)
		*newStoreMachine = sm;

	return true;
}

static StateMachine *
expandStateMachineToFunctionHead(VexPtr<StateMachine, &ir_heap> sm,
				 VexPtr<Oracle> &oracle,
				 AllowableOptimisations &opt,
				 GarbageCollectionToken token)
{
	__set_profiling(expandStateMachineToFunctionHead);
	assert(sm->freeVariables.empty());
	std::vector<unsigned long> previousInstructions;
	oracle->findPreviousInstructions(previousInstructions, sm->origin);
	if (previousInstructions.size() == 0) {
		/* Lacking any better ideas... */
		fprintf(_logfile, "cannot expand store machine...\n");
		return sm;
	}

	VexPtr<InferredInformation, &ir_heap> ii(new InferredInformation());
	ii->set(sm->origin, sm->root);

	InstructionSet interesting;
	interesting.rips.insert(sm->origin);

	std::set<unsigned long> terminalFunctions;

	VexPtr<StateMachine, &ir_heap> cr;

	for (std::vector<unsigned long>::iterator it = previousInstructions.begin();
	     !TIMEOUT && it != previousInstructions.end();
	     it++) {
		LibVEX_maybe_gc(token);

		VexPtr<CFGNode<unsigned long>, &ir_heap> cfg(
			buildCFGForRipSet(oracle->ms->addressSpace,
					  *it,
					  terminalFunctions,
					  oracle,
					  100));
		trimCFG(cfg.get(), interesting, INT_MAX, false);
		breakCycles(cfg.get());

		iiCrashReasons _(ii);
		cr = CFGtoCrashReason<unsigned long>(sm->tid,
						     cfg,
						     _,
						     StateMachineNoCrash::get(),
						     oracle);
		if (!cr) {
			fprintf(_logfile, "\tCannot build crash reason from CFG\n");
			return NULL;
		}

		cr = optimiseStateMachine(cr,
					  opt,
					  oracle,
					  false);
		cr->selectSingleCrashingPath();
		cr = optimiseStateMachine(cr,
					  opt,
					  oracle,
					  false);
	}
	if (TIMEOUT)
		return NULL;
	return cr;
}

static bool
considerStoreCFG(VexPtr<CFGNode<StackRip>, &ir_heap> cfg,
		 VexPtr<AddressSpace> &as,
		 VexPtr<Oracle> &oracle,
		 VexPtr<IRExpr, &ir_heap> assumption,
		 VexPtr<StateMachine, &ir_heap> &probeMachine,
		 VexPtr<CrashSummary, &ir_heap> &summary,
		 const InstructionSet &is,
		 bool needRemoteMacroSections,
		 unsigned tid,
		 GarbageCollectionToken token)
{
	__set_profiling(considerStoreCFG);
	VexPtr<StateMachine, &ir_heap> sm(CFGtoStoreMachine(tid, oracle.get(), cfg.get()));
	if (!sm) {
		fprintf(_logfile, "Cannot build store machine!\n");
		return true;
	}

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.enableassumeNoInterferingStores();
	opt.interestingStores = is.rips;
	opt.haveInterestingStoresSet = true;

	if (!determineWhetherStoreMachineCanCrash(sm, probeMachine, oracle, assumption, opt, token, NULL, NULL))
		return false;

	/* If it might crash with that machine, try expanding it to
	   include a bit more context and see if it still goes. */
	sm = expandStateMachineToFunctionHead(sm, oracle, opt, token);
	if (!sm) {
		fprintf(_logfile, "\t\tCannot expand store machine!\n");
		return true;
	}

	opt = opt.disablefreeVariablesMightAccessStack();

	fprintf(_logfile, "\t\tExpanded store machine:\n");
	printStateMachine(sm, _logfile);

	IRExpr *_newAssumption;
	StateMachine *_sm;
	if (!determineWhetherStoreMachineCanCrash(sm, probeMachine, oracle, assumption, opt, token, &_newAssumption, &_sm)) {
		fprintf(_logfile, "\t\tExpanded store machine cannot crash\n");
		return false;
	}
	sm = _sm;
	VexPtr<IRExpr, &ir_heap> newAssumption(_newAssumption);

	fprintf(_logfile, "\t\tExpanded assumption: ");
	ppIRExpr(newAssumption, _logfile);
	fprintf(_logfile, "\n");

	/* Okay, the expanded machine crashes.  That means we have to
	 * generate a fix. */
	CrashSummary::StoreMachineData *smd = new CrashSummary::StoreMachineData(sm, newAssumption);
	if (needRemoteMacroSections) {
		VexPtr<remoteMacroSectionsT, &ir_heap> remoteMacroSections(new remoteMacroSectionsT);
		if (!findRemoteMacroSections(probeMachine, sm, newAssumption, oracle, opt, remoteMacroSections, token)) {
			fprintf(_logfile, "\t\tChose a bad write machine...\n");
			return true;
		}
		if (!fixSufficient(sm, probeMachine, newAssumption, oracle, opt, remoteMacroSections, token)) {
			fprintf(_logfile, "\t\tHave a fix, but it was insufficient...\n");
			return true;
		}
		for (remoteMacroSectionsT::iterator it = remoteMacroSections->begin();
		     it != remoteMacroSections->end();
		     it++)
			smd->macroSections.push_back(CrashSummary::StoreMachineData::macroSectionT(it->start, it->end));
	}

	summary->storeMachines.push_back(smd);
	return true;
}

static bool
processConflictCluster(VexPtr<AddressSpace> &as,
		       VexPtr<StateMachine, &ir_heap> &sm,
		       VexPtr<Oracle> &oracle,
		       VexPtr<IRExpr, &ir_heap> &survive,
		       const InstructionSet &is,
		       VexPtr<CrashSummary, &ir_heap> &summary,
		       bool needRemoteMacroSections,
		       unsigned tid,
		       GarbageCollectionToken token)
{
	LibVEX_maybe_gc(token);

	if (is.rips.size() == 1 && sm->root->roughLoadCount() == StateMachineState::singleLoad) {
		fprintf(_logfile, "Single store versus single load -> no race possible\n");
		return false;
	}

	VexPtr<CallGraphEntry *, &ir_heap> cgRoots;
	int nr_roots;
	cgRoots = buildCallGraphForRipSet(as, is.rips, &nr_roots);
	if (!cgRoots) {
		fprintf(_logfile, "%s failed\n", __func__);
		return false;
	}
	bool result = false;
	for (int i = 0; !TIMEOUT && i < nr_roots; i++) {
		VexPtr<CFGNode<StackRip>, &ir_heap> storeCFG;
		storeCFG = buildCFGForCallGraph(as, cgRoots[i]);
		trimCFG(storeCFG.get(), is, 20, false);
		breakCycles(storeCFG.get());

		result |= considerStoreCFG(storeCFG, as, oracle,
					   survive, sm, summary, is,
					   needRemoteMacroSections,
					   tid, token);
	}
	return result;
}

StateMachine *
buildProbeMachine(std::vector<unsigned long> &previousInstructions,
		  VexPtr<InferredInformation, &ir_heap> &ii,
		  VexPtr<Oracle> &oracle,
		  unsigned long interestingRip,
		  ThreadId tid,
		  GarbageCollectionToken token)
{
	__set_profiling(buildProbeMachine);

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.enableignoreSideEffects();

	StateMachine *sm = NULL;

	for (std::vector<unsigned long>::iterator it = previousInstructions.begin();
	     !TIMEOUT && it != previousInstructions.end();
	     it++) {
		fprintf(_logfile, "Backtrack to %lx...\n", *it);
		LibVEX_maybe_gc(token);

		std::set<unsigned long> terminalFunctions;
		terminalFunctions.insert(0x757bf0);
		VexPtr<CFGNode<unsigned long>, &ir_heap> cfg(
			buildCFGForRipSet(oracle->ms->addressSpace,
					  *it,
					  terminalFunctions,
					  oracle,
					  100));
		InstructionSet interesting;
		interesting.rips.insert(interestingRip);
		trimCFG(cfg.get(), interesting, INT_MAX, true);

		iiCrashReasons _(ii);
		VexPtr<StateMachine, &ir_heap> cr(
			CFGtoCrashReason<unsigned long>(tid._tid(), cfg, _,
							StateMachineNoCrash::get(),
							oracle));
		if (!cr) {
			fprintf(_logfile, "\tCannot build crash reason from CFG\n");
			return NULL;
		}

		cr = optimiseStateMachine(cr,
					  opt,
					  oracle,
					  false);
		cr->selectSingleCrashingPath();
		cr = optimiseStateMachine(cr,
					  opt,
					  oracle,
					  false);

		if (dynamic_cast<StateMachineNoCrash *>(cr->root)) {
			/* Once you've reduced the machine to
			   definitely-doesn't-crash there's not much
			   point in looking any further, so stop. */
			fprintf(_logfile, "Machine definitely survives -> stop now\n");
			return NULL;
		}
		sm = cr;
	}
	if (TIMEOUT)
		return NULL;

	if (sm)
		sm = optimiseStateMachine(sm,
					  opt.disablefreeVariablesMightAccessStack(),
					  oracle,
					  true);

	return sm;
}

CrashSummary *
diagnoseCrash(VexPtr<StateMachine, &ir_heap> &probeMachine,
	      VexPtr<Oracle> &oracle,
	      VexPtr<MachineState> &ms,
	      bool needRemoteMacroSections,
	      GarbageCollectionToken token)
{
	__set_profiling(diagnoseCrash);
	fprintf(_logfile, "Probe machine:\n");
	printStateMachine(probeMachine, _logfile);
	fprintf(_logfile, "\n");

	std::set<InstructionSet> conflictClusters;
	getConflictingStoreClusters(probeMachine, oracle, conflictClusters);

	if (conflictClusters.size() == 0) {
		fprintf(_logfile, "\t\tNo available conflicting stores?\n");
		return NULL;
	}

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.enableignoreSideEffects()
		.disablefreeVariablesMightAccessStack();
	VexPtr<IRExpr, &ir_heap> survive(
		survivalConstraintIfExecutedAtomically(probeMachine, oracle, opt, token));
	if (!survive) {
		fprintf(_logfile, "\tTimed out computing survival constraint\n");
		return NULL;
	}
	survive = simplifyIRExpr(survive, opt);

	fprintf(_logfile, "\tComputed survival constraint ");
	ppIRExpr(survive, _logfile);
	fprintf(_logfile, "\n");

	/* Quick check that that vaguely worked.  If this reports
	   mightCrash == true then that probably means that the
	   theorem prover bits need more work.  If it reports
	   mightSurvive == false then the program is doomed and it's
	   not possible to fix it from this point. */
	bool mightSurvive, mightCrash;
	if (!evalMachineUnderAssumption(probeMachine, oracle, survive, opt, &mightSurvive, &mightCrash, token)) {
		fprintf(_logfile, "Timed out sanity checking machine survival constraint\n");
		return NULL;
	}
	if (TIMEOUT)
		return NULL;
	if (!mightSurvive) {
		fprintf(_logfile, "\tCan never survive...\n");
		return NULL;
	}
	if (mightCrash) {
		fprintf(_logfile, "WARNING: Cannot determine any condition which will definitely ensure that we don't crash, even when executed atomically -> probably won't be able to fix this\n");
		printf("WARNING: Cannot determine any condition which will definitely ensure that we don't crash, even when executed atomically -> probably won't be able to fix this\n");
		return NULL;
	}

	VexPtr<CrashSummary, &ir_heap> summary(new CrashSummary(probeMachine));

	bool foundRace = false;
	unsigned cntr = 0;
	for (std::set<InstructionSet>::iterator it = conflictClusters.begin();
	     !TIMEOUT && it != conflictClusters.end();
	     it++) {
		fprintf(_logfile, "\tCluster:");
		for (std::set<unsigned long>::iterator it2 = it->rips.begin();
		     it2 != it->rips.end();
		     it2++)
			fprintf(_logfile, " %lx", *it2);
		fprintf(_logfile, "\n");
		VexPtr<AddressSpace> as(ms->addressSpace);
		cntr++;
		foundRace |= processConflictCluster(as, probeMachine, oracle, survive, *it, summary, needRemoteMacroSections,
						    STORING_THREAD + cntr, token);
	}
	if (TIMEOUT)
		return NULL;

	if (!foundRace) {
		fprintf(_logfile, "\t\tCouldn't find any relevant-looking races\n");
		return NULL;
	}

	fprintf(_logfile, "\t\tFound relevant-looking races\n");

	if (summary->storeMachines.size() == 0) {
		fprintf(_logfile, "\t\t...but no store machines?\n");
		return NULL;
	}

	return summary;
}
			    
template <typename t> void
printCFG(const CFGNode<t> *cfg, FILE *f)
{
	std::vector<const CFGNode<t> *> pending;
	std::set<const CFGNode<t> *> done;

	pending.push_back(cfg);
	while (!pending.empty()) {
		cfg = pending.back();
		pending.pop_back();
		if (done.count(cfg))
			continue;
		fprintf(f, "%p: ", cfg);
		cfg->prettyPrint(f);
		fprintf(f, "\n");
		if (cfg->fallThrough)
			pending.push_back(cfg->fallThrough);
		if (cfg->branch)
			pending.push_back(cfg->branch);
		done.insert(cfg);
	}
}
/* Make it visible to the debugger. */
void __printCFG(const CFGNode<StackRip> *cfg) { printCFG(cfg, stdout); }

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
static CFGNode<unsigned long> *
buildCFGForRipSet(AddressSpace *as,
		  unsigned long start,
		  const std::set<unsigned long> &terminalFunctions,
		  Oracle *oracle,
		  unsigned max_depth)
{
	std::map<unsigned long, std::pair<CFGNode<unsigned long> *, unsigned> > builtSoFar;
	std::vector<std::pair<unsigned long, unsigned> > needed;
	unsigned depth;
	unsigned long rip;

	/* Mild hack to make some corned cases easier. */
	builtSoFar[0] = std::pair<CFGNode<unsigned long> *, unsigned>((CFGNode<unsigned long> *)NULL, max_depth);

	/* Step one: discover all of the instructions which we're
	 * going to need. */
	needed.push_back(std::pair<unsigned long, unsigned>(start, max_depth));
	while (!needed.empty()) {
		rip = needed.back().first;
		depth = needed.back().second;
		needed.pop_back();
		if (!depth ||
		    (builtSoFar.count(rip) && builtSoFar[rip].second >= depth))
			continue;
		IRSB *irsb = as->getIRSBForAddress(-1, rip);
		CFGNode<unsigned long> *work = new CFGNode<unsigned long>(rip);
		int x;
		for (x = 1; x < irsb->stmts_used; x++) {
			if (irsb->stmts[x]->tag == Ist_IMark) {
				work->fallThroughRip = irsb->stmts[x]->Ist.IMark.addr;
				needed.push_back(std::pair<unsigned long, unsigned>(work->fallThroughRip, depth - 1));
				break;
			}
			if (irsb->stmts[x]->tag == Ist_Exit) {
				assert(work->branch == 0);
				work->branchRip = irsb->stmts[x]->Ist.Exit.dst->Ico.U64;
				needed.push_back(std::pair<unsigned long, unsigned>(work->branchRip, depth - 1));
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
					needed.push_back(std::pair<unsigned long, unsigned>(work->fallThroughRip, depth - 1));
			} else if (irsb->jumpkind == Ijk_Ret) {
				work->accepting = true;
			} else {
				/* Don't currently try to trace across indirect branches. */
				if (irsb->next->tag == Iex_Const) {
					work->fallThroughRip = irsb->next->Iex.Const.con->Ico.U64;
					needed.push_back(std::pair<unsigned long, unsigned>(work->fallThroughRip, depth - 1));
				}
			}
		}
		builtSoFar[rip] = std::pair<CFGNode<unsigned long> *, unsigned>(work, depth);
	}

	/* Now we have a CFG node for every needed instruction.  Go
	   through and resolve exit branches. */
	for (std::map<unsigned long, std::pair<CFGNode<unsigned long> *, unsigned> >::iterator it = builtSoFar.begin();
	     it != builtSoFar.end();
	     it++) {
		if (it->second.first) {
			it->second.first->fallThrough = builtSoFar[it->second.first->fallThroughRip].first;
			it->second.first->branch = builtSoFar[it->second.first->branchRip].first;
		}
	}

	return builtSoFar[start].first;
}

template <typename t> StateMachine *
CFGtoCrashReason(unsigned tid,
		 CFGNode<t> *cfg,
		 abstract_map<t, StateMachineState *> &crashReasons,
		 StateMachineState *escapeState,
		 Oracle *oracle)
{
	class State {
		typedef std::pair<StateMachineState **, CFGNode<t> *> reloc_t;
		std::vector<CFGNode<t> *> pending;
		std::vector<reloc_t> relocs;
		abstract_map<t, StateMachineState *> &crashReasons;
	public:
		std::map<CFGNode<t> *, StateMachineState *> cfgToState;

		CFGNode<t> *nextNode() {
			while (1) {
				if (pending.empty()) {
					std::vector<reloc_t> newRelocs;
					for (auto it = relocs.begin(); it != relocs.end(); it++) {
						if (cfgToState.count(it->second)) {
							*it->first = cfgToState[it->second];
						} else if (crashReasons.hasKey(it->second->my_rip)) {
							*it->first = crashReasons.get(it->second->my_rip);
						} else {
							newRelocs.push_back(*it);
							pending.push_back(it->second);
						}
					}
					relocs = newRelocs;
					if (pending.empty())
						return NULL;
				}
				CFGNode<t> *res = pending.back();
				pending.pop_back();
				if (cfgToState.count(res))
					continue;
				return res;
			}
		}
		void addReloc(StateMachineState **p, CFGNode<t> *c)
		{
			*p = NULL;
			relocs.push_back(reloc_t(p, c));
		}

		State(abstract_map<t, StateMachineState *> &_crashReasons)
			: crashReasons(_crashReasons)
		{}
	} state(crashReasons);

	class FetchIrsb {
	public:
		AddressSpace *as;
		unsigned tid;
		FetchIrsb(AddressSpace *_as, unsigned _tid)
			: as(_as), tid(_tid)
		{}
		IRSB *operator()(t rip) {
			try {
				return as->getIRSBForAddress(tid, wrappedRipToRip(rip));
			} catch (BadMemoryException e) {
				return NULL;
			}
		}
	} fetchIrsb(oracle->ms->addressSpace, tid);

	class BuildStateForCfgNode {
		StateMachineEdge *backtrackOneStatement(IRStmt *stmt,
							ThreadRip rip,
							CFGNode<t> *branchTarget,
							StateMachineEdge *edge) {
			StateMachineSideEffect *se = NULL;
			switch (stmt->tag) {
			case Ist_NoOp:
			case Ist_IMark:
			case Ist_AbiHint:
				break;
			case Ist_Put:
				se = new StateMachineSideEffectPut(
					stmt->Ist.Put.offset,
					stmt->Ist.Put.data,
					rip);
				break;
			case Ist_PutI:
				/* Don't know how to handle these */
				abort();
			case Ist_WrTmp:
				se = new StateMachineSideEffectPut(
					-stmt->Ist.WrTmp.tmp - 1,
					stmt->Ist.WrTmp.data,
					rip);
				break;
			case Ist_Store:
				se = new StateMachineSideEffectStore(
					stmt->Ist.Store.addr,
					stmt->Ist.Store.data,
					rip);
				break;
			case Ist_Dirty:
				if (!strcmp(stmt->Ist.Dirty.details->cee->name,
					    "helper_load_8") ||
				    !strcmp(stmt->Ist.Dirty.details->cee->name,
					    "helper_load_16") ||
				    !strcmp(stmt->Ist.Dirty.details->cee->name,
					    "helper_load_64") ||
				    !strcmp(stmt->Ist.Dirty.details->cee->name,
					    "helper_load_32")) {
					StateMachineSideEffectLoad *smsel =
						new StateMachineSideEffectLoad(
							stmt->Ist.Dirty.details->args[0],
							rip);
					se = new StateMachineSideEffectPut(
						-stmt->Ist.Dirty.details->tmp - 1,
						IRExpr_Binder(smsel->key),
						rip);
					edge->prependSideEffect(se);
					se = smsel;
				}  else {
					abort();
				}
				break;
			case Ist_CAS:
				fprintf(_logfile, "Don't know how to backtrack across CAS statements?\n");
				return NULL;
			case Ist_MBE:
				break;
			case Ist_Exit:
				if (branchTarget) {
					StateMachineBifurcate *smb =
						new StateMachineBifurcate(
							rip.rip,
							stmt->Ist.Exit.guard,
							new StateMachineEdge(NULL),
							edge);
					assert(smb->trueTarget);
					state.addReloc(&smb->trueTarget->target, branchTarget);
					edge = new StateMachineEdge(smb);
				} else {
					/* We've decided to ignore this branch */
				}
				break;
			}
			if (se)
				edge->prependSideEffect(se);
			return edge;
		}

		StateMachineState *buildStateForCallInstruction(CFGNode<t> *cfg,
								IRSB *irsb,
								ThreadRip site)
		{
			assert(cfg->fallThrough);
			IRExpr *r;
			if (irsb->next->tag == Iex_Const) {
				unsigned long called_rip = irsb->next->Iex.Const.con->Ico.U64;
				Oracle::LivenessSet live = oracle->liveOnEntryToFunction(called_rip);

				/* We only consider arguments in registers.  This is
				   probably a bug; nevermind. */
				static const int argument_registers[6] = {
					OFFSET_amd64_RDI,
					OFFSET_amd64_RSI,
					OFFSET_amd64_RDX,
					OFFSET_amd64_RCX,
					OFFSET_amd64_R8,
					OFFSET_amd64_R9};

				int nr_args;
				nr_args = 0;
				for (int i = 0; i < 6; i++)
					if (live.isLive(argument_registers[i]))
						nr_args++;
				IRExpr **args = alloc_irexpr_array(nr_args + 1);
				nr_args = 0;
				for (int i = 0; i < 6; i++)
					if (live.isLive(argument_registers[i]))
						args[nr_args++] = IRExpr_Get(argument_registers[i], Ity_I64, site.thread);
				args[nr_args] = NULL;
				r = IRExpr_ClientCall(called_rip, site, args);
			} else {
				r = IRExpr_ClientCallFailed(irsb->next);
			}

			/* Pick up any temporaries calculated during
			 * the call instruction. */
			for (int i = irsb->stmts_used - 1; i >= 0; i--) {
				IRStmt *stmt = irsb->stmts[i];
				/* We ignore statements other than WrTmp if they
				   happen in a call instruction. */
				if (stmt->tag == Ist_WrTmp)
					r = rewriteTemporary(r, stmt->Ist.WrTmp.tmp, stmt->Ist.WrTmp.data);
			}

			StateMachineProxy *smp = new StateMachineProxy(site.rip, (StateMachineState *)NULL);
			assert(smp->target);
			state.addReloc(&smp->target->target, cfg->fallThrough);
			smp->target->prependSideEffect(
				new StateMachineSideEffectPut(
					OFFSET_amd64_RAX,
					r,
					site));
			return smp;
		}
	public:
		unsigned tid;
		State &state;
		StateMachineState *escapeState;
		Oracle *oracle;
		BuildStateForCfgNode(unsigned _tid, State &_state, StateMachineState *_escapeState,
				     Oracle *_oracle)
			: tid(_tid), state(_state), escapeState(_escapeState), oracle(_oracle)
		{}
		StateMachineState *operator()(CFGNode<t> *cfg,
					      IRSB *irsb) {
			if (!cfg->fallThrough && !cfg->branch)
				return escapeState;
			ThreadRip rip(ThreadRip::mk(tid, wrappedRipToRip(cfg->my_rip)));
			int endOfInstr;
			for (endOfInstr = 1;
			     endOfInstr < irsb->stmts_used && irsb->stmts[endOfInstr]->tag != Ist_IMark;
			     endOfInstr++)
				;
			if (endOfInstr == irsb->stmts_used && irsb->jumpkind == Ijk_Call) {
				/* This is a call node, which requires
				 * special handling. */
				return buildStateForCallInstruction(cfg, irsb, rip);
			}
			StateMachineEdge *edge = new StateMachineEdge(NULL);
			if (!cfg->fallThrough) {
				/* We've decided to force this one to take the
				   branch.  Trim the bit of the instruction
				   after the branch. */
				assert(cfg->branch);
				endOfInstr--;
				while (endOfInstr >= 0 && irsb->stmts[endOfInstr]->tag != Ist_Exit)
					endOfInstr--;
				assert(endOfInstr > 0);
				assert(edge);
				state.addReloc(&edge->target, cfg->branch);
			} else {
				assert(edge);
				state.addReloc(&edge->target, cfg->fallThrough);
			}
			for (int i = endOfInstr - 1; i >= 0; i--) {
				edge = backtrackOneStatement(irsb->stmts[i],
							     rip,
							     cfg->branch,
							     edge);
				if (!edge)
					return NULL;
			}
			return new StateMachineProxy(rip.rip, edge);
		}
	} buildStateForCfgNode(tid, state, escapeState, oracle);

	unsigned long original_rip = wrappedRipToRip(cfg->my_rip);
	StateMachineState *root = NULL;
	state.addReloc(&root, cfg);

	while (1) {
		cfg = state.nextNode();
		if (!cfg)
			break;
		if (crashReasons.hasKey(cfg->my_rip)) {
			state.cfgToState[cfg] = crashReasons.get(cfg->my_rip);
		} else {
			StateMachineState *s;
			IRSB *irsb = fetchIrsb(cfg->my_rip);
			if (irsb)
				s = buildStateForCfgNode(cfg, irsb);
			else
				s = StateMachineUnreached::get();
			if (!s)
				return NULL;
			state.cfgToState[cfg] = s;
		}
	}

	FreeVariableMap fv;
	StateMachine *sm = new StateMachine(root, original_rip, fv, tid);
	sm = optimiseStateMachine(sm, AllowableOptimisations::defaultOptimisations, oracle, false);
	crashReasons.set(original_rip, sm->root);
	return sm;
}

remoteMacroSectionsT::iterator::iterator(const remoteMacroSectionsT *_owner, unsigned _idx)
	: idx(_idx), owner(_owner)
{}

bool
remoteMacroSectionsT::iterator::operator!=(const iterator &other) const
{
	assert(other.owner == this->owner);
	return other.idx != this->idx;
}

void
remoteMacroSectionsT::iterator::operator++(int ign)
{
	this->idx++;
}

const remoteMacroSectionsT::iterator::__content *
remoteMacroSectionsT::iterator::operator->() const
{
	this->content.start = this->owner->content[this->idx].first;
	this->content.end = this->owner->content[this->idx].second;
	return &this->content;
}

remoteMacroSectionsT::iterator
remoteMacroSectionsT::begin() const
{
	return iterator(this, 0);
}

remoteMacroSectionsT::iterator
remoteMacroSectionsT::end() const
{
	return iterator(this, content.size());
}

void
remoteMacroSectionsT::insert(StateMachineSideEffectStore *start,
			     StateMachineSideEffectStore *end)
{
	for (contentT::iterator it = content.begin();
	     it != content.end();
	     it++) {
		if (it->first == start && it->second == end)
			return;
	}
	content.push_back(std::pair<StateMachineSideEffectStore *,
			            StateMachineSideEffectStore *>(start, end));
}

void
remoteMacroSectionsT::visit(HeapVisitor &hv)
{
	for (contentT::iterator it = content.begin();
	     it != content.end();
	     it++) {
		hv(it->first);
		hv(it->second);
	}
}
