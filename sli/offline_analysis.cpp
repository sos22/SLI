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
#include "ssa.hpp"
#include "libvex_prof.hpp"

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

class findAllLoadsVisitor : public StateMachineTransformer {
	StateMachineSideEffectLoad *transformOneSideEffect(StateMachineSideEffectLoad *smse, bool *)
	{
		out.insert(smse);
		return smse;
	}
	IRExpr *transformIRExpr(IRExpr *e, bool *)
	{
		return e;
	}
public:
	std::set<StateMachineSideEffectLoad *> &out;
	findAllLoadsVisitor(std::set<StateMachineSideEffectLoad *> &o)
		: out(o)
	{}
};
void
findAllLoads(StateMachine *sm, std::set<StateMachineSideEffectLoad *> &out)
{
	findAllLoadsVisitor v(out);
	v.transform(sm);
}

class findAllEdgesVisitor : public StateMachineTransformer {
	StateMachineEdge *transformOneEdge(StateMachineEdge *x, bool *)
	{
		out.insert(x);
		return NULL;
	}
	StateMachineSideEffect *transformSideEffect(StateMachineSideEffect *, bool *)
	{
		/* This should never be invoked, because we stop the
		   traversal in transformOneEdge. */
		abort();
	}
	IRExpr *transformIRExpr(IRExpr *e, bool *)
	{
		return e;
	}
public:
	std::set<StateMachineEdge *> &out;
	findAllEdgesVisitor(std::set<StateMachineEdge *> &o)
		: out(o)
	{}
};
void
findAllEdges(StateMachine *sm, std::set<StateMachineEdge *> &out)
{
	findAllEdgesVisitor v(out);
	v.transform(sm);
}

class findAllStatesVisitor : public StateMachineTransformer {
	StateMachineState *transformState(StateMachineState *s, bool *)
	{
		out.insert(s);
		return NULL;
	}
	StateMachineEdge *transformOneEdge(StateMachineEdge *e, bool *)
	{
		return NULL;
	}
	void transformFreeVariables(FreeVariableMap *fvm, bool *done_something)
	{
		return;
	}
	IRExpr *transformIRExpr(IRExpr *e, bool *)
	{
		/* We shouldn't get here: transformOneState() stops it
		   looking in state conditions, transformOneEdge()
		   stops it looking in side-effects, and
		   transformFreeVariables() stops it looking in the
		   free variable map, and there shouldn't be anywhere
		   else for free variables to be hiding. */
		abort();
	}
public:
	std::set<StateMachineState *> &out;
	findAllStatesVisitor(std::set<StateMachineState *> &o)
		: out(o)
	{}
};
void
findAllStates(StateMachine *sm, std::set<StateMachineState *> &out)
{
	findAllStatesVisitor v(out);
	v.transform(sm);
}

static void
canonicaliseRbp(StateMachine *sm, OracleInterface *oracle)
{
	long delta;

	if (!oracle->getRbpToRspDelta(sm->origin, &delta)) {
		/* Can't do anything if we don't know the delta */
		return;
	}
	/* Got RBP->RSP delta, want RSP->RBP */
	delta = -delta;
	StateMachineEdge *e = new StateMachineEdge(sm->root);
	e->sideEffects.push_back(
		new StateMachineSideEffectCopy(
			threadAndRegister::reg(sm->tid, OFFSET_amd64_RBP, 0),
			IRExpr_Associative(
				Iop_Add64,
				IRExpr_Get(
					threadAndRegister::reg(sm->tid, OFFSET_amd64_RSP, 0),
					Ity_I64),
				IRExpr_Const(
					IRConst_U64(delta)),
				NULL)));
	sm->root = new StateMachineProxy(sm->origin, e);
}

class BuildFreeVariableMapTransformer : public StateMachineTransformer {
public:
	std::set<threadAndRegister, threadAndRegister::fullCompare> accessedRegisters;
	std::set<threadAndRegister, threadAndRegister::fullCompare> puttedRegisters;
	FreeVariableMap &freeVariables;

	std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> map;

	StateMachineSideEffectCopy *transformOneSideEffect(StateMachineSideEffectCopy *c, bool *done_something)
	{
		puttedRegisters.insert(c->target);
		return StateMachineTransformer::transformOneSideEffect(c, done_something);
	}
	StateMachineSideEffectLoad *transformOneSideEffect(StateMachineSideEffectLoad *l, bool *done_something)
	{
		puttedRegisters.insert(l->target);
		return StateMachineTransformer::transformOneSideEffect(l, done_something);
	}
	IRExpr *transformIex(IRExprGet *what) {
		accessedRegisters.insert(what->reg);
		return StateMachineTransformer::transformIex(what);
	}
	BuildFreeVariableMapTransformer(FreeVariableMap &_freeVariables)
		: freeVariables(_freeVariables)
	{}
	/* It's not really a good idea to introduce more free
	   variables on behalf of an expression which is only used in
	   the free variable map. */
	void transformFreeVariables(FreeVariableMap *fvm, bool *done_something)
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
	std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> &map;
	IntroduceFreeVariablesRegisterTransformer(
		std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> &_map)
		: map(_map)
	{}
	IRExpr *transformIex(IRExprGet *what) {
		if (map.count(what->reg)) {
			IRExprFreeVariable *res = (IRExprFreeVariable *)map[what->reg];
			assert(res->tag == Iex_FreeVariable);
			fvDelta.push_back(std::pair<FreeVariableKey, IRExpr *>(res->key, currentIRExpr()));
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
			sm = optimiseSSA(sm, &done_something);
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
	return getInstructionSize(as, a);
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
				work->fallThroughRip = r.jump(((IRStmtIMark *)irsb->stmts[x])->addr);
				break;
			}
			if (irsb->stmts[x]->tag == Ist_Exit) {
				if (work->branchRip.valid) {
					assert(work->branchRip == r.jump(((IRStmtExit *)irsb->stmts[x])->dst->Ico.U64));
				} else {
					work->branchRip = r.jump(((IRStmtExit *)irsb->stmts[x])->dst->Ico.U64);
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
				work->fallThroughRip = r.jump(((IRExprConst *)irsb->next)->con->Ico.U64);
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
	sm = deSSA(sm);
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
		breakCycles(cr);
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
		.enableassumeNoInterferingStores()
		.setAddressSpace(as);
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
		.enableignoreSideEffects()
		.setAddressSpace(oracle->ms->addressSpace);

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
		breakCycles(cr);
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
				work->fallThroughRip = ((IRStmtIMark *)irsb->stmts[x])->addr;
				needed.push_back(std::pair<unsigned long, unsigned>(work->fallThroughRip, depth - 1));
				break;
			}
			if (irsb->stmts[x]->tag == Ist_Exit) {
				assert(work->branch == 0);
				work->branchRip = ((IRStmtExit *)irsb->stmts[x])->dst->Ico.U64;
				needed.push_back(std::pair<unsigned long, unsigned>(work->branchRip, depth - 1));
			}
		}
		if (x == irsb->stmts_used) {
			if (irsb->jumpkind == Ijk_Call) {
				work->fallThroughRip = extract_call_follower(irsb);
				if (irsb->next->tag == Iex_Const) {
					if (terminalFunctions.count(((IRExprConst *)irsb->next)->con->Ico.U64))
						work->fallThroughRip = ((IRExprConst *)irsb->next)->con->Ico.U64;
					else if (!oracle->functionCanReturn(((IRExprConst *)irsb->next)->con->Ico.U64))
						work->fallThroughRip = 0;
				}
				if (work->fallThroughRip)
					needed.push_back(std::pair<unsigned long, unsigned>(work->fallThroughRip, depth - 1));
			} else if (irsb->jumpkind == Ijk_Ret) {
				work->accepting = true;
			} else {
				/* Don't currently try to trace across indirect branches. */
				if (irsb->next->tag == Iex_Const) {
					work->fallThroughRip = ((IRExprConst *)irsb->next)->con->Ico.U64;
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

static IRExpr *
rewriteTemporary(IRExpr *sm,
		 IRTemp tmp,
		 IRExpr *newval)
{
	class _ : public IRExprTransformer {
		IRTemp tmp;
		IRExpr *to;
	protected:
		IRExpr *transformIex(IRExprGet *what)
		{
			if (what->reg.isTemp() && what->reg.asTemp() == tmp)
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
				se = new StateMachineSideEffectCopy(
					((IRStmtPut *)stmt)->target,
					((IRStmtPut *)stmt)->data);
				break;
			case Ist_PutI:
				/* Don't know how to handle these */
				abort();
			case Ist_Store:
				se = new StateMachineSideEffectStore(
					((IRStmtStore *)stmt)->addr,
					((IRStmtStore *)stmt)->data,
					rip);
				break;
			case Ist_Dirty:
				if (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
					    "helper_load_8") ||
				    !strcmp(((IRStmtDirty *)stmt)->details->cee->name,
					    "helper_load_16") ||
				    !strcmp(((IRStmtDirty *)stmt)->details->cee->name,
					    "helper_load_64") ||
				    !strcmp(((IRStmtDirty *)stmt)->details->cee->name,
					    "helper_load_32")) {
					se = new StateMachineSideEffectLoad(
						((IRStmtDirty *)stmt)->details->tmp,
						((IRStmtDirty *)stmt)->details->args[0],
						rip);
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
							((IRStmtExit *)stmt)->guard,
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
				unsigned long called_rip = ((IRExprConst *)irsb->next)->con->Ico.U64;
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
						args[nr_args++] = IRExpr_Get(argument_registers[i], Ity_I64, site.thread, 0);
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
				if (stmt->tag == Ist_Put) {
					IRStmtPut *p = (IRStmtPut *)stmt;
					if (p->target.isTemp())
						r = rewriteTemporary(r, p->target.asTemp(),
								     p->data);
				}
			}

			StateMachineProxy *smp = new StateMachineProxy(site.rip, (StateMachineState *)NULL);
			assert(smp->target);
			state.addReloc(&smp->target->target, cfg->fallThrough);
			smp->target->prependSideEffect(
				new StateMachineSideEffectCopy(
					threadAndRegister::reg(site.thread, OFFSET_amd64_RAX, 0),
					r));
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
	canonicaliseRbp(sm, oracle);
	sm = optimiseStateMachine(sm, AllowableOptimisations::defaultOptimisations, oracle, false);
	crashReasons.set(original_rip, sm->root);
	sm = convertToSSA(sm);
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
