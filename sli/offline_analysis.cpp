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

#define DEBUG_BUILD_STORE_CFGS 0

class CFGNode : public GarbageCollected<CFGNode, &ir_heap>, public PrettyPrintable {
public:
	VexRip fallThroughRip;
	VexRip branchRip;
	CFGNode *fallThrough;
	CFGNode *branch;

	VexRip my_rip;

	bool accepting;

	CFGNode(const VexRip &rip) : my_rip(rip), accepting(false) {}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%s: %s(%p), %s(%p)",
			my_rip.name(),
			fallThroughRip.name(),
			fallThrough,
			branchRip.name(),
			branch);
	}
	void visit(HeapVisitor &hv) {
		hv(fallThrough);
		hv(branch);
	}
	NAMED_CLASS
};

static void printCFG(const CFGNode *cfg, const char *prefix, FILE *f);
static StateMachine *CFGtoCrashReason(unsigned tid,
				      VexPtr<CFGNode, &ir_heap> &cfg,
				      VexPtr<gc_heap_map<VexRip, StateMachineState, &ir_heap>::type, &ir_heap> &crashReasons,
				      VexPtr<StateMachineState, &ir_heap> &escapeState,
				      AllowableOptimisations &opt,
				      bool simple_calls,
				      VexPtr<Oracle> &oracle,
				      GarbageCollectionToken token);

static CFGNode *buildCFGForRipSet(AddressSpace *as,
					  const VexRip &start,
					  const std::set<VexRip> &terminalFunctions,
					  Oracle *oracle,
					  unsigned max_depth);

static bool instructionIsInteresting(const InstructionSet &i, const VexRip &r);

static void
enumerateCFG(CFGNode *root, std::map<VexRip, CFGNode *> &rips)
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
trimCFG(CFGNode *root, const InstructionSet &interestingAddresses, int max_path_length, bool acceptingAreInteresting)
{
	std::map<VexRip, CFGNode *> uninteresting;
	std::map<VexRip, std::pair<CFGNode *, int> > interesting;
	/* Start on the assumption that everything is uninteresting. */
	enumerateCFG(root, uninteresting);
	/* addresses which are explicitly flagged as interesting are
	   not uninteresting. */
	for (auto it = uninteresting.begin();
	     it != uninteresting.end();
		) {
		if ((acceptingAreInteresting && it->second->accepting) ||
		    instructionIsInteresting(interestingAddresses, it->first)) {
			interesting[it->first] = std::pair<CFGNode *, int>(it->second, max_path_length);
			uninteresting.erase(it++);
		} else {
			it++;
		}
	}

	/* Tarski iteration */
	bool progress;
	do {
		progress = false;
		for (auto it = uninteresting.begin();
		     it != uninteresting.end();
			) {
			CFGNode *n = it->second;
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
				interesting[it->first] = std::pair<CFGNode *, int>(
					it->second, path_length);
				uninteresting.erase(it++);
			}
		}
	} while (progress);

	/* The uninteresting set should now be correct.  Eliminate any
	   edges which go to an uninteresting target. */
	for (auto it = interesting.begin();
	     it != interesting.end();
	     it++) {
		CFGNode *n = it->second.first;
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
static bool
breakCycles(CFGNode *cfg, std::map<CFGNode *, unsigned> &numbering,
	    CFGNode **lastBackEdge, std::set<CFGNode *> &onPath,
	    std::set<CFGNode *> &clean)
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
		CFGNode **p = lastBackEdge;
		if (numbering[cfg->branch] < numbering[cfg])
			p = &cfg->branch;
		if (cfg->branch == cfg)
			cfg->branch = NULL;
		else if (!breakCycles(cfg->branch, numbering, p, onPath, clean))
			return false;
	}
	if (cfg->fallThrough) {
		CFGNode **p = lastBackEdge;
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
static void
breakCycles(CFGNode *cfg)
{
	std::map<CFGNode *, unsigned> numbering;
	std::queue<CFGNode *> queue;
	CFGNode *tmp;

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

	std::set<CFGNode *> visited;
	std::set<CFGNode *> clean;
	while (!breakCycles(cfg, numbering, NULL, visited, clean)) {
		visited.clear();
		clean.clear();
	}
}

template <typename t> static void
findAllTypedSideEffects(StateMachine *sm, std::set<t *> &out)
{
	class _ : public StateMachineTransformer {
		std::set<t *> &out;
		t *transformOneSideEffect(t *smse, bool *done_something) {
			out.insert(smse);
			return NULL;
		}
		IRExpr *transformIRExpr(IRExpr *a, bool *done_something) {
			return a;
		}
	public:
		_(std::set<t *> &_out)
			: out(_out)
		{}
	} doit(out);
	doit.transform(sm);
}
void
findAllLoads(StateMachine *sm, std::set<StateMachineSideEffectLoad *> &out)
{
	findAllTypedSideEffects(sm, out);
}
void
findAllStores(StateMachine *sm, std::set<StateMachineSideEffectStore *> &out)
{
	findAllTypedSideEffects(sm, out);
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
canonicaliseRbp(StateMachine *sm, Oracle *oracle)
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

/* Find all of the states which definitely reach <survive> rather than
   <crash> and reduce them to just <survive> */
static void
removeSurvivingStates(StateMachine *sm, bool *done_something)
{
	std::set<StateMachineState *> survivingStates;
	std::set<StateMachineState *> allStates;
	bool progress;
	findAllStates(sm, survivingStates);
	allStates = survivingStates;
	do {
		progress = false;
		for (auto it = survivingStates.begin(); it != survivingStates.end(); ) {
			StateMachineState *s = *it;
			if (dynamic_cast<StateMachineCrash *>(s) ||
			    dynamic_cast<StateMachineUnreached *>(s) ||
			    (s->target0() && !survivingStates.count(s->target0()->target)) ||
			    (s->target1() && !survivingStates.count(s->target1()->target))) {
				survivingStates.erase(it++);
				progress = true;
			} else {
				it++;
			}
		}
	} while (progress);

	StateMachineEdge *noCrashEdge = NULL;
	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		StateMachineState *s = *it;
		StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(s);
		if (!smb)
			continue;
		if (smb->trueTarget->target != StateMachineNoCrash::get() &&
		    survivingStates.count(smb->trueTarget->target)) {
			if (!noCrashEdge) noCrashEdge = new StateMachineEdge(StateMachineNoCrash::get());
			smb->trueTarget = noCrashEdge;
			*done_something = true;
		}
		if (smb->falseTarget->target != StateMachineNoCrash::get() &&
		    survivingStates.count(smb->falseTarget->target)) {
			if (!noCrashEdge) noCrashEdge = new StateMachineEdge(StateMachineNoCrash::get());
			smb->falseTarget = noCrashEdge;
			*done_something = true;
		}
	}
}

StateMachine *
optimiseStateMachine(VexPtr<StateMachine, &ir_heap> &sm,
		     const AllowableOptimisations &opt,
		     VexPtr<Oracle> &oracle,
		     bool noExtendContext,
		     GarbageCollectionToken token)
{
	__set_profiling(optimiseStateMachine);
	sm->sanityCheck();
	Oracle::RegisterAliasingConfiguration alias(oracle->getAliasingConfigurationForRip(sm->origin));
	bool done_something;
	do {
		if (TIMEOUT)
			return sm;
		done_something = false;
		sm = internStateMachine(sm);
		sm = sm->optimise(opt, oracle, &done_something);
		if (opt.ignoreSideEffects)
			removeSurvivingStates(sm, &done_something);
		removeRedundantStores(sm, oracle, &done_something, opt);
		LibVEX_maybe_gc(token);
		sm = availExpressionAnalysis(sm, opt, alias, oracle, &done_something);
		LibVEX_maybe_gc(token);
		{
			bool d;
			do {
				d = false;
				sm = deadCodeElimination(sm, &d);
				done_something |= d;
			} while (d);
		}
		sm = sm->optimise(opt, oracle, &done_something);
		sm = bisimilarityReduction(sm, opt);
		if (noExtendContext) {
			sm->root->assertAcyclic();
			sm = introduceFreeVariables(sm, alias, opt, oracle, &done_something);
			sm = introduceFreeVariablesForRegisters(sm, &done_something);
			sm = optimiseFreeVariables(sm, &done_something);
			sm->root->assertAcyclic();
		}
		sm = optimiseSSA(sm, &done_something);
		sm = sm->optimise(opt, oracle, &done_something);
	} while (done_something);
	sm->sanityCheck();
	return sm;
}

static void
getConflictingStores(StateMachine *sm, Oracle *oracle, std::set<VexRip> &potentiallyConflictingStores)
{
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
}

static bool
instructionIsInteresting(const InstructionSet &i, const VexRip &r)
{
	return i.rips.count(r) != 0;
}

static StateMachine *
CFGtoStoreMachine(unsigned tid, VexPtr<Oracle> &oracle, VexPtr<CFGNode, &ir_heap> &cfg,
		  AllowableOptimisations &opt, GarbageCollectionToken token)
{
	VexPtr<gc_heap_map<VexRip, StateMachineState, &ir_heap>::type, &ir_heap> dummy(NULL);
	VexPtr<StateMachineState, &ir_heap> escape(StateMachineCrash::get());
	return CFGtoCrashReason(tid, cfg, dummy, escape, opt, true, oracle, token);
}

static bool
determineWhetherStoreMachineCanCrash(VexPtr<StateMachine, &ir_heap> &storeMachine,
				     VexPtr<StateMachine, &ir_heap> &probeMachine,
				     VexPtr<Oracle> &oracle,
				     VexPtr<IRExpr, &ir_heap> assumption,
				     const AllowableOptimisations &opt,
				     bool noExtendContext,
				     GarbageCollectionToken token,
				     IRExpr **assumptionOut,
				     StateMachine **newStoreMachine)
{
	__set_profiling(determineWhetherStoreMachineCanCrash);
	/* Specialise the state machine down so that we only consider
	   the interesting stores, and introduce free variables as
	   appropriate. */
	VexPtr<StateMachine, &ir_heap> sm;
	sm = optimiseStateMachine(storeMachine, opt, oracle, noExtendContext, token);

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
	std::vector<VexRip> previousInstructions;
	oracle->findPreviousInstructions(previousInstructions, sm->origin);
	if (previousInstructions.size() == 0) {
		/* Lacking any better ideas... */
		fprintf(_logfile, "cannot expand store machine...\n");
		return sm;
	}

	VexPtr<InferredInformation, &ir_heap> ii(new InferredInformation());
	sm = deSSA(sm);
	if (TIMEOUT)
		return sm;

	ii->set(sm->origin, sm->root);

	InstructionSet interesting;
	interesting.rips.insert(sm->origin);

	std::set<VexRip> terminalFunctions;

	VexPtr<StateMachine, &ir_heap> cr;

	auto it = previousInstructions.end();
	it--;

	LibVEX_maybe_gc(token);

	VexPtr<CFGNode, &ir_heap> cfg(
		buildCFGForRipSet(oracle->ms->addressSpace,
				  *it,
				  terminalFunctions,
				  oracle,
				  10 * previousInstructions.size()));
	trimCFG(cfg.get(), interesting, INT_MAX, false);

	{
		VexPtr<StateMachineState, &ir_heap> escape(StateMachineNoCrash::get());
		cr = CFGtoCrashReason(sm->tid,
				      cfg,
				      ii,
				      escape,
				      opt,
				      true,
				      oracle,
				      token);
	}
	if (!cr) {
		fprintf(_logfile, "\tCannot build crash reason from CFG\n");
		return NULL;
	}
	if (TIMEOUT)
		return NULL;
	cr = optimiseStateMachine(cr,
				  opt,
				  oracle,
				  false,
				  token);
	breakCycles(cr);
	cr->selectSingleCrashingPath();
	cr = optimiseStateMachine(cr,
				  opt,
				  oracle,
				  false,
				  token);
	return cr;
}

static bool
considerStoreCFG(VexPtr<CFGNode, &ir_heap> cfg,
		 VexPtr<Oracle> &oracle,
		 VexPtr<IRExpr, &ir_heap> assumption,
		 VexPtr<StateMachine, &ir_heap> &probeMachine,
		 VexPtr<CrashSummary, &ir_heap> &summary,
		 const std::set<VexRip> &is,
		 bool needRemoteMacroSections,
		 unsigned tid,
		 GarbageCollectionToken token)
{
	__set_profiling(considerStoreCFG);
	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.enableassumeNoInterferingStores()
		.setAddressSpace(oracle->ms->addressSpace);
	VexPtr<StateMachine, &ir_heap> sm(CFGtoStoreMachine(tid, oracle, cfg, opt, token));
	if (!sm) {
		fprintf(_logfile, "Cannot build store machine!\n");
		return true;
	}

	opt.interestingStores = is;
	opt.haveInterestingStoresSet = true;

	if (!determineWhetherStoreMachineCanCrash(sm, probeMachine, oracle, assumption, opt, false, token, NULL, NULL))
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
	if (!determineWhetherStoreMachineCanCrash(sm, probeMachine, oracle, assumption, opt, true, token, &_newAssumption, &_sm)) {
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

StateMachine *
buildProbeMachine(std::vector<VexRip> &previousInstructions,
		  VexPtr<InferredInformation, &ir_heap> &ii,
		  VexPtr<Oracle> &oracle,
		  const VexRip &interestingRip,
		  ThreadId tid,
		  GarbageCollectionToken token)
{
	__set_profiling(buildProbeMachine);

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.enableignoreSideEffects()
		.setAddressSpace(oracle->ms->addressSpace);

	VexPtr<StateMachine, &ir_heap> sm(NULL);

	for (auto it = previousInstructions.begin();
	     !TIMEOUT && it != previousInstructions.end();
	     it++) {
		fprintf(_logfile, "Backtrack to %s...\n", it->name());
		LibVEX_maybe_gc(token);

		std::set<VexRip> terminalFunctions;
		terminalFunctions.insert(VexRip::invent_vex_rip(0x757bf0));
		VexPtr<CFGNode, &ir_heap> cfg(
			buildCFGForRipSet(oracle->ms->addressSpace,
					  *it,
					  terminalFunctions,
					  oracle,
					  100));
		InstructionSet interesting;
		interesting.rips.insert(interestingRip);
		trimCFG(cfg.get(), interesting, INT_MAX, true);

		VexPtr<StateMachineState, &ir_heap> escape(StateMachineNoCrash::get());
		VexPtr<StateMachine, &ir_heap> cr(
			CFGtoCrashReason(tid._tid(), cfg, ii,
					 escape, opt, false, oracle, token));
		if (!cr) {
			fprintf(_logfile, "\tCannot build crash reason from CFG\n");
			return NULL;
		}

		cr = optimiseStateMachine(cr,
					  opt,
					  oracle,
					  false,
					  token);
		breakCycles(cr);
		cr->selectSingleCrashingPath();
		cr = optimiseStateMachine(cr,
					  opt,
					  oracle,
					  false,
					  token);

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
					  true,
					  token);

	return sm;
}

/* We know that only stores in @potentiallyConflictingStores are
   potentially relevant.  The task is then to find some fragments of
   the program's control flow graph which cover them.  You need to be
   a little careful here to group together instructions which are
   ``close'' together, and avoid grouping any which are a long way
   apart.  The approach we take works like this:

   1) Grab an arbitrary instruction from @potentiallyConflictingStores
   which isn't currently covered.
   2) Explore the control flow forwards from that instruction to some depth.
   If we encounter another instruction in @potentiallyConflictingStores
   then our action depends on whether the other instruction is already covered.
   If it is, we stop.  Otherwise, we reset the current depth to zero and
   continue.
   3) Iterate until every instruction in @potentiallyConflictingStores
   is covered.
   4) Pick some instructions out of the CFG to use as roots.  Every instruction
   must be reachable from some root, and no root may be reachable from
   another root, unless there's a cycle.

   Call and return instructions require special handling.  Basically,
   we always chase returns, using the return address in the VexRip,
   and we chase calls if there are any instructions in
   @potentiallyConflictingStores which might be encountered during the
   call (regardless of whether they're currently convered).
*/
namespace _getStoreCFGs {
#if 0 /* unconfuse emacs */
}
#endif
static int
countReachableNodes(CFGNode *root,
		    std::map<CFGNode *, int> &nr_available,
		    const std::set<CFGNode *> &interesting)
{
	auto it = nr_available.find(root);
	if (it != nr_available.end())
		return it->second;
	if (!interesting.count(root))
		return 0;
	/* Do it early to break cycles. */
	auto it2 = nr_available.insert(std::pair<CFGNode *, int>(root, 0));
	int acc = 1;
	if (root->fallThrough)
		acc += countReachableNodes(root->fallThrough, nr_available, interesting);
	if (root->branch)
		acc += countReachableNodes(root->branch, nr_available, interesting);
	it2.first->second = acc;
	return acc;
}

static void
purgeEverythingReachableFrom(std::set<CFGNode *> &st, CFGNode *root)
{
	if (!root)
		return;
	if (!st.count(root))
		return;
	st.erase(root);
	purgeEverythingReachableFrom(st, root->fallThrough);
	purgeEverythingReachableFrom(st, root->branch);
}

static CFGNode *
findBestRoot(const std::set<CFGNode *> avail)
{
	std::map<CFGNode *, int> nr_reachable;
	for (auto it = avail.begin(); it != avail.end(); it++)
		countReachableNodes(*it, nr_reachable, avail);
	int best_count = -1;
	CFGNode *bestItem = NULL;
	for (auto it = nr_reachable.begin(); it != nr_reachable.end(); it++) {
		if (it->second > best_count) {
			best_count = it->second;
			bestItem = it->first;
		}
	}
	assert(bestItem != NULL);
	assert(best_count > 0);
	return bestItem;
}

static void
buildRewriteTable(std::map<CFGNode *, CFGNode *> &rewriteTable,
		  std::set<CFGNode *> &avail,
		  CFGNode *root)
{
	if (!root || rewriteTable.count(root))
		return;
	CFGNode *newRoot;
	if (avail.count(root)) {
		newRoot = root;
		avail.erase(root);
	} else {
		newRoot = new CFGNode(*root);
	}
	rewriteTable[root] = newRoot;
	buildRewriteTable(rewriteTable, avail, root->fallThrough);
	buildRewriteTable(rewriteTable, avail, root->branch);
}

static void
rewriteCFG(CFGNode *root,
	   std::map<CFGNode *, CFGNode *> &rewriteTable)
{
	std::vector<CFGNode *> toVisit;
	std::set<CFGNode *> visited;
	toVisit.push_back(root);
	while (!toVisit.empty()) {
		CFGNode *vt = toVisit.back();
		toVisit.pop_back();
		if (visited.count(vt))
			continue;
		visited.insert(vt);

		if (vt->fallThrough) {
			auto it = rewriteTable.find(vt->fallThrough);
			if (it != rewriteTable.end())
				vt->fallThrough = it->second;
			toVisit.push_back(vt->fallThrough);
		}
		if (vt->branch) {
			auto it = rewriteTable.find(vt->branch);
			if (it != rewriteTable.end())
				vt->branch = it->second;
			toVisit.push_back(vt->branch);
		}
	}
}

static void
findAllReachableNodes(CFGNode *root, std::set<CFGNode *> &out)
{
	if (!root)
		return;

	auto i = out.insert(root);
	if (!i.second)
		return; /* Already discovered -> nothing to do */
	findAllReachableNodes(root->branch, out);
	findAllReachableNodes(root->fallThrough, out);
}

/* Duplicate CFG nodes within @cfgs so as to make them entirely
   disjoint.  We try to avoid duplicating nodes which don't need to be
   duplicated (e.g. if ones which are only reachable from one
   root). */
static void
makeCfgsDisjoint(std::set<CFGNode *> &cfgs)
{
	/* This is the set of nodes which haven't been used so far,
	   and so don't need to be duplicated. */
	std::set<CFGNode *> availableNodes;

	for (auto it = cfgs.begin(); it != cfgs.end(); it++)
		findAllReachableNodes(*it, availableNodes);

	std::set<CFGNode *> out;
	for (auto it = cfgs.begin(); it != cfgs.end(); it++) {
		/* Map from nodes in current node pool to the new,
		 * duplicated, form. */
		std::map<CFGNode *, CFGNode *> rewriteTable;
		buildRewriteTable(rewriteTable, availableNodes, *it);
		CFGNode *newRoot = rewriteTable[*it];
		rewriteCFG(newRoot, rewriteTable);
		out.insert(newRoot);
	}
	cfgs = out;
}

#if DEBUG_BUILD_STORE_CFGS == 0
/* Debug aid: print out anything reachable from @root which is in
 * @interesting.  Only works if @root is acyclic. */
static void
findTheseCfgNodes(CFGNode *root, const std::set<VexRip> &interesting)
{
	if (!root)
		return;
	if (interesting.count(root->my_rip))
		fprintf(_logfile, "\t\t%s\n", root->my_rip.name());
	findTheseCfgNodes(root->fallThrough, interesting);
	findTheseCfgNodes(root->branch, interesting);
}
#endif

static const unsigned MAX_INSTRS_IN_CFG_EXPLORATION = 10000;
static void
getStoreCFGs(std::set<VexRip> &potentiallyConflictingStores,
	     VexPtr<Oracle> &oracle,
	     VexPtr<CFGNode *, &ir_heap> &storeCFGs,
	     int *_nrStoreCfgs)
{
#if DEBUG_BUILD_STORE_CFGS
	fprintf(_logfile, "Potentially conflicting stores:\n");
	for (auto it = potentiallyConflictingStores.begin();
	     it != potentiallyConflictingStores.end();
	     it++)
		fprintf(_logfile, "\t%s\n", it->name());
#endif

	/* Instructions which we still need to visit.  We explore in
	 * breadth-first order starting from all of the roots until we
	 * have the desired number of instructions. */
	std::queue<VexRip> pendingInstructions;
	for (auto it = potentiallyConflictingStores.begin();
	     it != potentiallyConflictingStores.end();
	     it++)
		pendingInstructions.push(*it);

	std::map<VexRip, CFGNode *> ripsToCfgNodes;
	while (!pendingInstructions.empty() &&
	       ripsToCfgNodes.size() <= MAX_INSTRS_IN_CFG_EXPLORATION) {
	top_of_loop:
		VexRip next(pendingInstructions.front());
		pendingInstructions.pop();

		if (ripsToCfgNodes.count(next))
			continue;

		/* First time we've encountered this instruction.
		 * Have to go and decode it properly. */
		IRSB *irsb = oracle->getIRSBForRip(next);
		if (!irsb) {
			/* Whoops, end of the line. */
			continue;
		}

		/* Process all of the instructions in this IRSB.  This
		 * isn't quite breadth-first, but it doesn't make a
		 * great deal of difference in practice, provided that
		 * MAX_INSTRS_IN_CFG_EXPLORATION is much greater than
		 * the normal size of an IRSB. */
		int startOfInstruction = 0;
		int endOfInstruction = 0;
		CFGNode *currentNode = NULL;
		while (startOfInstruction < irsb->stmts_used) {
			assert(irsb->stmts[startOfInstruction]->tag == Ist_IMark);
			IRStmtIMark *startMark = (IRStmtIMark *)irsb->stmts[startOfInstruction];
			if (ripsToCfgNodes.count(startMark->addr.rip)) {
				/* We've run into the back of an
				   existing block.  There's no point
				   in exploring any further from
				   here. */
				goto top_of_loop;
			}

			currentNode = new CFGNode(startMark->addr.rip);
			for (endOfInstruction = startOfInstruction + 1;
			     endOfInstruction < irsb->stmts_used && irsb->stmts[endOfInstruction]->tag != Ist_IMark;
			     endOfInstruction++) {
				if (irsb->stmts[endOfInstruction]->tag == Ist_Exit) {
					assert(!currentNode->branchRip.isValid());
					currentNode->branchRip = ((IRStmtExit *)irsb->stmts[endOfInstruction])->dst.rip;
					pendingInstructions.push(currentNode->branchRip);
				}
			}

			if (endOfInstruction < irsb->stmts_used) {
				assert(irsb->stmts[endOfInstruction]->tag == Ist_IMark);
				IRStmtIMark *endMark = (IRStmtIMark *)irsb->stmts[endOfInstruction];
				currentNode->fallThroughRip = endMark->addr.rip;
			}

			ripsToCfgNodes.insert(std::pair<VexRip, CFGNode *>(currentNode->my_rip, currentNode));
			startOfInstruction = endOfInstruction;
		}

		assert(currentNode != NULL);

		if (irsb->jumpkind == Ijk_Call) {
			currentNode->fallThroughRip = extract_call_follower(irsb);
			assert(!currentNode->branchRip.isValid());
			if (irsb->next_is_const) {
				/* Should we try to explore the
				 * contents of this function as well?
				 * We do so if the fall through is a
				 * prefix of anything in the
				 * potentiallyConflictingStores set
				 * (which corresponds to the thing in
				 * the potentiallyConflictingStores
				 * set being called from this
				 * point). */
				bool traceIn = false;
				for (auto it = potentiallyConflictingStores.begin();
				     !traceIn && it != potentiallyConflictingStores.end();
				     it++) {
					if (currentNode->fallThroughRip.isPrefix(*it))
						traceIn = true;
				}
				if (traceIn) {
					/* Yes. */
#ifndef NDEBUG
					currentNode->branchRip = currentNode->fallThroughRip;
					currentNode->branchRip.call(
						irsb->next_const.rip.unwrap_vexrip());
					assert(currentNode->branchRip == irsb->next_const.rip);
#else
					currentNode->branchRip = irsb->next_const.rip;
#endif
					pendingInstructions.push(currentNode->branchRip);
				}
			} else {
				/* Don't consider inlining indirect
				   function calls; it's too hard. */
			}
		} else if (irsb->jumpkind == Ijk_Ret) {
			currentNode->fallThroughRip = currentNode->my_rip;
			currentNode->fallThroughRip.rtrn();
		} else if (irsb->next_is_const) {
			currentNode->fallThroughRip = irsb->next_const.rip;
		} else {
			/* Don't currently try to trace across
			 * indirect branches. */
		}

		if (currentNode->fallThroughRip.isValid())
			pendingInstructions.push(currentNode->fallThroughRip);
	}

#if DEBUG_BUILD_STORE_CFGS
	fprintf(_logfile, "Initial CFG:\n");
	for (auto it = ripsToCfgNodes.begin(); it != ripsToCfgNodes.end(); it++) {
		CFGNode *n = it->second;
		fprintf(_logfile, "\t%s\t-> %p", it->first.name(), n);
		if (n->fallThroughRip.isValid())
			fprintf(_logfile, " ft %s", n->fallThroughRip.name());
		if (n->branchRip.isValid())
			fprintf(_logfile, " b %s", n->branchRip.name());
		fprintf(_logfile, "\n");
	}
#endif

	/* When we get here, ripsToCfgNodes contains an entry for
	 * everything which is going to be in the final graph, but it
	 * might contain some extra ones, and the pointers have not
	 * been resolved. */

	/* Resolve pointers. */
	for (auto it = ripsToCfgNodes.begin();
	     it != ripsToCfgNodes.end();
	     it++) {
		CFGNode *node = it->second;
		assert(node);
		assert(!node->fallThrough);
		assert(!node->branch);

		/* Careful here.  We don't want to go
		   ripsToCfgNodes[node->fallThroughRip], because that
		   might create a new entry in ripsToCfgNodes, which
		   would invalidate the iterator. */
		if (node->fallThroughRip.isValid()) {
			auto it2 = ripsToCfgNodes.find(node->fallThroughRip);
			if (it2 != ripsToCfgNodes.end())
				node->fallThrough = it2->second;
		}
		if (node->branchRip.isValid()) {
			auto it2 = ripsToCfgNodes.find(node->branchRip);
			if (it2 != ripsToCfgNodes.end())
				node->branch = it2->second;
		}
	}

#if DEBUG_BUILD_STORE_CFGS
	fprintf(_logfile, "Resolved CFG:\n");
	for (auto it = ripsToCfgNodes.begin(); it != ripsToCfgNodes.end(); it++) {
		CFGNode *n = it->second;
		fprintf(_logfile, "\t%s\t-> %p", it->first.name(), n);
		if (n->fallThrough)
			fprintf(_logfile, " ft %p", n->fallThrough);
		if (n->branch)
			fprintf(_logfile, " b %p", n->branch);
		if (n->fallThrough)
			assert(n->fallThrough->my_rip == n->fallThroughRip);
		if (n->branch)
			assert(n->branch->my_rip == n->branchRip);
		fprintf(_logfile, "\n");
	}
#endif

	/* Now figure out which CFG nodes we're actually going to
	 * keep.  We keep anything in @potentiallyConflictingStores,
	 * and anything which can reach something in
	 * @potentiallyConflictingStores. */
	std::set<CFGNode *> nodesToKeep;
	for (auto it = potentiallyConflictingStores.begin();
	     it != potentiallyConflictingStores.end();
	     it++) {
		auto it2 = ripsToCfgNodes.find(*it);
		if (it2 != ripsToCfgNodes.end())
			nodesToKeep.insert(it2->second);
	}
	/* Fixed point iteration to find the nodes to keep. */
	bool progress;
	do {
		progress = false;
		for (auto it = ripsToCfgNodes.begin();
		     it != ripsToCfgNodes.end();
		     it++) {
			CFGNode *node = it->second;
			if (nodesToKeep.count(node))
				continue;
			if ((node->fallThrough && nodesToKeep.count(node->fallThrough)) ||
			    (node->branch && nodesToKeep.count(node->branch))) {
				nodesToKeep.insert(node);
				progress = true;
			}
		}
	} while (progress);

#if DEBUG_BUILD_STORE_CFGS
	fprintf(_logfile, "Instructions relevant to store threads:\n");
	for (auto it = nodesToKeep.begin();
	     it != nodesToKeep.end();
	     it++)
		fprintf(_logfile, "\t%s\n", (*it)->my_rip.name());
#endif

	/* Which then allows us to remove the nodes we don't want any more. */
	for (auto it = ripsToCfgNodes.begin();
	     it != ripsToCfgNodes.end();
		) {
		CFGNode *node = it->second;
		if (!nodesToKeep.count(node)) {
			ripsToCfgNodes.erase(it++);
		} else {
			if (node->fallThrough && !nodesToKeep.count(node->fallThrough))
				node->fallThrough = NULL;
			if (node->branch && !nodesToKeep.count(node->branch))
				node->branch = NULL;
			it++;
		}
	}

	/* ripsToCfgNodes now contains precisely the set of CFG nodes
	   which we're interested in.  We still need to remove any
	   cycles and identify the roots. */
	std::set<CFGNode *> unrootedCFGNodes;
	for (auto it = ripsToCfgNodes.begin();
	     it != ripsToCfgNodes.end();
	     it++)
		unrootedCFGNodes.insert(it->second);
	std::set<CFGNode *> roots;
	/* First heuristic: if something has no parents, it's
	   definitely a root. */
	std::set<CFGNode *> nodesWithNoParents(unrootedCFGNodes);
	for (auto it = unrootedCFGNodes.begin(); it != unrootedCFGNodes.end(); it++) {
		CFGNode *n = *it;
		if (n->fallThrough)
			nodesWithNoParents.erase(n->fallThrough);
		if (n->branch)
			nodesWithNoParents.erase(n->branch);
	}
	for (auto it = nodesWithNoParents.begin(); it != nodesWithNoParents.end(); it++) {
		CFGNode *newRoot = *it;
		roots.insert(newRoot);
		purgeEverythingReachableFrom(unrootedCFGNodes, newRoot);
	}
	if (!unrootedCFGNodes.empty()) {
		/* Trickier case.  Some nodes have no parents.  They
		   must necessarily be part of a cycle, and there must
		   be no node which is not part of a cycle which can
		   reach them.  We now want to pick whichever node can
		   reach the largest number of other nodes, with ties
		   broken by taking the smallest available address. */
		while (!unrootedCFGNodes.empty()) {
			CFGNode *root = findBestRoot(unrootedCFGNodes);
			roots.insert(root);
			purgeEverythingReachableFrom(unrootedCFGNodes, root);
		}
	}

	/* cycle breaking is subtle because you need to avoid losing
	   nodes, even when you have multiple roots.  The nasty case
	   is where you have a loop from A to B, a root X whose
	   successor is A, and a root Y whose successor is B:

           X       Y
	   v       v
	   v       v
	   v       v
	   A------>B
	   ^       v
	   ^       v
	   +-------+

	   If you consider root X first then you might be tempted to
	   break the B->A edge to produce a graph like this:

	   X--->A--->B

	   The problem is that the Y root then produces just Y----->B
	   i.e. it's lost A.  Likewise, if you break the A->B edge,
	   the Y root gets a graph Y---->B---->A but the X root gets
	   just X--->A.

	   This is moderately unusual (if it happens, the program
	   wasn't nicely block structured, because it has a
	   multi-entry loop), but not so unusual that we can just
	   ignore it (sometimes the compiler takes a nicely structured
	   program and makes it slightly less structured e.g. if one
	   path to the head of the loop tells you something about the
	   loop condition).  The fix is actually really simple: just
	   duplicate the CFG for every root.  Usually that's a no-op,
	   and we have a little lookaside thing saying whether it's
	   safe to just re-use the existing nodes.
	*/
	makeCfgsDisjoint(roots);

	/* Finally, break cycles. */
	for (auto it = roots.begin(); it != roots.end(); it++)
		breakCycles(*it);

	fprintf(_logfile, "Store clustering:\n");
	for (auto it = roots.begin(); it != roots.end(); it++) {
		fprintf(_logfile, "\tRoot %s:\n", (*it)->my_rip.name());
#if DEBUG_BUILD_STORE_CFGS
		printCFG(*it, "\t\t", _logfile);
#else
		/* Slightly less verbose bit of debugging: show where
		   instructions which were in the input set ended up,
		   but not the ones we discovered on our way
		   around. */
		findTheseCfgNodes(*it, potentiallyConflictingStores);
#endif
	}

	/* Reformat results so that caller can use them. */
	storeCFGs = (CFGNode **)__LibVEX_Alloc_Ptr_Array(&ir_heap, roots.size());
	unsigned cntr = 0;
	for (auto it = roots.begin(); it != roots.end(); it++) {
		storeCFGs[cntr] = *it;
		cntr++;
	}
	*_nrStoreCfgs = roots.size();
}

} /* End namespace */

static void
getStoreCFGs(std::set<VexRip> &potentiallyConflictingStores,
	     VexPtr<Oracle> &oracle,
	     VexPtr<CFGNode *, &ir_heap> &storeCFGs,
	     int *_nrStoreCfgs)
{
	_getStoreCFGs::getStoreCFGs(potentiallyConflictingStores,
				    oracle,
				    storeCFGs,
				    _nrStoreCfgs);
}

static bool
isSingleNodeCfg(CFGNode *root)
{
	return root->fallThrough == NULL && root->branch == NULL;
}

static bool
probeMachineToSummary(VexPtr<StateMachine, &ir_heap> &probeMachine,
		      VexPtr<Oracle> &oracle,
		      VexPtr<IRExpr, &ir_heap> &survive,
		      VexPtr<CrashSummary, &ir_heap> &summary,
		      bool needRemoteMacroSections,
		      std::set<VexRip> &potentiallyConflictingStores,
		      GarbageCollectionToken token)
{
	assert(potentiallyConflictingStores.size() > 0);

	VexPtr<CFGNode *, &ir_heap> storeCFGs;
	int nrStoreCfgs;
	getStoreCFGs(potentiallyConflictingStores, oracle, storeCFGs, &nrStoreCfgs);
	if (TIMEOUT)
		return false;
	assert(nrStoreCfgs != 0);

	auto roughLoadCount = probeMachine->root->roughLoadCount();

	bool foundRace;
	foundRace = false;
	for (int i = 0; i < nrStoreCfgs; i++) {
		if (roughLoadCount == StateMachineState::singleLoad &&
		    isSingleNodeCfg(storeCFGs[i])) {
			fprintf(_logfile, "Single store versus single load -> no race possible\n");
			continue;
		}

		VexPtr<CFGNode, &ir_heap> storeCFG(storeCFGs[i]);
		foundRace |= considerStoreCFG(storeCFG,
					      oracle,
					      survive,
					      probeMachine,
					      summary,
					      potentiallyConflictingStores,
					      needRemoteMacroSections,
					      STORING_THREAD + i,
					      token);
	}

	return foundRace;
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

	std::set<VexRip> potentiallyConflictingStores;
	getConflictingStores(probeMachine, oracle, potentiallyConflictingStores);
	if (potentiallyConflictingStores.size() == 0) {
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

	bool foundRace = probeMachineToSummary(probeMachine, oracle, survive,
					       summary, needRemoteMacroSections,
					       potentiallyConflictingStores,
					       token);
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
			    
static void
printCFG(const CFGNode *cfg, const char *prefix, FILE *f)
{
	std::vector<const CFGNode *> pending;
	std::set<const CFGNode *> done;

	pending.push_back(cfg);
	while (!pending.empty()) {
		cfg = pending.back();
		pending.pop_back();
		if (done.count(cfg))
			continue;
		fprintf(f, "%s%p: ", prefix, cfg);
		cfg->prettyPrint(f);
		fprintf(f, "\n");
		if (cfg->fallThrough)
			pending.push_back(cfg->fallThrough);
		if (cfg->branch)
			pending.push_back(cfg->branch);
		done.insert(cfg);
	}
}
/* Make it more visible to the debugger. */
void __printCFG(const CFGNode *cfg) { printCFG(cfg, "", stdout); }

/* Build a control flow graph which covers all of the RIPs in @rips.
 * @output is filled in with pointers to all of the possible start
 * nodes.
 */
/* This only really makes sense if @rips are similar enough that the
 * CFGs are likely to overlap. */
static CFGNode *
buildCFGForRipSet(AddressSpace *as,
		  const VexRip &start,
		  const std::set<VexRip> &terminalFunctions,
		  Oracle *oracle,
		  unsigned max_depth)
{
	std::map<VexRip, std::pair<CFGNode *, unsigned> > builtSoFar;
	std::priority_queue<std::pair<unsigned, VexRip> > needed;
	unsigned depth;
	VexRip rip;

	/* Step one: discover all of the instructions which we're
	 * going to need. */
	needed.push(std::pair<unsigned, VexRip>(max_depth, start));
	while (!needed.empty()) {
		rip = needed.top().second;
		depth = needed.top().first;
		needed.pop();
		if (!depth ||
		    (builtSoFar.count(rip) && builtSoFar[rip].second >= depth))
			continue;
		IRSB *irsb = as->getIRSBForAddress(ThreadRip::mk(-1, rip));
		auto work = new CFGNode(rip);
		int x;
		for (x = 1; x < irsb->stmts_used; x++) {
			if (irsb->stmts[x]->tag == Ist_IMark) {
				work->fallThroughRip = ((IRStmtIMark *)irsb->stmts[x])->addr.rip;
				break;
			}
			if (irsb->stmts[x]->tag == Ist_Exit) {
				assert(!work->branchRip.isValid());
				work->branchRip = ((IRStmtExit *)irsb->stmts[x])->dst.rip;
			}
		}
		if (x == irsb->stmts_used) {
			if (irsb->jumpkind == Ijk_Call) {
				VexRip follower = extract_call_follower(irsb);
				if (irsb->next_is_const) {
					if (terminalFunctions.count(irsb->next_const.rip)) {
						/* Inline this function */
						work->branchRip = irsb->next_const.rip;
					} else if (oracle->functionCanReturn(irsb->next_const.rip)) {
						/* Treat this function as pure. */
						work->fallThroughRip = follower;
					} else {
						/* This function can't
						   return, and wasn't
						   on the stack when
						   we crashed -> it
						   was never called.
						   We encode that by
						   leaving both the
						   branch and
						   fallThrough fields
						   empty. */
					}
				} else {
					work->fallThroughRip = follower;
				}
			} else if (irsb->jumpkind == Ijk_Ret) {
				work->fallThroughRip = work->my_rip;
				work->fallThroughRip.rtrn();
			} else {
				/* Don't currently try to trace across indirect branches. */
				if (irsb->next_is_const)
					work->fallThroughRip = irsb->next_const.rip;
			}
		}
		if (work->fallThroughRip.isValid())
			needed.push(std::pair<unsigned, VexRip>(depth - 1, work->fallThroughRip));
		if (work->branchRip.isValid())
			needed.push(std::pair<unsigned, VexRip>(depth - 1, work->branchRip));
		builtSoFar[rip] = std::pair<CFGNode *, unsigned>(work, depth);
	}

	/* Now we have a CFG node for every needed instruction.  Go
	   through and resolve exit branches. */
	for (auto it = builtSoFar.begin();
	     it != builtSoFar.end();
	     it++) {
		auto *node = it->second.first;
		if (!node) {
			/* This happens if a node has been killed by
			 * the depth limit. */
			continue;
		}
		node->fallThrough = builtSoFar[node->fallThroughRip].first;
		node->branch = builtSoFar[node->branchRip].first;
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
	return rt.doit(sm);
}

static StateMachine *
CFGtoCrashReason(unsigned tid,
		 VexPtr<CFGNode, &ir_heap> &cfg,
		 VexPtr<gc_heap_map<VexRip, StateMachineState, &ir_heap>::type, &ir_heap> &crashReasons,
		 VexPtr<StateMachineState, &ir_heap> &escapeState,
		 AllowableOptimisations &opt,
		 bool simple_calls,
		 VexPtr<Oracle> &oracle,
		 GarbageCollectionToken token)
{
	typedef gc_heap_map<VexRip, StateMachineState, &ir_heap>::type inferredInformation;

	class State {
		typedef std::pair<StateMachineState **, CFGNode *> reloc_t;
		std::vector<CFGNode *> pending;
		std::vector<reloc_t> relocs;
		inferredInformation *crashReasons;
	public:
		std::map<CFGNode *, StateMachineState *> cfgToState;

		CFGNode *nextNode() {
			while (1) {
				if (pending.empty()) {
					std::vector<reloc_t> newRelocs;
					for (auto it = relocs.begin(); it != relocs.end(); it++) {
						if (cfgToState.count(it->second)) {
							*it->first = cfgToState[it->second];
						} else if (crashReasons && crashReasons->hasKey(it->second->my_rip)) {
							*it->first = crashReasons->get(it->second->my_rip);
						} else {
							newRelocs.push_back(*it);
							pending.push_back(it->second);
						}
					}
					relocs = newRelocs;
					if (pending.empty())
						return NULL;
				}
				CFGNode *res = pending.back();
				pending.pop_back();
				if (cfgToState.count(res))
					continue;
				return res;
			}
		}
		void addReloc(StateMachineState **p, CFGNode *c)
		{
			*p = NULL;
			relocs.push_back(reloc_t(p, c));
		}

		State(inferredInformation *_crashReasons)
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
		IRSB *operator()(const VexRip &rip) {
			try {
				return as->getIRSBForAddress(ThreadRip::mk(tid, rip));
			} catch (BadMemoryException e) {
				return NULL;
			}
		}
	} fetchIrsb(oracle->ms->addressSpace, tid);

	class BuildStateForCfgNode {
		StateMachineEdge *backtrackOneStatement(IRStmt *stmt,
							const ThreadVexRip rip,
							CFGNode *branchTarget,
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

		StateMachineState *buildStateForCallInstruction(CFGNode *cfg,
								IRSB *irsb,
								const ThreadVexRip &site)
		{
			IRExpr *r;
			if (simple_calls) {
				IRExpr **args = alloc_irexpr_array(1);
				args[0] = NULL;
				r = IRExpr_ClientCall(VexRip(), site, args);
			} else if (irsb->next_is_const) {
				VexRip called_rip = irsb->next_const.rip;
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
				r = IRExpr_ClientCallFailed(irsb->next_nonconst);
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
			if (cfg->fallThrough)
				state.addReloc(&smp->target->target, cfg->fallThrough);
			else
				smp->target->target = escapeState;
			smp->target->prependSideEffect(
				new StateMachineSideEffectCopy(
					threadAndRegister::reg(site.thread, OFFSET_amd64_RAX, 0),
					r));
			return smp;
		}
	public:
		bool simple_calls;
		unsigned tid;
		State &state;
		StateMachineState *escapeState;
		Oracle *oracle;
		BuildStateForCfgNode(bool _simple_calls, unsigned _tid, State &_state,
				     StateMachineState *_escapeState, Oracle *_oracle)
			: simple_calls(_simple_calls), tid(_tid), state(_state),
			  escapeState(_escapeState), oracle(_oracle)
		{}
		StateMachineState *operator()(CFGNode *cfg,
					      IRSB *irsb) {
			if (!cfg)
				return escapeState;
			ThreadVexRip rip;
			rip.thread = tid;
			rip.rip = cfg->my_rip;
			int endOfInstr;
			for (endOfInstr = 1;
			     endOfInstr < irsb->stmts_used && irsb->stmts[endOfInstr]->tag != Ist_IMark;
			     endOfInstr++)
				;
			StateMachineEdge *edge;
			if (endOfInstr == irsb->stmts_used && irsb->jumpkind == Ijk_Call) {
				/* This is a call node, which requires
				 * special handling. */
				if (cfg->branch) {
					/* We want to inline this
					 * call, in effect. */
					edge = new StateMachineEdge(NULL);
					state.addReloc(&edge->target, cfg->branch);
				} else {
					return buildStateForCallInstruction(cfg, irsb, rip);
				}
			} else {
				edge = new StateMachineEdge(NULL);
				if (!cfg->fallThrough && cfg->branch) {
					/* We've decided to force this one to take the
					   branch.  Trim the bit of the instruction
					   after the branch. */
					assert(cfg->branch);
					endOfInstr--;
					while (endOfInstr >= 0 && irsb->stmts[endOfInstr]->tag != Ist_Exit)
						endOfInstr--;
					assert(endOfInstr > 0);
					state.addReloc(&edge->target, cfg->branch);
				} else if (cfg->fallThrough) {
					state.addReloc(&edge->target, cfg->fallThrough);
				} else {
					edge->target = escapeState;
				}
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
	} buildStateForCfgNode(simple_calls, tid, state, escapeState, oracle);

	VexRip original_rip = cfg->my_rip;
	StateMachineState *root = NULL;
	state.addReloc(&root, cfg);

	while (1) {
		cfg = state.nextNode();
		if (!cfg)
			break;
		if (crashReasons && crashReasons->hasKey(cfg->my_rip)) {
			state.cfgToState[cfg] = crashReasons->get(cfg->my_rip);
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
	VexPtr<StateMachine, &ir_heap> sm(new StateMachine(root, original_rip, fv, tid));
	sm->sanityCheck();
	canonicaliseRbp(sm, oracle);
	sm = optimiseStateMachine(sm, opt, oracle, false, token);
	if (crashReasons)
		crashReasons->set(original_rip, sm->root);
	sm = convertToSSA(sm);
	if (TIMEOUT)
		return NULL;
	sm->sanityCheck();
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
