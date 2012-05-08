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
#include "cfgnode.hpp"

#define DEBUG_BUILD_STORE_CFGS 0

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
	enumerateCFG(root->fallThrough.second, rips);
	for (auto it = root->branches.begin(); it != root->branches.end(); it++)
		enumerateCFG(it->second, rips);
}

/* Remove all of the nodes which appear to be uninteresting.  A node
   is uninteresting if it is not in the initial interesting set and
   there are no paths from it to an interesting node. */
static void
trimCFG(CFGNode *root, const InstructionSet &interestingAddresses)
{
	std::map<VexRip, CFGNode *> uninteresting;
	std::map<VexRip, CFGNode *> interesting;
	/* Start on the assumption that everything is uninteresting. */
	enumerateCFG(root, uninteresting);
	/* addresses which are explicitly flagged as interesting are
	   not uninteresting. */
	for (auto it = uninteresting.begin();
	     it != uninteresting.end();
		) {
		if (instructionIsInteresting(interestingAddresses, it->first)) {
			interesting[it->first] = it->second;
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
			progress = true;
			interesting[it->first] = it->second;
			uninteresting.erase(it++);
		}
	} while (progress);

	/* The uninteresting set should now be correct.  Eliminate any
	   edges which go to an uninteresting target. */
	for (auto it = interesting.begin();
	     it != interesting.end();
	     it++) {
		CFGNode *n = it->second;
		assert(n);
		if (n->fallThrough.second && uninteresting.count(n->fallThrough.second->my_rip))
			n->fallThrough.second = NULL;
		for (auto it = n->branches.begin(); it != n->branches.end(); it++)
			if (it->second && uninteresting.count(it->second->my_rip))
				it->second = NULL;
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
	for (auto it = cfg->branches.begin(); it != cfg->branches.end(); it++) {
		if (it->second) {
			CFGNode **p = lastBackEdge;
			if (numbering[it->second] < numbering[cfg])
				p = &it->second;
			if (it->second == cfg)
				it->second = NULL;
			else if (!breakCycles(it->second, numbering, p, onPath, clean))
				return false;
		}
	}
	if (cfg->fallThrough.second) {
		CFGNode **p = lastBackEdge;
		if (numbering[cfg->fallThrough.second] < numbering[cfg])
			p = &cfg->fallThrough.second;
		if (cfg->fallThrough.second == cfg)
			cfg->fallThrough.second = NULL;
		else if (!breakCycles(cfg->fallThrough.second, numbering, p, onPath, clean))
			return false;
	}

	onPath.erase(cfg);

        clean.insert(cfg);
	return true;
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

void
findAllStates(StateMachine *sm, std::set<StateMachineState *> &out)
{
	enumStates(sm, &out);
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
	StateMachineSideEffect *smse =
		new StateMachineSideEffectCopy(
			threadAndRegister::reg(sm->tid, OFFSET_amd64_RBP, 0),
			IRExpr_Associative(
				Iop_Add64,
				IRExpr_Get(
					threadAndRegister::reg(sm->tid, OFFSET_amd64_RSP, 0),
					Ity_I64),
				IRExpr_Const(
					IRConst_U64(delta)),
				NULL));
	sm->root = new StateMachineSideEffecting(sm->origin, smse, sm->root);
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
			bool definitely_survives = true;
			if (dynamic_cast<StateMachineCrash *>(s) ||
			    dynamic_cast<StateMachineUnreached *>(s))
				definitely_survives = false;
			if (definitely_survives) {
				std::vector<StateMachineState *> targets;
				s->targets(targets);
				for (auto it = targets.begin(); definitely_survives && it != targets.end(); it++)
					if (!survivingStates.count(*it))
						definitely_survives = false;
			}
			if (!definitely_survives) {
				survivingStates.erase(it++);
				progress = true;
			} else {
				it++;
			}
		}
	} while (progress);

	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		StateMachineState *s = *it;
		StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(s);
		if (!smb)
			continue;
		if (smb->trueTarget != StateMachineNoCrash::get() &&
		    survivingStates.count(smb->trueTarget)) {
			smb->trueTarget = StateMachineNoCrash::get();
			*done_something = true;
		}
		if (smb->falseTarget != StateMachineNoCrash::get() &&
		    survivingStates.count(smb->falseTarget)) {
			smb->falseTarget = StateMachineNoCrash::get();
			*done_something = true;
		}
	}
}

StateMachine *
optimiseStateMachine(VexPtr<StateMachine, &ir_heap> &sm,
		     const AllowableOptimisations &opt,
		     VexPtr<Oracle> &oracle,
		     bool noExtendContext,
		     bool is_ssa,
		     GarbageCollectionToken token)
{
	__set_profiling(optimiseStateMachine);
	sm->sanityCheck();
	Oracle::RegisterAliasingConfiguration alias, *aliasp;

	/* Careful here.  We can only use the aliasing configuration
	   if the machine is in SSA form, because that guarantees that
	   there won't be any writes to gen -1 registers, which in
	   turn means that a single aliasing configuration is valid
	   for the entire machine. */
	if (is_ssa) {
		alias = oracle->getAliasingConfigurationForRip(sm->origin);
		aliasp = &alias;
		sm->assertSSA();
	} else {
		aliasp = NULL;
	}
	bool done_something;
	do {
		if (TIMEOUT)
			return sm;
		done_something = false;
		sm = internStateMachine(sm);
		sm = sm->optimise(opt, oracle, &done_something);
		if (opt.ignoreSideEffects())
			removeSurvivingStates(sm, &done_something);
		removeRedundantStores(sm, oracle, &done_something, aliasp, opt);
		LibVEX_maybe_gc(token);
		sm = availExpressionAnalysis(sm, opt, aliasp, is_ssa, oracle, &done_something);
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
			sm->assertAcyclic();
			sm = introduceFreeVariables(sm, aliasp, opt, oracle, &done_something);
			sm = introduceFreeVariablesForRegisters(sm, &done_something);
			sm = optimiseFreeVariables(sm, &done_something);
			sm->assertAcyclic();
		}
		if (is_ssa)
			sm = optimiseSSA(sm, &done_something);
		sm = sm->optimise(opt, oracle, &done_something);
	} while (done_something);
	sm->sanityCheck();
	if (is_ssa)
		sm->assertSSA();
	return sm;
}

static void
getConflictingStores(StateMachine *sm, Oracle *oracle, std::set<DynAnalysisRip> &potentiallyConflictingStores)
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
	sm = optimiseStateMachine(storeMachine, opt, oracle, noExtendContext, true, token);

	if (dynamic_cast<StateMachineUnreached *>(sm->root)) {
		/* This store machine is unusable, probably because we
		 * don't have the machine code for the relevant
		 * library */
		fprintf(_logfile, "\t\tStore machine is unusable\n");
		return false;
	}

	fprintf(_logfile, "\t\tStore machine:\n");
	printStateMachine(sm, _logfile);

	VexPtr<IRExpr, &ir_heap> writeMachineConstraint(
		writeMachineCrashConstraint(sm,
					    IRExpr_Const(IRConst_U1(0)),
					    assumption,
					    IRExpr_Const(IRConst_U1(0)),
					    opt));
	if (!writeMachineConstraint) {
		fprintf(_logfile, "\t\tCannot derive write machine crash constraint\n");
		return false;
	}

	assumption = writeMachineSuitabilityConstraint(
		sm,
		probeMachine,
		oracle,
		assumption,
		opt,
		token);

	if (!assumption) {
		fprintf(_logfile, "\t\tCannot derive write machine suitability constraint\n");
		return false;
	}

	fprintf(_logfile, "\t\tWrite machine suitability constraint: ");
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
	trimCFG(cfg.get(), interesting);

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
				  false,
				  token);
	breakCycles(cr);
	if (TIMEOUT)
		return NULL;
	cr = optimiseStateMachine(cr,
				  opt,
				  oracle,
				  false,
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
		 const std::set<DynAnalysisRip> &is,
		 bool needRemoteMacroSections,
		 unsigned tid,
		 const AllowableOptimisations &optIn,
		 GarbageCollectionToken token)
{
	__set_profiling(considerStoreCFG);
	AllowableOptimisations opt =
		optIn
		.enableassumeNoInterferingStores();
	VexPtr<StateMachine, &ir_heap> sm(CFGtoStoreMachine(tid, oracle, cfg, opt, token));
	if (!sm) {
		fprintf(_logfile, "Cannot build store machine!\n");
		return true;
	}

	opt = opt.setinterestingStores(&is);

	VexPtr<StateMachine, &ir_heap> sm_ssa(convertToSSA(sm));
	if (!sm_ssa)
		return false;
	if (!determineWhetherStoreMachineCanCrash(sm_ssa, probeMachine, oracle, assumption, opt, false, token, NULL, NULL))
		return false;

	/* If it might crash with that machine, try expanding it to
	   include a bit more context and see if it still goes. */
	sm = expandStateMachineToFunctionHead(sm, oracle, opt, token);
	if (!sm) {
		fprintf(_logfile, "\t\tCannot expand store machine!\n");
		return true;
	}

	opt = opt.enablefreeVariablesNeverAccessStack();

	sm = convertToSSA(sm);
	if (!sm)
		return false;

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
		  const AllowableOptimisations &optIn,
		  GarbageCollectionToken token)
{
	__set_profiling(buildProbeMachine);

	AllowableOptimisations opt =
		optIn
		.enableignoreSideEffects();

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
		trimCFG(cfg.get(), interesting);

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
					  false,
					  token);
		breakCycles(cr);
		if (TIMEOUT)
			return NULL;
		cr = optimiseStateMachine(cr,
					  opt,
					  oracle,
					  false,
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

	if (sm) {
		sm = convertToSSA(sm);
		if (TIMEOUT)
			return NULL;
		sm->sanityCheck();
		sm = optimiseStateMachine(sm,
					  opt.enablefreeVariablesNeverAccessStack(),
					  oracle,
					  true,
					  true,
					  token);
	}

	return sm;
}

static bool
isSingleNodeCfg(CFGNode *root)
{
	return root->fallThrough.second == NULL && root->branches.empty();
}

static bool
probeMachineToSummary(VexPtr<StateMachine, &ir_heap> &probeMachine,
		      VexPtr<Oracle> &oracle,
		      VexPtr<IRExpr, &ir_heap> &survive,
		      VexPtr<CrashSummary, &ir_heap> &summary,
		      bool needRemoteMacroSections,
		      std::set<DynAnalysisRip> &potentiallyConflictingStores,
		      const AllowableOptimisations &optIn,
		      GarbageCollectionToken token)
{
	assert(potentiallyConflictingStores.size() > 0);

	VexPtr<CFGNode *, &ir_heap> storeCFGs;
	int nrStoreCfgs;
	{
		CFGNode **n;
		getStoreCFGs(potentiallyConflictingStores, oracle, &n, &nrStoreCfgs);
		storeCFGs = n;
	}
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
					      optIn,
					      token);
	}

	return foundRace;
}

CrashSummary *
diagnoseCrash(VexPtr<StateMachine, &ir_heap> &probeMachine,
	      VexPtr<Oracle> &oracle,
	      VexPtr<MachineState> &ms,
	      bool needRemoteMacroSections,
	      const AllowableOptimisations &optIn,
	      GarbageCollectionToken token)
{
	__set_profiling(diagnoseCrash);
	fprintf(_logfile, "Probe machine:\n");
	printStateMachine(probeMachine, _logfile);
	fprintf(_logfile, "\n");

	std::set<DynAnalysisRip> potentiallyConflictingStores;
	getConflictingStores(probeMachine, oracle, potentiallyConflictingStores);
	if (potentiallyConflictingStores.size() == 0) {
		fprintf(_logfile, "\t\tNo available conflicting stores?\n");
		return NULL;
	}

	VexPtr<IRExpr, &ir_heap> survive;

	{
		/* We start by figuring out some properties of the
		   probe machine when it's run atomically. */
		AllowableOptimisations opt =
			optIn
			.enableignoreSideEffects()
			.enablefreeVariablesNeverAccessStack()
			.enableassumeNoInterferingStores()
			.enableassumeExecutesAtomically();
		VexPtr<StateMachine, &ir_heap> atomicProbeMachine;
		atomicProbeMachine = duplicateStateMachine(probeMachine);
		atomicProbeMachine = optimiseStateMachine(atomicProbeMachine, opt, oracle,
							  true, true, token);
		VexPtr<IRExpr, &ir_heap> nullexpr(NULL);
		survive = survivalConstraintIfExecutedAtomically(atomicProbeMachine, nullexpr, oracle, opt, token);
		if (!survive) {
			fprintf(_logfile, "\tTimed out computing survival constraint\n");
			return NULL;
		}
		survive = simplifyIRExpr(survive, opt);

		fprintf(_logfile, "\tComputed survival constraint ");
		ppIRExpr(survive, _logfile);
		fprintf(_logfile, "\n");

		/* Quick check that that vaguely worked.  If this
		   reports mightCrash == true then that probably means
		   that the theorem prover bits need more work.  If it
		   reports mightSurvive == false then the program is
		   doomed and it's not possible to fix it from this
		   point. */
		bool mightSurvive, mightCrash;
		if (!evalMachineUnderAssumption(atomicProbeMachine, oracle, survive, opt, &mightSurvive, &mightCrash, token)) {
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
			dbg_break("Bad things are happening\n");
			return NULL;
		}
	}

	VexPtr<CrashSummary, &ir_heap> summary(new CrashSummary(probeMachine));

	bool foundRace = probeMachineToSummary(probeMachine, oracle, survive,
					       summary, needRemoteMacroSections,
					       potentiallyConflictingStores,
					       optIn,
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
			    
void
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
		const char *flavour = (const char *)0xf001;
		switch (cfg->flavour) {
		case CFGNode::true_target_instr:
			flavour = "true";
			break;
		case CFGNode::dupe_target_instr:
			flavour = "dupe";
			break;
		case CFGNode::ordinary_instr:
			flavour = "boring";
			break;
		}
		fprintf(f, "%s%p(%s): ", prefix, cfg, flavour);
		cfg->prettyPrint(f);
		fprintf(f, "\n");
		if (cfg->fallThrough.second)
			pending.push_back(cfg->fallThrough.second);
		for (auto it = cfg->branches.begin();
		     it != cfg->branches.end();
		     it++)
			if (it->second)
				pending.push_back(it->second);
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
		auto work = new CFGNode(rip, CFGNode::ordinary_instr);
		int x;
		for (x = 1; x < irsb->stmts_used; x++) {
			if (irsb->stmts[x]->tag == Ist_IMark) {
				work->fallThrough.first = ((IRStmtIMark *)irsb->stmts[x])->addr.rip;
				break;
			}
			if (irsb->stmts[x]->tag == Ist_Exit) {
				work->branches.push_back(
					CFGNode::successor_t(((IRStmtExit *)irsb->stmts[x])->dst.rip,
							     NULL));
			}
		}
		if (x == irsb->stmts_used) {
			if (irsb->jumpkind == Ijk_Call) {
				VexRip follower = extract_call_follower(irsb);
				if (irsb->next_is_const) {
					if (terminalFunctions.count(irsb->next_const.rip)) {
						/* Inline this function */
						work->branches.push_back(
							CFGNode::successor_t(irsb->next_const.rip, NULL));
					} else if (oracle->functionCanReturn(irsb->next_const.rip)) {
						/* Treat this function as pure. */
						work->fallThrough.first = follower;
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
					work->fallThrough.first = follower;
				}
			} else if (irsb->jumpkind == Ijk_Ret) {
				work->fallThrough.first = work->my_rip;
				work->fallThrough.first.rtrn();
			} else {
				/* Don't currently try to trace across indirect branches. */
				if (irsb->next_is_const)
					work->fallThrough.first = irsb->next_const.rip;
			}
		}
		if (work->fallThrough.first.isValid())
			needed.push(std::pair<unsigned, VexRip>(depth - 1, work->fallThrough.first));
		for (auto it = work->branches.begin(); it != work->branches.end(); it++)
			needed.push(std::pair<unsigned, VexRip>(depth - 1, it->first));
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
		node->fallThrough.second = builtSoFar[node->fallThrough.first].first;
		for (auto it = node->branches.begin(); it != node->branches.end(); it++)
			it->second = builtSoFar[it->first].first;
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
		 VexPtr<InferredInformation, &ir_heap> &crashReasons,
		 VexPtr<StateMachineState, &ir_heap> &escapeState,
		 AllowableOptimisations &opt,
		 bool simple_calls,
		 VexPtr<Oracle> &oracle,
		 GarbageCollectionToken token)
{
	std::map<ThreadRip, unsigned> accessGenerationNumbers;

	class State {
		typedef std::pair<StateMachineState **, CFGNode *> reloc_t;
		std::vector<CFGNode *> pending;
		std::vector<reloc_t> relocs;
		InferredInformation *crashReasons;
	public:
		std::map<CFGNode *, StateMachineState *> cfgToState;

		CFGNode *nextNode() {
			while (1) {
				if (pending.empty()) {
					std::vector<reloc_t> newRelocs;
					for (auto it = relocs.begin(); it != relocs.end(); it++) {
						assert(*it->first == NULL);
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

		State(InferredInformation *_crashReasons)
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
		MemoryAccessIdentifier getAccessIdentifier(const ThreadRip &rip)
		{
			/* Yay, compiler bug.  You might think that
			   we'd be better off copying the value of foo
			   into its only use, and you'd be right,
			   except that if you do that then gcc 4.4
			   forgets that first_dynamic_generation is a
			   static const and gets upset that it can't
			   find a definition anywhere.  This only
			   seems to happen with optimisations off;
			   with optimisations on either variant
			   compiles just fine. */
			unsigned foo = MemoryAccessIdentifier::first_dynamic_generation;
			auto it = accessGenerationNumbers.insert(
				std::pair<ThreadRip, unsigned>(rip, foo)).first;
			return MemoryAccessIdentifier(rip, it->second++);
		}

		StateMachineState *backtrackOneStatement(IRStmt *stmt,
							 const ThreadRip &rip,
							 CFGNode *branchTarget,
							 StateMachineState *fallThrough) {
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
					getAccessIdentifier(rip));
				break;
			case Ist_Dirty: {
				IRType ity;
				if (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
					    "helper_load_8")) {
					ity = Ity_I8;
				} else if (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
						   "helper_load_16")) {
					ity = Ity_I16;
				} else if (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
						   "helper_load_64")) {
					ity = Ity_I64;
				} else if (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
						   "helper_load_32")) {
					ity = Ity_I32;
				}  else {
					abort();
				}
				se = new StateMachineSideEffectLoad(
					((IRStmtDirty *)stmt)->details->tmp,
					((IRStmtDirty *)stmt)->details->args[0],
					getAccessIdentifier(rip),
					ity);
				break;
			}
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
							NULL,
							fallThrough);
					state.addReloc(&smb->trueTarget, branchTarget);
					return smb;
				} else {
					/* We've decided to ignore this branch */
				}
				break;
			}
			if (se)
				return new StateMachineSideEffecting(rip.rip, se, fallThrough);
			else
				return fallThrough;
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

			StateMachineSideEffectCopy *smsec =
				new StateMachineSideEffectCopy(
					threadAndRegister::reg(site.thread, OFFSET_amd64_RAX, 0),
					r);
			IRExpr **realR = &smsec->value;
			StateMachineSideEffecting *lastState =
				new StateMachineSideEffecting(
					site.rip,
					smsec,
					NULL);
			StateMachineState *headState = lastState;

			/* Pick up any temporaries calculated during
			 * the call instruction. */
			for (int i = irsb->stmts_used - 1; i >= 0; i--) {
				IRStmt *stmt = irsb->stmts[i];
				/* We ignore statements other than
				   WrTmp and Load if they happen in a
				   call instruction. */
				if (stmt->tag == Ist_Put) {
					IRStmtPut *p = (IRStmtPut *)stmt;
					if (p->target.isTemp())
						*realR = rewriteTemporary(
							*realR,
							p->target.asTemp(),
							p->data);
				}
				if (stmt->tag == Ist_Dirty) {
					IRDirty *details = ((IRStmtDirty *)stmt)->details;
					if (!strcmp(details->cee->name, "helper_load_64")) {
						headState =
							new StateMachineSideEffecting(
								site.rip,
								new StateMachineSideEffectLoad(
									details->tmp,
									details->args[0],
									getAccessIdentifier(site),
									Ity_I64),
								headState);
					} else {
						/* Other dirty calls
						   inside a call
						   instruction
						   indicate that
						   something has gone
						   wrong. */
						abort();
					}
				}
			}

			if (cfg->fallThrough.second)
				state.addReloc(&lastState->target, cfg->fallThrough.second);
			else
				lastState->target = escapeState;
			return headState;
		}
	public:
		bool simple_calls;
		unsigned tid;
		State &state;
		StateMachineState *escapeState;
		Oracle *oracle;
		std::map<ThreadRip, unsigned> &accessGenerationNumbers;
		BuildStateForCfgNode(bool _simple_calls, unsigned _tid, State &_state,
				     StateMachineState *_escapeState, Oracle *_oracle,
				     std::map<ThreadRip, unsigned> &_accessGenerationNumbers)
			: simple_calls(_simple_calls), tid(_tid), state(_state),
			  escapeState(_escapeState), oracle(_oracle),
			  accessGenerationNumbers(_accessGenerationNumbers)
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
			if (endOfInstr == irsb->stmts_used &&
			    irsb->jumpkind == Ijk_Call &&
			    (cfg->branches.empty() ||
			     cfg->branches[0].second == NULL))
				return buildStateForCallInstruction(cfg, irsb, rip);
			CFGNode *relocTo;
			StateMachineSideEffecting *lastState =
				new StateMachineSideEffecting(
					rip.rip,
					NULL,
					NULL);
			StateMachineState *res = lastState;
			
#warning Only considering a single branch here, which isn't always sufficient '
			if (endOfInstr == irsb->stmts_used && irsb->jumpkind == Ijk_Call) {
				/* We want to inline this call, in
				 * effect. */
				relocTo = cfg->branches[0].second;
			} else {
				if (!cfg->fallThrough.second && !cfg->branches.empty() && cfg->branches[0].second) {
					/* We've decided to force this one to take the
					   branch.  Trim the bit of the instruction
					   after the branch. */
					endOfInstr--;
					while (endOfInstr >= 0 && irsb->stmts[endOfInstr]->tag != Ist_Exit)
						endOfInstr--;
					assert(endOfInstr > 0);
					relocTo = cfg->branches[0].second;
				} else if (cfg->fallThrough.second) {
					relocTo = cfg->fallThrough.second;
				} else {
					relocTo = NULL;
				}
			}

			for (int i = endOfInstr - 1; i >= 0; i--) {
				res = backtrackOneStatement(irsb->stmts[i],
							    rip,
							    cfg->branches.empty() ? NULL : cfg->branches[0].second,
							    res);
				if (!res)
					return NULL;
			}
			if (relocTo)
				state.addReloc(&lastState->target, relocTo);
			else
				lastState->target = escapeState;
			return res;
		}
	} buildStateForCfgNode(simple_calls, tid, state, escapeState, oracle, accessGenerationNumbers);

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
	canonicaliseRbp(sm, oracle);
	sm = optimiseStateMachine(sm, opt, oracle, false, false, token);
	if (crashReasons)
		crashReasons->set(original_rip, sm->root);
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

void
checkWhetherInstructionCanCrash(const VexRip &rip,
				VexPtr<MachineState> &ms,
				VexPtr<Thread> &thr,
				VexPtr<Oracle> &oracle,
				FixConsumer &df,
				GarbageCollectionToken token)
{
	VexPtr<StateMachineState, &ir_heap> proximal(getProximalCause(ms, ThreadRip::mk(thr->tid._tid(), rip), thr));
	if (!proximal) {
		fprintf(_logfile, "No proximal cause -> can't do anything\n");
		return;
	}

	VexPtr<InferredInformation, &ir_heap> ii(new InferredInformation());
	ii->set(rip, proximal);

	std::vector<VexRip> previousInstructions;
	oracle->findPreviousInstructions(previousInstructions, rip);

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.setAddressSpace(oracle->ms->addressSpace);
	VexPtr<StateMachine, &ir_heap> probeMachine;
	probeMachine = buildProbeMachine(previousInstructions, ii, oracle, rip, thr->tid, opt, token);
	if (probeMachine) {
		VexPtr<CrashSummary, &ir_heap> summary;
		summary = diagnoseCrash(probeMachine, oracle, ms, false, opt, token);
		if (summary)
			df(summary, token);
	}
}

