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
#include "alloc_mai.hpp"

#define DEBUG_BUILD_STORE_CFGS 0

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

template <typename t> static void
findAllTypedSideEffects(StateMachine *sm, std::set<t *> &out)
{
	class _ : public StateMachineTransformer {
		std::set<t *> &out;
		t *transformOneSideEffect(t *smse, bool *) {
			out.insert(smse);
			return NULL;
		}
		IRExpr *transformIRExpr(IRExpr *a, bool *) {
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
	for (auto it = sm->origin.begin(); it != sm->origin.end(); it++) {
		long delta;
		if (!oracle->getRbpToRspDelta(it->second, &delta)) {
			/* Can't do anything if we don't know the
			 * delta */
			continue;
		}
		/* Got RBP->RSP delta, want RSP->RBP */
		delta = -delta;
		StateMachineSideEffect *smse =
			new StateMachineSideEffectCopy(
				threadAndRegister::reg(it->first, OFFSET_amd64_RBP, 0),
				IRExpr_Associative(
					Iop_Add64,
					IRExpr_Get(
						threadAndRegister::reg(it->first, OFFSET_amd64_RSP, 0),
						Ity_I64),
					IRExpr_Const(
						IRConst_U64(delta)),
					NULL));
		sm->root = new StateMachineSideEffecting(it->second, smse, sm->root);
	}
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
		     bool is_ssa,
		     GarbageCollectionToken token,
		     bool *progress)
{
	__set_profiling(optimiseStateMachine);
	sm->sanityCheck();
	Oracle::RegisterAliasingConfiguration alias, *aliasp;

	/* Careful here.  We can only use the aliasing configuration
	   if the machine is in SSA form, because that guarantees that
	   there won't be any writes to gen -1 registers, which in
	   turn means that a single aliasing configuration is valid
	   for the entire machine. */
	if (is_ssa && sm->origin.size() == 1) {
		alias = oracle->getAliasingConfiguration(sm->origin);
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
		sm = sm->optimise(opt, &done_something);
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
				sm = deadCodeElimination(sm, &d, opt);
				done_something |= d;
			} while (d);
		}
		sm = sm->optimise(opt, &done_something);
		sm = bisimilarityReduction(sm, opt);
		if (is_ssa)
			sm = optimiseSSA(sm, &done_something);
		if (opt.noExtend())
			sm = useInitialMemoryLoads(sm, opt, oracle, &done_something);
		sm = sm->optimise(opt, &done_something);
		if (progress)
			*progress |= done_something;
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

static StateMachine *
CFGtoStoreMachine(unsigned tid, Oracle *oracle, CFGNode *cfg,
		  MemoryAccessIdentifierAllocator &mai)
{
	StateMachine *sm = storeCFGToMachine(oracle, tid, cfg, mai);
	canonicaliseRbp(sm, oracle);
	return sm;
}

/* If there's precisely one interesting store in the store machine and
 * one interesting load in the probe machine then the whole thing
 * becomes very easy. */
static bool
singleLoadVersusSingleStore(StateMachine *storeMachine, StateMachine *probeMachine,
			    const AllowableOptimisations &opt, Oracle *oracle)
{
	std::set<StateMachineSideEffectStore *> storeMachineStores;
	std::set<StateMachineSideEffectLoad *> probeMachineLoads;
	enumSideEffects(storeMachine, storeMachineStores);
	enumSideEffects(probeMachine, probeMachineLoads);

	StateMachineSideEffectStore *racingStore = NULL;
	StateMachineSideEffectLoad *racingLoad = NULL;
	for (auto it = storeMachineStores.begin(); it != storeMachineStores.end(); it++) {
		StateMachineSideEffectStore *store = *it;
		bool races = false;
		for (auto it2 = probeMachineLoads.begin();
		     !races && it2 != probeMachineLoads.end();
		     it2++) {
			StateMachineSideEffectLoad *load = *it2;
			if (oracle->memoryAccessesMightAlias(opt, load, store)) {
				if (racingLoad) {
					/* Multiple racing loads */
					return false;
				}
				racingLoad = load;
				races = true;
			}
		}
		if (races) {
			if (racingStore) {
				/* We have multiple racing stores */
				return false;
			}
			racingStore = store;
		}
	}

	/* There must be *some* races in here, or else machine
	   construction must have gone wrong. */
	assert(racingStore != NULL);
	assert(racingLoad != NULL);

	for (auto it = probeMachineLoads.begin(); it != probeMachineLoads.end(); it++) {
		StateMachineSideEffectLoad *load = *it;
		if (racingLoad == load)
			continue;
		if (oracle->memoryAccessesMightAlias(opt, load, racingStore))
			return false;
	}

	return true;
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
	sm = duplicateStateMachine(storeMachine);
	sm = optimiseStateMachine(sm, opt, oracle, true, token);

	if (dynamic_cast<StateMachineUnreached *>(sm->root)) {
		/* This store machine is unusable, probably because we
		 * don't have the machine code for the relevant
		 * library */
		fprintf(_logfile, "\t\tStore machine is unusable\n");
		return false;
	}

	fprintf(_logfile, "\t\tStore machine:\n");
	printStateMachine(sm, _logfile);

	/* Special case: if the only possible interaction between the
	   probe machine and the store machine is a single load in the
	   probe machine and a single store in the store machine then
	   we don't need to do anything. */
	if (singleLoadVersusSingleStore(storeMachine, probeMachine, opt, oracle)) {
		fprintf(_logfile, "\t\tSingle store versus single load -> crash impossible.\n");
		return false;
	}

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
		writeMachineConstraint,
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
		 MemoryAccessIdentifierAllocator &mai,
		 GarbageCollectionToken token)
{
	__set_profiling(considerStoreCFG);
	AllowableOptimisations opt =
		optIn
		.enableassumeNoInterferingStores();
	VexPtr<StateMachine, &ir_heap> sm(CFGtoStoreMachine(tid, oracle, cfg, mai));
	if (!sm) {
		fprintf(_logfile, "Cannot build store machine!\n");
		return true;
	}
	opt = opt.setinterestingStores(&is);
	sm = optimiseStateMachine(sm, opt, oracle, false, token);

	VexPtr<StateMachine, &ir_heap> sm_ssa(convertToSSA(sm));
	if (!sm_ssa)
		return false;

	IRExpr *_newAssumption;
	StateMachine *_sm;
	if (!determineWhetherStoreMachineCanCrash(sm_ssa, probeMachine, oracle, assumption, opt, token, &_newAssumption, &_sm)) {
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

bool
buildProbeMachine(VexPtr<Oracle> &oracle,
		  const DynAnalysisRip &targetRip,
		  VexPtr<StateMachineState, &ir_heap> &proximal,
		  ThreadId tid,
		  const AllowableOptimisations &optIn,
		  StateMachine ***out,
		  unsigned *nr_out_machines,
		  MemoryAccessIdentifierAllocator &mai,
		  GarbageCollectionToken token)
{
	__set_profiling(buildProbeMachine);

	*nr_out_machines = 0;

	AllowableOptimisations opt =
		optIn
		.enableignoreSideEffects();

	VexPtr<StateMachine *, &ir_heap> sms;
	unsigned nr_sms;
	{
		std::set<CFGNode *> roots;
		if (!getProbeCFGs(oracle, targetRip, roots)) {
			fprintf(_logfile, "Cannot get probe CFGs!\n");
			return false;
		}
		std::set<StateMachine *> machines;
		probeCFGsToMachine(oracle, tid._tid(), roots, targetRip, proximal, mai, machines);
		sms = (StateMachine **)__LibVEX_Alloc_Ptr_Array(&ir_heap, machines.size());
		nr_sms = 0;
		for (auto it = machines.begin(); it != machines.end(); it++) {
			sms[nr_sms] = *it;
			nr_sms++;
		}
	}
	if (TIMEOUT)
		return false;

	LibVEX_maybe_gc(token);

	for (unsigned x = 0; x < nr_sms; x++) {
		VexPtr<StateMachine, &ir_heap> sm(sms[x]);
		sm->sanityCheck();

		canonicaliseRbp(sm, oracle);
		sm = optimiseStateMachine(sm,
					  opt,
					  oracle,
					  false,
					  token);

		sm = convertToSSA(sm);
		if (TIMEOUT)
			return false;
		sm->sanityCheck();
		sm = optimiseStateMachine(sm,
					  opt,
					  oracle,
					  true,
					  token);

		sms[x] = sm;
	}

	*out = (StateMachine **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_sms);
	for (unsigned x = 0; x < nr_sms; x++)
		(*out)[x] = sms[x];
	*nr_out_machines = nr_sms;
	return true;
}

static bool
isSingleNodeCfg(CFGNode *root)
{
	return root->fallThrough.second == NULL && root->branches.empty();
}

static bool
machineHasOneRacingLoad(StateMachine *sm, const VexRip &vr, Oracle *oracle)
{
	std::set<StateMachineSideEffectLoad *> loads;
	enumSideEffects(sm, loads);
	bool got_one = false;
	for (auto it = loads.begin(); it != loads.end(); it++) {
		StateMachineSideEffectLoad *load = *it;
		if (oracle->memoryAccessesMightAliasCrossThread(load->rip.rip.rip, vr)) {
			if (got_one)
				return false;
			got_one = true;
		}
	}
	/* If there are no racing loads at all then something has gone
	   wrong building the machines. */
	assert(got_one);
	return true;
}

static bool
probeMachineToSummary(VexPtr<StateMachine, &ir_heap> &probeMachine,
		      VexPtr<Oracle> &oracle,
		      VexPtr<IRExpr, &ir_heap> &survive,
		      VexPtr<CrashSummary, &ir_heap> &summary,
		      bool needRemoteMacroSections,
		      std::set<DynAnalysisRip> &potentiallyConflictingStores,
		      const AllowableOptimisations &optIn,
		      const MemoryAccessIdentifierAllocator &mai,
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
		bool singleNodeCfg = isSingleNodeCfg(storeCFGs[i]);
		if (roughLoadCount == StateMachineState::singleLoad && singleNodeCfg) {
			fprintf(_logfile, "Single store versus single load -> no race possible\n");
			continue;
		}

		if (singleNodeCfg &&
		    machineHasOneRacingLoad(probeMachine, storeCFGs[i]->my_rip, oracle)) {
			fprintf(_logfile, "Single store versus single shared load -> no race possible\n");
			continue;
		}

		VexPtr<CFGNode, &ir_heap> storeCFG(storeCFGs[i]);
		MemoryAccessIdentifierAllocator storeMai(mai);
		foundRace |= considerStoreCFG(storeCFG,
					      oracle,
					      survive,
					      probeMachine,
					      summary,
					      potentiallyConflictingStores,
					      needRemoteMacroSections,
					      STORING_THREAD + i,
					      optIn,
					      storeMai,
					      token);
	}

	return foundRace;
}

static StateMachine *
duplicateStateMachineNoAssertions(StateMachine *inp, bool *done_something)
{
	struct : public StateMachineTransformer {
		StateMachineSideEffecting *transformOneState(
			StateMachineSideEffecting *a, bool *done_something)
		{
			if (a->sideEffect && a->sideEffect->type == StateMachineSideEffect::AssertFalse) {
				*done_something = true;
				return new StateMachineSideEffecting(a->origin, NULL, a->target);
			} else {
				return NULL;
			}
		}
		IRExpr *transformIRExpr(IRExpr *, bool *) {
			return NULL;
		}
	} doit;
	return doit.transform(inp, done_something);
}

CrashSummary *
diagnoseCrash(VexPtr<StateMachine, &ir_heap> &probeMachine,
	      VexPtr<Oracle> &oracle,
	      bool needRemoteMacroSections,
	      const AllowableOptimisations &optIn,
	      const MemoryAccessIdentifierAllocator &mai,
	      GarbageCollectionToken token)
{
	__set_profiling(diagnoseCrash);
	fprintf(_logfile, "Probe machine:\n");
	printStateMachine(probeMachine, _logfile);
	fprintf(_logfile, "\n");

	std::set<DynAnalysisRip> potentiallyConflictingStores;
	{
		/* If the only reason a load is live is to evaluate a
		   later assertion, it doesn't count for the purposes
		   of computing potentiallyConflictingStores.  The
		   easy way of dealing with that is just to remove
		   them and then re-optimise the machine. */
		VexPtr<StateMachine, &ir_heap> reducedProbeMachine(probeMachine);
		/* Iterate to make sure we get rid of any assertions
		   introduced by the optimiser itself. */
		while (!TIMEOUT) {
			bool done_something = false;
			reducedProbeMachine = duplicateStateMachineNoAssertions(reducedProbeMachine, &done_something);
			if (!done_something)
				break;
			done_something = false;
			reducedProbeMachine = optimiseStateMachine(
				reducedProbeMachine,
				optIn.enableignoreSideEffects(),
				oracle, true, token, &done_something);
			if (!done_something)
				break;
		}
		if (TIMEOUT)
			return NULL;
		getConflictingStores(reducedProbeMachine, oracle, potentiallyConflictingStores);
	}
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
			.enableassumeNoInterferingStores()
			.enableassumeExecutesAtomically()
			.enablenoExtend();
		VexPtr<StateMachine, &ir_heap> atomicProbeMachine;
		atomicProbeMachine = duplicateStateMachine(probeMachine);
		atomicProbeMachine = optimiseStateMachine(atomicProbeMachine, opt, oracle,
							  true, token);
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
					       mai,
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
remoteMacroSectionsT::iterator::operator++(int)
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
checkWhetherInstructionCanCrash(const DynAnalysisRip &targetRip,
				unsigned tid,
				VexPtr<Oracle> &oracle,
				FixConsumer &df,
				GarbageCollectionToken token)
{
	MemoryAccessIdentifierAllocator mai;
	VexPtr<StateMachineState, &ir_heap> proximal(getProximalCause(oracle->ms, ThreadRip::mk(tid, targetRip.toVexRip()), mai));
	if (!proximal) {
		fprintf(_logfile, "No proximal cause -> can't do anything\n");
		return;
	}

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.setAddressSpace(oracle->ms->addressSpace);
	VexPtr<StateMachine *, &ir_heap> probeMachines;
	unsigned nrProbeMachines;
	{
		StateMachine **_probeMachines;
		if (!buildProbeMachine(oracle, targetRip, proximal, tid, opt, &_probeMachines, &nrProbeMachines, mai, token))
			return;
		probeMachines = _probeMachines;
	}
	for (unsigned x = 0; x < nrProbeMachines; x++) {
		VexPtr<CrashSummary, &ir_heap> summary;
		VexPtr<StateMachine, &ir_heap> probeMachine(probeMachines[x]);
		summary = diagnoseCrash(probeMachine, oracle, false, opt, mai, token);
		if (summary)
			df(summary, token);
	}
}

