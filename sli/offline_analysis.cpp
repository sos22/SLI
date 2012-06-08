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
#include "sat_checker.hpp"
#include "allowable_optimisations.hpp"

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
		bool rewriteNewStates() const { return false; }
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
removeSurvivingStates(StateMachine *sm, const AllowableOptimisations &opt, bool *done_something)
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
			if (s->getSideEffect() &&
			    s->getSideEffect()->type == StateMachineSideEffect::AssertFalse &&
			    opt.preferCrash())
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
	sm->assertAcyclic();
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
			removeSurvivingStates(sm, opt, &done_something);
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
		if (opt.noLocalSurvival())
			sm = removeLocalSurvival(sm, opt, &done_something);
		sm = sm->optimise(opt, &done_something);
		if (progress)
			*progress |= done_something;
	} while (done_something);
	sm->assertAcyclic();
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

	/* We can sometimes find that there are no races possible
	   between the two machines.  The most common reason for this
	   is that the dynamic aliasing analysis divides memory up
	   into 8-byte chunks, and considers two operations to alias
	   if they hit the same chunk.  That's not completely valid
	   for sub-word accesses, and so we can end up with the
	   aliasing table saying that two accesses alias even when
	   they provably can't.  That shows up here when we generate
	   two machines which provably don't interact. */
	if (!racingStore) {
		assert(!racingLoad);
		return true;
	}
	assert(racingLoad);

	for (auto it = probeMachineLoads.begin(); it != probeMachineLoads.end(); it++) {
		StateMachineSideEffectLoad *load = *it;
		if (racingLoad == load)
			continue;
		if (oracle->memoryAccessesMightAlias(opt, load, racingStore))
			return false;
	}

	return true;
}


static IRExpr *
atomicSurvivalConstraint(VexPtr<StateMachine, &ir_heap> &machine,
			 StateMachine **_atomicMachine,
			 VexPtr<Oracle> &oracle,
			 const AllowableOptimisations &opt,
			 GarbageCollectionToken token)
{
	VexPtr<StateMachine, &ir_heap> atomicMachine;
	atomicMachine = duplicateStateMachine(machine);
	atomicMachine = optimiseStateMachine(atomicMachine, opt, oracle, true, token);
	VexPtr<IRExpr, &ir_heap> nullexpr(NULL);
	IRExpr *survive = survivalConstraintIfExecutedAtomically(atomicMachine, nullexpr, oracle, false, opt, token);
	if (!survive) {
		fprintf(_logfile, "\tTimed out computing survival constraint\n");
		return NULL;
	}
	survive = simplifyIRExpr(survive, opt);

	if (_atomicMachine)
		*_atomicMachine = atomicMachine;
	return survive;
}

static AllowableOptimisations
atomicSurvivalOptimisations(const AllowableOptimisations &opt)
{
	return opt
		.enableignoreSideEffects()
		.enableassumeNoInterferingStores()
		.enableassumeExecutesAtomically()
		.enablenoExtend();
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
		bool rewriteNewStates() const { return false; }
	} doit;
	return doit.transform(inp, done_something);
}

StateMachine *
removeAssertions(StateMachine *_sm, const AllowableOptimisations &opt, VexPtr<Oracle> &oracle,
		 bool is_ssa, GarbageCollectionToken token)
{
	VexPtr<StateMachine, &ir_heap> sm(_sm);
	/* Iterate to make sure we get rid of any assertions
	   introduced by the optimiser itself. */
	while (1) {
		if (TIMEOUT)
			return NULL;
		bool done_something = false;
		sm = duplicateStateMachineNoAssertions(sm, &done_something);
		if (!done_something)
			break;
		done_something = false;
		sm = optimiseStateMachine(sm, opt, oracle, is_ssa,
					  token, &done_something);
		if (!done_something)
			break;
	}
	return sm;
}
      
static IRExpr *
verificationConditionForStoreMachine(VexPtr<StateMachine, &ir_heap> &storeMachine,
				     VexPtr<StateMachine, &ir_heap> probeMachine,
				     VexPtr<Oracle> &oracle,
				     const AllowableOptimisations &optIn,
				     GarbageCollectionToken token)
{
	__set_profiling(verificationConditionForStoreMachine);
	AllowableOptimisations storeOptimisations =
		optIn.
		   enableassumeExecutesAtomically().
		   enableassumeNoInterferingStores();
	AllowableOptimisations probeOptimisations =
		optIn.
		   enableignoreSideEffects();

	VexPtr<StateMachine, &ir_heap> sm;
	sm = duplicateStateMachine(storeMachine);
	sm = optimiseStateMachine(sm, storeOptimisations, oracle, true, token);

	if (dynamic_cast<StateMachineUnreached *>(sm->root)) {
		/* This store machine is unusable, probably because we
		 * don't have the machine code for the relevant
		 * library */
		fprintf(_logfile, "\t\tStore machine is unusable\n");
		return NULL;
	}

	fprintf(_logfile, "\t\tStore machine:\n");
	printStateMachine(sm, _logfile);

	probeMachine = optimiseStateMachine(probeMachine, probeOptimisations, oracle, true, token);

	fprintf(_logfile, "\t\tAssertion-free probe machine:\n");
	printStateMachine(probeMachine, _logfile);

	/* Special case: if the only possible interaction between the
	   probe machine and the store machine is a single load in the
	   probe machine and a single store in the store machine then
	   we don't need to do anything. */
	if (singleLoadVersusSingleStore(storeMachine, probeMachine, optIn, oracle)) {
		fprintf(_logfile, "\t\tSingle store versus single load -> crash impossible.\n");
		return NULL;
	}

	VexPtr<IRExpr, &ir_heap> assumption;
	assumption = atomicSurvivalConstraint(probeMachine, NULL, oracle,
					      atomicSurvivalOptimisations(probeOptimisations.enablepreferCrash()),
					      token);
	if (!assumption)
		return NULL;

	VexPtr<IRExpr, &ir_heap> writeMachineConstraint(
		writeMachineCrashConstraint(sm,
					    IRExpr_Const(IRConst_U1(0)),
					    assumption,
					    IRExpr_Const(IRConst_U1(0)),
					    storeOptimisations));
	if (!writeMachineConstraint) {
		fprintf(_logfile, "\t\tCannot derive write machine crash constraint\n");
		return NULL;
	}

	assumption = writeMachineSuitabilityConstraint(
		sm,
		probeMachine,
		oracle,
		writeMachineConstraint,
		optIn.enablepreferCrash(),
		token);

	if (!assumption) {
		fprintf(_logfile, "\t\tCannot derive write machine suitability constraint\n");
		return NULL;
	}

	/* Figure out when the cross product machine will be at risk
	 * of crashing. */
	IRExpr *crash_constraint =
		crossProductSurvivalConstraint(
			probeMachine,
			sm,
			oracle,
			assumption,
			optIn.disablepreferCrash(),
			token);
	if (!crash_constraint) {
		fprintf(_logfile, "\t\tfailed to build crash constraint\n");
		return NULL;
	}

	/* And we hope that that will lead to a contradiction when
	   combined with the assumption.  The verification condition
	   is (assumption) & ~(crash_condition), and is 1 in precisely
	   those states which might suffer a bug of the desired
	   kind. */
	IRExpr *verification_condition =
		IRExpr_Binop(
			Iop_And1,
			assumption,
			IRExpr_Unop(
				Iop_Not1,
				crash_constraint));
	verification_condition = simplifyIRExpr(verification_condition, optIn);
	
	return verification_condition;
}

static StateMachine *
truncateStateMachine(StateMachine *sm, StateMachineSideEffectMemoryAccess *truncateAt)
{
	StateMachineBifurcate *smb =
		new StateMachineBifurcate(
			truncateAt->rip.rip.rip,
			IRExpr_Unop(
				Iop_BadPtr,
				truncateAt->addr),
			StateMachineCrash::get(),
			StateMachineNoCrash::get());
	std::map<const StateMachineState *, StateMachineState *> rewriteRules;
	std::set<StateMachineSideEffecting *> s;
	enumStates(sm, &s);
	for (auto it = s.begin(); it != s.end(); it++) {
		if ((*it)->getSideEffect() == truncateAt)
			rewriteRules[*it] = smb;
	}
	StateMachineTransformer::rewriteMachine(sm, rewriteRules, false);
	assert(rewriteRules.count(sm->root));
	assert(rewriteRules[sm->root] != sm->root);
	return new StateMachine(rewriteRules[sm->root], sm->origin);
}

static void
logUseOfInduction(const DynAnalysisRip &used_in, const DynAnalysisRip &used)
{
	static FILE *inductionLog;
	if (!inductionLog) {
		inductionLog = fopen("induction.log", "a");
		if (!inductionLog)
			err(1, "cannot open induction log");
		setlinebuf(inductionLog);
	}
	fprintf(inductionLog, "%s -> %s\n", used.name(), used_in.name());
}

static StateMachine *
localiseLoads(VexPtr<StateMachine, &ir_heap> &probeMachine,
	      VexPtr<StateMachine, &ir_heap> &storeMachine,
	      const AllowableOptimisations &opt,
	      VexPtr<Oracle> &oracle,
	      GarbageCollectionToken token,
	      bool *done_something = NULL)
{
	std::set<DynAnalysisRip> nonLocalLoads;
	{
		std::set<StateMachineSideEffectStore *> stores;
		enumSideEffects(storeMachine, stores);
		std::set<StateMachineSideEffectLoad *> loads;
		enumSideEffects(probeMachine, loads);
		for (auto it = loads.begin(); it != loads.end(); it++) {
			StateMachineSideEffectLoad *load = *it;
			bool found_one = false;
			for (auto it2 = stores.begin(); !found_one && it2 != stores.end(); it2++) {
				StateMachineSideEffectStore *store = *it2;
				if (oracle->memoryAccessesMightAlias(opt, load, store))
					found_one = true;
			}
			if (found_one)
				nonLocalLoads.insert(DynAnalysisRip(load->rip.rip.rip));
		}
	}
	return optimiseStateMachine(
		probeMachine,
		opt.setnonLocalLoads(&nonLocalLoads),
		oracle,
		true,
		token,
		done_something);
}

static StateMachine *
localiseLoads(VexPtr<StateMachine, &ir_heap> &probeMachine,
	      const std::set<DynAnalysisRip> &stores,
	      const AllowableOptimisations &opt,
	      VexPtr<Oracle> &oracle,
	      GarbageCollectionToken token,
	      bool *done_something = NULL)
{
	std::set<DynAnalysisRip> nonLocalLoads;
	{
		std::set<StateMachineSideEffectLoad *> loads;
		enumSideEffects(probeMachine, loads);
		for (auto it = loads.begin(); it != loads.end(); it++) {
			StateMachineSideEffectLoad *load = *it;
			bool found_one = false;
			for (auto it2 = stores.begin(); !found_one && it2 != stores.end(); it2++) {
				DynAnalysisRip store = *it2;
				if (oracle->memoryAccessesMightAliasCrossThread(DynAnalysisRip(load->rip.rip.rip), store))
					found_one = true;
			}
			if (found_one)
				nonLocalLoads.insert(DynAnalysisRip(load->rip.rip.rip));
		}
	}
	return optimiseStateMachine(
		probeMachine,
		opt.setnonLocalLoads(&nonLocalLoads),
		oracle,
		true,
		token,
		done_something);
}

static CrashSummary *
considerStoreCFG(const DynAnalysisRip &target_rip,
		 VexPtr<CFGNode, &ir_heap> cfg,
		 VexPtr<Oracle> &oracle,
		 VexPtr<StateMachine, &ir_heap> probeMachine,
		 bool needRemoteMacroSections,
		 unsigned tid,
		 const AllowableOptimisations &optIn,
		 MemoryAccessIdentifierAllocator &mai,
		 GarbageCollectionToken token)
{
	__set_profiling(considerStoreCFG);
	VexPtr<StateMachine, &ir_heap> sm(CFGtoStoreMachine(tid, oracle, cfg, mai));
	if (!sm) {
		fprintf(_logfile, "Cannot build store machine!\n");
		return NULL;
	}
	sm = optimiseStateMachine(
		sm,
		optIn.
		       enableassumeNoInterferingStores().
		       enableassumeExecutesAtomically(),
		oracle,
		false,
		token);

	VexPtr<StateMachine, &ir_heap> sm_ssa(convertToSSA(sm));
	if (!sm_ssa)
		return NULL;

	sm_ssa = optimiseStateMachine(
		sm_ssa,
		optIn.enableassumeExecutesAtomically().enableassumeNoInterferingStores(),
		oracle,
		true,
		token);
	probeMachine = duplicateStateMachine(probeMachine);
	probeMachine = localiseLoads(probeMachine,
				     sm_ssa,
				     optIn.enableignoreSideEffects(),
				     oracle,
				     token);

	VexPtr<IRExpr, &ir_heap> base_verification_condition(
		verificationConditionForStoreMachine(
			sm_ssa,
			probeMachine,
			oracle,
			optIn,
			token));
	if (!base_verification_condition)
		return NULL;

	fprintf(_logfile, "\t\tBase verification condition: ");
	ppIRExpr(base_verification_condition, _logfile);
	fprintf(_logfile, "\n");

	if (!satisfiable(base_verification_condition, optIn)) {
		fprintf(_logfile, "\t\tCrash impossible.\n");
		return NULL;
	}

	/* Now have a look at whether we have anything we can use the
	 * induction rule on.  That means look at the probe machine
	 * and pulling out all of the loads which are present in the
	 * type index and then just assuming that we won't generate
	 * any crash summaries for them.  Once we've processed every
	 * instruction we have to go back and look for any cycles. */
	VexPtr<StateMachineSideEffectMemoryAccess *, &ir_heap> inductionAccesses;
	unsigned nrInductionAccesses;
	{
		std::set<StateMachineSideEffectMemoryAccess *> probeAccesses;
		enumSideEffects(probeMachine, probeAccesses);
		std::set<StateMachineSideEffectMemoryAccess *> typeDbProbeAccesses;
		for (auto it = probeAccesses.begin(); it != probeAccesses.end(); it++) {
			DynAnalysisRip dr((*it)->rip.rip.rip);
			if (oracle->type_index->ripPresent(dr))
				typeDbProbeAccesses.insert(*it);
		}
		inductionAccesses = (StateMachineSideEffectMemoryAccess **)__LibVEX_Alloc_Ptr_Array(&ir_heap, typeDbProbeAccesses.size());
		auto it = typeDbProbeAccesses.begin();
		nrInductionAccesses = 0;
		while (it != typeDbProbeAccesses.end()) {
			inductionAccesses[nrInductionAccesses] = *it;
			nrInductionAccesses++;
			it++;
		}
		assert(nrInductionAccesses == typeDbProbeAccesses.size());
	}
	VexPtr<IRExpr, &ir_heap> residual_verification_condition(base_verification_condition);
	std::set<DynAnalysisRip> inductionRips;
	for (unsigned x = 0; x < nrInductionAccesses; x++) {
		if (TIMEOUT)
			return NULL;
		VexPtr<StateMachine, &ir_heap> truncatedMachine(
			truncateStateMachine(
				probeMachine,
				inductionAccesses[x]));
		truncatedMachine = optimiseStateMachine(truncatedMachine, optIn, oracle, true, token);
		IRExpr *t = verificationConditionForStoreMachine(
			sm_ssa,
			truncatedMachine,
			oracle,
			optIn,
			token);
		if (!t || t == residual_verification_condition ||
		    (t->tag == Iex_Const &&
		     ((IRExprConst *)t)->con->Ico.U1 == 0))
			continue;
		fprintf(_logfile, "Induction probe machine:\n");
		printStateMachine(truncatedMachine, _logfile);
		fprintf(_logfile, "Induction rule: ");
		ppIRExpr(t, _logfile);
		fprintf(_logfile, "\n");
		fprintf(_logfile, "Residual:       ");
		ppIRExpr(residual_verification_condition, _logfile);
		fprintf(_logfile, "\n");
		residual_verification_condition =
			IRExpr_Binop(
				Iop_And1,
				residual_verification_condition,
				IRExpr_Unop(
					Iop_Not1,
					t));
		residual_verification_condition =
			simplifyIRExpr(residual_verification_condition, optIn);
		fprintf(_logfile, "After simplification: ");
		ppIRExpr(residual_verification_condition, _logfile);
		fprintf(_logfile, "\n");
		logUseOfInduction(
			target_rip,
			DynAnalysisRip(inductionAccesses[x]->rip.rip.rip));
		if (residual_verification_condition->tag == Iex_Const &&
		    ((IRExprConst *)residual_verification_condition.get())->con->Ico.U1 == 0) {
			fprintf(_logfile, "\t\tCrash impossible.\n");
			return NULL;
		}
	}

	/* Okay, final check: is the verification condition satisfiable? */
	if (!satisfiable(residual_verification_condition, optIn)) {
		fprintf(_logfile, "\t\tVerification condition is unsatisfiable -> no bug\n");
		return NULL;
	}

	/* Okay, the expanded machine crashes.  That means we have to
	 * generate a fix. */
	VexPtr<CrashSummary, &ir_heap> res(new CrashSummary(probeMachine, sm, residual_verification_condition));
	if (needRemoteMacroSections) {
		VexPtr<remoteMacroSectionsT, &ir_heap> remoteMacroSections(new remoteMacroSectionsT);
		if (!findRemoteMacroSections(probeMachine, sm, residual_verification_condition,
					     oracle, optIn, remoteMacroSections, token)) {
			fprintf(_logfile, "\t\tChose a bad write machine...\n");
			return NULL;
		}
		if (!fixSufficient(sm, probeMachine, residual_verification_condition,
				   oracle, optIn, remoteMacroSections, token)) {
			fprintf(_logfile, "\t\tHave a fix, but it was insufficient...\n");
			return NULL;
		}
		for (remoteMacroSectionsT::iterator it = remoteMacroSections->begin();
		     it != remoteMacroSections->end();
		     it++)
			res->macroSections.push_back(CrashSummary::macroSectionT(it->start, it->end));
	}

	return res;
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
probeMachineToSummary(const DynAnalysisRip &targetRip,
		      VexPtr<StateMachine, &ir_heap> &probeMachine,
		      VexPtr<StateMachine, &ir_heap> &assertionFreeProbeMachine,
		      VexPtr<Oracle> &oracle,
		      FixConsumer &df,
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

	auto roughLoadCount = assertionFreeProbeMachine->root->roughLoadCount();

	bool foundRace;
	foundRace = false;
	for (int i = 0; i < nrStoreCfgs; i++) {
		bool singleNodeCfg = isSingleNodeCfg(storeCFGs[i]);
		if (roughLoadCount == StateMachineState::singleLoad && singleNodeCfg) {
			fprintf(_logfile, "Single store versus single load -> no race possible\n");
			continue;
		}

		if (singleNodeCfg &&
		    machineHasOneRacingLoad(assertionFreeProbeMachine, storeCFGs[i]->my_rip, oracle)) {
			fprintf(_logfile, "Single store versus single shared load -> no race possible\n");
			continue;
		}

		VexPtr<CFGNode, &ir_heap> storeCFG(storeCFGs[i]);
		MemoryAccessIdentifierAllocator storeMai(mai);
		VexPtr<CrashSummary, &ir_heap> summary;

		summary = considerStoreCFG(targetRip,
					   storeCFG,
					   oracle,
					   probeMachine,
					   needRemoteMacroSections,
					   STORING_THREAD + i,
					   optIn.setinterestingStores(&potentiallyConflictingStores),
					   storeMai,
					   token);
		if (summary)
			df(summary, token);
	}

	return foundRace;
}

bool
diagnoseCrash(const DynAnalysisRip &targetRip,
	      VexPtr<StateMachine, &ir_heap> &probeMachine,
	      VexPtr<Oracle> &oracle,
	      FixConsumer &df,
	      bool needRemoteMacroSections,
	      const AllowableOptimisations &optIn,
	      const MemoryAccessIdentifierAllocator &mai,
	      GarbageCollectionToken token)
{
	__set_profiling(diagnoseCrash);

	fprintf(_logfile, "Probe machine:\n");
	printStateMachine(probeMachine, _logfile);
	fprintf(_logfile, "\n");

	/* We now need to figure out which stores are potentially
	   conflicting, and hence which loads can be safely localised.
	   The conflicting stores are those which might alias with
	   loads issued by the probe machine, and loads can be
	   localised if they do not conflict with stores issued by the
	   probe machine.

	   Subtlty: we want to exclude loads of values which are only
	   used to satisfy assertions when we're calculating the
	   potentially conflicting store set (the later analysis
	   phases should be able to avoid generating summaries for
	   them, but it's faster to filter them out now).  The easiest
	   way of doing so is simply to remove the assertions and
	   optimise the probe machine before calculating it.

	   Subtlty 2: localisation can sometimes enable other
	   simplifications in the state machine optimiser, which can
	   (very occasionally) show that a particular load is not
	   interesting, and hence change the conflicting stores set.
	   Avoid the issue by just iterating to a fixed point. */
	std::set<DynAnalysisRip> potentiallyConflictingStores;
	VexPtr<StateMachine, &ir_heap> reducedProbeMachine(probeMachine);

	reducedProbeMachine = removeAssertions(probeMachine, optIn.enableignoreSideEffects(), oracle, true, token);
	if (!reducedProbeMachine)
		return NULL;
	getConflictingStores(reducedProbeMachine, oracle, potentiallyConflictingStores);
	if (potentiallyConflictingStores.size() == 0) {
		fprintf(_logfile, "\t\tNo available conflicting stores?\n");
		return NULL;
	}
	bool localised_loads = false;
	probeMachine = localiseLoads(probeMachine,
				     potentiallyConflictingStores,
				     optIn.enableignoreSideEffects(),
				     oracle,
				     token,
				     &localised_loads);
	if (localised_loads) {
		std::set<DynAnalysisRip> newPotentiallyConflictingStores;
		while (1) {
			reducedProbeMachine = removeAssertions(probeMachine, optIn.enableignoreSideEffects(), oracle, true, token);
			if (!reducedProbeMachine)
				return NULL;
			getConflictingStores(reducedProbeMachine, oracle, newPotentiallyConflictingStores);
			if (potentiallyConflictingStores.size() == 0) {
				fprintf(_logfile, "\t\tNo available conflicting stores?\n");
				return NULL;
			}
			if (newPotentiallyConflictingStores == potentiallyConflictingStores)
				break;
			potentiallyConflictingStores = newPotentiallyConflictingStores;
			localised_loads = false;
			probeMachine = localiseLoads(probeMachine,
						     potentiallyConflictingStores,
						     optIn.enableignoreSideEffects(),
						     oracle, token, &localised_loads);
			if (!localised_loads)
				break;
		}
	}

	if (potentiallyConflictingStores.size() == 0) {
		fprintf(_logfile, "\t\tNo available conflicting stores after localisation?\n");
		return NULL;
	}

	return probeMachineToSummary(targetRip,
				     probeMachine,
				     reducedProbeMachine,
				     oracle,
				     df,
				     needRemoteMacroSections,
				     potentiallyConflictingStores,
				     optIn,
				     mai,
				     token);
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
		.setAddressSpace(oracle->ms->addressSpace)
		.enablenoExtend();
	VexPtr<StateMachine *, &ir_heap> probeMachines;
	unsigned nrProbeMachines;
	{
		StateMachine **_probeMachines;
		if (!buildProbeMachine(oracle, targetRip, proximal, tid, opt, &_probeMachines, &nrProbeMachines, mai, token))
			return;
		probeMachines = _probeMachines;
	}
	for (unsigned x = 0; x < nrProbeMachines; x++) {
		VexPtr<StateMachine, &ir_heap> probeMachine(probeMachines[x]);
		diagnoseCrash(targetRip, probeMachine, oracle,
			      df, false, opt.enablenoLocalSurvival(),
			      mai, token);
	}
}

