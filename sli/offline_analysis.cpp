/* A load of random stuff which doesn't really belong anywhere. */
#include <limits.h>
#include <queue>
#include <sys/time.h>

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
#include "control_domination_map.hpp"

#ifndef NDEBUG
static bool debugOptimiseStateMachine = false;
#else
#define debugOptimiseStateMachine false
#endif

/* Find all of the states which definitely reach <survive> rather than
   <crash> and reduce them to just <survive> */
static void
removeSurvivingStates(StateMachine *sm, const AllowableOptimisations &opt, bool *done_something)
{
	std::set<StateMachineState *> survivingStates;
	std::set<StateMachineState *> allStates;
	bool progress;
	enumStates(sm, &survivingStates);
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

static StateMachine *
enforceMustStoreBeforeCrash(StateMachine *sm, bool *progress)
{
	/* We're not allowed to branch from state X to state Crash if
	   there's no way for the machine to issue a store before
	   reaching X.  Turn all such branches into branches to state
	   Survive. */
	std::set<StateMachineState *> storeStates;
	std::vector<StateMachineState *> todo;
	{
		std::set<StateMachineSideEffecting *> s;
		enumStates(sm, &s);
		for (auto it = s.begin(); it != s.end(); it++) {
			if ( (*it)->getSideEffect() &&
			     (*it)->getSideEffect()->type == StateMachineSideEffect::Store )
				todo.push_back(*it);
		}
	}
	while (!todo.empty()) {
		StateMachineState *s = todo.back();
		todo.pop_back();
		if (!storeStates.insert(s).second)
			continue;
		std::vector<StateMachineState *> targets;
		s->targets(targets);
		todo.insert(todo.end(), targets.begin(), targets.end());
	}
	std::set<StateMachineState *> allStates;
	enumStates(sm, &allStates);
	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		StateMachineState *s = *it;
		if (storeStates.count(s))
			continue;
		std::vector<StateMachineState **> targets;
		s->targets(targets);
		for (auto it = targets.begin(); it != targets.end(); it++) {
			if (**it == StateMachineCrash::get()) {
				*progress = true;
				**it = StateMachineNoCrash::get();
			}
		}
	}
	return sm;
}

/* Find any stores which definitely aren't loaded by this machine and
 * remove them.  This is kind of redundant with realias, except that
 * here we don't rely on havign access to stack layout information. */
static StateMachine *
removeTerminalStores(const MaiMap &mai,
		     StateMachine *sm,
		     const AllowableOptimisations &opt,
		     OracleInterface *oracle,
		     bool *done_something)
{
	std::set<StateMachineSideEffecting *> states;
	enumStates(sm, &states);
	for (auto it = states.begin(); it != states.end(); it++) {
		StateMachineSideEffect *se = (*it)->sideEffect;
		if (!se || se->type != StateMachineSideEffect::Store)
			continue;
		StateMachineSideEffectStore *store = (StateMachineSideEffectStore *)se;
		bool mightBeLoaded = false;
		std::queue<StateMachineState *> q;
		((StateMachineState *)(*it))->targets(q);
		while (!mightBeLoaded && !q.empty()) {
			StateMachineState *s = q.front();
			q.pop();
			if (s->getSideEffect() &&
			    s->getSideEffect()->type == StateMachineSideEffect::Load &&
			    oracle->memoryAccessesMightAlias(
				    mai,
				    opt,
				    (StateMachineSideEffectLoad *)s->getSideEffect(),
				    store) &&
			    !definitelyNotEqual(store->addr,
						((StateMachineSideEffectLoad *)s->getSideEffect())->addr,
						opt)) {
				/* This load might load the store. */
				mightBeLoaded = true;
			} else if (s->getSideEffect() &&
				   s->getSideEffect()->type == StateMachineSideEffect::Store &&
				   oracle->memoryAccessesMightAlias(
					   mai,
					   opt,
					   (StateMachineSideEffectStore *)s->getSideEffect(),
					   store) &&
				   definitelyEqual(store->addr,
						   ((StateMachineSideEffectStore *)s->getSideEffect())->addr,
						   opt)) {
				/* This store will clobber the results
				   of the store we're looking at -> it
				   can't be loaded on this path ->
				   don't look at successors. */
			} else {
				s->targets(q);
			}
		}
		if (!mightBeLoaded) {
			*done_something = true;
			(*it)->sideEffect = NULL;
		}
	}
	return sm;
}

static StateMachine *
_optimiseStateMachine(VexPtr<MaiMap, &ir_heap> &mai,
		      VexPtr<StateMachine, &ir_heap> sm,
		      const AllowableOptimisations &opt,
		      const VexPtr<OracleInterface> &oracle,
		      bool is_ssa,
		      GarbageCollectionToken token,
		      bool *progress)
{
	__set_profiling(optimiseStateMachine);
	sm->sanityCheck(*mai);
	sm->assertAcyclic();

	if (debugOptimiseStateMachine) {
		printf("%s(sm=..., opt = %s, is_ssa = %s)\n",
		       __func__, opt.name(), is_ssa ? "true" : "false");
		printStateMachine(sm, stdout);
	}

	bool done_something;
	do {
		if (TIMEOUT)
			return sm;
		done_something = false;

		bool p = false;
		sm = sm->optimise(opt, &p);
		if (debugOptimiseStateMachine && p) {
			printf("Local optimise 1:\n");
			printStateMachine(sm, stdout);
		}
		done_something |= p;

		sm = internStateMachine(sm);
		if (opt.ignoreSideEffects()) {
			p = false;
			removeSurvivingStates(sm, opt, &p);
			if (debugOptimiseStateMachine && p) {
				printf("Remove surviving stores:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;
		}

		{
			bool d;
			p = false;
			do {
				d = false;
				sm = deadCodeElimination(sm, &d, opt);
				p |= d;
			} while (d);
			if (debugOptimiseStateMachine && p) {
				printf("deadCodeElimination:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;
		}
		p = false;
		sm = sm->optimise(opt, &p);
		if (p) {
			if (is_ssa)
				sm = internStateMachine(sm); /* Local optimisation only maintains SSA form if interned */
			if (debugOptimiseStateMachine) {
				printf("Local optimise 2:\n");
				printStateMachine(sm, stdout);
			}
		}
		done_something |= p;

		LibVEX_maybe_gc(token);

		p = false;
		sm = availExpressionAnalysis(*mai, sm, opt, is_ssa, oracle, &p);
		if (debugOptimiseStateMachine && p) {
			printf("availExpressionAnalysis:\n");
			printStateMachine(sm, stdout);
		}
		done_something |= p;

		LibVEX_maybe_gc(token);

		p = false;
		sm = bisimilarityReduction(sm, is_ssa, *mai, &p);
		if (debugOptimiseStateMachine && p) {
			printf("bisimilarityReduction:\n");
			printStateMachine(sm, stdout);
		}
		done_something |= p;

		if (is_ssa) {
			p = false;
			sm = undefinednessSimplification(sm, &p);
			if (debugOptimiseStateMachine && p) {
				printf("Undefinedness:\n");
				printStateMachine(sm, stdout);
			}
		}
		if (opt.noExtend()) {
			p = false;
			sm = useInitialMemoryLoads(*mai, sm, opt, oracle, &p);
			if (debugOptimiseStateMachine && p) {
				printf("useInitialMemoryLoads:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;
		}
		if (opt.noLocalSurvival()) {
			p = false;
			sm = removeLocalSurvival(sm, opt, &p);
			if (debugOptimiseStateMachine && p) {
				printf("removeLocalSurvival:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;
		}
		if (opt.mustStoreBeforeCrash()) {
			p = false;
			sm = enforceMustStoreBeforeCrash(sm, &p);
			if (debugOptimiseStateMachine && p) {
				printf("enforceMustStoreBeforeCrash:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;
		}

		if (opt.ignoreSideEffects() && !done_something) {
			p = false;
			sm = removeTerminalStores(*mai, sm, opt, oracle, &p);
			if (debugOptimiseStateMachine && p) {
				printf("removeTerminalStores:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;
		}

		if (!done_something && is_ssa) {
			/* Note that we use the same CDM for
			   functionAliasAnalysis and phi elimination,
			   without trying to recompute it.  That's
			   fine, because function alias analysis won't
			   modify the control-flow structure of the
			   machine. */

			ControlDominationMap cdm;
			cdm.init(sm, opt);
			if (TIMEOUT)
				break;

			p = false;
			sm = functionAliasAnalysis(*mai, sm, opt, oracle, cdm, &p);
			if (debugOptimiseStateMachine && p) {
				printf("functionAliasAnalysis:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;

			if (!p) {
				sm = phiElimination(sm, opt, cdm, &p);
				if (debugOptimiseStateMachine && p) {
					printf("phiElimination:\n");
					printStateMachine(sm, stdout);
				}
				done_something |= p;
			}
		}

		if (progress)
			*progress |= done_something;
	} while (done_something);
	sm->assertAcyclic();
	sm->sanityCheck(*mai);
	if (is_ssa)
		sm->assertSSA();
	return sm;
}
StateMachine *
optimiseStateMachine(VexPtr<MaiMap, &ir_heap> &mai,
		     VexPtr<StateMachine, &ir_heap> sm,
		     const AllowableOptimisations &opt,
		     const VexPtr<OracleInterface> &oracle,
		     bool is_ssa,
		     GarbageCollectionToken token,
		     bool *progress)
{
	return _optimiseStateMachine(mai, sm, opt, oracle, is_ssa, token, progress);
}
StateMachine *
optimiseStateMachine(VexPtr<MaiMap, &ir_heap> &mai,
		     VexPtr<StateMachine, &ir_heap> sm,
		     const AllowableOptimisations &opt,
		     const VexPtr<Oracle> &oracle,
		     bool is_ssa,
		     GarbageCollectionToken token,
		     bool *progress)
{
	VexPtr<OracleInterface> oracleI(oracle);
	return _optimiseStateMachine(mai, sm, opt, oracleI, is_ssa, token, progress);
}

static void
getConflictingStores(const MaiMap &mai, StateMachine *sm, Oracle *oracle, std::set<DynAnalysisRip> &potentiallyConflictingStores)
{
	std::set<StateMachineSideEffectLoad *> allLoads;
	enumSideEffects(sm, allLoads);
	if (allLoads.size() == 0) {
		fprintf(_logfile, "\t\tNo loads left in store machine?\n");
		return;
	}
	for (std::set<StateMachineSideEffectLoad *>::iterator it = allLoads.begin();
	     it != allLoads.end();
	     it++)
		oracle->findConflictingStores(mai, *it, potentiallyConflictingStores);
}

/* If there's precisely one interesting store in the store machine and
 * one interesting load in the probe machine then the whole thing
 * becomes very easy. */
static bool
singleLoadVersusSingleStore(const MaiMap &mai, StateMachine *storeMachine, StateMachine *probeMachine,
			    const AllowableOptimisations &opt, OracleInterface *oracle)
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
			if (oracle->memoryAccessesMightAlias(mai, opt, load, store)) {
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
		if (oracle->memoryAccessesMightAlias(mai, opt, load, racingStore))
			return false;
	}

	return true;
}

static IRExpr *
atomicSurvivalConstraint(VexPtr<MaiMap, &ir_heap> &mai,
			 VexPtr<StateMachine, &ir_heap> &machine,
			 StateMachine **_atomicMachine,
			 VexPtr<OracleInterface> &oracle,
			 const AllowableOptimisations &opt,
			 GarbageCollectionToken token)
{
	VexPtr<StateMachine, &ir_heap> atomicMachine;
	atomicMachine = duplicateStateMachine(machine);
	atomicMachine = optimiseStateMachine(mai, atomicMachine, opt, oracle, true, token);
	VexPtr<IRExpr, &ir_heap> nullexpr(NULL);
	if (_atomicMachine)
		*_atomicMachine = atomicMachine;
	if (atomicMachine->root->type == StateMachineState::Unreached) {
		/* This machine can definitely never survive if run
		 * atomically! */
		return IRExpr_Const(IRConst_U1(0));
	}
	IRExpr *survive = survivalConstraintIfExecutedAtomically(mai, atomicMachine, nullexpr, oracle, false, opt, token);
	if (!survive) {
		fprintf(_logfile, "\tTimed out computing survival constraint\n");
		return NULL;
	}
	return simplifyIRExpr(survive, opt);
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
duplicateStateMachineNoAnnotations(StateMachine *inp, bool *done_something)
{
	struct : public StateMachineTransformer {
		static bool removeThisOne(StateMachineSideEffect::sideEffectType t) {
			switch (t) {
			case StateMachineSideEffect::AssertFalse:
			case StateMachineSideEffect::StartFunction:
			case StateMachineSideEffect::EndFunction:
			case StateMachineSideEffect::PointerAliasing:
			case StateMachineSideEffect::StackLayout:
				return true;
			case StateMachineSideEffect::Unreached:
			case StateMachineSideEffect::Load:
			case StateMachineSideEffect::Store:
			case StateMachineSideEffect::Copy:
			case StateMachineSideEffect::Phi:
			case StateMachineSideEffect::StartAtomic:
			case StateMachineSideEffect::EndAtomic:
				return false;
			}
			abort();
		}
		StateMachineSideEffecting *transformOneState(
			StateMachineSideEffecting *a, bool *done_something)
		{
			if (a->sideEffect && removeThisOne(a->sideEffect->type)) {
				*done_something = true;
				return new StateMachineSideEffecting(a->dbg_origin, NULL, a->target);
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
removeAnnotations(VexPtr<MaiMap, &ir_heap> &mai,
		  VexPtr<StateMachine, &ir_heap> sm,
		  const AllowableOptimisations &opt,
		  const VexPtr<OracleInterface> &oracle,
		  bool is_ssa,
		  GarbageCollectionToken token)
{
	/* Iterate to make sure we get rid of any assertions
	   introduced by the optimiser itself. */
	while (1) {
		if (TIMEOUT)
			return NULL;
		bool done_something = false;
		sm = duplicateStateMachineNoAnnotations(sm, &done_something);
		if (!done_something)
			break;
		done_something = false;
		sm = optimiseStateMachine(mai, sm, opt, oracle, is_ssa,
					  token, &done_something);
		if (!done_something)
			break;
	}
	return sm;
}
      
static IRExpr *
verificationConditionForStoreMachine(VexPtr<StateMachine, &ir_heap> &storeMachine,
				     VexPtr<StateMachine, &ir_heap> probeMachine,
				     VexPtr<OracleInterface> &oracle,
				     VexPtr<MaiMap, &ir_heap> &mai,
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
	sm = optimiseStateMachine(mai, sm, storeOptimisations, oracle, true, token);

	if (dynamic_cast<StateMachineUnreached *>(sm->root)) {
		/* This store machine is unusable, probably because we
		 * don't have the machine code for the relevant
		 * library */
		fprintf(_logfile, "\t\tStore machine is unusable\n");
		return NULL;
	}

	fprintf(_logfile, "\t\tStore machine:\n");
	printStateMachine(sm, _logfile);

	probeMachine = optimiseStateMachine(mai, probeMachine, probeOptimisations, oracle, true, token);

	fprintf(_logfile, "\t\tAssertion-free probe machine:\n");
	printStateMachine(probeMachine, _logfile);

	/* Special case: if the only possible interaction between the
	   probe machine and the store machine is a single load in the
	   probe machine and a single store in the store machine then
	   we don't need to do anything. */
	if (singleLoadVersusSingleStore(*mai, storeMachine, probeMachine, optIn, oracle)) {
		fprintf(_logfile, "\t\tSingle store versus single load -> crash impossible.\n");
		return NULL;
	}

	VexPtr<IRExpr, &ir_heap> assumption;
	assumption = atomicSurvivalConstraint(mai, probeMachine, NULL, oracle,
					      atomicSurvivalOptimisations(probeOptimisations.enablepreferCrash()),
					      token);
	if (!assumption)
		return NULL;

	assumption = writeMachineSuitabilityConstraint(
		mai,
		sm,
		probeMachine,
		oracle,
		assumption,
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
			mai,
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
truncateStateMachine(const MaiMap &mai, StateMachine *sm, StateMachineSideEffectMemoryAccess *truncateAt)
{
	StateMachineBifurcate *smb =
		new StateMachineBifurcate(
			mai.begin(truncateAt->rip).node()->rip,
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
	rewriteRules[StateMachineCrash::get()] = StateMachineCrash::get();
	rewriteRules[StateMachineNoCrash::get()] = StateMachineNoCrash::get();
	StateMachineTransformer::rewriteMachine(sm, rewriteRules, false);
	assert(rewriteRules.count(sm->root));
	assert(rewriteRules[sm->root] != sm->root);
	return new StateMachine(sm, rewriteRules[sm->root]);
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
localiseLoads(VexPtr<MaiMap, &ir_heap> &mai,
	      const VexPtr<StateMachine, &ir_heap> &probeMachine,
	      const VexPtr<StateMachine, &ir_heap> &storeMachine,
	      const AllowableOptimisations &opt,
	      const VexPtr<OracleInterface> &oracle,
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
			for (auto it2 = mai->begin(load->rip); !it2.finished(); it2.advance()) {
				DynAnalysisRip dr(it2.dr());
				bool found_one = false;
				for (auto it3 = stores.begin(); !found_one && it3 != stores.end(); it3++) {
					StateMachineSideEffectStore *store = *it3;
					if (store->tag != load->tag)
						continue;
					for (auto it4 = mai->begin(store->rip); !found_one && !it4.finished(); it4.advance())
						if (oracle->memoryAccessesMightAliasCrossThread(dr, it4.dr()))
							found_one = true;
				}
				if (found_one)
					nonLocalLoads.insert(dr);
			}
		}
	}
	return optimiseStateMachine(
		mai,
		probeMachine,
		opt.setnonLocalLoads(&nonLocalLoads),
		oracle,
		true,
		token,
		done_something);
}

static StateMachine *
localiseLoads(VexPtr<MaiMap, &ir_heap> &mai,
	      const VexPtr<StateMachine, &ir_heap> &probeMachine,
	      const std::set<DynAnalysisRip> &stores,
	      const AllowableOptimisations &opt,
	      const VexPtr<OracleInterface> &oracle,
	      GarbageCollectionToken token,
	      bool *done_something = NULL)
{
	std::set<DynAnalysisRip> nonLocalLoads;
	{
		std::set<StateMachineSideEffectLoad *> loads;
		enumSideEffects(probeMachine, loads);
		for (auto it = loads.begin(); it != loads.end(); it++) {
			StateMachineSideEffectLoad *load = *it;
			for (auto it3 = mai->begin(load->rip); !it3.finished(); it3.advance()) {
				bool found_one = false;
				for (auto it2 = stores.begin(); !found_one && it2 != stores.end(); it2++) {
					DynAnalysisRip store = *it2;
					if (oracle->memoryAccessesMightAliasCrossThread(it3.dr(), store))
						found_one = true;
				}
				if (found_one)
					nonLocalLoads.insert(it3.dr());
			}
		}
	}
	return optimiseStateMachine(
		mai,
		probeMachine,
		opt.setnonLocalLoads(&nonLocalLoads),
		oracle,
		true,
		token,
		done_something);
}

static CrashSummary *
considerStoreCFG(const DynAnalysisRip &target_rip,
		 const VexPtr<CFGNode, &ir_heap> cfg,
		 const VexPtr<Oracle> &oracle,
		 VexPtr<StateMachine, &ir_heap> probeMachine,
		 bool needRemoteMacroSections,
		 unsigned tid,
		 const AllowableOptimisations &optIn,
		 const VexPtr<MaiMap, &ir_heap> &maiIn,
		 GarbageCollectionToken token)
{
	__set_profiling(considerStoreCFG);
	VexPtr<MaiMap, &ir_heap> mai(maiIn->dupe());
	VexPtr<StateMachine, &ir_heap> sm(storeCFGToMachine(oracle, tid, cfg, *mai));
	if (!sm) {
		fprintf(_logfile, "Cannot build store machine!\n");
		return NULL;
	}
	AllowableOptimisations storeOptimisations =
		optIn.
			enableassumeNoInterferingStores().
			enableassumeExecutesAtomically().
			enablemustStoreBeforeCrash();
	AllowableOptimisations probeOptimisations =
		optIn.
			enableignoreSideEffects();
	VexPtr<OracleInterface> oracleI(oracle);
	sm = optimiseStateMachine(
		mai,
		sm,
		storeOptimisations,
		oracle,
		false,
		token);

	VexPtr<StateMachine, &ir_heap> sm_ssa(convertToSSA(sm));
	if (!sm_ssa)
		return NULL;

	sm_ssa = optimiseStateMachine(
		mai,
		sm_ssa,
		storeOptimisations,
		oracle,
		true,
		token);
	probeMachine = duplicateStateMachine(probeMachine);
	probeMachine = localiseLoads(mai,
				     probeMachine,
				     sm_ssa,
				     probeOptimisations,
				     oracleI,
				     token);

	VexPtr<IRExpr, &ir_heap> base_verification_condition(
		verificationConditionForStoreMachine(
			sm_ssa,
			probeMachine,
			oracleI,
			mai,
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
			for (auto it2 = mai->begin((*it)->rip); !it2.finished(); it2.advance()) {
				if (oracle->type_index->ripPresent(it2.dr())) {
					typeDbProbeAccesses.insert(*it);
					break;
				}
			}
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
				*mai,
				probeMachine,
				inductionAccesses[x]));
		truncatedMachine = optimiseStateMachine(mai, truncatedMachine, optIn, oracle, true, token);
		IRExpr *t = verificationConditionForStoreMachine(
			sm_ssa,
			truncatedMachine,
			oracleI,
			mai,
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
		ppIRExpr(residual_verification_condition,  _logfile);
		fprintf(_logfile, "\n");
		for (auto it = mai->begin(inductionAccesses[x]->rip); !it.finished(); it.advance())
			logUseOfInduction(target_rip, it.dr());
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
	VexPtr<CrashSummary, &ir_heap> res(new CrashSummary(probeMachine, sm_ssa, residual_verification_condition, oracle, mai));
	if (needRemoteMacroSections) {
		VexPtr<remoteMacroSectionsT, &ir_heap> remoteMacroSections(new remoteMacroSectionsT);
		if (!findRemoteMacroSections(mai, probeMachine, sm_ssa, residual_verification_condition,
					     oracleI, optIn, remoteMacroSections, token)) {
			fprintf(_logfile, "\t\tChose a bad write machine...\n");
			return NULL;
		}
		if (!fixSufficient(mai, sm, probeMachine, residual_verification_condition,
				   oracleI, optIn, remoteMacroSections, token)) {
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
buildProbeMachine(CfgLabelAllocator &allocLabel,
		  const VexPtr<Oracle> &oracle,
		  const DynAnalysisRip &targetRip,
		  ThreadId tid,
		  const AllowableOptimisations &optIn,
		  StateMachine ***out,
		  unsigned *nr_out_machines,
		  VexPtr<MaiMap, &ir_heap> &mai,
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
		HashedSet<HashedPtr<CFGNode> > roots;
		HashedSet<HashedPtr<const CFGNode> > proximalNodes;
		if (!getProbeCFGs(allocLabel, oracle, targetRip, roots, proximalNodes)) {
			fprintf(_logfile, "Cannot get probe CFGs!\n");
			return false;
		}
		std::set<StateMachine *> machines;
		probeCFGsToMachine(oracle, tid._tid(),
				   roots,
				   proximalNodes,
				   *mai,
				   machines);
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
		sm->sanityCheck(*mai);

		sm = optimiseStateMachine(mai,
					  sm,
					  opt,
					  oracle,
					  false,
					  token);

		sm = convertToSSA(sm);
		if (TIMEOUT)
			return false;
		sm->sanityCheck(*mai);
		sm = optimiseStateMachine(mai,
					  sm,
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
	return root->successors.empty();
}

static bool
machineHasOneRacingLoad(const MaiMap &mai, StateMachine *sm, const VexRip &vr, OracleInterface *oracle)
{
	std::set<StateMachineSideEffectLoad *> loads;
	enumSideEffects(sm, loads);
	bool got_one = false;
	for (auto it = loads.begin(); it != loads.end(); it++) {
		StateMachineSideEffectLoad *load = *it;
		bool races = false;
		for (auto it2 = mai.begin(load->rip); !races && !it2.finished(); it2.advance()) {
			if (oracle->memoryAccessesMightAliasCrossThread(it2.node()->rip, vr))
				races = true;
		}
		if (races) {
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
probeMachineToSummary(CfgLabelAllocator &allocLabel,
		      const DynAnalysisRip &targetRip,
		      const VexPtr<StateMachine, &ir_heap> &probeMachine,
		      const VexPtr<StateMachine, &ir_heap> &assertionFreeProbeMachine,
		      const VexPtr<Oracle> &oracle,
		      FixConsumer &df,
		      bool needRemoteMacroSections,
		      std::set<DynAnalysisRip> &potentiallyConflictingStores,
		      const AllowableOptimisations &optIn,
		      const VexPtr<MaiMap, &ir_heap> &maiIn,
		      GarbageCollectionToken token)
{
	assert(potentiallyConflictingStores.size() > 0);

	VexPtr<CFGNode *, &ir_heap> storeCFGs;
	int nrStoreCfgs;
	{
		CFGNode **n;
		getStoreCFGs(allocLabel, potentiallyConflictingStores, oracle, &n, &nrStoreCfgs);
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
		    machineHasOneRacingLoad(*maiIn, assertionFreeProbeMachine, storeCFGs[i]->rip, oracle)) {
			fprintf(_logfile, "Single store versus single shared load -> no race possible\n");
			continue;
		}

		VexPtr<CFGNode, &ir_heap> storeCFG(storeCFGs[i]);
		VexPtr<CrashSummary, &ir_heap> summary;

		summary = considerStoreCFG(targetRip,
					   storeCFG,
					   oracle,
					   probeMachine,
					   needRemoteMacroSections,
					   STORING_THREAD + i,
					   optIn.setinterestingStores(&potentiallyConflictingStores),
					   maiIn,
					   token);
		if (summary)
			df(summary, token);

		if (TIMEOUT) {
			fprintf(_logfile, "Processed %d/%d store CFGs\n", i, nrStoreCfgs);
			break;
		}
	}

	return foundRace;
}

bool
diagnoseCrash(CfgLabelAllocator &allocLabel,
	      const DynAnalysisRip &targetRip,
	      VexPtr<StateMachine, &ir_heap> probeMachine,
	      const VexPtr<Oracle> &oracle,
	      FixConsumer &df,
	      bool needRemoteMacroSections,
	      const AllowableOptimisations &optIn,
	      VexPtr<MaiMap, &ir_heap> &mai,
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

	VexPtr<OracleInterface> oracleI(oracle);
	reducedProbeMachine = removeAnnotations(mai, probeMachine, optIn.enableignoreSideEffects(), oracleI, true, token);
	if (!reducedProbeMachine)
		return NULL;
	getConflictingStores(*mai, reducedProbeMachine, oracle, potentiallyConflictingStores);
	if (potentiallyConflictingStores.size() == 0) {
		fprintf(_logfile, "\t\tNo available conflicting stores?\n");
		return NULL;
	}
	bool localised_loads = false;
	probeMachine = localiseLoads(mai,
				     probeMachine,
				     potentiallyConflictingStores,
				     optIn.enableignoreSideEffects(),
				     oracleI,
				     token,
				     &localised_loads);
	if (localised_loads) {
		std::set<DynAnalysisRip> newPotentiallyConflictingStores;
		while (1) {
			reducedProbeMachine = removeAnnotations(mai, probeMachine, optIn.enableignoreSideEffects(), oracleI, true, token);
			if (!reducedProbeMachine)
				return NULL;
			getConflictingStores(*mai, reducedProbeMachine, oracle, newPotentiallyConflictingStores);
			if (potentiallyConflictingStores.size() == 0) {
				fprintf(_logfile, "\t\tNo available conflicting stores?\n");
				return NULL;
			}
			if (newPotentiallyConflictingStores == potentiallyConflictingStores)
				break;
			potentiallyConflictingStores = newPotentiallyConflictingStores;
			localised_loads = false;
			probeMachine = localiseLoads(mai, probeMachine,
						     potentiallyConflictingStores,
						     optIn.enableignoreSideEffects(),
						     oracleI, token, &localised_loads);
			if (!localised_loads)
				break;
		}
	}

	if (potentiallyConflictingStores.size() == 0) {
		fprintf(_logfile, "\t\tNo available conflicting stores after localisation?\n");
		return NULL;
	}

	return probeMachineToSummary(allocLabel,
				     targetRip,
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
				const VexPtr<Oracle> &oracle,
				FixConsumer &df,
				GarbageCollectionToken token)
{
	VexPtr<MaiMap, &ir_heap> mai(MaiMap::empty());

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.setAddressSpace(oracle->ms->addressSpace)
		.enablenoExtend();
	VexPtr<StateMachine *, &ir_heap> probeMachines;
	unsigned nrProbeMachines;
	CfgLabelAllocator allocLabel;
	{
		StateMachine **_probeMachines;
		struct timeval start;
		gettimeofday(&start, NULL);
		if (!buildProbeMachine(allocLabel, oracle, targetRip, tid, opt,
				       &_probeMachines, &nrProbeMachines, mai,
				       token))
			return;
		struct timeval end;
		gettimeofday(&end, NULL);
		end.tv_sec -= start.tv_sec;
		end.tv_usec -= start.tv_usec;
		if (end.tv_usec < 0) {
			end.tv_usec += 1000000;
			end.tv_sec--;
		}
		printf("buildProbeMachine takes %ld.%06ld\n", end.tv_sec, end.tv_usec);

		probeMachines = _probeMachines;
	}
	for (unsigned x = 0; x < nrProbeMachines; x++) {
		VexPtr<StateMachine, &ir_heap> probeMachine(probeMachines[x]);
		diagnoseCrash(allocLabel, targetRip, probeMachine, oracle,
			      df, false, opt.enablenoLocalSurvival(),
			      mai, token);
	}
}

