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

static StateMachine *
enforceMustStoreBeforeCrash(SMScopes *scopes, StateMachine *sm, bool *progress)
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
	std::set<StateMachineTerminal *> terminals;
	enumStates(sm, &terminals);
	for (auto it = terminals.begin(); it != terminals.end(); it++) {
		StateMachineTerminal *s = *it;
		if (storeStates.count(s))
			continue;
		if (s->res == scopes->smrs.cnst(smr_survive) || s->res == scopes->smrs.cnst(smr_unreached))
			continue;
		std::map<StateMachineRes, bbdd *> selectors(smrbdd::to_selectors(&scopes->bools, s->res));
		if (!selectors.count(smr_crash))
			continue;
		smrbdd::enablingTableT tab;
		if (selectors.count(smr_survive))
			tab[selectors[smr_survive]] = scopes->smrs.cnst(smr_survive);
		if (selectors.count(smr_unreached))
			tab[selectors[smr_unreached]] = scopes->smrs.cnst(smr_unreached);
		tab[selectors[smr_crash]] = scopes->smrs.cnst(smr_unreached);
		*progress = true;
		s->res = smrbdd::from_enabling(&scopes->smrs, tab, scopes->smrs.cnst(smr_unreached));
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

class OptimisationRecorder {
public:
#if CONFIG_RECORD_MACHINE_OPTIMISATIONS
	char *prefix;
	bool skip;
	OptimisationRecorder()
		: prefix(NULL)
	{}
	~OptimisationRecorder() { free(prefix); }
	void start(SMScopes *scopes, MaiMap *mai, StateMachine *sm, bool is_ssa,
		   const AllowableOptimisations &opt)
	{
		if (random() % CONFIG_RECORD_MACHINE_OPTIMISATIONS) {
			skip = true;
			return;
		}
		skip = false;

		static int idx;
		while (1) {
			prefix = my_asprintf("machines/%d", idx);
			if (mkdir(prefix, 0700) == -1) {
				if (errno == EEXIST) {
					idx++;
					free(prefix);
					continue;
				}
				err(1, "creating %s", prefix);
			} else {
				break;
			}
		}
		FILE *f = fopenf("w", "%s/opt", prefix);
		fprintf(f, "%s", opt.name());
		fclose(f);
		f = fopenf("w", "%s/pre_mai", prefix);
		mai->print(f);
		fclose(f);
		f = fopenf("w", "%s/pre_machine", prefix);
		printStateMachine(sm, f);
		fclose(f);
		f = fopenf("w", "%s/is_ssa", prefix);
		if (is_ssa)
			fprintf(f, "true\n");
		else
			fprintf(f, "false\n");
		fclose(f);
		f = fopenf("w", "%s/pre_scopes", prefix);
		scopes->prettyPrint(f);
		fclose(f);
		fprintf(_logfile, "Optimisation log: %s\n", prefix);
	}
	void finish(SMScopes *scopes, MaiMap *mai, StateMachine *sm)
	{
		if (skip)
			return;
		FILE *f = fopenf("w", "%s/post_mai", prefix);
		mai->print(f);
		fclose(f);
		f = fopenf("w", "%s/post_machine", prefix);
		printStateMachine(sm, f);
		fclose(f);
		f = fopenf("w", "%s/post_scopes", prefix);
		scopes->prettyPrint(f);
		fclose(f);
	}
#else
	void start(MaiMap *, StateMachine *, bool , const AllowableOptimisations &)
	{}
	void finish(MaiMap *, StateMachine *)
	{}
#endif
};

static StateMachine *
_optimiseStateMachine(SMScopes *scopes,
		      VexPtr<MaiMap, &ir_heap> &mai,
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

	OptimisationRecorder optrec;
	optrec.start(scopes, mai, sm, is_ssa, opt);

	bool done_something;
	do {
		if (TIMEOUT)
			return sm;
		done_something = false;

		bool p = false;
		sm = sm->optimise(scopes, opt, &p);
		if (debugOptimiseStateMachine && p) {
			printf("Local optimise 1:\n");
			printStateMachine(sm, stdout);
		}
		done_something |= p;

		sm = internStateMachine(scopes, sm);
		if (TIMEOUT)
			return sm;

		{
			bool d;
			p = false;
			do {
				d = false;
				sm = deadCodeElimination(scopes, sm, &d, is_ssa);
				p |= d;
			} while (d);
			if (debugOptimiseStateMachine && p) {
				printf("deadCodeElimination:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;
		}
		p = false;
		sm = sm->optimise(scopes, opt, &p);
		if (p) {
			if (is_ssa) {
				/* Local optimisation only maintains SSA form if interned */
				sm = internStateMachine(scopes, sm);
				if (TIMEOUT)
					return sm;
			}
			if (debugOptimiseStateMachine) {
				printf("Local optimise 2:\n");
				printStateMachine(sm, stdout);
			}
		}
		done_something |= p;

		LibVEX_maybe_gc(token);

		p = false;
		sm = availExpressionAnalysis(scopes, *mai, sm, opt, is_ssa, oracle, &p);
		if (debugOptimiseStateMachine && p) {
			printf("availExpressionAnalysis:\n");
			printStateMachine(sm, stdout);
		}
		done_something |= p;

		LibVEX_maybe_gc(token);

		p = false;
		sm = bisimilarityReduction(scopes, sm, is_ssa, *mai, &p);
		if (debugOptimiseStateMachine && p) {
			printf("bisimilarityReduction:\n");
			printStateMachine(sm, stdout);
		}
		done_something |= p;

		if (opt.noExtend()) {
			p = false;
			sm = useInitialMemoryLoads(scopes, *mai, sm, opt, oracle, &p);
			if (debugOptimiseStateMachine && p) {
				printf("useInitialMemoryLoads:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;
		}
		if (opt.mustStoreBeforeCrash()) {
			p = false;
			sm = enforceMustStoreBeforeCrash(scopes, sm, &p);
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
			sm = phiElimination(scopes, sm, &p);
			if (debugOptimiseStateMachine && p) {
				printf("phiElimination:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;
		}

		if (!done_something && is_ssa && !TIMEOUT) {
			ControlDominationMap cdm;
			cdm.init(scopes, sm, opt);
			if (TIMEOUT)
				break;

			p = false;
			sm = functionAliasAnalysis(scopes, *mai, sm, opt, oracle, cdm, &p);
			if (debugOptimiseStateMachine && p) {
				printf("functionAliasAnalysis:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;
		}

		if (progress)
			*progress |= done_something;
	} while (done_something);
	sm->assertAcyclic();
	sm->sanityCheck(*mai);
	if (is_ssa)
		sm->assertSSA();
	if (!TIMEOUT)
		optrec.finish(scopes, mai, sm);
	return sm;
}
StateMachine *
optimiseStateMachine(SMScopes *scopes,
		     VexPtr<MaiMap, &ir_heap> &mai,
		     VexPtr<StateMachine, &ir_heap> sm,
		     const AllowableOptimisations &opt,
		     const VexPtr<OracleInterface> &oracle,
		     bool is_ssa,
		     GarbageCollectionToken token,
		     bool *progress)
{
	return _optimiseStateMachine(scopes, mai, sm, opt, oracle, is_ssa, token, progress);
}
StateMachine *
optimiseStateMachine(SMScopes *scopes,
		     VexPtr<MaiMap, &ir_heap> &mai,
		     VexPtr<StateMachine, &ir_heap> sm,
		     const AllowableOptimisations &opt,
		     const VexPtr<Oracle> &oracle,
		     bool is_ssa,
		     GarbageCollectionToken token,
		     bool *progress)
{
	VexPtr<OracleInterface> oracleI(oracle);
	return _optimiseStateMachine(scopes, mai, sm, opt, oracleI, is_ssa, token, progress);
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
 * one interesting memory access in the probe machine then the whole
 * thing becomes very easy. */
static bool
singleLoadVersusSingleStore(const MaiMap &mai, StateMachine *storeMachine, StateMachine *probeMachine,
			    const AllowableOptimisations &opt, OracleInterface *oracle)
{
	std::set<StateMachineSideEffectStore *> storeMachineStores;
	std::set<StateMachineSideEffectMemoryAccess *> probeMachineAccesses;
	enumSideEffects(storeMachine, storeMachineStores);
	enumSideEffects(probeMachine, probeMachineAccesses);

	StateMachineSideEffectStore *racingStore = NULL;
	StateMachineSideEffectMemoryAccess *racingLoad = NULL;
	for (auto it = storeMachineStores.begin(); it != storeMachineStores.end(); it++) {
		StateMachineSideEffectStore *store = *it;
		bool races = false;
		for (auto it2 = probeMachineAccesses.begin();
		     !races && it2 != probeMachineAccesses.end();
		     it2++) {
			StateMachineSideEffectMemoryAccess *load = *it2;
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

	for (auto it = probeMachineAccesses.begin(); it != probeMachineAccesses.end(); it++) {
		StateMachineSideEffectMemoryAccess *load = *it;
		if (racingLoad == load)
			continue;
		if (oracle->memoryAccessesMightAlias(mai, opt, load, racingStore))
			return false;
	}

	return true;
}

static bbdd *
atomicSurvivalConstraint(SMScopes *scopes,
			 VexPtr<MaiMap, &ir_heap> &mai,
			 VexPtr<StateMachine, &ir_heap> &machine,
			 StateMachine **_atomicMachine,
			 VexPtr<OracleInterface> &oracle,
			 const AllowableOptimisations &opt,
			 GarbageCollectionToken token)
{
	VexPtr<StateMachine, &ir_heap> atomicMachine;
	atomicMachine = duplicateStateMachine(machine);
	atomicMachine = optimiseStateMachine(scopes, mai, atomicMachine, opt, oracle, true, token);
	if (_atomicMachine)
		*_atomicMachine = atomicMachine;
	VexPtr<bbdd, &ir_heap> nullexpr(NULL);
	bbdd *survive = survivalConstraintIfExecutedAtomically(scopes, mai, atomicMachine, nullexpr, oracle, false, opt, token);
	if (!survive)
		fprintf(_logfile, "\tTimed out computing survival constraint\n");
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
duplicateStateMachineNoAnnotations(StateMachine *inp, bool *done_something)
{
	struct {
		bool operator()(StateMachineSideEffect::sideEffectType t) {
			switch (t) {
			case StateMachineSideEffect::Load:
			case StateMachineSideEffect::Store:
			case StateMachineSideEffect::Unreached:
			case StateMachineSideEffect::Copy:
			case StateMachineSideEffect::Phi:
			case StateMachineSideEffect::StartAtomic:
			case StateMachineSideEffect::EndAtomic:
			case StateMachineSideEffect::ImportRegister:
				return false;
			case StateMachineSideEffect::AssertFalse:
			case StateMachineSideEffect::StartFunction:
			case StateMachineSideEffect::EndFunction:
			case StateMachineSideEffect::StackLayout:
				return true;
			}
			abort();
		}
	} isAnnotationType;
	std::map<const StateMachineState *, StateMachineState *> map;
	std::queue<StateMachineState **> relocs;
	StateMachineState *newRoot = inp->root;
	relocs.push(&newRoot);
	bool progress = false;
	while (!relocs.empty()) {
		StateMachineState **slot = relocs.front();
		relocs.pop();
		const StateMachineState *oldState = *slot;
		auto it_did_insert = map.insert(std::pair<const StateMachineState *, StateMachineState *>(oldState, (StateMachineState *)NULL));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (!did_insert) {
			assert(it->second != NULL);
			*slot = it->second;
			continue;
		}

		/* Figure out where @oldState is going to be mapped
		 * to. */
		StateMachineState *newState = (StateMachineState *)0xf001deadul;
		switch (oldState->type) {
		case StateMachineState::Terminal:
			/* Singletons are easy. */
			newState = (StateMachineState *)oldState;
			break;
		case StateMachineState::Bifurcate: {
			auto smb = (const StateMachineBifurcate *)oldState;
			auto newSmb = new StateMachineBifurcate(*smb);
			relocs.push(&newSmb->trueTarget);
			relocs.push(&newSmb->falseTarget);
			newState = newSmb;
			break;
		}
		case StateMachineState::SideEffecting: {
			auto sme = (const StateMachineSideEffecting *)oldState;
			auto newSme = new StateMachineSideEffecting(*sme);
			relocs.push(&newSme->target);
			if (newSme->sideEffect && isAnnotationType(newSme->sideEffect->type)) {
				newSme->sideEffect = NULL;
				progress = true;
			}
			newState = newSme;
			break;
		}
		}
		it->second = newState;
		*slot = newState;
	}
	if (!progress)
		return inp;
	*done_something = true;
	return new StateMachine(inp, newRoot);
}

StateMachine *
removeAnnotations(SMScopes *scopes,
		  VexPtr<MaiMap, &ir_heap> &mai,
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
		sm = optimiseStateMachine(scopes, mai, sm, opt, oracle, is_ssa,
					  token, &done_something);
		if (!done_something)
			break;
	}
	return sm;
}
      
static IRExpr *
verificationConditionForStoreMachine(SMScopes *scopes,
				     VexPtr<StateMachine, &ir_heap> &storeMachine,
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
	sm = optimiseStateMachine(scopes, mai, sm, storeOptimisations, oracle, true, token);

	fprintf(_logfile, "\t\tStore machine:\n");
	printStateMachine(sm, _logfile);

	probeMachine = optimiseStateMachine(scopes, mai, probeMachine, probeOptimisations, oracle, true, token);

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

	VexPtr<bbdd, &ir_heap> assumption;
	assumption = atomicSurvivalConstraint(scopes, mai, probeMachine, NULL, oracle,
					      atomicSurvivalOptimisations(probeOptimisations.enablepreferCrash()),
					      token);
	if (!assumption)
		return NULL;

	assumption = writeMachineSuitabilityConstraint(
		scopes,
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
	bbdd *crash_constraint =
		crossProductSurvivalConstraint(
			scopes,
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
		bbdd::to_irexpr(
			bbdd::And(
				&scopes->bools,
				bbdd::invert(
					&scopes->bools,
					crash_constraint),
				assumption));
	verification_condition = simplifyIRExpr(verification_condition, optIn);
	verification_condition = simplify_via_anf(verification_condition);
	verification_condition = simplifyIRExpr(verification_condition, optIn);
	verification_condition = interval_simplify(verification_condition);
	verification_condition = simplifyIRExpr(verification_condition, optIn);
	return verification_condition;
}

static StateMachine *
truncateStateMachine(SMScopes *scopes, const MaiMap &mai, StateMachine *sm, StateMachineSideEffectMemoryAccess *truncateAt)
{
	const VexRip &vr(mai.begin(truncateAt->rip).node()->rip);
	StateMachineTerminal *newTerminal =
		new StateMachineTerminal(
			vr,
			smrbdd::ifelse(
				&scopes->smrs,
				exprbdd::to_bbdd(
					&scopes->bools,
					exprbdd::unop(
						&scopes->exprs,
						&scopes->bools,
						Iop_BadPtr,
						truncateAt->addr)),
				scopes->smrs.cnst(smr_crash),
				scopes->smrs.cnst(smr_survive)));
	std::map<const StateMachineState *, StateMachineState *> map;
	std::queue<StateMachineState **> relocs;
	StateMachineState *newRoot = sm->root;
	relocs.push(&newRoot);
	bool found = false;
	while (!relocs.empty()) {
		StateMachineState **r = relocs.front();
		relocs.pop();
		const StateMachineState *oldState = *r;
		auto it_did_insert = map.insert(std::pair<const StateMachineState *, StateMachineState *>(oldState, (StateMachineState *)NULL));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert) {
			StateMachineState *newState;
			/* Shut compiler up */
			newState = (StateMachineState *)0xdead;
			switch (oldState->type) {
			case StateMachineState::Bifurcate: {
				auto smb = (const StateMachineBifurcate *)oldState;
				newState = new StateMachineBifurcate(*smb);
				break;
			}
			case StateMachineState::SideEffecting: {
				auto sme = (const StateMachineSideEffecting *)oldState;
				if (sme->sideEffect == truncateAt) {
					found = true;
					newState = newTerminal;
				} else {
					newState = new StateMachineSideEffecting(*sme);
				}
				break;
			}
			case StateMachineState::Terminal: {
				/* Get rid of the old way of crashing. */
				auto smt = (const StateMachineTerminal *)oldState;
				std::map<StateMachineRes, bbdd *> selectors(smrbdd::to_selectors(&scopes->bools, smt->res));
				smrbdd::enablingTableT tab;
				if (selectors.count(smr_crash))
					tab[selectors[smr_crash]] = scopes->smrs.cnst(smr_survive);
				if (selectors.count(smr_survive))
					tab[selectors[smr_survive]] = scopes->smrs.cnst(smr_survive);
				if (selectors.count(smr_unreached))
					tab[selectors[smr_unreached]] = scopes->smrs.cnst(smr_unreached);
				smrbdd *newRes = smrbdd::from_enabling(&scopes->smrs, tab, scopes->smrs.cnst(smr_unreached));
				assert(newRes);
				newRes->sanity_check(&scopes->ordering);
				newState = new StateMachineTerminal(smt->dbg_origin, newRes);
				break;
			}
			}
			it->second = newState;
			if (newState != newTerminal) {
				std::vector<StateMachineState **> succ;
				newState->targets(succ);
				for (auto it = succ.begin(); it != succ.end(); it++)
					relocs.push(*it);
			}
		}
		*r = it->second;
	}
	assert(found);
	assert(newRoot != sm->root);
	return new StateMachine(sm, newRoot);
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
localiseLoads(SMScopes *scopes,
	      VexPtr<MaiMap, &ir_heap> &mai,
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
		for (auto it = loads.begin(); !TIMEOUT && it != loads.end(); it++) {
			StateMachineSideEffectLoad *load = *it;
			for (auto it2 = mai->begin(load->rip); !TIMEOUT && !it2.finished(); it2.advance()) {
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
		scopes,
		mai,
		probeMachine,
		opt.setnonLocalLoads(&nonLocalLoads),
		oracle,
		true,
		token,
		done_something);
}

static StateMachine *
localiseLoads(SMScopes *scopes,
	      VexPtr<MaiMap, &ir_heap> &mai,
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
		for (auto it = loads.begin(); !TIMEOUT && it != loads.end(); it++) {
			StateMachineSideEffectLoad *load = *it;
			for (auto it3 = mai->begin(load->rip); !TIMEOUT && !it3.finished(); it3.advance()) {
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
		scopes,
		mai,
		probeMachine,
		opt.setnonLocalLoads(&nonLocalLoads),
		oracle,
		true,
		token,
		done_something);
}

static CrashSummary *
considerStoreCFG(SMScopes *scopes,
		 const DynAnalysisRip &target_rip,
		 const VexPtr<CFGNode, &ir_heap> cfg,
		 const VexPtr<Oracle> &oracle,
		 VexPtr<StateMachine, &ir_heap> probeMachine,
		 unsigned tid,
		 const AllowableOptimisations &optIn,
		 const VexPtr<MaiMap, &ir_heap> &maiIn,
		 GarbageCollectionToken token)
{
	__set_profiling(considerStoreCFG);
	VexPtr<MaiMap, &ir_heap> mai(maiIn->dupe());
	VexPtr<StateMachine, &ir_heap> sm(storeCFGToMachine(scopes, oracle, tid, cfg, *mai));
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
		scopes,
		mai,
		sm,
		storeOptimisations,
		oracle,
		false,
		token);

	VexPtr<StateMachine, &ir_heap> sm_ssa(convertToSSA(scopes, sm));
	if (!sm_ssa || TIMEOUT)
		return NULL;

	sm_ssa = optimiseStateMachine(
		scopes,
		mai,
		sm_ssa,
		storeOptimisations,
		oracle,
		true,
		token);
	probeMachine = duplicateStateMachine(probeMachine);
	probeMachine = localiseLoads(scopes,
				     mai,
				     probeMachine,
				     sm_ssa,
				     probeOptimisations,
				     oracleI,
				     token);
	if (TIMEOUT)
		return NULL;

	VexPtr<IRExpr, &ir_heap> base_verification_condition(
		verificationConditionForStoreMachine(
			scopes,
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

	VexPtr<IRExpr, &ir_heap> residual_verification_condition(base_verification_condition);
	if (CONFIG_USE_INDUCTION && !optIn.allPointersGood()) {
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
					if (oracle->type_db->ripPresent(it2.dr())) {
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
					scopes,
					*mai,
					probeMachine,
					inductionAccesses[x]));
			truncatedMachine = optimiseStateMachine(scopes, mai, truncatedMachine, optIn, oracle, true, token);
			IRExpr *t = verificationConditionForStoreMachine(
				scopes,
				sm_ssa,
				truncatedMachine,
				oracleI,
				mai,
				optIn,
				token);
			if (!t || t == residual_verification_condition ||
			    (t->tag == Iex_Const &&
			     ((IRExprConst *)t)->Ico.U1 == 0))
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
			    ((IRExprConst *)residual_verification_condition.get())->Ico.U1 == 0) {
				fprintf(_logfile, "\t\tCrash impossible.\n");
				return NULL;
			}
		}

		/* Okay, final check: is the verification condition satisfiable? */
		if (!satisfiable(residual_verification_condition, optIn)) {
			fprintf(_logfile, "\t\tVerification condition is unsatisfiable -> no bug\n");
			return NULL;
		}
	}

	/* Okay, the expanded machine crashes.  That means we have to
	 * generate a fix. */
	return new CrashSummary(scopes, probeMachine, sm_ssa, residual_verification_condition, oracle, mai);
}

StateMachine *
buildProbeMachine(SMScopes *scopes,
		  CfgLabelAllocator &allocLabel,
		  const VexPtr<Oracle> &oracle,
		  const VexRip &targetRip,
		  ThreadId tid,
		  const AllowableOptimisations &optIn,
		  VexPtr<MaiMap, &ir_heap> &mai,
		  GarbageCollectionToken token)
{
	__set_profiling(buildProbeMachine);

	AllowableOptimisations opt =
		optIn
		.enableignoreSideEffects();

	VexPtr<StateMachine, &ir_heap> sm;
	{
		HashedSet<HashedPtr<CFGNode> > roots;
		HashedSet<HashedPtr<const CFGNode> > proximalNodes;
		if (!getProbeCFGs(allocLabel, oracle, targetRip, roots, proximalNodes)) {
			fprintf(_logfile, "Cannot get probe CFGs!\n");
			return NULL;
		}
		sm = probeCFGsToMachine(scopes, oracle, tid._tid(),
					roots,
					proximalNodes,
					*mai);
	}
	if (TIMEOUT)
		return NULL;

	LibVEX_maybe_gc(token);

	sm->sanityCheck(*mai);
	sm = optimiseStateMachine(scopes,
				  mai,
				  sm,
				  opt,
				  oracle,
				  false,
				  token);
	
	sm = convertToSSA(scopes, sm);
	if (TIMEOUT)
		return NULL;
	sm->sanityCheck(*mai);
	sm = optimiseStateMachine(scopes,
				  mai,
				  sm,
				  opt,
				  oracle,
				  true,
				  token);
	return sm;
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
probeMachineToSummary(SMScopes *scopes,
		      CfgLabelAllocator &allocLabel,
		      const DynAnalysisRip &targetRip,
		      const VexPtr<StateMachine, &ir_heap> &probeMachine,
		      const VexPtr<StateMachine, &ir_heap> &assertionFreeProbeMachine,
		      const VexPtr<Oracle> &oracle,
		      FixConsumer &df,
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

		summary = considerStoreCFG(scopes,
					   targetRip,
					   storeCFG,
					   oracle,
					   probeMachine,
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
diagnoseCrash(SMScopes *scopes,
	      CfgLabelAllocator &allocLabel,
	      const DynAnalysisRip &targetRip,
	      VexPtr<StateMachine, &ir_heap> probeMachine,
	      const VexPtr<Oracle> &oracle,
	      FixConsumer &df,
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
	reducedProbeMachine = removeAnnotations(scopes, mai, probeMachine, optIn.enableignoreSideEffects(), oracleI, true, token);
	if (!reducedProbeMachine)
		return NULL;
	getConflictingStores(*mai, reducedProbeMachine, oracle, potentiallyConflictingStores);
	if (potentiallyConflictingStores.size() == 0) {
		fprintf(_logfile, "\t\tNo available conflicting stores?\n");
		return NULL;
	}
	bool localised_loads = false;
	probeMachine = localiseLoads(scopes,
				     mai,
				     probeMachine,
				     potentiallyConflictingStores,
				     optIn.enableignoreSideEffects(),
				     oracleI,
				     token,
				     &localised_loads);
	if (localised_loads) {
		std::set<DynAnalysisRip> newPotentiallyConflictingStores;
		while (1) {
			reducedProbeMachine = removeAnnotations(scopes, mai, probeMachine, optIn.enableignoreSideEffects(), oracleI, true, token);
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
			probeMachine = localiseLoads(scopes, mai, probeMachine,
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

	return probeMachineToSummary(scopes,
				     allocLabel,
				     targetRip,
				     probeMachine,
				     reducedProbeMachine,
				     oracle,
				     df,
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
				const AllowableOptimisations &opt,
				GarbageCollectionToken token)
{
	SMScopes scopes;

	/* Quick pre-check: see whether this instruction might crash
	 * in isolation.  A lot can't (e.g. accesses to BSS) */
	{
		StateMachineState *t = getProximalCause(&scopes,
							oracle->ms,
							oracle,
							*MaiMap::empty(),
							NULL,
							targetRip.toVexRip(),
							tid);
		if (t->type == StateMachineState::Terminal) {
			auto term = (StateMachineTerminal *)t;
			if (term->res == scopes.smrs.cnst(smr_unreached) ||
			    term->res == scopes.smrs.cnst(smr_survive)) {
				fprintf(_logfile, "Instruction is definitely non-crashing\n");
				return;
			}
		}
	}

	VexPtr<MaiMap, &ir_heap> mai(MaiMap::empty());

	VexPtr<StateMachine, &ir_heap> probeMachine;
	CfgLabelAllocator allocLabel;
	{
		struct timeval start;
		gettimeofday(&start, NULL);
		probeMachine = buildProbeMachine(&scopes, allocLabel, oracle, targetRip.toVexRip(),
						 tid, opt, mai, token);
		if (!probeMachine)
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
	}
	if (TIMEOUT)
		return;
	diagnoseCrash(&scopes, allocLabel, targetRip, probeMachine, oracle,
		      df, opt.enablenoLocalSurvival(), mai, token);
}

