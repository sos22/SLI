/* A load of random stuff which doesn't really belong anywhere. */
#include <limits.h>
#include <queue>
#include <sys/time.h>
#include <errno.h>

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
#include "allowable_optimisations.hpp"
#include "predecessor_map.hpp"
#include "control_dependence_graph.hpp"

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
			tab.set(selectors[smr_survive],  scopes->smrs.cnst(smr_survive));
		if (selectors.count(smr_unreached))
			tab.set(selectors[smr_unreached], scopes->smrs.cnst(smr_unreached));
		tab.set(selectors[smr_crash], scopes->smrs.cnst(smr_unreached));
		*progress = true;
		s->set_res(smrbdd::from_enabling(&scopes->smrs, tab, scopes->smrs.cnst(smr_unreached)));
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
	void start(SMScopes *, MaiMap *, StateMachine *, bool , const AllowableOptimisations &)
	{}
	void finish(SMScopes *, MaiMap *, StateMachine *)
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

	bool zapped_realias_info = false;

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

		sm = internStateMachine(sm);
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
				sm = internStateMachine(sm);
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

#if CONFIG_LOAD_ELIMINATION || CONFIG_PHI_ELIMINATION
		if (!done_something && is_ssa) {
			predecessor_map pred(sm);
			control_dependence_graph cdg(sm, &scopes->bools);

			p = false;
			sm = cdgOptimise(scopes, sm, cdg, &p);
			if (debugOptimiseStateMachine && p) {
				printf("cdgOptimise:\n");
				printStateMachine(sm, stdout);
			}
			if (p)
				pred.recompute(sm);
			done_something |= p;

			if (CONFIG_LOAD_ELIMINATION && !zapped_realias_info) {
				sm = functionAliasAnalysis(scopes, *mai, sm, opt,
							   oracle, cdg, pred, &p);
				if (debugOptimiseStateMachine && p) {
					printf("functionAliasAnalysis:\n");
					printStateMachine(sm, stdout);
				}
				done_something |= p;
			}

#if CONFIG_PHI_ELIMINATION
			p = false;
			sm = phiElimination(scopes, sm, pred, cdg, &p);
			if (debugOptimiseStateMachine && p) {
				printf("phiElimination:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;
#endif
		}
#endif

#if !CONFIG_NO_STATIC_ALIASING
		if (opt.noExtend() && is_ssa && !done_something && !zapped_realias_info) {
			p = false;
			sm = zapRealiasInfo(scopes, sm, &p);
			if (debugOptimiseStateMachine && p) {
				printf("zapRealiasInfo:\n");
				printStateMachine(sm, stdout);
			}
			done_something |= p;
			zapped_realias_info = true;
		}
#endif

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
			    const IRExprOptimisations &opt, OracleInterface *oracle)
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

StateMachine *
mapUnreached(smrbdd::scope *scope, StateMachine *inp, StateMachineRes res)
{
	std::vector<StateMachineTerminal *> terminals;
	enumStates(inp, &terminals);
	for (auto it = terminals.begin(); it != terminals.end(); it++)
		(*it)->set_res(smrbdd::replaceTerminal(scope, smr_unreached, res, (*it)->res));
	return inp;
}

static bbdd *
atomicSurvivalConstraint(SMScopes *scopes,
			 VexPtr<MaiMap, &ir_heap> &mai,
			 VexPtr<StateMachine, &ir_heap> &machine,
			 StateMachine **_atomicMachine,
			 VexPtr<OracleInterface> &oracle,
			 const VexPtr<bbdd, &ir_heap> &assumption,
			 const AllowableOptimisations &opt,
			 GarbageCollectionToken token)
{
	VexPtr<StateMachine, &ir_heap> atomicMachine;
	atomicMachine = duplicateStateMachine(machine);
	atomicMachine = mapUnreached(&scopes->smrs, atomicMachine, smr_crash);
	atomicMachine = optimiseStateMachine(scopes, mai, atomicMachine, opt, oracle, true, token);
	if (_atomicMachine)
		*_atomicMachine = atomicMachine;
	bbdd *survive = survivalConstraintIfExecutedAtomically(scopes, mai, atomicMachine, assumption, oracle, false, opt, token);
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
#if !CONFIG_NO_STATIC_ALIASING
			case StateMachineSideEffect::StartFunction:
			case StateMachineSideEffect::EndFunction:
			case StateMachineSideEffect::StackLayout:
#endif
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
					tab.set(selectors[smr_crash], scopes->smrs.cnst(smr_survive));
				if (selectors.count(smr_survive))
					tab.set(selectors[smr_survive], scopes->smrs.cnst(smr_survive));
				if (selectors.count(smr_unreached))
					tab.set(selectors[smr_unreached], scopes->smrs.cnst(smr_unreached));
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

static StateMachineSideEffect *
optimiseAssuming(SMScopes *scopes, StateMachineSideEffect *se, bbdd *assumption)
{
	switch (se->type) {
	case StateMachineSideEffect::Load: {
		auto sml = (StateMachineSideEffectLoad *)se;
		auto addr = exprbdd::assume(&scopes->exprs, sml->addr, assumption);
		if (addr == sml->addr)
			return sml;
		else
			return new StateMachineSideEffectLoad(sml, addr);
	}
	case StateMachineSideEffect::Store: {
		auto sms = (StateMachineSideEffectStore *)se;
		auto addr = exprbdd::assume(&scopes->exprs, sms->addr, assumption);
		auto data = exprbdd::assume(&scopes->exprs, sms->data, assumption);
		if (addr == sms->addr && data == sms->data)
			return sms;
		else
			return new StateMachineSideEffectStore(sms, addr, data);
	}
	case StateMachineSideEffect::Copy: {
		auto smc = (StateMachineSideEffectCopy *)se;
		auto data = exprbdd::assume(&scopes->exprs, smc->value, assumption);
		if (data == smc->value)
			return smc;
		else
			return new StateMachineSideEffectCopy(smc, data);
	}
	case StateMachineSideEffect::AssertFalse: {
		auto sma = (StateMachineSideEffectAssertFalse *)se;
		auto data = bbdd::assume(&scopes->bools, sma->value, assumption);
		if (data == sma->value)
			return sma;
		else
			return new StateMachineSideEffectAssertFalse(sma, data);
	}
	case StateMachineSideEffect::StartAtomic:
	case StateMachineSideEffect::EndAtomic:
	case StateMachineSideEffect::Unreached:
	case StateMachineSideEffect::ImportRegister:
		return se;
	case StateMachineSideEffect::Phi: {
		auto smp = (StateMachineSideEffectPhi *)se;
		unsigned i;
		exprbdd *v;
		for (i = 0; i < smp->generations.size(); i++) {
			v = exprbdd::assume(&scopes->exprs, smp->generations[i].val, assumption);
			if (v != smp->generations[i].val)
				break;
		}
		if (i == smp->generations.size())
			return se;
		std::vector<StateMachineSideEffectPhi::input> inputs(smp->generations);
		inputs[i].val = v;
		for (i++; i < inputs.size(); i++) {
			inputs[i].val = exprbdd::assume(&scopes->exprs, inputs[i].val, assumption);
		}
		return new StateMachineSideEffectPhi(smp, inputs);
	}

#if !CONFIG_NO_STATIC_ALIASING
	case StateMachineSideEffect::StackLayout:
		return se;
	case StateMachineSideEffect::StartFunction: {
		auto smsf = (StateMachineSideEffectStartFunction *)se;
		auto rsp = exprbdd::assume(&scopes->exprs, smsf->rsp, assumption);
		if (rsp == smsf->rsp) {
			return se;
		} else {
			return new StateMachineSideEffectStartFunction(smsf, rsp);
		}
	}
	case StateMachineSideEffect::EndFunction: {
		auto smsf = (StateMachineSideEffectEndFunction *)se;
		auto rsp = exprbdd::assume(&scopes->exprs, smsf->rsp, assumption);
		if (rsp == smsf->rsp) {
			return se;
		} else {
			return new StateMachineSideEffectEndFunction(smsf, rsp);
		}
	}
#endif
	}
	abort();
}

/* Simple optimisation if we know that @condition must be true. */
void
optimiseAssuming(SMScopes *scopes, StateMachine *sm, bbdd *condition, bool *done_something)
{
	std::vector<StateMachineState *> states;
	enumStates(sm, &states);
	for (auto it = states.begin(); it != states.end(); it++) {
		StateMachineState *s = *it;
		switch (s->type) {
		case StateMachineState::Bifurcate: {
			auto smb = (StateMachineBifurcate *)s;
			*done_something |= smb->set_condition(
				bbdd::assume(&scopes->bools, smb->condition, condition));
			break;
		}
		case StateMachineState::Terminal: {
			auto smt = (StateMachineTerminal *)s;
			*done_something |= smt->set_res(
				smrbdd::assume(&scopes->smrs, smt->res, condition));
			break;
		}
		case StateMachineState::SideEffecting: {
			auto sme = (StateMachineSideEffecting *)s;
			if (sme->sideEffect) {
				auto newSe = optimiseAssuming(scopes, sme->sideEffect, condition);
				*done_something |= (newSe != sme->sideEffect);
				sme->sideEffect = newSe;
			}
			break;
		}
		}
	}
}

static CrashSummary *
considerStoreCFG(SMScopes *scopes,
		 const DynAnalysisRip &target_rip,
		 const VexPtr<CFGNode, &ir_heap> cfg,
		 const VexPtr<Oracle> &oracle,
		 VexPtr<StateMachine, &ir_heap> probeMachine,
		 VexPtr<bbdd, &ir_heap> atomicSurvival,
		 unsigned tid,
		 const AllowableOptimisations &optIn,
		 const VexPtr<MaiMap, &ir_heap> &maiIn,
		 GarbageCollectionToken token)
{
	__set_profiling(considerStoreCFG);
	VexPtr<MaiMap, &ir_heap> mai(maiIn->dupe());
	VexPtr<StateMachine, &ir_heap> sm(storeCFGToMachine(scopes, oracle, tid, cfg, *mai));
	if (!sm || TIMEOUT) {
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

	std::map<threadAndRegister, threadAndRegister> ssaCorrespondence;
	VexPtr<StateMachine, &ir_heap> sm_ssa(convertToSSA(scopes, sm, ssaCorrespondence));
	ssaCorrespondence.clear();
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
	bool redoAtomicSurvival = false;
	probeMachine = localiseLoads(scopes,
				     mai,
				     probeMachine,
				     sm_ssa,
				     probeOptimisations,
				     oracleI,
				     token,
				     &redoAtomicSurvival);
	if (TIMEOUT)
		return NULL;

	fprintf(_logfile, "\t\tLocalised probe machine:\n");
	printStateMachine(probeMachine, _logfile);
	fprintf(_logfile, "\t\tStore machine:\n");
	printStateMachine(sm_ssa, _logfile);

	/* Special case: if the only possible interaction between the
	   probe machine and the store machine is a single load in the
	   probe machine and a single store in the store machine then
	   we don't need to do anything. */
	if (singleLoadVersusSingleStore(*mai, sm_ssa, probeMachine, probeOptimisations, oracle)) {
		fprintf(_logfile, "\t\tSingle store versus single load -> crash impossible.\n");
		return NULL;
	}

	if (redoAtomicSurvival) {
		atomicSurvival = atomicSurvivalConstraint(
			scopes,
			mai,
			probeMachine,
			NULL,
			oracleI,
			atomicSurvival,
			atomicSurvivalOptimisations(probeOptimisations.enablepreferCrash()),
			token);
		if (!atomicSurvival) {
			return NULL;
		}
		bool needReopt = false;
		optimiseAssuming(scopes, probeMachine, atomicSurvival, &needReopt);
		if (needReopt) {
			probeMachine = optimiseStateMachine(scopes, mai, probeMachine, probeOptimisations, oracle, true, token);
		}
	}

	atomicSurvival =
		writeMachineSuitabilityConstraint(
			scopes,
			mai,
			sm_ssa,
			probeMachine,
			oracleI,
			atomicSurvival,
			atomicSurvivalOptimisations(optIn.enablepreferCrash()),
			token);
	if (!atomicSurvival) {
		fprintf(_logfile, "\t\tCannot derive write machine suitability constraint\n");
		return NULL;
	}

	fprintf(_logfile, "\t\tInferred assumption:\n");
	atomicSurvival->prettyPrint(_logfile);

	VexPtr<bbdd, &ir_heap> crash_constraint;
	{
		VexPtr<StateMachine, &ir_heap> dupe_store_machine;
		dupe_store_machine = duplicateStateMachine(sm_ssa);
		crash_constraint =
			crossProductSurvivalConstraint(
				scopes,
				probeMachine,
				sm,
				oracleI,
				atomicSurvival,
				optIn.disablepreferCrash(),
				mai,
				token);
		if (!crash_constraint) {
			fprintf(_logfile, "\t\tFailed to derive crash condition\n");
			return NULL;
		}
		crash_constraint = bbdd::invert(&scopes->bools, crash_constraint);
		if (!crash_constraint || TIMEOUT) {
			return NULL;
		}
	}

	VexPtr<bbdd, &ir_heap> verification_condition;
	verification_condition =
		bbdd::And(&scopes->bools, crash_constraint, atomicSurvival);
	if (!verification_condition || TIMEOUT) {
		return NULL;
	}
	if (verification_condition == scopes->bools.cnst(false)) {
		fprintf(_logfile, "\t\tCrash impossible.\n");
		return NULL;
	}

	fprintf(_logfile, "\t\tVerification condition:\n");
	verification_condition->prettyPrint(_logfile);

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
			VexPtr<bbdd, &ir_heap> truncAtomicSurvival(
				atomicSurvivalConstraint(
					scopes,
					mai,
					truncatedMachine,
					NULL,
					oracleI,
					atomicSurvival,
					atomicSurvivalOptimisations(optIn.enablepreferCrash()),
					token));
			if (!truncAtomicSurvival) {
				continue;
			}
			truncAtomicSurvival =
				writeMachineSuitabilityConstraint(
					scopes,
					mai,
					sm_ssa,
					truncatedMachine,
					oracleI,
					truncAtomicSurvival,
					atomicSurvivalOptimisations(optIn.enablepreferCrash()),
					token);
			if (!truncAtomicSurvival) {
				continue;
			}

			bbdd *truncCrashConstraint;
			{
				VexPtr<StateMachine, &ir_heap> dupe_store_machine;
				dupe_store_machine = duplicateStateMachine(sm_ssa);
				truncCrashConstraint =
					crossProductSurvivalConstraint(
						scopes,
						probeMachine,
						sm,
						oracleI,
						truncAtomicSurvival,
						optIn.disablepreferCrash(),
						mai,
						token);
				if (!truncCrashConstraint ||
				    truncCrashConstraint->isLeaf()) {
					continue;
				}
			}

			auto t = bbdd::Or(&scopes->bools, truncAtomicSurvival, truncCrashConstraint);
			if (!t) {
				continue;
			}
			t = bbdd::invert(&scopes->bools, t);
			if (!t) {
				continue;
			}
			fprintf(_logfile, "Induction rule for %s\n",
				inductionAccesses[x]->rip.name());
			t->prettyPrint(_logfile);

			t = bbdd::And(&scopes->bools, t, atomicSurvival);
			if (!t) {
				continue;
			}
			atomicSurvival = t;
			for (auto it = mai->begin(inductionAccesses[x]->rip); !it.finished(); it.advance())
				logUseOfInduction(target_rip, it.dr());
		}

		verification_condition =
			bbdd::And(&scopes->bools, crash_constraint, atomicSurvival);
		if (!verification_condition || TIMEOUT) {
			return NULL;
		}
		if (verification_condition == scopes->bools.cnst(false)) {
			fprintf(_logfile, "\t\tCrash blocked by induction.\n");
			return NULL;
		}

		fprintf(_logfile, "\t\tInduction reduced verification condition:\n");
		verification_condition->prettyPrint(_logfile);
	}

	/* Okay, the expanded machine crashes.  That means we have to
	 * generate a fix. */
	return new CrashSummary(scopes, probeMachine, sm_ssa, atomicSurvival, crash_constraint, oracle, mai);
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
	
	std::map<threadAndRegister, threadAndRegister> ssaCorrespondence;
	sm = convertToSSA(scopes, sm, ssaCorrespondence);
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
		      const VexPtr<bbdd, &ir_heap> &atomicSurvival,
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
					   atomicSurvival,
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

	VexPtr<bbdd, &ir_heap> atomicSurvival;
	VexPtr<bbdd, &ir_heap> nullExpr(NULL);
	atomicSurvival = atomicSurvivalConstraint(scopes, mai, probeMachine, NULL, oracleI,
						  nullExpr,
						  atomicSurvivalOptimisations(optIn.enablepreferCrash()),
						  token);
	if (!atomicSurvival) {
		return NULL;
	}

	bool needReopt = false;
	optimiseAssuming(scopes, probeMachine, atomicSurvival, &needReopt);
	if (needReopt) {
		probeMachine = optimiseStateMachine(scopes, mai, probeMachine,
						    optIn.enableignoreSideEffects(),
						    oracle, true, token);
	}

	return probeMachineToSummary(scopes,
				     allocLabel,
				     targetRip,
				     probeMachine,
				     atomicSurvival,
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

