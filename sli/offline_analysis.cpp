/* A load of random stuff which doesn't really belong anywhere. */
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
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
#include "stacked_cdf.hpp"
#include "timers.hpp"

extern FILE *
bubble_plot_log;
extern FILE *
bubble_plot2_log;

#ifndef NDEBUG
static bool debugOptimiseStateMachine = false;
static bool debug_localise_loads = false;
#else
#define debugOptimiseStateMachine false
#define debug_localise_loads false
#endif

extern FILE *better_log;

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
 * here we don't rely on having access to stack layout information. */
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
		std::set<StateMachineState *> visited;
		assert(visited.empty());
		while (!mightBeLoaded && !q.empty()) {
			StateMachineState *s = q.front();
			q.pop();
			if (!visited.insert(s).second) {
				continue;
			}
			auto se = s->getSideEffect();
			if (se &&
			    se->type == StateMachineSideEffect::Load &&
			    oracle->memoryAccessesMightAlias(
				    mai,
				    opt,
				    (StateMachineSideEffectLoad *)se,
				    store) &&
			    !definitelyNotEqual(store->addr,
						((StateMachineSideEffectLoad *)se)->addr,
						opt)) {
				/* This load might load the store. */
				mightBeLoaded = true;
			} else if (se &&
				   se->type == StateMachineSideEffect::Store &&
				   oracle->memoryAccessesMightAlias(
					   mai,
					   opt,
					   (StateMachineSideEffectStore *)se,
					   store) &&
				   definitelyEqual(store->addr,
						   ((StateMachineSideEffectStore *)se)->addr,
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
		scopes->prettyPrint(f, NULL);
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
		scopes->prettyPrint(f, NULL);
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

	stackedCdf::startOptimise();
	OptimisationRecorder optrec;
	optrec.start(scopes, mai, sm, is_ssa, opt);

	bool zapped_realias_info = false;

	bool done_something;
	do {
		done_something = false;

		bool p = false;
		sm = sm->optimise(scopes, opt, &p);
		if (debugOptimiseStateMachine && p) {
			printf("Local optimise 1:\n");
			printStateMachine(sm, stdout);
		}
		done_something |= p;

		sm = internStateMachine(sm);

		p = false;
		sm = deadCodeElimination(scopes, sm, &p, is_ssa, opt);
		if (debugOptimiseStateMachine && p) {
			printf("deadCodeElimination:\n");
			printStateMachine(sm, stdout);
		}
		done_something |= p;

		LibVEX_maybe_gc(token);

		p = false;
		sm = availExpressionAnalysis(scopes, *mai, sm, opt, is_ssa, oracle, done_something, &p);
		if (debugOptimiseStateMachine && p) {
			printf("availExpressionAnalysis:\n");
			printStateMachine(sm, stdout);
		}
		done_something |= p;

		LibVEX_maybe_gc(token);

		p = false;
		sm = useInitialMemoryLoads(scopes, *mai, sm, opt, oracle, &p);
		if (debugOptimiseStateMachine && p) {
			printf("useInitialMemoryLoads:\n");
			printStateMachine(sm, stdout);
		}
		done_something |= p;

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
			bool invalidate_cdg;

			p = false;
			invalidate_cdg = false;
			sm = cdgOptimise(scopes, sm, cdg, &p, &invalidate_cdg);
			if (debugOptimiseStateMachine && p) {
				printf("cdgOptimise:\n");
				printStateMachine(sm, stdout);
			}
			if (p)
				pred.recompute(sm);
			done_something |= p;

			if (CONFIG_LOAD_ELIMINATION && !invalidate_cdg && !zapped_realias_info) {
				sm = functionAliasAnalysis(scopes, *mai, sm, opt,
							   oracle, cdg, pred, &p);
				if (debugOptimiseStateMachine && p) {
					printf("functionAliasAnalysis:\n");
					printStateMachine(sm, stdout);
				}
				done_something |= p;
			}

			if (CONFIG_PHI_ELIMINATION && !invalidate_cdg) {
				p = false;
				sm = phiElimination(scopes, sm, pred, cdg, &p);
				if (debugOptimiseStateMachine && p) {
					printf("phiElimination:\n");
					printStateMachine(sm, stdout);
				}
				done_something |= p;
			}
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
	optrec.finish(scopes, mai, sm);
	stackedCdf::stopOptimise();
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
getConflictingStores(const MaiMap &mai, StateMachine *sm, Oracle *oracle,
		     sane_map<DynAnalysisRip, IRType> &potentiallyConflictingStores,
		     bool &haveMuxOps)
{
	std::set<StateMachineSideEffectLoad *> allLoads;
	haveMuxOps = false;
	enumSideEffects(sm, allLoads);
	if (allLoads.size() == 0) {
		fprintf(_logfile, "\t\tNo loads left in store machine?\n");
		return;
	}
	for (std::set<StateMachineSideEffectLoad *>::iterator it = allLoads.begin();
	     it != allLoads.end();
	     it++) {
		if ( (*it)->tag == MemoryTag::mutex() ) {
			haveMuxOps = true;
		}
		std::set<DynAnalysisRip> ss;
		oracle->findConflictingStores(mai, *it, ss);
		for (auto it2 = ss.begin(); it2 != ss.end(); it2++) {
			auto it_di = potentiallyConflictingStores.insert(*it2, (*it)->type);
			if (!it_di.second && it_di.first->second < (*it)->type) {
				it_di.first->second = (*it)->type;
			}
		}
	}
}

#if !CONFIG_W_ISOLATION
static void
getCommunicatingInstructions(const MaiMap &mai, StateMachine *sm, Oracle *oracle,
			     std::set<DynAnalysisRip> &out)
{
	std::set<StateMachineSideEffectStore *> allStores;
	enumSideEffects(sm, allStores);
	if (allStores.size() == 0) {
		return;
	}
	for (auto it = allStores.begin(); it != allStores.end(); it++) {
		std::set<DynAnalysisRip> ls;
		oracle->findConflictingLoads(mai, *it, out);
	}
}
#endif

/* If there's precisely one interesting store in the store machine and
 * one interesting memory access in the probe machine then the whole
 * thing becomes very easy. */
static bool
singleLoadVersusSingleStore(const MaiMap &mai, StateMachine *storeMachine, StateMachine *probeMachine,
			    const IRExprOptimisations &opt, OracleInterface *oracle)
{
#if CONFIG_W_ISOLATION
	std::set<StateMachineSideEffectStore *> storeMachineAccesses;
#else
	std::set<StateMachineSideEffectMemoryAccess *> storeMachineAccesses;
#endif
	std::set<StateMachineSideEffectMemoryAccess *> probeMachineAccesses;

	enumSideEffects(storeMachine, storeMachineAccesses);
	enumSideEffects(probeMachine, probeMachineAccesses);

	StateMachineSideEffectMemoryAccess *racingStore = NULL;
	StateMachineSideEffectMemoryAccess *racingLoad = NULL;
	for (auto it = storeMachineAccesses.begin(); it != storeMachineAccesses.end(); it++) {
		auto store = *it;
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
	for (auto it = terminals.begin(); it != terminals.end(); it++) {
		(*it)->set_res(smrbdd::replaceTerminal(scope, smr_unreached, res, (*it)->res));
	}
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
	stackedCdf::startDeriveRAtomic();
	VexPtr<StateMachine, &ir_heap> atomicMachine;
	atomicMachine = duplicateStateMachine(machine);
	stackedCdf::startDeriveRAtomicResimplify();
	atomicMachine = mapUnreached(&scopes->smrs, atomicMachine, smr_crash);
	atomicMachine = optimiseStateMachine(scopes, mai, atomicMachine, opt, oracle, true, token);
	stackedCdf::stopDeriveRAtomicResimplify();
	if (_atomicMachine)
		*_atomicMachine = atomicMachine;
	stackedCdf::startDeriveRAtomicSymbolicExecute();
	bbdd *survive = survivalConstraintIfExecutedAtomically(scopes, mai, atomicMachine, assumption, oracle, false, opt, token);
	stackedCdf::stopDeriveRAtomicSymbolicExecute();
	if (!survive)
		fprintf(_logfile, "\tTimed out computing survival constraint\n");
	stackedCdf::stopDeriveRAtomic();
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
#if TRACK_FRAMES
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
		bool done_something = false;
		sm = duplicateStateMachineNoAnnotations(sm, &done_something);
		if (!done_something)
			break;
		done_something = false;
		sm = optimiseStateMachine(scopes, mai, sm, opt.enableignoreUnreached(),
					  oracle, is_ssa, token, &done_something);
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

static void
findNonLocalLoads(const MaiMap &mai,
		  OracleInterface *oracle,
		  StateMachine *storeMachine,
		  StateMachine *probeMachine,
		  std::set<DynAnalysisRip> &nonLocalLoads)
{
	std::set<StateMachineSideEffectStore *> stores;
	enumSideEffects(storeMachine, stores);
	std::set<StateMachineSideEffectLoad *> loads;
	enumSideEffects(probeMachine, loads);
	for (auto it = loads.begin(); it != loads.end(); it++) {
		StateMachineSideEffectLoad *load = *it;
		if (debug_localise_loads) {
			printf("Load %s\n", load->rip.name());
		}
		for (auto it2 = mai.begin(load->rip); !it2.finished(); it2.advance()) {
			DynAnalysisRip dr(it2.dr());
			bool found_one = false;
			if (debug_localise_loads) {
				printf("    Sub-load %s\n", dr.name());
			}
			for (auto it3 = stores.begin(); !found_one && it3 != stores.end(); it3++) {
				StateMachineSideEffectStore *store = *it3;
				if (debug_localise_loads) {
					printf("        Store %s\n", store->rip.name());
				}
				if (store->tag != load->tag)
					continue;
				for (auto it4 = mai.begin(store->rip); !found_one && !it4.finished(); it4.advance()) {
					if (oracle->memoryAccessesMightAliasCrossThread(dr, it4.dr())) {
						if (debug_localise_loads) {
							printf("            Sub-store %s aliases\n", it4.dr().name());
						}
						found_one = true;
					} else {
						if (debug_localise_loads) {
							printf("            Sub-store %s no alias\n", it4.dr().name());
						}
					}
				}
			}
			if (found_one) {
				if (debug_localise_loads) {
					printf("    Sub-load %s is non-local\n", dr.name());
				}
				nonLocalLoads.insert(dr);
			} else {
				if (debug_localise_loads) {
					printf("    Sub-load %s is local\n", dr.name());
				}
			}
		}
	}
}

static StateMachine *
localiseLoads1(SMScopes *scopes,
	       VexPtr<MaiMap, &ir_heap> &mai,
	       const VexPtr<StateMachine, &ir_heap> &probeMachine,
	       const VexPtr<StateMachine, &ir_heap> &storeMachine,
	       const AllowableOptimisations &opt,
	       const VexPtr<OracleInterface> &oracle,
	       GarbageCollectionToken token,
	       bool *done_something = NULL)
{
	if (debug_localise_loads) {
		printf("%s\n", __PRETTY_FUNCTION__);
	}

	std::set<DynAnalysisRip> nonLocalLoads;
	findNonLocalLoads(*mai, oracle, storeMachine, probeMachine, nonLocalLoads);
#if !CONFIG_W_ISOLATION
	findNonLocalLoads(*mai, oracle, probeMachine, storeMachine, nonLocalLoads);
#endif
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
localiseLoads2(SMScopes *scopes,
	       VexPtr<MaiMap, &ir_heap> &mai,
	       const VexPtr<StateMachine, &ir_heap> &probeMachine,
	       const std::map<DynAnalysisRip, IRType> &stores,
	       const AllowableOptimisations &opt,
	       const VexPtr<OracleInterface> &oracle,
	       GarbageCollectionToken token,
	       bool *done_something = NULL)
{
	std::set<DynAnalysisRip> nonLocalLoads;
	{
		std::set<StateMachineSideEffectLoad *> loads;
		enumSideEffects(probeMachine, loads);
		if (debug_localise_loads && loads.empty()) {
			printf("localiseLoads: loads set is empty?\n");
		}
		for (auto it = loads.begin(); it != loads.end(); it++) {
			StateMachineSideEffectLoad *load = *it;
			if (debug_localise_loads) {
				printf("Check whether %s is local...\n", load->rip.name());
			}
			for (auto it3 = mai->begin(load->rip); !it3.finished(); it3.advance()) {
				bool found_one = false;
				if (debug_localise_loads) {
					printf("    Load %s\n", it3.dr().name());
				}
				for (auto it2 = stores.begin(); !found_one && it2 != stores.end(); it2++) {
					DynAnalysisRip store = it2->first;
					if (oracle->memoryAccessesMightAliasCrossThread(it3.dr(), store)) {
						if (debug_localise_loads) {
							printf("       Store %s -> alias\n", store.name());
						}
						found_one = true;
					} else {
						if (debug_localise_loads) {
							printf("        Store %s -> no alias\n", store.name());
						}
					}
				}
				if (found_one) {
					if (debug_localise_loads) {
						printf("    %s is non-local\n", it3.dr().name());
					}
					nonLocalLoads.insert(it3.dr());
				} else {
					if (debug_localise_loads) {
						printf("    %s is local\n", it3.dr().name());
					}
				}
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

StateMachineSideEffect *
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

#if TRACK_FRAMES
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

#if !CONFIG_W_ISOLATION
static void
rebuildConflictingStores(const MaiMap &decode,
			 const AllowableOptimisations &opt,
			 OracleInterface *oracle,
			 StateMachine *probeMachine,
			 StateMachine *storeMachine,
			 sane_map<DynAnalysisRip, IRType> &out)
{
	struct {
		sane_map<DynAnalysisRip, IRType> *out;
		void operator()(const DynAnalysisRip &dr, IRType ty) {
			auto it_did_insert = out->insert(dr, ty);
			if (it_did_insert.first->second < ty) {
				it_did_insert.first->second = ty;
			}
		}
	} add;
	add.out = &out;
	std::set<StateMachineSideEffectLoad *> loads;
	std::set<StateMachineSideEffectStore *> stores;
	enumSideEffects(probeMachine, stores);
	enumSideEffects(storeMachine, loads);
	for (auto it = loads.begin(); it != loads.end(); it++) {
		auto l = *it;
		for (auto it2 = stores.begin(); it2 != stores.end(); it2++) {
			auto s = *it2;
			if (l->tag != s->tag) {
				break;
			}
			if (l->tag == MemoryTag::last_free() || l->tag == MemoryTag::mutex()) {
				for (auto it3 = decode.begin(s->rip); !it3.finished(); it3.advance()) {
					add(it3.dr(), l->type);
				}
				continue;
			}
			if (definitelyNotEqual(l->addr, s->addr, opt)) {
				continue;
			}
			for (auto it3 = decode.begin(l->rip); !it3.finished(); it3.advance()) {
				for (auto it4 = decode.begin(s->rip); !it4.finished(); it4.advance()) {
					if (oracle->memoryAccessesMightAliasCrossThread(it3.dr(), it4.dr())) {
						add(it4.dr(), l->type);
					}
				}
			}
		}
	}
}
#endif

static int
countMachineStates(StateMachine *sm)
{
	std::set<StateMachineState *> states;
	enumStates(sm, &states);
	return states.size();
}

static int
countCfgInstructions(const CFGNode *root)
{
	std::set<const CFGNode *> visited;
	std::vector<const CFGNode *> q;
	q.push_back(root);
	while (!q.empty()) {
		const CFGNode *n = q.back();
		q.pop_back();
		if (!visited.insert(n).second) {
			continue;
		}
		for (auto it = n->successors.begin(); it != n->successors.end(); it++) {
			if (it->instr) {
				q.push_back(it->instr);
			}
		}
	}
	return visited.size();
}
static int
countCfgInstructions(const HashedSet<HashedPtr<CFGNode> > &roots)
{
	std::set<const CFGNode *> visited;
	std::vector<const CFGNode *> q;
	for (auto it = roots.begin(); !it.finished(); it.advance()) {
		q.push_back(*it);
	}
	while (!q.empty()) {
		const CFGNode *n = q.back();
		q.pop_back();
		if (!visited.insert(n).second) {
			continue;
		}
		for (auto it = n->successors.begin(); it != n->successors.end(); it++) {
			if (it->instr) {
				q.push_back(it->instr);
			}
		}
	}
	return visited.size();
}

static StateMachine *
buildStoreMachine(SMScopes *scopes,
		  const VexPtr<Oracle> &oracle,
		  unsigned tid,
		  unsigned idx,
		  unsigned nrStoreCfgs,
		  const VexPtr<CFGNode, &ir_heap> &cfg,
		  VexPtr<MaiMap, &ir_heap> &mai,
		  const AllowableOptimisations &storeOptimisations,
		  GarbageCollectionToken token)
{
	stackedCdf::startCompileStoreMachine();
	fprintf(bubble_plot2_log, "%f: start compiling interfering CFG\n", now());
	VexPtr<StateMachine, &ir_heap> sm(storeCFGToMachine(scopes, oracle, tid, cfg, *mai));
	fprintf(bubble_plot2_log, "%f: stop compiling interfering CFG\n", now());
	stackedCdf::stopCompileStoreMachine();

	fprintf(better_log, "%d/%d: Initial interfering StateMachine has %d states\n",
		idx, nrStoreCfgs, countMachineStates(sm));
	stackedCdf::startStoreInitialSimplify();
	fprintf(bubble_plot2_log, "%f: start simplifying interfering CFG\n", now());
	sm = optimiseStateMachine(
		scopes,
		mai,
		sm,
		storeOptimisations,
		oracle,
		false,
		token);
	fprintf(bubble_plot2_log, "%f: stop simplifying interfering CFG\n", now());
	stackedCdf::stopStoreInitialSimplify();

	std::map<threadAndRegister, threadAndRegister> ssaCorrespondence;
	stackedCdf::startStoreConvertToSSA();
	fprintf(bubble_plot2_log, "%f: start compiling interfering CFG\n", now());
	VexPtr<StateMachine, &ir_heap> sm_ssa(convertToSSA(scopes, sm, ssaCorrespondence));
	ssaCorrespondence.clear();
	fprintf(bubble_plot2_log, "%f: stop compiling interfering CFG\n", now());
	stackedCdf::stopStoreConvertToSSA();

	stackedCdf::startStoreSecondSimplify();
	fprintf(bubble_plot2_log, "%f: start simplifying interfering CFG\n", now());
	sm_ssa = optimiseStateMachine(
		scopes,
		mai,
		sm_ssa,
		storeOptimisations,
		oracle,
		true,
		token);
	fprintf(bubble_plot2_log, "%f: stop simplifying interfering CFG\n", now());
	stackedCdf::stopStoreSecondSimplify();

	fprintf(better_log, "%d/%d: Simplified interfering StateMachine has %d states\n",
		idx, nrStoreCfgs, countMachineStates(sm_ssa));

	return sm_ssa;
}

static CrashSummary *
considerStoreCFG(SMScopes *scopes,
		 const DynAnalysisRip &target_rip,
		 const VexPtr<CFGNode, &ir_heap> cfg,
		 const VexPtr<Oracle> &oracle,
		 VexPtr<StateMachine, &ir_heap> probeMachine,
		 VexPtr<bbdd, &ir_heap> atomicSurvival,
		 unsigned tid,
		 unsigned idx,
		 unsigned nrStoreCfgs,
		 const AllowableOptimisations &optIn,
		 const VexPtr<MaiMap, &ir_heap> &maiIn,
#if !CONFIG_W_ISOLATION
		 const sane_map<DynAnalysisRip, IRType> &potentiallyConflictingStores,
#endif
		 GarbageCollectionToken token)
{
	__set_profiling(considerStoreCFG);
	VexPtr<MaiMap, &ir_heap> mai(maiIn->dupe());
	AllowableOptimisations storeOptimisations = optIn.enablemustStoreBeforeCrash();
	AllowableOptimisations probeOptimisations = optIn;
	if (CONFIG_W_ISOLATION) {
		probeOptimisations = probeOptimisations.enableignoreSideEffects();
		storeOptimisations = storeOptimisations
			.enableassumeNoInterferingStores()
			.enableassumeExecutesAtomically();
	}

	VexPtr<StateMachine, &ir_heap> sm_ssa;

	{
		Stopwatch s;
		sm_ssa = buildStoreMachine(scopes, oracle, tid, idx, nrStoreCfgs, cfg,
					   mai, storeOptimisations,
					   token);
		if (!sm_ssa) {
			fprintf(better_log, "%d/%d: buildStoreMachine timed out\n",
				idx, nrStoreCfgs);
			return NULL;
		}
		fprintf(better_log, "%d/%d: buildStoreMachine took %f\n",
			idx, nrStoreCfgs, s.sample());
	}

	Stopwatch s;

	fprintf(bubble_plot2_log, "%f: start rederive crashing\n", now());
#if !CONFIG_W_ISOLATION
	sane_map<DynAnalysisRip, IRType> newConflicting(potentiallyConflictingStores);
	rebuildConflictingStores(*mai, optIn, oracle, probeMachine, sm_ssa, newConflicting);
	probeOptimisations = probeOptimisations.setinterestingStores(&newConflicting);
#endif

	VexPtr<OracleInterface> oracleI(oracle);
	probeMachine = duplicateStateMachine(probeMachine);
	bool redoAtomicSurvival = false;
	probeMachine = localiseLoads1(scopes,
				      mai,
				      probeMachine,
				      sm_ssa,
				      probeOptimisations,
				      oracleI,
				      token,
				      &redoAtomicSurvival);
	fprintf(bubble_plot2_log, "%f: stop rederive crashing\n", now());

	/* Special case: if the only possible interaction between the
	   probe machine and the store machine is a single load in the
	   probe machine and a single store in the store machine then
	   we don't need to do anything. */
	fprintf(bubble_plot2_log, "%f: start early-out\n", now());
	if (singleLoadVersusSingleStore(*mai, sm_ssa, probeMachine, probeOptimisations, oracle)) {
		fprintf(bubble_plot2_log, "%f: stop early-out\n", now());
		fprintf(bubble_plot2_log, "%f: early out\n", now());
		fprintf(_logfile, "\t\tSingle store versus single load -> crash impossible.\n");
		fprintf(better_log, "%d/%d: single store versus single load, after localise (%f)\n",
			idx, nrStoreCfgs, s.sample());
		return NULL;
	}
	fprintf(bubble_plot2_log, "%f: stop early-out\n", now());

	if (redoAtomicSurvival) {
		fprintf(bubble_plot2_log, "%f: start rederive crashing\n", now());
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
			fprintf(bubble_plot2_log, "%f: stop rederive crashing\n", now());
			fprintf(bubble_plot2_log, "%f: failed rederive crashing\n", now());
			fprintf(better_log, "%d/%d: rederive CI atomic timed out\n", idx, nrStoreCfgs);
			return NULL;
		}
		if (atomicSurvival == scopes->bools.cnst(false)) {
			fprintf(_logfile, "\t\tCannot survive when run atomically -> give up\n");
			fprintf(better_log, "%d/%d: rederived CI atomic is false (%f)\n", idx, nrStoreCfgs, s.sample());
			fprintf(bubble_plot2_log, "%f: stop rederive crashing\n", now());
			fprintf(bubble_plot2_log, "%f: ic-atomic is false\n", now());
			return NULL;
		}
		bool needReopt = false;
		optimiseAssuming(scopes, probeMachine, atomicSurvival, &needReopt);
		if (needReopt) {
			probeMachine = optimiseStateMachine(scopes, mai, probeMachine, probeOptimisations, oracle, true, token);
		}
		fprintf(bubble_plot2_log, "%f: stop rederive crashing\n", now());
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
		fprintf(better_log, "%d/%d: IC atomic timed out\n", idx, nrStoreCfgs);
		return NULL;
	}
	if (atomicSurvival == scopes->bools.cnst(false)) {
		fprintf(_logfile, "\t\tWrite machine constraint is false!\n");
		fprintf(better_log, "%d/%d: IC is false (%f)\n", idx, nrStoreCfgs, s.sample());
		fprintf(bubble_plot2_log, "%f: ic-atomic is false\n", now());
		return NULL;
	}

	VexPtr<bbdd, &ir_heap> crash_constraint;
	{
		VexPtr<StateMachine, &ir_heap> dupe_store_machine;
		fprintf(bubble_plot2_log, "%f: start cross build\n", now());
		dupe_store_machine = duplicateStateMachine(sm_ssa);
		fprintf(bubble_plot2_log, "%f: stop cross build\n", now());
		crash_constraint =
			crossProductSurvivalConstraint(
				scopes,
				probeMachine,
				sm_ssa,
				oracleI,
				atomicSurvival,
				optIn.disablepreferCrash(),
				mai,
				token);
		if (!crash_constraint) {
			fprintf(_logfile, "\t\tFailed to derive crash condition\n");
			fprintf(better_log, "%d/%d: crash timed out\n", idx, nrStoreCfgs);
			return NULL;
		}
	}
	fprintf(bubble_plot2_log, "%f: start sat check\n", now());
	crash_constraint = bbdd::invert(&scopes->bools, crash_constraint);

	VexPtr<bbdd, &ir_heap> verification_condition;
	verification_condition =
		bbdd::And(&scopes->bools, crash_constraint, atomicSurvival);
	verification_condition = subst_eq(&scopes->bools, verification_condition);
	fprintf(bubble_plot2_log, "%f: stop sat check\n", now());
	if (verification_condition == scopes->bools.cnst(false)) {
		fprintf(_logfile, "\t\tCrash impossible.\n");
		fprintf(better_log, "%d/%d: crash impossible (%f)\n", idx, nrStoreCfgs, s.sample());
		fprintf(bubble_plot2_log, "%f: unsatisfiable\n", now());
		return NULL;
	}
	fprintf(bubble_plot2_log, "%f: satisfiable\n", now());

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
						sm_ssa,
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
		if (verification_condition == scopes->bools.cnst(false)) {
			fprintf(_logfile, "\t\tCrash blocked by induction.\n");
			return NULL;
		}

		fprintf(_logfile, "\t\tInduction reduced verification condition:\n");
		verification_condition->prettyPrint(_logfile);
	}

	fprintf(better_log, "%d/%d: generated VC (%f)\n", idx, nrStoreCfgs, s.sample());

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
		optIn;

	if (CONFIG_W_ISOLATION) {
		opt = opt.enableignoreSideEffects();
	}

	VexPtr<StateMachine, &ir_heap> sm;
	{
		HashedSet<HashedPtr<CFGNode> > roots;
		HashedSet<HashedPtr<const CFGNode> > proximalNodes;
		fprintf(bubble_plot_log, "%f: start build crashing CFG\n", now());
		auto r = getProbeCFGs(allocLabel, oracle, targetRip, roots, proximalNodes);
		if (!r) {
			fprintf(bubble_plot_log, "%f: failed build crashing CFG\n", now());
			fprintf(_logfile, "Cannot get probe CFGs!\n");
			return NULL;
		}
		fprintf(bubble_plot_log, "%f: stop build crashing CFG\n", now());
		fprintf(better_log, "Crashing CFG has %d instructions\n",
			countCfgInstructions(roots));
		stackedCdf::startCompileProbeMachine();
		fprintf(bubble_plot_log, "%f: start compile crashing machine\n", now());
		sm = probeCFGsToMachine(scopes, oracle, tid._tid(),
					roots,
					proximalNodes,
					*mai);
		fprintf(bubble_plot_log, "%f: stop compile crashing machine\n", now());
		stackedCdf::stopCompileProbeMachine();
	}
	fprintf(better_log, "Initial crashing machine has %d states\n",
		countMachineStates(sm));

	fprintf(bubble_plot_log, "%f: start GC\n", now());
	LibVEX_maybe_gc(token);
	fprintf(bubble_plot_log, "%f: stop GC\n", now());

	sm->sanityCheck(*mai);
	stackedCdf::startProbeInitialSimplify();
	fprintf(bubble_plot_log, "%f: start simplify crashing machine\n", now());
	sm = optimiseStateMachine(scopes,
				  mai,
				  sm,
				  opt,
				  oracle,
				  false,
				  token);
	fprintf(bubble_plot_log, "%f: stop simplify crashing machine\n", now());
	stackedCdf::stopProbeInitialSimplify();

	std::map<threadAndRegister, threadAndRegister> ssaCorrespondence;
	stackedCdf::startProbeConvertSSA();
	fprintf(bubble_plot_log, "%f: start compile crashing machine\n", now());
	sm = convertToSSA(scopes, sm, ssaCorrespondence);
	fprintf(bubble_plot_log, "%f: stop compile crashing machine\n", now());
	stackedCdf::stopProbeConvertSSA();
	sm->sanityCheck(*mai);
	stackedCdf::startProbeSecondSimplify();
	fprintf(bubble_plot_log, "%f: start simplify crashing machine\n", now());
	sm = optimiseStateMachine(scopes,
				  mai,
				  sm,
				  opt,
				  oracle,
				  true,
				  token);
	fprintf(bubble_plot_log, "%f: stop simplify crashing machine\n", now());
	stackedCdf::stopProbeSecondSimplify();
	fprintf(better_log, "Simplified crashing machine has %d states\n",
		countMachineStates(sm));
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

static void
processOneStoreCfg(SMScopes *scopes,
		   const DynAnalysisRip &targetRip,
		   const VexPtr<CFGNode *, &ir_heap> &storeCFGs,
		   int i,
		   int nrStoreCfgs,
		   enum StateMachineState::RoughLoadCount roughLoadCount,
		   const VexPtr<StateMachine, &ir_heap> &probeMachine,
		   const VexPtr<bbdd, &ir_heap> &atomicSurvival,
		   const VexPtr<StateMachine, &ir_heap> &assertionFreeProbeMachine,
		   const VexPtr<Oracle> &oracle,
		   FixConsumer &df,
		   const sane_map<DynAnalysisRip, IRType> &potentiallyConflictingStores,
#if !CONFIG_W_ISOLATION
		   const std::set<DynAnalysisRip> &communicatingInstructions,
#endif
		   bool preserveMux,
		   const AllowableOptimisations &optIn,
		   const VexPtr<MaiMap, &ir_heap> &maiIn,
		   GarbageCollectionToken token)
{
	fprintf(better_log, "%d/%d: Interfering CFG has %d instructions\n",
		i, nrStoreCfgs, countCfgInstructions(storeCFGs[i]));
	bool singleNodeCfg = isSingleNodeCfg(storeCFGs[i]);
	if (CONFIG_W_ISOLATION && roughLoadCount == StateMachineState::singleLoad && singleNodeCfg) {
		fprintf(_logfile, "Single store versus single load -> no race possible\n");
		fprintf(better_log, "%d/%d: single store versus single load\n",
			i, nrStoreCfgs);
		return;
	}

	if (CONFIG_W_ISOLATION &&
	    singleNodeCfg &&
	    machineHasOneRacingLoad(*maiIn, assertionFreeProbeMachine, storeCFGs[i]->rip, oracle)) {
		fprintf(_logfile, "Single store versus single shared load -> no race possible\n");
		fprintf(better_log, "%d/%d: single store versus single shared load\n",
			i, nrStoreCfgs);
		return;
	}

	VexPtr<CFGNode, &ir_heap> storeCFG(storeCFGs[i]);
	VexPtr<CrashSummary, &ir_heap> summary;

	if (run_in_child(bubble_plot2_log, token)) {
		return;
	}

	TimeoutTimer timer2;
	timer2.timeoutAfterSeconds(CONFIG_TIMEOUT2);
	fprintf(bubble_plot2_log, "%f: start interfering CFG\n", now());
	summary = considerStoreCFG(scopes,
				   targetRip,
				   storeCFG,
				   oracle,
				   probeMachine,
				   atomicSurvival,
				   STORING_THREAD + i,
				   i,
				   nrStoreCfgs,
				   optIn
#if CONFIG_W_ISOLATION
				   .setinterestingStores(&potentiallyConflictingStores)
#endif
				   .setmutexStoresInteresting(preserveMux),
				   maiIn,
#if !CONFIG_W_ISOLATION
				   potentiallyConflictingStores,
#endif
				   token);
	fprintf(bubble_plot2_log, "%f: stop interfering CFG\n", now());
	if (summary)
		df(summary, token);

	exit(0);
}

static void
probeMachineToSummary(SMScopes *scopes,
		      CfgLabelAllocator &allocLabel,
		      const DynAnalysisRip &targetRip,
		      const VexPtr<StateMachine, &ir_heap> &probeMachine,
		      const VexPtr<bbdd, &ir_heap> &atomicSurvival,
		      const VexPtr<StateMachine, &ir_heap> &assertionFreeProbeMachine,
		      const VexPtr<Oracle> &oracle,
		      FixConsumer &df,
		      const sane_map<DynAnalysisRip, IRType> &potentiallyConflictingStores,
#if !CONFIG_W_ISOLATION
		      const std::set<DynAnalysisRip> &communicatingInstructions,
#endif
		      bool preserveMux,
		      const AllowableOptimisations &optIn,
		      const VexPtr<MaiMap, &ir_heap> &maiIn,
		      TimeoutTimer &timer,
		      int only_store_cfg,
		      int expected_nr_store_cfgs,
		      GarbageCollectionToken token)
{
	assert(potentiallyConflictingStores.size() > 0);

	VexPtr<CFGNode *, &ir_heap> storeCFGs;
	int nrStoreCfgs;
	{
		CFGNode **n;
		Stopwatch s;

		stackedCdf::startBuildStoreCFGs();
		fprintf(bubble_plot_log, "%f: start derive interfering CFGs\n", now());
		getStoreCFGs(allocLabel, potentiallyConflictingStores,
#if !CONFIG_W_ISOLATION
			     communicatingInstructions,
#endif
			     oracle, &n, &nrStoreCfgs);
		fprintf(bubble_plot_log, "%f: stop derive interfering CFGs\n", now());
		stackedCdf::stopBuildStoreCFGs();
		storeCFGs = n;

		fprintf(better_log,
			"getStoreCFGs took %f seconds, produced %d \n",
			s.sample(),
			nrStoreCfgs);
	}
	assert(nrStoreCfgs != 0);

	if (expected_nr_store_cfgs != -1 && expected_nr_store_cfgs != nrStoreCfgs) {
		errx(1, "Expected %d store CFGs, found %d",
		     expected_nr_store_cfgs, nrStoreCfgs);
	}
	auto roughLoadCount = assertionFreeProbeMachine->root->roughLoadCount();

	timer.cancel();

	fprintf(bubble_plot_log, "%f: start process interfering CFGs\n", now());
	if (only_store_cfg == -1) {
		for (int i = 0; i < nrStoreCfgs; i++) {
			processOneStoreCfg(scopes, targetRip, storeCFGs, i, nrStoreCfgs,
					   roughLoadCount, probeMachine, atomicSurvival,
					   assertionFreeProbeMachine, oracle, df,
					   potentiallyConflictingStores,
#if !CONFIG_W_ISOLATION
					   communicatingInstructions,
#endif
					   preserveMux, optIn, maiIn, token);
		}
	} else {
		processOneStoreCfg(scopes, targetRip, storeCFGs, only_store_cfg, nrStoreCfgs,
				   roughLoadCount, probeMachine, atomicSurvival,
				   assertionFreeProbeMachine, oracle, df,
				   potentiallyConflictingStores,
#if !CONFIG_W_ISOLATION
				   communicatingInstructions,
#endif
				   preserveMux, optIn, maiIn, token);
	}
	fprintf(bubble_plot_log, "%f: stop process interfering CFGs\n", now());
}

void
diagnoseCrash(SMScopes *scopes,
	      CfgLabelAllocator &allocLabel,
	      const DynAnalysisRip &targetRip,
	      VexPtr<StateMachine, &ir_heap> probeMachine,
	      const VexPtr<Oracle> &oracle,
	      FixConsumer &df,
	      const AllowableOptimisations &optIn,
	      VexPtr<MaiMap, &ir_heap> &mai,
	      TimeoutTimer &timer,
	      int only_store_cfg,
	      int expected_nr_store_cfgs,
	      GarbageCollectionToken token)
{
	__set_profiling(diagnoseCrash);

	AllowableOptimisations probeOpt = optIn;
	if (CONFIG_W_ISOLATION) {
		probeOpt = probeOpt.enableignoreSideEffects();
	}

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
	bool haveMuxOps;
	sane_map<DynAnalysisRip, IRType> potentiallyConflictingStores;
	VexPtr<StateMachine, &ir_heap> reducedProbeMachine(probeMachine);

	stackedCdf::startFindConflictingStores();
	VexPtr<OracleInterface> oracleI(oracle);
	/* Note that removeAnnotations always gets
	   enableignoreSideEffects(), even in the non-W_ISOLATION
	   case, because it's only used to find the interfering stores
	   set. */
	fprintf(bubble_plot_log, "%f: start derive interfering CFGs\n", now());
	reducedProbeMachine = removeAnnotations(scopes, mai, probeMachine, optIn.enableignoreSideEffects(), oracleI, true, token);
	getConflictingStores(*mai, reducedProbeMachine, oracle, potentiallyConflictingStores, haveMuxOps);
	fprintf(bubble_plot_log, "%f: stop derive interfering CFGs\n", now());
	if (potentiallyConflictingStores.size() == 0) {
		stackedCdf::stopFindConflictingStores();
		fprintf(_logfile, "\t\tNo available conflicting stores?\n");
		fprintf(better_log, "no conflicting stores\n");
		fprintf(bubble_plot_log, "%f: no interfering stores\n", now());
		return;
	}
	fprintf(bubble_plot_log, "%f: start simplify crashing machine\n", now());
	bool localised_loads = false;
	probeMachine = localiseLoads2(scopes,
				      mai,
				      probeMachine,
				      potentiallyConflictingStores,
				      probeOpt,
				      oracleI,
				      token,
				      &localised_loads);
	fprintf(bubble_plot_log, "%f: stop simplify crashing machine\n", now());

	if (localised_loads) {
		sane_map<DynAnalysisRip, IRType> newPotentiallyConflictingStores;
		while (1) {
			fprintf(bubble_plot_log, "%f: start derive interfering CFGs\n", now());
			reducedProbeMachine = removeAnnotations(scopes, mai, probeMachine, probeOpt, oracleI, true, token);
			if (!reducedProbeMachine) {
				stackedCdf::stopFindConflictingStores();
				fprintf(better_log, "removeAnnotations timed out (%d)\n", __LINE__);
				fprintf(bubble_plot_log, "%f: stop derive interfering CFGs\n", now());
				fprintf(bubble_plot_log, "%f: failed derive interfering CFGs\n", now());
				return;
			}
			getConflictingStores(*mai, reducedProbeMachine, oracle, newPotentiallyConflictingStores, haveMuxOps);
			fprintf(bubble_plot_log, "%f: stop derive interfering CFGs\n", now());
			if (potentiallyConflictingStores.size() == 0) {
				fprintf(_logfile, "\t\tNo available conflicting stores?\n");
				stackedCdf::stopFindConflictingStores();
				fprintf(better_log, "No conflicting stores (%d)\n", __LINE__);
				fprintf(bubble_plot_log, "%f: no interfering stores\n", now());
				return;
			}
			if (newPotentiallyConflictingStores == potentiallyConflictingStores)
				break;
			potentiallyConflictingStores = newPotentiallyConflictingStores;
			localised_loads = false;
			fprintf(bubble_plot_log, "%f: start simplify crashing machine\n", now());
			probeMachine = localiseLoads2(scopes, mai, probeMachine,
						      potentiallyConflictingStores,
						      probeOpt,
						      oracleI, token, &localised_loads);
			fprintf(bubble_plot_log, "%f: stop simplify crashing machine\n", now());
			if (!localised_loads)
				break;
		}
	}
	stackedCdf::stopFindConflictingStores();

	if (potentiallyConflictingStores.size() == 0) {
		fprintf(_logfile, "\t\tNo available conflicting stores after localisation?\n");
		fprintf(better_log, "No conflicting stores (%d)\n", __LINE__);
		fprintf(bubble_plot_log, "%f: no interfering stores\n", now());
		return;
	}

	VexPtr<bbdd, &ir_heap> atomicSurvival;
	VexPtr<bbdd, &ir_heap> nullExpr(NULL);
	{
		Stopwatch s;
		fprintf(bubble_plot_log, "%f: start derive c-atomic\n", now());
		atomicSurvival = atomicSurvivalConstraint(scopes, mai, probeMachine, NULL, oracleI,
							  nullExpr,
							  atomicSurvivalOptimisations(optIn.enablepreferCrash()),
							  token);
		fprintf(bubble_plot_log, "%f: stop derive c-atomic\n", now());
		if (!atomicSurvival) {
			fprintf(better_log, "atomicSurvivalConstraint timed out\n");
			fprintf(bubble_plot_log, "%f: failed derive c-atomic\n", now());
			return;
		}
		fprintf(better_log, "atomicSurvivalConstraint took %f\n", s.sample());
	}
	if (atomicSurvival == scopes->bools.cnst(false)) {
		fprintf(_logfile, "\t\tAtomic constraint of reduced machine is <false> -> no crash possible\n");
		fprintf(better_log, "atomicSurvivalConstraint is false\n");
		fprintf(bubble_plot_log, "%f: c-atomic is false\n", now());
		return;
	}
	bool needReopt = false;
	fprintf(bubble_plot_log, "%f: start simplify crashing machine\n", now());
	optimiseAssuming(scopes, probeMachine, atomicSurvival, &needReopt);
	if (needReopt) {
		stackedCdf::startProbeResimplify();
		probeMachine = optimiseStateMachine(scopes, mai, probeMachine,
						    probeOpt,
						    oracle, true, token);
		stackedCdf::stopProbeResimplify();
	}
	fprintf(bubble_plot_log, "%f: stop simplify crashing machine\n", now());

#if !CONFIG_W_ISOLATION
	std::set<DynAnalysisRip> communicatingInstructions;
	VexPtr<StateMachine, &ir_heap> semiReduced;
	fprintf(bubble_plot_log, "%f: start derive interfering CFGs\n", now());
	semiReduced = removeAnnotations(scopes, mai, probeMachine, optIn, oracleI, true, token);
	getCommunicatingInstructions(*mai, semiReduced, oracle, communicatingInstructions);
	fprintf(bubble_plot_log, "%f: stop derive interfering CFGs\n", now());
#endif

	probeMachineToSummary(scopes,
			      allocLabel,
			      targetRip,
			      probeMachine,
			      atomicSurvival,
			      reducedProbeMachine,
			      oracle,
			      df,
			      potentiallyConflictingStores,
#if !CONFIG_W_ISOLATION
			      communicatingInstructions,
#endif
			      haveMuxOps,
			      optIn,
			      mai,
			      timer,
			      only_store_cfg,
			      expected_nr_store_cfgs,
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
				int only_store_cfg,
				int expected_nr_store_cfgs,
				GarbageCollectionToken token)
{
	if (better_log) {
		fclose(better_log);
	}
	{
		/* We need to set append mode so that we can share the
		   file between parent and child. */
		char *pathbuf = my_asprintf("%s.log", targetRip.name());
		unlink(pathbuf);
		better_log = fopen(pathbuf, "a");
		free(pathbuf);
		setlinebuf(better_log);
	}

	if (run_in_child(bubble_plot_log, token)) {
		return;
	}

	fprintf(better_log, "Start processing\n");
	TimeoutTimer timer1;

	timer1.timeoutAfterSeconds(CONFIG_TIMEOUT1);

	SMScopes scopes;

	/* Quick pre-check: see whether this instruction might crash
	 * in isolation.  A lot can't (e.g. accesses to BSS) */
	{
		stackedCdf::startBuildProbeMachine();
		fprintf(bubble_plot_log, "%f: start early-out check\n", now());
		StateMachineState *t = getProximalCause(&scopes,
							oracle->ms,
							oracle,
							NULL,
							targetRip.toVexRip(),
							tid);
		fprintf(bubble_plot_log, "%f: stop early-out check\n", now());
		stackedCdf::stopBuildProbeMachine();
		if (t->type == StateMachineState::Terminal) {
			auto term = (StateMachineTerminal *)t;
			if (term->res == scopes.smrs.cnst(smr_unreached) ||
			    term->res == scopes.smrs.cnst(smr_survive)) {
				fprintf(_logfile, "Instruction is definitely non-crashing\n");
				fprintf(bubble_plot_log, "%f: early out\n", now());
				fprintf(better_log, "Early out\n");
				exit(0);
			}
		}
	}

	VexPtr<MaiMap, &ir_heap> mai(MaiMap::empty());

	VexPtr<StateMachine, &ir_heap> probeMachine;
	CfgLabelAllocator allocLabel;
	{
		Stopwatch timeTaken;
		stackedCdf::startBuildProbeMachine();
		probeMachine = buildProbeMachine(&scopes, allocLabel, oracle, targetRip.toVexRip(),
						 tid, opt, mai, token);
		stackedCdf::stopBuildProbeMachine();
		printf("buildProbeMachine takes %f\n", timeTaken.sample());
		fprintf(better_log, "buildProbeMachine took %f\n", timeTaken.sample());
	}

	diagnoseCrash(&scopes, allocLabel, targetRip, probeMachine, oracle,
		      df, opt.enablenoLocalSurvival(), mai, timer1, only_store_cfg,
		      expected_nr_store_cfgs, token);
	exit(0);
}

