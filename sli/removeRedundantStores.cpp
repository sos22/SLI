/* Look at the state machine, compare it to the tags table, and remove
   any stores which are definitely never loaded (assuming that the
   tags table is correct). */
#include "sli.h"
#include "offline_analysis.hpp"
#include "oracle.hpp"
#include "libvex_prof.hpp"

namespace _removeRedundantStores {
/* Unconfuse emacs */
#if 0
}
#endif

static bool storeMightBeLoadedAfterState(StateMachineState *sme,
					 const AllowableOptimisations &opt,
					 StateMachineSideEffectStore *smses,
					 const Oracle::RegisterAliasingConfiguration *alias,
					 Oracle *oracle,
					 std::set<StateMachineState *> &memo);

static bool
storeMightBeLoadedByState(StateMachineState *sm,
			  StateMachineSideEffectStore *smses,
			  const AllowableOptimisations &opt,
			  const Oracle::RegisterAliasingConfiguration *alias,
			  Oracle *oracle,
			  std::set<StateMachineState *> &memo)
{
	if (memo.count(sm))
		return false;
	memo.insert(sm);

	if (sm->type == StateMachineState::SideEffecting) {
		StateMachineSideEffect *se = ((StateMachineSideEffecting *)sm)->sideEffect;
		if (se) {
			if (se == smses) {
				/* We've reached a cycle without hitting a
				   load of this store, so this path, at least,
				   is clear. */
				return false;
			}
			if (se->type == StateMachineSideEffect::Load) {
				StateMachineSideEffectLoad *smsel =
					dynamic_cast<StateMachineSideEffectLoad *>(se);
				assert(smsel);
				if ((!alias || alias->ptrsMightAlias(smsel->addr, smses->addr)) &&
				    oracle->memoryAccessesMightAlias(opt, smsel, smses))
					return true;
			}
		}
	}
	return storeMightBeLoadedAfterState(sm, opt, smses, alias, oracle, memo);
}

static bool
storeMightBeLoadedAfterState(StateMachineState *sm,
			     const AllowableOptimisations &opt,
			     StateMachineSideEffectStore *smses,
			     const Oracle::RegisterAliasingConfiguration *alias,
			     Oracle *oracle,
			     std::set<StateMachineState *> &memo)
{
	std::vector<StateMachineState *> edges;
	sm->targets(edges);
	for (auto it = edges.begin(); it != edges.end(); it++)
		if (storeMightBeLoadedByState(*it, smses, opt, alias, oracle, memo))
			return true;
	return false;
}

static bool
storeMightBeLoadedAfterState(StateMachineState *sm,
			     const AllowableOptimisations &opt,
			     StateMachineSideEffectStore *smses,
			     const Oracle::RegisterAliasingConfiguration *alias,
			     Oracle *oracle)
{
	std::set<StateMachineState *> memo;
	return storeMightBeLoadedAfterState(sm, opt, smses, alias, oracle, memo);
}


static void removeRedundantStores(StateMachineState *sm, Oracle *oracle, bool *done_something,
				  const Oracle::RegisterAliasingConfiguration *alias,
				  std::set<StateMachineState *> &visited,
				  const AllowableOptimisations &opt);

static void
removeRedundantStores(StateMachineState *sm, Oracle *oracle, bool *done_something,
		      const Oracle::RegisterAliasingConfiguration *alias,
		      std::set<StateMachineState *> &visited,
		      const AllowableOptimisations &opt)
{
	if (TIMEOUT)
		return;

	if (visited.count(sm))
		return;
	visited.insert(sm);

	if (sm->type == StateMachineState::SideEffecting) {
		StateMachineSideEffecting *se = (StateMachineSideEffecting *)sm;
		if (se->sideEffect) {
			if (StateMachineSideEffectStore *smses =  dynamic_cast<StateMachineSideEffectStore *>(se->sideEffect)) {
				bool canRemove = opt.ignoreStore(smses->rip.rip.rip);
				if (!canRemove && opt.assumePrivateStack() && alias &&
				    !alias->mightPointOutsideStack(smses->addr)) {
					/* If we have assumePrivateStack set,
					   and this is definitely a stack
					   store, it's worth considering
					   removing it from the machine. */
					canRemove = true;
				}

				if (canRemove &&
				    !storeMightBeLoadedAfterState(se, opt, smses, alias, oracle)) {
					se->sideEffect =
						new StateMachineSideEffectAssertFalse(
							IRExpr_Unop(
								Iop_BadPtr,
								smses->addr));
					*done_something = true;
				}
			}
		}
	}

	std::vector<StateMachineState *> edges;
	sm->targets(edges);
#warning why not just use enumStates?
	for (auto it = edges.begin(); it != edges.end(); it++)
		removeRedundantStores(*it, oracle, done_something, alias, visited, opt);
}

static void
removeRedundantStores(StateMachine *sm, Oracle *oracle, bool *done_something,
		      const Oracle::RegisterAliasingConfiguration *alias,
		      const AllowableOptimisations &opt)
{
	__set_profiling(removeRedundantStores);
	std::set<StateMachineState *> visited;
	removeRedundantStores(sm->root, oracle, done_something, alias, visited, opt);
}

/* End of namespace */
}

void
removeRedundantStores(StateMachine *sm, Oracle *oracle, bool *done_something,
		      const Oracle::RegisterAliasingConfiguration *alias,
		      const AllowableOptimisations &opt)
{
	_removeRedundantStores::removeRedundantStores(sm, oracle, done_something, alias, opt);
}
