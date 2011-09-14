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

static bool storeMightBeLoadedByState(StateMachineState *sm, StateMachineSideEffectStore *smses, OracleInterface *oracle,
				      std::set<StateMachineEdge *> &memo);
static bool
storeMightBeLoadedByStateEdge(StateMachineEdge *sme, StateMachineSideEffectStore *smses, OracleInterface *oracle,
			      std::set<StateMachineEdge *> &memo)
{
	if (TIMEOUT)
		return true;
	if (memo.count(sme))
		return false;
	memo.insert(sme);
	for (unsigned y = 0; y < sme->sideEffects.size(); y++) {
		if (sme->sideEffects[y] == smses) {
			/* We've reached a cycle without hitting a
			   load of this store, so this path, at least,
			   is clear. */
			return false;
		}
		if (sme->sideEffects[y]->type == StateMachineSideEffect::Load) {
			StateMachineSideEffectLoad *smsel =
				dynamic_cast<StateMachineSideEffectLoad *>(sme->sideEffects[y]);
			assert(smsel);
			if (oracle->memoryAccessesMightAlias(smsel, smses))
				return true;
		}
	}
	return storeMightBeLoadedByState(sme->target, smses, oracle, memo);
}

static bool
storeMightBeLoadedByState(StateMachineState *sm, StateMachineSideEffectStore *smses, OracleInterface *oracle,
			  std::set<StateMachineEdge *> &memo)
{
	if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm))
		return storeMightBeLoadedByStateEdge(smp->target, smses, oracle, memo);
	if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm))
		return storeMightBeLoadedByStateEdge(smb->trueTarget, smses, oracle, memo) ||
			storeMightBeLoadedByStateEdge(smb->falseTarget, smses, oracle, memo);
	return false;
}

static bool
storeMightBeLoadedFollowingSideEffect(StateMachineEdge *sme, unsigned idx,
				      StateMachineSideEffectStore *smses,
				      OracleInterface *oracle)
{
	for (unsigned y = idx + 1; y < sme->sideEffects.size(); y++) {
		if (sme->sideEffects[y]->type == StateMachineSideEffect::Load) {
			StateMachineSideEffectLoad *smsel =
				dynamic_cast<StateMachineSideEffectLoad *>(sme->sideEffects[y]);
			assert(smsel);
			if (oracle->memoryAccessesMightAlias(smsel, smses))
				return true;
		}
	}
	std::set<StateMachineEdge *> memo;
	return storeMightBeLoadedByState(sme->target, smses, oracle, memo);
}

static void removeRedundantStores(StateMachineState *sm, OracleInterface *oracle, bool *done_something,
				  std::set<StateMachineState *> &visited,
				  const AllowableOptimisations &opt);

static void
removeRedundantStores(StateMachineEdge *sme, OracleInterface *oracle, bool *done_something,
		      std::set<StateMachineState *> &visited,
		      const AllowableOptimisations &opt)
{
	if (TIMEOUT)
		return;
	for (unsigned x = 0; x < sme->sideEffects.size(); x++) {
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(sme->sideEffects[x])) {
			if (opt.ignoreStore(smses->rip.rip) &&
			    !storeMightBeLoadedFollowingSideEffect(sme, x, smses, oracle)) {
				sme->sideEffects[x] =
					new StateMachineSideEffectAssertFalse(
						IRExpr_Unop(
							Iop_BadPtr,
							smses->addr));
				sme->sideEffects.erase(
					sme->sideEffects.begin() + x);
				x--;
				*done_something = true;
			}
		}
	}
	removeRedundantStores(sme->target, oracle, done_something, visited, opt);
}

static void
removeRedundantStores(StateMachineState *sm, OracleInterface *oracle, bool *done_something,
		      std::set<StateMachineState *> &visited,
		      const AllowableOptimisations &opt)
{
	if (visited.count(sm))
		return;
	visited.insert(sm);
	if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
		removeRedundantStores(smp->target, oracle, done_something, visited, opt);
		return;
	}
	if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm)) {
		removeRedundantStores(smb->trueTarget, oracle, done_something, visited, opt);
		removeRedundantStores(smb->falseTarget, oracle, done_something, visited, opt);
		return;
	}
	assert(dynamic_cast<StateMachineUnreached *>(sm) ||
	       dynamic_cast<StateMachineCrash *>(sm) ||
	       dynamic_cast<StateMachineNoCrash *>(sm) ||
	       dynamic_cast<StateMachineStub *>(sm));
}

static void
removeRedundantStores(StateMachine *sm, OracleInterface *oracle, bool *done_something,
		      const AllowableOptimisations &opt)
{
	__set_profiling(removeRedundantStores);
	std::set<StateMachineState *> visited;

	removeRedundantStores(sm->root, oracle, done_something, visited, opt);
}

/* End of namespace */
}

void
removeRedundantStores(StateMachine *sm, OracleInterface *oracle, bool *done_something,
		      const AllowableOptimisations &opt)
{
	_removeRedundantStores::removeRedundantStores(sm, oracle, done_something, opt);
}
