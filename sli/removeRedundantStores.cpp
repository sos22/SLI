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

static bool storeMightBeLoadedByState(StateMachineState *sm, StateMachineSideEffectStore *smses,
				      const AllowableOptimisations &opt,
				      const Oracle::RegisterAliasingConfiguration *alias,
				      bool freeVariablesMightAccessStack,
				      Oracle *oracle,
				      std::set<StateMachineEdge *> &memo);
static bool
storeMightBeLoadedByStateEdge(StateMachineEdge *sme, StateMachineSideEffectStore *smses,
			      const AllowableOptimisations &opt,
			      const Oracle::RegisterAliasingConfiguration *alias,
			      bool freeVariablesMightAccessStack,
			      Oracle *oracle,
			      std::set<StateMachineEdge *> &memo)
{
	if (TIMEOUT)
		return true;
	if (memo.count(sme))
		return false;
	memo.insert(sme);
	for (auto it = sme->sideEffects.begin(); it != sme->sideEffects.end(); it++) {
		StateMachineSideEffect *se = *it;
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
			if ((!alias || alias->ptrsMightAlias(smsel->addr, smses->addr, freeVariablesMightAccessStack)) &&
			    oracle->memoryAccessesMightAlias(opt, smsel, smses))
				return true;
		}
	}
	return storeMightBeLoadedByState(sme->target, smses, opt, alias, freeVariablesMightAccessStack, oracle, memo);
}

static bool
storeMightBeLoadedByState(StateMachineState *sm, StateMachineSideEffectStore *smses,
			  const AllowableOptimisations &opt,
			  const Oracle::RegisterAliasingConfiguration *alias,
			  bool freeVariablesMightAccessStack,
			  Oracle *oracle,
			  std::set<StateMachineEdge *> &memo)
{
	if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm))
		return storeMightBeLoadedByStateEdge(smp->target, smses, opt, alias, freeVariablesMightAccessStack, oracle, memo);
	if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm))
		return storeMightBeLoadedByStateEdge(smb->trueTarget, smses, opt, alias, freeVariablesMightAccessStack, oracle, memo) ||
			storeMightBeLoadedByStateEdge(smb->falseTarget, smses, opt, alias, freeVariablesMightAccessStack, oracle, memo);
	return false;
}

static bool
storeMightBeLoadedFollowingSideEffect(StateMachineEdge *sme,
				      std::vector<StateMachineSideEffect *>::iterator it,
				      const AllowableOptimisations &opt,
				      StateMachineSideEffectStore *smses,
				      const Oracle::RegisterAliasingConfiguration *alias,
				      bool freeVariablesMightAccessStack,
				      Oracle *oracle)
{
	it++;
	while (it != sme->sideEffects.end()) {
		if ((*it)->type == StateMachineSideEffect::Load) {
			StateMachineSideEffectLoad *smsel =
				dynamic_cast<StateMachineSideEffectLoad *>(*it);
			assert(smsel);
			if ((!alias || alias->ptrsMightAlias(smsel->addr, smses->addr,
							     freeVariablesMightAccessStack)) &&
			    oracle->memoryAccessesMightAlias(opt, smsel, smses))
				return true;
		}
		it++;
	}
	std::set<StateMachineEdge *> memo;
	return storeMightBeLoadedByState(sme->target, smses, opt, alias, freeVariablesMightAccessStack, oracle, memo);
}

static void removeRedundantStores(StateMachineState *sm, Oracle *oracle, bool *done_something,
				  const Oracle::RegisterAliasingConfiguration *alias,
				  std::set<StateMachineState *> &visited,
				  const AllowableOptimisations &opt);

static void
removeRedundantStores(StateMachineEdge *sme, Oracle *oracle, bool *done_something,
		      const Oracle::RegisterAliasingConfiguration *alias,
		      std::set<StateMachineState *> &visited,
		      const AllowableOptimisations &opt)
{
	if (TIMEOUT)
		return;
	for (auto it = sme->sideEffects.begin(); it != sme->sideEffects.end(); it++) {
		if (StateMachineSideEffectStore *smses =  dynamic_cast<StateMachineSideEffectStore *>(*it)) {
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
			    !storeMightBeLoadedFollowingSideEffect(sme, it, opt, smses, alias, !opt.freeVariablesNeverAccessStack(), oracle)) {
				*it =
					new StateMachineSideEffectAssertFalse(
						IRExpr_Unop(
							Iop_BadPtr,
							smses->addr));
				*done_something = true;
			}
		}
	}
	removeRedundantStores(sme->target, oracle, done_something, alias, visited, opt);
}

static void
removeRedundantStores(StateMachineState *sm, Oracle *oracle, bool *done_something,
		      const Oracle::RegisterAliasingConfiguration *alias,
		      std::set<StateMachineState *> &visited,
		      const AllowableOptimisations &opt)
{
	if (visited.count(sm))
		return;
	visited.insert(sm);
	if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
		removeRedundantStores(smp->target, oracle, done_something, alias, visited, opt);
		return;
	}
	if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm)) {
		removeRedundantStores(smb->trueTarget, oracle, done_something, alias, visited, opt);
		removeRedundantStores(smb->falseTarget, oracle, done_something, alias, visited, opt);
		return;
	}
	assert(dynamic_cast<StateMachineUnreached *>(sm) ||
	       dynamic_cast<StateMachineCrash *>(sm) ||
	       dynamic_cast<StateMachineNoCrash *>(sm) ||
	       dynamic_cast<StateMachineStub *>(sm));
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
