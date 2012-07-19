/* Look at the state machine, compare it to the tags table, and remove
   any stores which are definitely never loaded (assuming that the
   tags table is correct). */
#include "sli.h"
#include "offline_analysis.hpp"
#include "oracle.hpp"
#include "libvex_prof.hpp"
#include "allowable_optimisations.hpp"

namespace _removeRedundantStores {
/* Unconfuse emacs */
#if 0
}
#endif

/* We only handle the case where @rsp and @ptr are either RSP or
   k+RSP, where k is a constant.  We don't consider the overflow case
   here; the stack pointer underflowing through 0 or overflowing
   through 2**64 is just too weird to worry about.  */
static bool
stackPointerDead(IRExpr *ptr, IRExpr *rsp)
{
	assert(ptr->type() == Ity_I64);
	assert(rsp->type() == Ity_I64);

	IRExprGet *ptrGet, *rspGet;
	IRExprConst *ptrConst, *rspConst;
	if (ptr->tag == Iex_Get) {
		ptrGet = (IRExprGet *)ptr;
		ptrConst = NULL;
	} else if (ptr->tag == Iex_Associative &&
		   ((IRExprAssociative *)ptr)->op == Iop_Add64 &&
		   ((IRExprAssociative *)ptr)->nr_arguments == 2 &&
		   ((IRExprAssociative *)ptr)->contents[0]->tag == Iex_Const &&
		   ((IRExprAssociative *)ptr)->contents[1]->tag == Iex_Get) {
		ptrConst = (IRExprConst *)((IRExprAssociative *)ptr)->contents[0];
		ptrGet = (IRExprGet *)((IRExprAssociative *)ptr)->contents[1];
	} else {
		return false;
	}
	if (rsp->tag == Iex_Get) {
		rspGet = (IRExprGet *)rsp;
		rspConst = NULL;
	} else if (rsp->tag == Iex_Associative &&
		   ((IRExprAssociative *)rsp)->op == Iop_Add64 &&
		   ((IRExprAssociative *)rsp)->nr_arguments == 2 &&
		   ((IRExprAssociative *)rsp)->contents[0]->tag == Iex_Const &&
		   ((IRExprAssociative *)rsp)->contents[1]->tag == Iex_Get) {
		rspConst = (IRExprConst *)((IRExprAssociative *)rsp)->contents[0];
		rspGet = (IRExprGet *)((IRExprAssociative *)rsp)->contents[1];
	} else {
		return false;
	}
	assert(rspGet);
	assert(ptrGet);
	if (!threadAndRegister::fullEq(rspGet->reg, ptrGet->reg))
		return false;

	long ptrDelta, rspDelta;
	if (ptrConst)
		ptrDelta = (long)ptrConst->con->Ico.U64;
	else
		ptrDelta = 0;
	if (rspConst)
		rspDelta = (long)rspConst->con->Ico.U64;
	else
		rspDelta = 0;
	return ptrDelta < rspDelta;
}

static bool storeMightBeLoadedAfterState(CfgDecode &decode,
					 StateMachineState *sme,
					 const AllowableOptimisations &opt,
					 StateMachineSideEffectStore *smses,
					 const Oracle::RegisterAliasingConfiguration *alias,
					 OracleInterface *oracle,
					 std::set<StateMachineState *> &memo);

static bool
storeMightBeLoadedByState(CfgDecode &decode,
			  StateMachineState *sm,
			  StateMachineSideEffectStore *smses,
			  const AllowableOptimisations &opt,
			  const Oracle::RegisterAliasingConfiguration *alias,
			  OracleInterface *oracle,
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
				if ((!alias || alias->ptrsMightAlias(smsel->addr, smses->addr, opt)) &&
				    oracle->memoryAccessesMightAlias(decode, opt, smsel, smses))
					return true;
			}
			if (se->type == StateMachineSideEffect::Store) {
				StateMachineSideEffectStore *smses2 =
					dynamic_cast<StateMachineSideEffectStore *>(se);
				assert(smses2);
				/* If this store will definitely
				   clobber the value we're looking for
				   then the original store will
				   definitely not be loaded on this
				   path. */
				if (smses2->data->type() == smses->data->type() &&
				    (!alias || alias->ptrsMightAlias(smses2->addr, smses->addr, opt)) &&
				    oracle->memoryAccessesMightAlias(decode, opt, smses2, smses) &&
				    definitelyEqual(smses2->addr, smses->addr, opt))
					return false;
			}
			if (se->type == StateMachineSideEffect::EndFunction) {
				auto s = (StateMachineSideEffectEndFunction *)se;
				/* Bit of a hack: we rely on the fact
				   that we can only say that X is
				   definitely less than Y if X and Y
				   are both offsets from the same
				   value, so that this does what we
				   want. */
				if (stackPointerDead(smses->addr, s->rsp)) {
					/* This store is to the
					   current function's frame,
					   and now we've hit the end
					   of the function, so it's
					   not possible for anything
					   to load the value. */
					return false;
				}
			}
		}
	}
	return storeMightBeLoadedAfterState(decode, sm, opt, smses, alias, oracle, memo);
}

static bool
storeMightBeLoadedAfterState(CfgDecode &decode,
			     StateMachineState *sm,
			     const AllowableOptimisations &opt,
			     StateMachineSideEffectStore *smses,
			     const Oracle::RegisterAliasingConfiguration *alias,
			     OracleInterface *oracle,
			     std::set<StateMachineState *> &memo)
{
	std::vector<StateMachineState *> edges;
	sm->targets(edges);
	for (auto it = edges.begin(); it != edges.end(); it++)
		if (storeMightBeLoadedByState(decode, *it, smses, opt, alias, oracle, memo))
			return true;
	return false;
}

static bool
storeMightBeLoadedAfterState(CfgDecode &decode,
			     StateMachineState *sm,
			     const AllowableOptimisations &opt,
			     StateMachineSideEffectStore *smses,
			     const Oracle::RegisterAliasingConfiguration *alias,
			     OracleInterface *oracle)
{
	std::set<StateMachineState *> memo;
	return storeMightBeLoadedAfterState(decode, sm, opt, smses, alias, oracle, memo);
}


static void removeRedundantStores(CfgDecode &decode,
				  StateMachineState *sm,
				  OracleInterface *oracle,
				  bool *done_something,
				  const Oracle::RegisterAliasingConfiguration *alias,
				  std::set<StateMachineState *> &visited,
				  const AllowableOptimisations &opt);

static void
removeRedundantStores(CfgDecode &decode,
		      StateMachineState *sm,
		      OracleInterface *oracle,
		      bool *done_something,
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
			if (StateMachineSideEffectStore *smses = dynamic_cast<StateMachineSideEffectStore *>(se->sideEffect)) {
				bool canRemove = opt.ignoreStore(decode(smses->rip.where)->rip);
				if (!canRemove && opt.assumePrivateStack() && alias &&
				    !alias->mightPointOutsideStack(smses->addr, opt)) {
					/* If we have assumePrivateStack set,
					   and this is definitely a stack
					   store, it's worth considering
					   removing it from the machine. */
					canRemove = true;
				}

				if (canRemove &&
				    !storeMightBeLoadedAfterState(decode, se, opt, smses, alias, oracle)) {
					se->sideEffect =
						new StateMachineSideEffectAssertFalse(
							IRExpr_Unop(
								Iop_BadPtr,
								smses->addr),
							true);
					*done_something = true;
				}
			}
		}
	}

	std::vector<StateMachineState *> edges;
	sm->targets(edges);
#warning why not just use enumStates?
	for (auto it = edges.begin(); it != edges.end(); it++)
		removeRedundantStores(decode, *it, oracle, done_something, alias, visited, opt);
}

static void
removeRedundantStores(StateMachine *sm, OracleInterface *oracle, bool *done_something,
		      const Oracle::RegisterAliasingConfiguration *alias,
		      const AllowableOptimisations &opt)
{
	__set_profiling(removeRedundantStores);
	std::set<StateMachineState *> visited;
	CfgDecode decode;
	decode.addMachine(sm);
	removeRedundantStores(decode, sm->root, oracle, done_something, alias, visited, opt);
}

/* End of namespace */
}

void
removeRedundantStores(StateMachine *sm, OracleInterface *oracle, bool *done_something,
		      const Oracle::RegisterAliasingConfiguration *alias,
		      const AllowableOptimisations &opt)
{
	_removeRedundantStores::removeRedundantStores(sm, oracle, done_something, alias, opt);
}
