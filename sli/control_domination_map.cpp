#include "sli.h"
#include "control_domination_map.hpp"
#include "state_machine.hpp"
#include "sat_checker.hpp"

#include <queue>

#ifndef NDEBUG
static bool debug_state_domination = false;
#else
#define debug_state_domination false
#endif

typedef std::map<const StateMachineState *, int> stateLabelT;

static void
computeMaxDistanceMap(StateMachine *sm, std::map<StateMachineState *, int> &distanceMap)
{
	std::priority_queue<std::pair<int, StateMachineState *> > pending;
	pending.push(std::pair<int, StateMachineState *>(0, sm->root));
	while (!pending.empty()) {
		std::pair<int, StateMachineState *> p(pending.top());
		pending.pop();
		auto it_did_insert = distanceMap.insert(std::pair<StateMachineState *, int>(p.second, p.first));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (!did_insert && it->second >= p.first)
			continue;
		it->second = p.first;
		std::vector<StateMachineState *> targets;
		p.second->targets(targets);
		for (auto it = targets.begin(); it != targets.end(); it++)
			pending.push(std::pair<int, StateMachineState *>(p.first + 1, *it));
	}
}

void
ControlDominationMap::init(StateMachine *sm,
			   const AllowableOptimisations &opt)
{
	stateLabelT stateLabels;
	if (debug_state_domination) {
		printf("Computing control-flow domination map for:\n");
		printStateMachine(sm, stdout, stateLabels);
	}

	/* We try to process states so that we pick whatever is
	 * ``closest'' to the root first, where we measure distance
	 * according to the *longest* path from the root to the state.
	 * This means that by the time we want to calculate the
	 * condition for a state all of its inputs are available and
	 * we never have to do any recomputation, which helps to make
	 * things a bit faster. */
	std::map<StateMachineState *, int> stateDistances;
	computeMaxDistanceMap(sm, stateDistances);

	/* States whose successors might need updating. The first
	   argument is just a depth argument to make sure we handle
	   states in the right order. */
	typedef std::pair<int, StateMachineState *> needsUpdateEntryT;
	std::priority_queue<needsUpdateEntryT> needsUpdate;
	dominatingExpressions[sm->root] = IRExpr_Const(IRConst_U1(1));
	needsUpdate.push(needsUpdateEntryT(0, sm->root));
	struct _ {
		const AllowableOptimisations &opt;
		std::map<StateMachineState *, IRExpr *> &dominatingExpressions;
		std::map<StateMachineState *, int> &stateDistances;
		std::priority_queue<needsUpdateEntryT> &needsUpdate;
		void operator()(StateMachineState *s, IRExpr *cond) {
			cond = simplifyIRExpr(cond, opt);
			auto it_did_insert = dominatingExpressions.insert(
				std::pair<StateMachineState *, IRExpr *>(s, cond));
			auto it = it_did_insert.first;
			auto did_insert = it_did_insert.second;
			if (did_insert) {
				needsUpdate.push(needsUpdateEntryT(-stateDistances[s], s));
				return;
			}
			IRExpr *oldCond = it->second;
			it->second = IRExpr_Binop(Iop_Or1,
						  oldCond,
						  cond);
			it->second = simplify_via_anf(simplifyIRExpr(it->second, opt));
			if (!definitelyEqual(it->second, oldCond, opt))
				needsUpdate.push(needsUpdateEntryT(-stateDistances[s], s));
		}
		_(const AllowableOptimisations &_opt,
		  std::map<StateMachineState *, IRExpr *> &_dominatingExpressions,
		  std::map<StateMachineState *, int> &_stateDistances,
		  std::priority_queue<needsUpdateEntryT> &_needsUpdate)
			: opt(_opt),
			  dominatingExpressions(_dominatingExpressions),
			  stateDistances(_stateDistances),
			  needsUpdate(_needsUpdate)
		{}
	} discoverPathToState(opt, dominatingExpressions, stateDistances, needsUpdate);

	while (!needsUpdate.empty() && !TIMEOUT) {
		StateMachineState *s = needsUpdate.top().second;
		needsUpdate.pop();
		/* Build the exprAtExit starting from the expression
		   at entry to the state. */
		if (debug_state_domination)
			printf("Recompute domination condition for l%d\n", stateLabels[s]);
		IRExpr *exprAtEntry = dominatingExpressions[s];
		assert(exprAtEntry); /* should definitely have been
					populated by now */
		switch (s->type) {
		case StateMachineState::Unreached:
		case StateMachineState::Crash:
		case StateMachineState::NoCrash:
		case StateMachineState::Stub:
			/* No exit states, so it doesn't matter what
			 * the exprAtExit is. */
			break;
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
			IRExpr *trueCond = IRExpr_Binop(
				Iop_And1,
				smb->condition,
				exprAtEntry);
			IRExpr *falseCond = IRExpr_Binop(
				Iop_And1,
				IRExpr_Unop(Iop_Not1, smb->condition),
				exprAtEntry);
			discoverPathToState(smb->trueTarget, trueCond);
			discoverPathToState(smb->falseTarget, falseCond);
			break;
		}
		case StateMachineState::SideEffecting: {
			/* The side effect can also tell us something
			   interesting about what happens next. */
			StateMachineSideEffecting *effecting = (StateMachineSideEffecting *)s;
			IRExpr *exprAtExit = exprAtEntry;
			if (effecting->sideEffect) {
				switch (effecting->sideEffect->type) {
				case StateMachineSideEffect::Load:
				case StateMachineSideEffect::Store: {
					StateMachineSideEffectMemoryAccess *m = (StateMachineSideEffectMemoryAccess *)effecting->sideEffect;
					exprAtExit = IRExpr_Binop(
						Iop_And1,
						IRExpr_Unop(
							Iop_Not1,
							IRExpr_Unop(
								Iop_BadPtr,
								m->addr)),
						exprAtEntry);
					break;
				}
				case StateMachineSideEffect::Unreached:
					exprAtExit = IRExpr_Const(IRConst_U1(0));
					break;
				case StateMachineSideEffect::AssertFalse: {
					StateMachineSideEffectAssertFalse *a = (StateMachineSideEffectAssertFalse *)effecting->sideEffect;
					exprAtExit = IRExpr_Binop(
						Iop_And1,
						IRExpr_Unop(
							Iop_Not1,
							a->value),
						exprAtEntry);
					break;
				}
				case StateMachineSideEffect::Copy:
				case StateMachineSideEffect::Phi:
				case StateMachineSideEffect::StartAtomic:
				case StateMachineSideEffect::EndAtomic:
				case StateMachineSideEffect::StartFunction:
				case StateMachineSideEffect::EndFunction:
				case StateMachineSideEffect::StackUnescaped:
				case StateMachineSideEffect::PointerAliasing:
				case StateMachineSideEffect::StackLayout:
					break;
				}
			}
			discoverPathToState(effecting->target, exprAtExit);
			break;
		}
		}
	}

	if (debug_state_domination) {
		printf("State domination table:\n");
		prettyPrint(stdout, stateLabels);
	}
}

void
ControlDominationMap::prettyPrint(FILE *f, const stateLabelT &labels)
{
	for (auto it = dominatingExpressions.begin();
	     it != dominatingExpressions.end();
	     it++) {
		auto it2 = labels.find(it->first);
		fprintf(f, "l%d: %s\n", it2 == labels.end() ? -1 : it2->second, nameIRExpr(it->second));
	}
}
