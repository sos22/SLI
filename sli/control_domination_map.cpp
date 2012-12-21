#include "sli.h"
#include "control_domination_map.hpp"
#include "state_machine.hpp"
#include "sat_checker.hpp"
#include "allowable_optimisations.hpp"

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
ControlDominationMap::init(SMScopes *scopes,
			   StateMachine *sm,
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
	std::set<needsUpdateEntryT> needsUpdate;
	dominatingExpressions[sm->root] = scopes->bools.cnst(true);
	needsUpdate.insert(needsUpdateEntryT(0, sm->root));
	struct _ {
		const AllowableOptimisations &opt;
		bbdd::scope *scope;
		std::map<StateMachineState *, bbdd *> &dominatingExpressions;
		std::map<StateMachineState *, int> &stateDistances;
		std::set<needsUpdateEntryT> &needsUpdate;
		void operator()(StateMachineState *s, bbdd *cond) {
			auto it_did_insert = dominatingExpressions.insert(
				std::pair<StateMachineState *, bbdd *>(s, cond));
			auto it = it_did_insert.first;
			auto did_insert = it_did_insert.second;
			if (did_insert) {
				needsUpdate.insert(needsUpdateEntryT(stateDistances[s], s));
				return;
			}
			bbdd *oldCond = it->second;
			it->second = bbdd::Or(scope, oldCond, cond);
			if (it->second != oldCond)
				needsUpdate.insert(needsUpdateEntryT(stateDistances[s], s));
		}
		_(const AllowableOptimisations &_opt,
		  bbdd::scope *_scope,
		  std::map<StateMachineState *, bbdd *> &_dominatingExpressions,
		  std::map<StateMachineState *, int> &_stateDistances,
		  std::set<needsUpdateEntryT> &_needsUpdate)
			: opt(_opt),
			  scope(_scope),
			  dominatingExpressions(_dominatingExpressions),
			  stateDistances(_stateDistances),
			  needsUpdate(_needsUpdate)
		{}
	} discoverPathToState(opt, &scopes->bools, dominatingExpressions, stateDistances, needsUpdate);

	while (!needsUpdate.empty() && !TIMEOUT) {
		auto it = needsUpdate.begin();
		StateMachineState *s = it->second;
		if (debug_state_domination)
			printf("Recompute domination condition for l%d (%d)\n",
			       stateLabels[s],
			       it->first);

		for (it = needsUpdate.begin(); it != needsUpdate.end(); ) {
			if (it->second == s)
				needsUpdate.erase(it++);
			else
				it++;
		}

		/* Build the exprAtExit starting from the expression
		   at entry to the state. */

		bbdd *exprAtEntry = dominatingExpressions[s];
		assert(exprAtEntry); /* should definitely have been
					populated by now */
		switch (s->type) {
		case StateMachineState::Terminal:
			/* No exit states, so it doesn't matter what
			 * the exprAtExit is. */
			break;
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
			bbdd *trueCond = bbdd::And(
				&scopes->bools,
				smb->condition,
				exprAtEntry);
			bbdd *falseCond = bbdd::And(
				&scopes->bools,
				bbdd::invert(&scopes->bools, smb->condition),
				exprAtEntry);
			discoverPathToState(smb->trueTarget, trueCond);
			discoverPathToState(smb->falseTarget, falseCond);
			break;
		}
		case StateMachineState::SideEffecting: {
			/* The side effect can also tell us something
			   interesting about what happens next. */
			StateMachineSideEffecting *effecting = (StateMachineSideEffecting *)s;
			bbdd *exprAtExit = exprAtEntry;
			if (effecting->sideEffect) {
				switch (effecting->sideEffect->type) {
				case StateMachineSideEffect::Load:
				case StateMachineSideEffect::Store: {
					StateMachineSideEffectMemoryAccess *m = (StateMachineSideEffectMemoryAccess *)effecting->sideEffect;
					exprAtExit = bbdd::And(
						&scopes->bools,
						exprAtEntry,
						bbdd::invert(
							&scopes->bools,
							exprbdd::to_bbdd(
								&scopes->bools,
								exprbdd::unop(
									&scopes->exprs,
									&scopes->bools,
									Iop_BadPtr,
									m->addr))));
					break;
				}
				case StateMachineSideEffect::Unreached:
					exprAtExit = scopes->bools.cnst(false);
					break;
				case StateMachineSideEffect::AssertFalse: {
					StateMachineSideEffectAssertFalse *a = (StateMachineSideEffectAssertFalse *)effecting->sideEffect;
					exprAtExit = bbdd::And(
						&scopes->bools,
						bbdd::invert(
							&scopes->bools,
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
				case StateMachineSideEffect::ImportRegister:
				case StateMachineSideEffect::StackLayout:
					break;
				}
			}
			if (!TIMEOUT)
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
		fprintf(f, "l%d:\n", it2 == labels.end() ? -1 : it2->second);
		it->second->prettyPrint(stdout);
	}
}
