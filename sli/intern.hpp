#ifndef INTERN_HPP__
#define INTERN_HPP__

#include "state_machine.hpp"

struct internStateMachineTable : public internIRExprTable {
	std::map<StateMachineSideEffect *, StateMachineSideEffect *> sideEffects;
	std::map<StateMachineState *, StateMachineState *> states;
	std::set<StateMachineSideEffectStore *> stores;
	std::set<StateMachineSideEffectLoad *> loads;
	std::set<StateMachineSideEffectCopy *> copies;
	std::set<StateMachineSideEffectPhi *> phis;
	std::set<StateMachineSideEffectAssertFalse *> asserts;
	std::set<StateMachineSideEffectStartFunction *> StartFunction;
	std::set<StateMachineSideEffectEndFunction *> EndFunction;
	std::set<StateMachineBifurcate *> states_bifurcate;
	std::set<StateMachineStub *> states_stub;
	std::set<StateMachineSideEffecting *> states_side_effect;
	std::set<StateMachineNdChoice *> states_ndchoice;
};

IRExpr *internIRExpr(IRExpr *x);
StateMachine *internStateMachine(StateMachine *sm);
StateMachine *internStateMachine(
	StateMachine *sm,
	internStateMachineTable &t);

#endif /* !INTERN_HPP__ */

