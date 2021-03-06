#ifndef INTERN_HPP__
#define INTERN_HPP__

#include "state_machine.hpp"

class internStateMachineTable {
	void _runGc(HeapVisitor &hv);
public:
	std::map<StateMachineSideEffect *, StateMachineSideEffect *> sideEffects;
	std::map<StateMachineState *, StateMachineState *> states;
	std::map<const CFGNode *, const CFGNode *> cfgNodes;
	std::set<StateMachineSideEffectStore *> stores;
	std::set<StateMachineSideEffectLoad *> loads;
	std::set<StateMachineSideEffectCopy *> copies;
	std::set<StateMachineSideEffectPhi *> phis;
	std::set<StateMachineSideEffectAssertFalse *> asserts;
#if TRACK_FRAMES
	std::set<StateMachineSideEffectStartFunction *> StartFunction;
	std::set<StateMachineSideEffectEndFunction *> EndFunction;
	std::set<StateMachineSideEffectStackLayout *> StackLayout;
#endif
	std::set<StateMachineSideEffectImportRegister *> ImportRegister;
	std::set<StateMachineBifurcate *> states_bifurcate;
	std::set<StateMachineSideEffecting *> states_side_effect;
	std::set<StateMachineTerminal *> states_terminal;
	std::set<const CFGNode *> cfgNodesS;
	std::map<bbdd *, bbdd *> bbdds;
	std::map<smrbdd *, smrbdd *> smrbdds;
	std::map<exprbdd *, exprbdd *> exprbdds;
};

StateMachine *internStateMachine(StateMachine *sm);
StateMachine *internStateMachine(
	StateMachine *sm,
	internStateMachineTable &t);
void internStateMachineCfg(StateMachine *sm);

#endif /* !INTERN_HPP__ */

