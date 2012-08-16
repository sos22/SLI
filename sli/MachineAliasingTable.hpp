#ifndef MACHINE_ALIASING_TABLE_HPP__
#define MACHINE_ALIASING_TABLE_HPP__

#include "oracle.hpp"

class StateMachineState;

class MachineAliasingTable {
	/* Map from state machine states to the aliasing configuration
	   at the *start* of the state. */
	std::map<StateMachineState *, Oracle::RegisterAliasingConfiguration> configs;

	static Oracle::ThreadRegisterAliasingConfiguration maximalThreadConfig();
	static void setRegister(Oracle::RegisterAliasingConfiguration &,
				const threadAndRegister &tr,
				const PointerAliasingSet &val);
	Oracle::RegisterAliasingConfiguration getConfig(StateMachineState *);
	bool updateStateConfig(StateMachineState *,
			       const Oracle::RegisterAliasingConfiguration &);
public:
	void initialise(StateMachine *sm);
	bool ptrsMightAlias(StateMachineState *where,
			    IRExpr *ptr1,
			    IRExpr *ptr2,
			    const AllowableOptimisations &opt) const;
	bool findConfig(StateMachineState *, Oracle::RegisterAliasingConfiguration *) const;
};

#endif /* !MACHINE_ALIASING_TABLE_HPP__ */
