#ifndef CONTROL_DOMINATION_MAP_HPP__
#define CONTROL_DOMINATION_MAP_HPP__

class StateMachineState;
class IRExpr;
class AllowableOptimisations;
class StateMachine;

class ControlDominationMap {
	std::map<StateMachineState *, IRExpr *> dominatingExpressions;
public:
	void init(StateMachine *sm,
		  const AllowableOptimisations &opt);
	void prettyPrint(FILE *f, const std::map<const StateMachineState *, int> &labels);
	IRExpr *get(StateMachineState *sm) const {
		auto it = dominatingExpressions.find(sm);
		assert(it != dominatingExpressions.end());
		return it->second;
	}
};


#endif /* CONTROL_DOMINATION_MAP_HPP__ */

