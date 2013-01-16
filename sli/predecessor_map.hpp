#ifndef PREDECESSOR_MAP_HPP__
#define PREDECESSOR_MAP_HPP__

#include <map>
#include <vector>

class StateMachineState;
class StateMachine;

class predecessor_map {
	std::map<StateMachineState *, std::set<StateMachineState *> > content;
public:
	predecessor_map(StateMachine *sm);
	void getPredecessors(StateMachineState *s, std::vector<StateMachineState *> &out) const;
};

#endif /* !PREDECESSOR_MAP_HPP__ */
