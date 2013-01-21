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
	/* Update map now that @predecessor is no longer a predecessor
	 * of @state. */
	void removePredecessor(StateMachineState *state, StateMachineState *predecessor);
	/* Update map to note that @predecessor is now a predecessor
	 * of @state. */
	void addPredecessor(StateMachineState *state, StateMachineState *predecessor);
	void recompute(StateMachine *sm);
};

#endif /* !PREDECESSOR_MAP_HPP__ */
