#include "sli.h"
#include "predecessor_map.hpp"
#include "state_machine.hpp"

predecessor_map::predecessor_map(StateMachine *sm)
{
	recompute(sm);
}

void
predecessor_map::recompute(StateMachine *sm)
{
	content.clear();

	/* Root state is special; make sure it's present, even if we
	   never find a predecessor for it (which we won't, if the
	   machine is acyclic). */
	std::set<StateMachineState *> empty;
	content.insert(std::pair<StateMachineState *, std::set<StateMachineState *> >(sm->root, empty));

	std::set<StateMachineState *> s;
	enumStates(sm, &s);
	for (auto it = s.begin(); it != s.end(); it++) {
		std::vector<StateMachineState *> ss;
		(*it)->targets(ss);
		for (auto it2 = ss.begin(); it2 != ss.end(); it2++)
			content[*it2].insert(*it);
	}
}

void
predecessor_map::getPredecessors(StateMachineState *s, std::vector<StateMachineState *> &out) const
{
	auto i = content.find(s);
	assert(i != content.end());
	out.insert(out.end(), i->second.begin(), i->second.end());
}

void
predecessor_map::removePredecessor(StateMachineState *state, StateMachineState *predecessor)
{
	assert(content.count(state));
	assert(content[state].count(predecessor));
	content[state].erase(predecessor);
}

void
predecessor_map::addPredecessor(StateMachineState *state, StateMachineState *predecessor)
{
	assert(!content[state].count(predecessor));
	content[state].insert(predecessor);
}

