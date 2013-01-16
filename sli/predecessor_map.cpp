#include "sli.h"
#include "predecessor_map.hpp"
#include "state_machine.hpp"

predecessor_map::predecessor_map(StateMachine *sm)
{
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
predecessor_map::getPredecessors(StateMachineState *s, std::vector<StateMachineState *> &out) const {
		auto i = content.find(s);
		assert(i != content.end());
		out.insert(out.end(), i->second.begin(), i->second.end());
}
