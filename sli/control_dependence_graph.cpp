#include "sli.h"
#include "control_dependence_graph.hpp"
#include "state_machine.hpp"

#ifndef NDEBUG
static bool debug_control_dependence = false;
#else
#define debug_control_dependence false
#endif

bbdd *
control_dependence_graph::domOf(StateMachineState *s) const
{
	auto i = content.find(s);
	assert(i != content.end());
	return i->second;
}

control_dependence_graph::control_dependence_graph(StateMachine *sm,
						   bbdd::scope *scope)
{
	std::map<const StateMachineState *, int> labels;

	if (debug_control_dependence) {
		printf("Calculate CDG:\n");
		printStateMachine(sm, stdout, labels);
	}

	std::map<StateMachineState *, unsigned> pendingParents;
	std::vector<StateMachineState *> allStates;
	enumStates(sm, &allStates);
	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		std::vector<StateMachineState *> t;
		(*it)->targets(t);
		for (auto it2 = t.begin(); it2 != t.end(); it2++)
			pendingParents[*it2]++;
	}
	pendingParents[sm->root] = 0;

	std::vector<StateMachineState *> pending;
	struct {
		std::vector<StateMachineState *> *pending;
		std::map<StateMachineState *, unsigned> *pendingParents;
		bbdd::scope *scope;
		void operator()(bbdd *&slot,
				bbdd *newPath,
				StateMachineState *owner) {
			if (slot)
				slot = bbdd::Or(scope, slot, newPath);
			else
				slot = newPath;
			(*pendingParents)[owner]--;
			if ((*pendingParents)[owner] == 0)
				pending->push_back(owner);
		}
	} addPath;
	addPath.pending = &pending;
	addPath.pendingParents = &pendingParents;
	addPath.scope = scope;

	int nr_complete = 0;
	content[sm->root] = scope->cnst(true);
	pending.push_back(sm->root);
	while (!TIMEOUT && !pending.empty()) {
		StateMachineState *s = pending.back();
		pending.pop_back();
		assert(pendingParents.count(s));
		assert(pendingParents[s] == 0);

		bbdd *dom = content[s];
		assert(dom);
		if (debug_control_dependence) {
			printf("Redo control dependence of state l%d (%d/%zd complete); current = \n", labels[s], nr_complete, labels.size());
			dom->prettyPrint(stdout);
		}
		nr_complete++;
		switch (s->type) {
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
			bbdd *cond = smb->condition;
			bbdd *trueCond = bbdd::And(scope, dom, cond);
			bbdd *falseCond = bbdd::And(scope, dom, bbdd::invert(scope, cond));
			if (TIMEOUT)
				break;
			assert(trueCond);
			assert(falseCond);
			addPath(content[smb->trueTarget],
				trueCond,
				smb->trueTarget);
			addPath(content[smb->falseTarget],
				falseCond,
				smb->falseTarget);
			if (debug_control_dependence) {
				printf("Condition:\n");
				cond->prettyPrint(stdout);
				printf("Combine with dom constraint\n");
				dom->prettyPrint(stdout);
				printf("-> true\n");
				trueCond->prettyPrint(stdout);
				printf("-> false\n");
				falseCond->prettyPrint(stdout);

				printf("Update l%d to:\n", labels[smb->trueTarget]);
				content[smb->trueTarget]->prettyPrint(stdout);
				printf("Update l%d to:\n", labels[smb->falseTarget]);
				content[smb->falseTarget]->prettyPrint(stdout);
			}
			break;
		}
		case StateMachineState::SideEffecting: {
			StateMachineSideEffecting *sme = (StateMachineSideEffecting *)s;
			addPath(content[sme->target],
				dom,
				sme->target);
			if (debug_control_dependence) {
				printf("Update l%d to:\n", labels[sme->target]);
				content[sme->target]->prettyPrint(stdout);
			}
			break;
		}
		case StateMachineState::Terminal:
			break;
		}
	}
}

void
control_dependence_graph::prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const
{
	fprintf(f, "CDG:\n");
	for (auto it = content.begin(); it != content.end(); it++) {
		fprintf(f, "l%d:\n", labels[it->first]);
		it->second->prettyPrint(f);
	}
}
