#ifndef CONTROL_DEPENDENCE_GRAPH_HPP__
#define CONTROL_DEPENDENCE_GRAPH_HPP__

#include <map>
#include <stdio.h>

#include "bdd.hpp"

class StateMachineState;
class StateMachine;
class SMScopes;

class control_dependence_graph {
	std::map<const StateMachineState *, bbdd *> content;
public:
	control_dependence_graph(const StateMachine *sm, bbdd::scope *scope);
	/* Condition for @s to execute */
	bbdd *domOf(const StateMachineState *s) const;
	/* Condition for the edge from @a to @b to be taken. */
	bbdd *edgeCondition(SMScopes *scopes, const StateMachineState *a, const StateMachineState *b) const;
	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const;

	void introduceState(StateMachineState *s, bbdd *);
};

StateMachine *cdgOptimise(SMScopes *scopes, StateMachine *inp, control_dependence_graph &cdg, bool *done_something);

#endif /* !CONTROL_DEPENDENCE_GRAPH_HPP */
