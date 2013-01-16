#ifndef CONTROL_DEPENDENCE_GRAPH_HPP__
#define CONTROL_DEPENDENCE_GRAPH_HPP__

#include <map>
#include <stdio.h>

#include "bdd.hpp"

class bbdd;
class StateMachineState;
class StateMachine;

class control_dependence_graph {
	std::map<StateMachineState *, bbdd *> content;
public:
	control_dependence_graph(StateMachine *sm, bbdd::scope *scope);
	bbdd *domOf(StateMachineState *s) const;
	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const;
};

#endif /* !CONTROL_DEPENDENCE_GRAPH_HPP */
