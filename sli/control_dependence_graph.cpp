#include "sli.h"
#include "control_dependence_graph.hpp"
#include "state_machine.hpp"

#ifndef NDEBUG
static bool debug_control_dependence = false;
#else
#define debug_control_dependence false
#endif

bbdd *
control_dependence_graph::domOf(const StateMachineState *s) const
{
	auto i = content.find(s);
	assert(i != content.end());
	return i->second;
}

control_dependence_graph::control_dependence_graph(const StateMachine *sm,
						   bbdd::scope *scope)
{
	std::map<const StateMachineState *, int> labels;

	if (debug_control_dependence) {
		printf("Calculate CDG:\n");
		printStateMachine(sm, stdout, labels);
	}

	std::map<const StateMachineState *, unsigned> pendingParents;
	std::vector<const StateMachineState *> allStates;
	enumStates(sm, &allStates);
	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		std::vector<const StateMachineState *> t;
		(*it)->targets(t);
		for (auto it2 = t.begin(); it2 != t.end(); it2++)
			pendingParents[*it2]++;
	}
	pendingParents[sm->root] = 0;

	std::vector<const StateMachineState *> pending;
	struct {
		std::vector<const StateMachineState *> *pending;
		std::map<const StateMachineState *, unsigned> *pendingParents;
		bbdd::scope *scope;
		void operator()(bbdd *&slot,
				bbdd *newPath,
				const StateMachineState *owner) {
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
		const StateMachineState *s = pending.back();
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
			const StateMachineBifurcate *smb = (const StateMachineBifurcate *)s;
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
			const StateMachineSideEffecting *sme = (const StateMachineSideEffecting *)s;
			if (sme->sideEffect &&
			    sme->sideEffect->type == StateMachineSideEffect::AssertFalse) {
				addPath(content[sme->target],
					bbdd::And(
						scope,
						dom,
						bbdd::invert(
							scope,
							((StateMachineSideEffectAssertFalse *)sme->sideEffect)->value)),
					sme->target);
			} else {
				addPath(content[sme->target],
					dom,
					sme->target);
			}
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

bbdd *
control_dependence_graph::edgeCondition(SMScopes *scopes,
					const StateMachineState *a,
					const StateMachineState *b) const
{
	bbdd *base = domOf(a);
	bbdd *res = base;
	if (a->type == StateMachineState::Bifurcate) {
		const StateMachineBifurcate *smb = (const StateMachineBifurcate *)a;
		if (smb->trueTarget != smb->falseTarget) {
			if (b == smb->trueTarget) {
				res = bbdd::And(
					&scopes->bools,
					base,
					smb->condition);
			} else {
				assert(b == smb->falseTarget);
				res = bbdd::And(
					&scopes->bools,
					base,
					bbdd::invert(&scopes->bools, smb->condition));
			}
		}
	} else if (a->type == StateMachineState::SideEffecting) {
		const StateMachineSideEffecting *sme = (const StateMachineSideEffecting *)a;
		assert(b == sme->target);
		if (sme->sideEffect && sme->sideEffect->type == StateMachineSideEffect::AssertFalse) {
			res = bbdd::And(
				&scopes->bools,
				base,
				bbdd::invert(
					&scopes->bools,
					((StateMachineSideEffectAssertFalse *)sme->sideEffect)->value));
		}
	}
	return res;
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

void
control_dependence_graph::introduceState(StateMachineState *s, bbdd *cond)
{
	assert(!content.count(s));
	content[s] = cond;
}

/* Very simple optimiseation pass which just removes any states which
 * the CDG says are unreachable. */
StateMachine *
cdgOptimise(SMScopes *scopes, StateMachine *sm, control_dependence_graph &cdg, bool *done_something)
{
	std::vector<std::pair<StateMachineState *, StateMachineState *> > killedEdges;
	std::vector<StateMachineState *> states;
	enumStates(sm, &states);
	for (auto it = states.begin(); !TIMEOUT && it != states.end(); it++) {
		std::vector<StateMachineState **> targs;
		(*it)->targets(targs);
		for (auto it2 = targs.begin(); !TIMEOUT && it2 != targs.end(); it2++) {
			bbdd *dom = cdg.edgeCondition(scopes, *it, **it2);
			if (!TIMEOUT && dom->isLeaf() && dom->leaf() == false) {
				/* This edge can never be taken. */
				if (debug_control_dependence) {
					killedEdges.push_back(
						std::pair<StateMachineState *, StateMachineState *>
						(*it, **it2));
				}
				*done_something = true;
				StateMachineState *ns =
					new StateMachineTerminal(
						(*it)->dbg_origin,
						scopes->smrs.cnst(smr_unreached));
				**it2 = ns;
				cdg.introduceState(ns, dom);
			}
		}
	}

	if (debug_control_dependence && !killedEdges.empty()) {
		std::map<const StateMachineState *, int> labels;
		printf("cdgOptimise:\n");
		printStateMachine(sm, stdout, labels);
		for (auto it = killedEdges.begin(); it != killedEdges.end(); it++) {
			printf("Killed edge l%d -> l%d\n",
			       labels[it->first],
			       labels[it->second]);
		}
	}

	return sm;
}
