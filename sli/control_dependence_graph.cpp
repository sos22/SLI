#include "sli.h"
#include "control_dependence_graph.hpp"
#include "state_machine.hpp"
#include "offline_analysis.hpp"
#include "stacked_cdf.hpp"

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
	stackedCdf::startBuildCDG();
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
	while (!pending.empty()) {
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
	stackedCdf::stopBuildCDG();
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
cdgOptimise(SMScopes *scopes, StateMachine *sm, control_dependence_graph &cdg,
	    bool *done_something, bool *invalidate_cdg)
{
	std::map<const StateMachineState *, int> labels;

	if (debug_control_dependence) {
		printf("cdgOptimise, input:");
		printStateMachine(sm, stdout, labels);
	}

	bool p;

	std::vector<StateMachineState *> states;
	enumStates(sm, &states);
	for (auto it = states.begin(); it != states.end(); it++) {
		StateMachineState *state = *it;
		bbdd *stateDom = cdg.domOf(state);
		if (stateDom->isLeaf()) {
			if (!stateDom->leaf()) {
				*invalidate_cdg = true;
			}
			continue;
		}
		switch (state->type) {
		case StateMachineState::SideEffecting: {
			auto e = (StateMachineSideEffecting *)state;
			if (e->sideEffect) {
				auto newSe = optimiseAssuming(scopes, e->sideEffect, stateDom);
				if (newSe != e->sideEffect) {
					if (debug_control_dependence) {
						printf("CDG rewrites side effect:\n");
						e->sideEffect->prettyPrint(stdout);
						printf(" -> ");
						if (newSe) {
							newSe->prettyPrint(stdout);
						} else {
							printf("<null>\n");
						}
					}
					*done_something = true;
					e->sideEffect = newSe;
				}
			}
			break;
		}
		case StateMachineState::Terminal: {
			auto t = (StateMachineTerminal *)state;
			auto newRes = smrbdd::assume(&scopes->smrs, t->res, stateDom);
			if (!newRes) {
				newRes = scopes->smrs.cnst(smr_unreached);
			}
			p = t->set_res(newRes);
			if (p) {
				if (debug_control_dependence) {
					printf("Terminal l%d changes:\n", labels[state]);
					newRes->prettyPrint(stdout);
				}
				*done_something = true;
			}
			break;
		}
		case StateMachineState::Bifurcate: {
			auto b = (StateMachineBifurcate *)state;
			auto newCond = bbdd::assume(&scopes->bools, b->condition, stateDom);
			if (newCond) {
				p = b->set_condition(newCond);
				if (p) {
					if (debug_control_dependence) {
						printf("Bifurcate l%d condition changes:\n",
						       labels[state]);
						newCond->prettyPrint(stdout);
					}
					if (newCond->isLeaf()) {
						*invalidate_cdg = true;
					}
					*done_something = true;
				}
			}
			break;
		}
		}
	}

	return sm;
}
