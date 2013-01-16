/* Idea here is to eliminate Phi nodes by replacing them with muxes
 * wherever possible.  Basic approach is to enumerate all paths to the
 * Phi and classify each according to which input that path selects,
 * then look at conditions on the path to try to figure out some
 * discriminant which'll tell us what we need. */
#include <math.h>

#include "sli.h"
#include "state_machine.hpp"
#include "offline_analysis.hpp"
#include "bdd.hpp"
#include "predecessor_map.hpp"
#include "control_dependence_graph.hpp"

#ifndef NDEBUG
static bool debug_build_paths = false;
static bool debug_toplevel = false;
#else
#define debug_build_paths false
#define debug_toplevel false
#endif

namespace _phi_elimination {

static exprbdd *
build_selection_bdd(SMScopes *scopes,
		    StateMachine *sm,
		    StateMachineSideEffectPhi *phi,
		    control_dependence_graph &cdg,
		    predecessor_map &pm,
		    std::map<const StateMachineState *, int> &labels,
		    std::map<unsigned, exprbdd *> &canonResult)
{
	std::set<StateMachineState *> mightReachPhi;
	{
		std::vector<StateMachineState *> allStates;
		enumStates(sm, &allStates);
		bool progress = true;
		while (progress) {
			progress = false;
			for (auto it = allStates.begin(); it != allStates.end(); it++) {
				if (mightReachPhi.count(*it))
					continue;
				if ( (*it)->getSideEffect() == phi ) {
					mightReachPhi.insert(*it);
					progress = true;
					continue;
				}
				std::vector<StateMachineState *> targets;
				(*it)->targets(targets);
				for (auto it2 = targets.begin(); it2 != targets.end(); it2++) {
					if (mightReachPhi.count(*it2)) {
						mightReachPhi.insert(*it);
						progress = true;
						break;
					}
				}
			}
		}
	}

	if (debug_build_paths) {
		printf("Phi-reaching states: {");
		for (auto it = mightReachPhi.begin();
		     it != mightReachPhi.end();
		     it++) {
			if (it != mightReachPhi.begin())
				printf(", ");
			printf("l%d", labels[*it]);
		}
		printf("}\n");
	}

	std::set<StateMachineSideEffecting *> sideEffecting;
	enumStates(sm, &sideEffecting);

	/* Map from states to an exprbdd which provides the result if
	   we issue the phi immediately after that state. */
	std::map<StateMachineState *, exprbdd *> m;

	/* States whose success entries in @m might need updating */
	std::queue<StateMachineState *> toUpdate;

	/* Set up initial map */
	for (unsigned x = 0; x < phi->generations.size(); x++) {
		const threadAndRegister &tr(phi->generations[x].reg);
		for (auto it2 = sideEffecting.begin();
		     it2 != sideEffecting.end();
		     it2++) {
			StateMachineSideEffect *sr = (*it2)->sideEffect;
			if (!sr)
				continue;
			threadAndRegister def(threadAndRegister::invalid());
			if (sr->definesRegister(def) && def == tr) {
				assert(!m.count(*it2));
				m[*it2] = canonResult[x];
				toUpdate.push(*it2);
			}
		}
	}

	if (debug_build_paths) {
		printf("Initial map:\n");
		for (auto it = m.begin(); it != m.end(); it++) {
			printf("l%d: ", labels[it->first]);
			it->second->prettyPrint(stdout);
		}
	}

	int done = 0;

	/* Expand the map to get the final result. */
	while (!toUpdate.empty()) {
		StateMachineState *s = toUpdate.front();
		toUpdate.pop();
		assert(m.count(s));

		if (debug_build_paths) {
			printf("Extend from l%d\n", labels[s]);
			m[s]->prettyPrint(stdout);
		}

		std::vector<StateMachineState *> ss;
		s->targets(ss);
		for (auto it = ss.begin();
		     it != ss.end();
		     it++) {
			StateMachineState *state = *it;
			if (!mightReachPhi.count(state) || m.count(state))
				continue;
			if (debug_build_paths)
				printf("Consider extending to l%d\n", labels[state]);
			std::vector<StateMachineState *> pred;
			pm.getPredecessors(state, pred);
			assert(!pred.empty());
			bool missing = false;
			for (auto it2 = pred.begin(); !missing && it2 != pred.end(); it2++) {
				if (!m.count(*it2)) {
					if (debug_build_paths)
						printf("No extend; predecessor l%d missing\n",
						       labels[*it2]);
					missing = true;
				}
			}
			if (missing)
				continue;
			done++;
			exprbdd::enablingTableT enabling;
			bbdd *assumption = cdg.domOf(state);
			if (assumption == scopes->bools.cnst(false)) {
				/* This state is completely
				 * unreachable.  Hmm. */
				if (debug_build_paths)
					printf("Unreachable state l%d?\n", labels[state]);
				return NULL;
			}
			bool failed = false;
			for (auto it = pred.begin(); !failed && it != pred.end(); it++) {
				bbdd *ass = assumption;
				bbdd *condition = cdg.edgeCondition(scopes, *it, state);
				condition = bbdd::assume(&scopes->bools, condition, ass);
				exprbdd *res = exprbdd::assume(&scopes->exprs, m[*it], ass);
				exprbdd **slot = enabling.getSlot(condition, res);
				if (*slot != res)
					failed = true;
			}
			if (failed) {
				if (debug_build_paths)
					printf("Failed to build initial enabling table\n");
				return NULL;
			}
			if (debug_build_paths) {
				printf("Enabling table:\n");
				for (auto it = enabling.begin(); !it.finished(); it.advance()) {
					if (it.started())
						printf("------------------\n");
					printf("Cond:\n");
					it.key()->prettyPrint(stdout);
					printf("Result:\n");
					it.value()->prettyPrint(stdout);
				}
			}
			if (TIMEOUT)
				return NULL;
			exprbdd *flattened = exprbdd::from_enabling(&scopes->exprs, enabling, 0);
			if (!flattened) {
				if (debug_build_paths)
					printf("Failed to flatten enabling table\n");
				return NULL;
			}

			if (debug_build_paths) {
				printf("Mux for l%d is:\n", labels[state]);
				flattened->prettyPrint(stdout);
			}
			if (state->getSideEffect() == phi) {
				if (debug_build_paths)
					printf("...and that's the end of the analysis.\n");
				return flattened;
			}
			m[state] = flattened;
			toUpdate.push(state);
		}
	}

	if (debug_build_paths)
		printf("Mux builder failed?\n");

	return NULL;
}

static StateMachine *
replaceSideEffects(SMScopes *scopes, StateMachine *sm, std::map<StateMachineSideEffect *, StateMachineSideEffect *> &rewrites)
{
	struct : public StateMachineTransformer {
		std::map<StateMachineSideEffect *, StateMachineSideEffect *> *rewrites;
		StateMachineSideEffecting *transformOneState(SMScopes *,
							     StateMachineSideEffecting *smse,
							     bool *done_something)
		{
			if (!smse->sideEffect)
				return NULL;
			auto it = rewrites->find(smse->sideEffect);
			if (it == rewrites->end())
				return NULL;
			*done_something = true;
			return new StateMachineSideEffecting(smse, it->second);
		}
		bool rewriteNewStates() const { return true; }
	} doit;
	doit.rewrites = &rewrites;
	return doit.transform(scopes, sm);
}

static StateMachine *
phiElimination(SMScopes *scopes, StateMachine *sm,
	       predecessor_map &pm, control_dependence_graph &cdg,
	       bool *done_something)
{
	std::map<const StateMachineState *, int> labels;

	if (debug_build_paths || debug_toplevel) {
		printf("phiElimination:\n");
		printStateMachine(sm, stdout, labels);
	}

	std::map<StateMachineSideEffect *, StateMachineSideEffect *> replacements;

	if (debug_toplevel)
		cdg.prettyPrint(stdout, labels);

	std::set<StateMachineSideEffectPhi *> phiEffects;
	internIRExprTable intern;
	enumSideEffects(sm, phiEffects);
	for (auto it = phiEffects.begin(); !TIMEOUT && it != phiEffects.end(); it++) {
		StateMachineSideEffectPhi *phi = *it;

		if (debug_toplevel) {
			printf("Consider side effect ");
			phi->prettyPrint(stdout);
			printf("\n");
		}
		/* The result canoniser is a mapping from indexes in
		   the generation array to the exprbdd which we select
		   if we pick thaht generation.  This allows us to
		   merge generations which ultimately produce the same
		   value, which can sometimes result in simpler
		   intbdds. */
		std::map<unsigned, exprbdd *> resultCanoniser;
		for (unsigned x = 0; x < phi->generations.size(); x++) {
			exprbdd *expr = phi->generations[x].val;
			bool found_one = false;
			for (unsigned y = 0; !found_one && y < x; y++) {
				if (phi->generations[y].val == expr) {
					resultCanoniser[x] = resultCanoniser[y];
					found_one = true;
				}
			}
			if (!found_one)
				resultCanoniser[x] = expr;
		}
		exprbdd *sel_bdd = build_selection_bdd(scopes, sm, phi, cdg, pm, labels, resultCanoniser);
		if (!sel_bdd) {
			if (debug_toplevel)
				printf("Failed to build bdd!\n");
			continue;
		}
		if (debug_toplevel) {
			printf("Replace side effect with:\n");
			sel_bdd->prettyPrint(stdout);
		}
		replacements[phi] = new StateMachineSideEffectCopy(
			phi->reg, sel_bdd);
	}

	if (replacements.empty()) {
		if (debug_toplevel)
			printf("Nothing to do\n");
		return sm;
	}
	if (debug_toplevel) {
		printf("Replacements:\n");
		for (auto it = replacements.begin(); it != replacements.end(); it++) {
			it->first->prettyPrint(stdout);
			printf("\t--->\t");
			it->second->prettyPrint(stdout);
			printf("\n");
		}
	}
	*done_something = true;
	return replaceSideEffects(scopes, sm, replacements);
}

/* End of namespace */
};

StateMachine *
phiElimination(SMScopes *scopes, StateMachine *sm,
	       predecessor_map &pred, control_dependence_graph &cdg,
	       bool *done_something)
{
	return _phi_elimination::phiElimination(scopes, sm, pred, cdg, done_something);
}
