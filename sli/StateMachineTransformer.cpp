#include "sli.h"
#include "offline_analysis.hpp"
#include "state_machine.hpp"

StateMachineSideEffectLoad *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectLoad *l, bool *c)
{
	bool b = false;
	IRExpr *a = doit(l->addr, &b);
	if (b) {
		*c = true;
		return new StateMachineSideEffectLoad(l->target, a, l->rip, l->type);
	} else {
		return NULL;
	}
}

StateMachineSideEffectStore *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectStore *s, bool *c)
{
	bool b = false;
	IRExpr *a = doit(s->addr, &b), *d = doit(s->data, &b);
	if (b) {
		*c = true;
		return new StateMachineSideEffectStore(a, d, s->rip);
	} else {
		return NULL;
	}
}

StateMachineSideEffectAssertFalse *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectAssertFalse *a, bool *d)
{
	bool b = false;
	IRExpr *v = doit(a->value, &b);
	if (b) {
		*d = true;
		return new StateMachineSideEffectAssertFalse(v, a->reflectsActualProgram);
	} else {
		return NULL;
	}
}

StateMachineSideEffectCopy *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectCopy *c, bool *d)
{
	bool b = false;
	IRExpr *v = doit(c->value, &b);
	if (b) {
		*d = true;
		return new StateMachineSideEffectCopy(c->target, v);
	} else {
		return NULL;
	}
}

StateMachineSideEffect *
StateMachineTransformer::transformSideEffect(StateMachineSideEffect *se, bool *done_something)
{
	switch (se->type) {
#define do_type(t)							\
		case StateMachineSideEffect:: t:			\
			return transformOneSideEffect(			\
				(StateMachineSideEffect ## t *)se,	\
				done_something)
		do_type(Load);
		do_type(Store);
		do_type(AssertFalse);
		do_type(Copy);
		do_type(Unreached);
		do_type(Phi);
		do_type(StartAtomic);
		do_type(EndAtomic);
#undef do_type
	}
	abort();
}

StateMachineState *
StateMachineTransformer::transformState(StateMachineState *s, bool *done_something)
{
	switch (s->type) {
#define do_type(name)							\
		case StateMachineState:: name :				\
			return transformOneState((StateMachine ## name *)s, done_something);
		all_state_types(do_type);
#undef do_type
	}
	abort();
}

static void
enumStates(const StateMachineState *start, std::set<const StateMachineState *> *out)
{
	if (!out->insert(start).second)
		return;
	std::vector<const StateMachineState *> targets;
	start->targets(targets);
	for (auto it = targets.begin(); it != targets.end(); it++)
		enumStates(*it, out);
}

void
StateMachineTransformer::rewriteMachine(const StateMachine *sm,
					std::map<const StateMachineState *, StateMachineState *> &stateRewrites)
{
	std::set<const StateMachineState *> allStates;
	enumStates(sm, &allStates);

	for (auto it = stateRewrites.begin(); it != stateRewrites.end(); it++)
		enumStates(it->second, &allStates);

	/* Step 2 of state machine transformation: If we're rewriting
	   a state, we have to rewrite all of the edges which target
	   it, and if we're rewriting an edge then we have to rewrite
	   all of the states which branch to it.  Take a (kind of)
	   closure of the rewrites obtained thus far to ensure that we
	   get this right. */
	bool progress;
	do {
		progress = false;
		for (auto it = allStates.begin(); it != allStates.end(); it++) {
			const StateMachineState *s = *it;
			if (stateRewrites.count(s))
				continue;
			std::vector<const StateMachineState *> edges;
			s->targets(edges);
			bool do_rewrite = false;
			for (auto it = edges.begin(); !do_rewrite && it != edges.end(); it++)
				if (stateRewrites.count(*it))
					do_rewrite = true;
			if (do_rewrite) {
				/* Need to rewrite this one as well. */
				progress = true;

				/* Because terminals don't have targets. */
				assert(!StateMachineState::stateTypeIsTerminal(s->type));

				switch (s->type) {
				case StateMachineState::SideEffecting: {
					StateMachineSideEffecting *smp = (StateMachineSideEffecting *)s;
					stateRewrites[s] =
						new StateMachineSideEffecting(smp->origin,
									      smp->sideEffect,
									      smp->target);
					break;
				}
				case StateMachineState::Bifurcate: {
					StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
					stateRewrites[s] =
						new StateMachineBifurcate(smb->origin,
									  smb->condition,
									  smb->trueTarget,
									  smb->falseTarget);
					break;
				}
				case StateMachineState::NdChoice: {
					StateMachineNdChoice *smnd = (StateMachineNdChoice *)s;
					stateRewrites[s] =
						new StateMachineNdChoice(smnd->origin, smnd->successors);
					break;
				}

				case StateMachineState::Unreached:
				case StateMachineState::Crash:
				case StateMachineState::NoCrash:
				case StateMachineState::Stub:
					abort();
				}
			}
		}
	} while (progress);

	/* Step 3: We now know how we're going to be doing the
	 * rewrites.  Go through and do them. */
	for (auto it = stateRewrites.begin(); it != stateRewrites.end(); it++) {
		StateMachineState *replacement = it->second;

		struct {
			void operator()(StateMachineState *&target, const StateMachineState *o,
					std::map<const StateMachineState *, StateMachineState *> &edgeRewrites) {
				assert(o);
				auto it = edgeRewrites.find(o);
				if (it == edgeRewrites.end())
					target = const_cast<StateMachineState *>(o);
				else
					target = it->second;
			};
		} doEdge;

		std::vector<StateMachineState **> newTargets;
		replacement->targets(newTargets);
		for (unsigned x = 0; x < newTargets.size(); x++)
			doEdge(*newTargets[x], *newTargets[x], stateRewrites);
	}

}

StateMachine *
StateMachineTransformer::transform(StateMachine *sm, bool *done_something)
{
	aborted = false;

	bool _b;
	if (!done_something) done_something = &_b;
	std::set<StateMachineState *> allStates;
	enumStates(sm, &allStates);

	/* Step 1: walk over the state machine states and figure out
	   which ones need to be changed due to the actual
	   transformation. */
	std::map<const StateMachineState *, StateMachineState *> stateRewrites; /* From old state to new state */

	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		StateMachineState *s = *it;
		StateMachineState *res = transformState(s, done_something);
		if (res != NULL && res != s) {
			/* This one got rewritten */
			stateRewrites[s] = res;
			*done_something = true;
		}
		if (aborted)
			return NULL;
	}

	rewriteMachine(sm, stateRewrites);

	bool b = false;

	StateMachineState *newRoot;
	if (stateRewrites.count(sm->root))
		newRoot = stateRewrites[sm->root];
	else
		newRoot = sm->root;

	if (!b && newRoot == sm->root) {
		/* All transformations are in-place */
		return sm;
	}

	/* Construct new machine */
	return new StateMachine(newRoot, sm->origin);
}

StateMachineSideEffectPhi *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectPhi *phi,
						bool *done_something)
{
	bool t = false;
	unsigned x = 0;
	IRExpr *newE;

	for (x = 0; x < phi->generations.size(); x++) {
		if (phi->generations[x].second)
			newE = transformIRExpr(phi->generations[x].second, &t);
		if (t)
			break;
	}
	if (x == phi->generations.size())
		return NULL;
	*done_something = true;
	StateMachineSideEffectPhi *newPhi = new StateMachineSideEffectPhi(*phi);
	newPhi->generations[x].second = newE;

	x++;
	while (x < newPhi->generations.size()) {
		if (newPhi->generations[x].second)
			newPhi->generations[x].second =
				transformIRExpr(newPhi->generations[x].second, &t);
		x++;
	}
	return newPhi;
}

