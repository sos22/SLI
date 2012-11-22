#include "sli.h"
#include "offline_analysis.hpp"
#include "state_machine.hpp"

StateMachineSideEffectLoad *
StateMachineTransformer::transformOneSideEffect(SMScopes *, StateMachineSideEffectLoad *l, bool *c)
{
	bool b = false;
	IRExpr *a = doit(l->addr, &b);
	if (b) {
		*c = true;
		return new StateMachineSideEffectLoad(l, a);
	} else {
		return NULL;
	}
}

StateMachineSideEffectStore *
StateMachineTransformer::transformOneSideEffect(SMScopes *, StateMachineSideEffectStore *s, bool *c)
{
	bool b = false;
	IRExpr *a = doit(s->addr, &b), *d = doit(s->data, &b);
	if (b) {
		*c = true;
		return new StateMachineSideEffectStore(s, a, d);
	} else {
		return NULL;
	}
}

StateMachineSideEffectAssertFalse *
StateMachineTransformer::transformOneSideEffect(SMScopes *, StateMachineSideEffectAssertFalse *a, bool *d)
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

StateMachineSideEffectStartFunction *
StateMachineTransformer::transformOneSideEffect(SMScopes *, StateMachineSideEffectStartFunction *a, bool *d)
{
	bool b = false;
	IRExpr *v = doit(a->rsp, &b);
	if (b) {
		*d = true;
		return new StateMachineSideEffectStartFunction(v, a->frame);
	} else {
		return NULL;
	}
}

StateMachineSideEffectEndFunction *
StateMachineTransformer::transformOneSideEffect(SMScopes *, StateMachineSideEffectEndFunction *a, bool *d)
{
	bool b = false;
	IRExpr *v = doit(a->rsp, &b);
	if (b) {
		*d = true;
		return new StateMachineSideEffectEndFunction(v, a->frame);
	} else {
		return NULL;
	}
}

StateMachineSideEffectCopy *
StateMachineTransformer::transformOneSideEffect(SMScopes *scopes, StateMachineSideEffectCopy *c, bool *d)
{
	bool b = false;
	exprbdd *v = transform_exprbdd(&scopes->bools, &scopes->exprs, c->value, &b);
	if (b) {
		*d = true;
		return new StateMachineSideEffectCopy(c->target, v);
	} else {
		return NULL;
	}
}

StateMachineSideEffect *
StateMachineTransformer::transformSideEffect(SMScopes *scopes, StateMachineSideEffect *se, bool *done_something)
{
	switch (se->type) {
#define do_type(t)							\
		case StateMachineSideEffect:: t:			\
			return transformOneSideEffect(scopes,		\
				(StateMachineSideEffect ## t *)se,	\
				done_something);
		all_side_effect_types(do_type);
#undef do_type
	}
	abort();
}

StateMachineState *
StateMachineTransformer::transformState(SMScopes *scopes, StateMachineState *s, bool *done_something)
{
	switch (s->type) {
#define do_type(name)							\
		case StateMachineState:: name :				\
			return transformOneState(scopes, (StateMachine ## name *)s, done_something);
		all_state_types(do_type);
#undef do_type
	}
	abort();
}

void
StateMachineTransformer::rewriteMachine(const StateMachine *sm,
					std::map<const StateMachineState *, StateMachineState *> &stateRewrites,
					bool rewriteNewStates)
{
	std::set<const StateMachineState *> allStates;
	enumStates(sm, &allStates);

	if (rewriteNewStates)
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

				switch (s->type) {
				case StateMachineState::SideEffecting: {
					StateMachineSideEffecting *smp = (StateMachineSideEffecting *)s;
					stateRewrites[s] = new StateMachineSideEffecting(smp);
					break;
				}
				case StateMachineState::Bifurcate: {
					StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
					stateRewrites[s] = new StateMachineBifurcate(smb);
					break;
				}

				case StateMachineState::Terminal:
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
StateMachineTransformer::transform(SMScopes *scopes, StateMachine *sm, bool *done_something)
{
	aborted = false;
	currentState = NULL;

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
		assert(currentState == NULL);
		currentState = s;
		StateMachineState *res = transformState(scopes, s, done_something);
		assert(currentState == s);
		currentState = NULL;

		if (res != NULL && res != s) {
			/* This one got rewritten */
			stateRewrites[s] = res;
			*done_something = true;
		}
		if (aborted)
			return NULL;
	}

	rewriteMachine(sm, stateRewrites, rewriteNewStates());

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
	return new StateMachine(sm, newRoot);
}

StateMachineSideEffectPhi *
StateMachineTransformer::transformOneSideEffect(SMScopes *scopes,
						StateMachineSideEffectPhi *phi,
						bool *done_something)
{
	bool t = false;
	unsigned x = 0;
	exprbdd *newE;

	newE = (exprbdd *)0xf001deadul; /* Shut the compiler up */
	for (x = 0; x < phi->generations.size(); x++) {
		if (phi->generations[x].val)
			newE = transform_exprbdd(&scopes->bools, &scopes->exprs, phi->generations[x].val, &t);
		if (t)
			break;
	}
	if (x == phi->generations.size())
		return NULL;
	*done_something = true;
	StateMachineSideEffectPhi *newPhi = new StateMachineSideEffectPhi(*phi);
	newPhi->generations[x].val = newE;

	x++;
	while (x < newPhi->generations.size()) {
		if (newPhi->generations[x].val)
			newPhi->generations[x].val =
				transform_exprbdd(&scopes->bools, &scopes->exprs, newPhi->generations[x].val, &t);
		x++;
	}
	return newPhi;
}

