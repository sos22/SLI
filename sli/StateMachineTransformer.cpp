#include "sli.h"
#include "offline_analysis.hpp"
#include "state_machine.hpp"

StateMachineSideEffectLoad *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectLoad *l, bool *)
{
	bool b = false;
	IRExpr *a = doit(l->addr, &b);
	if (b)
		return new StateMachineSideEffectLoad(l->target, a, l->rip, l->type);
	else
		return NULL;
}

StateMachineSideEffectStore *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectStore *s, bool *)
{
	bool b = false;
	IRExpr *a = doit(s->addr, &b), *d = doit(s->data, &b);
	if (b)
		return new StateMachineSideEffectStore(a, d, s->rip);
	else
		return NULL;
}

StateMachineSideEffectAssertFalse *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectAssertFalse *a, bool *)
{
	bool b = false;
	IRExpr *v = doit(a->value, &b);
	if (b)
		return new StateMachineSideEffectAssertFalse(v);
	else
		return NULL;
}

StateMachineSideEffectCopy *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectCopy *c, bool *)
{
	bool b = false;
	IRExpr *v = doit(c->value, &b);
	if (b)
		return new StateMachineSideEffectCopy(c->target, v);
	else
		return NULL;
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
#undef do_type
	}
	abort();
}

StateMachineEdge *
StateMachineTransformer::transformOneEdge(StateMachineEdge *edge, bool *done_something)
{
	StateMachineSideEffect *trans;
	if (edge->sideEffect) {
		trans = transformSideEffect(edge->sideEffect, done_something);
		if (trans == NULL)
			trans = edge->sideEffect;
	} else
		trans = NULL;
	if (trans == edge->sideEffect)
		return NULL;
	return new StateMachineEdge(trans, NULL);
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

StateMachine *
StateMachineTransformer::transform(StateMachine *sm, bool *done_something)
{
	bool _b;
	if (!done_something) done_something = &_b;
	std::set<StateMachineState *> allStates;
	std::set<StateMachineEdge *> allEdges;
	enumStatesAndEdges(sm, &allStates, &allEdges);

	/* Step 1: walk over the state machine states and edges, and
	   figure out which ones need to be changed due to the actual
	   transformation. */
	std::map<StateMachineState *, StateMachineState *> stateRewrites; /* From old state to new state */
	std::map<StateMachineEdge *, StateMachineEdge *> edgeRewrites;

	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		StateMachineState *s = *it;
		StateMachineState *res = transformState(s, done_something);
		if (res != NULL && res != s) {
			/* This one got rewritten */
			stateRewrites[s] = res;
			*done_something = true;
		}
	}
	for (auto it = allEdges.begin(); it != allEdges.end(); it++) {
		StateMachineEdge *e = *it;
		StateMachineEdge *res = transformOneEdge(e, done_something);
		if (res != NULL && res != e) {
			edgeRewrites[e] = res;
			*done_something = true;
		}
	}

	/* Step 2: If we're rewriting a state, we have to rewrite all
	   of the edges which target it, and if we're rewriting an
	   edge then we have to rewrite all of the states which branch
	   to it.  Take a (kind of) closure of the rewrites obtained
	   thus far to ensure that we get this right. */
	bool progress;
	do {
		progress = false;
		for (auto it = allStates.begin(); it != allStates.end(); it++) {
			StateMachineState *s = *it;
			if (stateRewrites.count(s))
				continue;
			std::vector<StateMachineEdge *> edges;
			s->targets(edges);
			bool do_rewrite = false;
			for (auto it = edges.begin(); !do_rewrite && it != edges.end(); it++)
				if (edgeRewrites.count(*it))
					do_rewrite = true;
			if (do_rewrite) {
				/* Need to rewrite this one as well. */
				progress = true;

				/* Because terminals don't have targets. */
				assert(!StateMachineState::stateTypeIsTerminal(s->type));

				switch (s->type) {
				case StateMachineState::Proxy: {
					StateMachineProxy *smp = (StateMachineProxy *)s;
					stateRewrites[s] =
						new StateMachineProxy(smp->origin,
								      (StateMachineEdge *)NULL);
					break;
				}
				case StateMachineState::SideEffecting: {
					StateMachineSideEffecting *smp = (StateMachineSideEffecting *)s;
					stateRewrites[s] =
						new StateMachineSideEffecting(smp->origin,
									      smp->sideEffect,
									      NULL);
					break;
				}
				case StateMachineState::Bifurcate: {
					StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
					stateRewrites[s] =
						new StateMachineBifurcate(smb->origin,
									  smb->condition,
									  (StateMachineEdge *)NULL,
									  (StateMachineEdge *)NULL);
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
		for (auto it = allEdges.begin(); it != allEdges.end(); it++) {
			StateMachineEdge *e = *it;
			if (edgeRewrites.count(e))
				continue;
			if (stateRewrites.count(e->target)) {
				progress = true;
				StateMachineEdge *n = new StateMachineEdge(*e);
				n->target = NULL;
				edgeRewrites[e] = n;
			}
		}
	} while (progress);

	/* Step 3: We now know how we're going to be doing the
	 * rewrites.  Go through and do them. */
	for (auto it = edgeRewrites.begin(); it != edgeRewrites.end(); it++) {
		StateMachineEdge *old = it->first;
		StateMachineEdge *replacement = it->second;
		StateMachineState *oldTarget;

		if (replacement->target)
			oldTarget = replacement->target;
		else
			oldTarget = old->target;

		auto it2 = stateRewrites.find(oldTarget);
		if (it2 == stateRewrites.end())
			replacement->target = oldTarget;
		else
			replacement->target = it2->second;
	}
	for (auto it = stateRewrites.begin(); it != stateRewrites.end(); it++) {
		StateMachineState *old = it->first;
		StateMachineState *replacement = it->second;

		struct {
			void operator()(StateMachineEdge *&target, StateMachineEdge *o,
					std::map<StateMachineEdge *, StateMachineEdge *> &edgeRewrites) {
				StateMachineEdge *oldTarget = target;
				if (!oldTarget)
					oldTarget = o;
				auto it = edgeRewrites.find(oldTarget);
				if (it == edgeRewrites.end())
					target = oldTarget;
				else
					target = it->second;
			};
		} doEdge;

		switch (old->type) {
		case StateMachineState::Proxy: {
			StateMachineProxy *smp = (StateMachineProxy *)old;
			assert(replacement->type == StateMachineState::Proxy);
			StateMachineProxy *repl = (StateMachineProxy *)replacement;
			doEdge(repl->target, smp->target, edgeRewrites);
			break;
		}
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)old;
			assert(replacement->type == StateMachineState::Bifurcate);
			StateMachineBifurcate *repl = (StateMachineBifurcate *)replacement;
			doEdge(repl->trueTarget, smb->trueTarget, edgeRewrites);
			doEdge(repl->falseTarget, smb->falseTarget, edgeRewrites);
			break;
		}
		case StateMachineState::SideEffecting: {
			StateMachineSideEffecting *smp = (StateMachineSideEffecting *)old;
			assert(replacement->type == StateMachineState::SideEffecting);
			StateMachineSideEffecting *repl = (StateMachineSideEffecting *)replacement;
			doEdge(repl->target, smp->target, edgeRewrites);
			break;
		}
		case StateMachineState::Crash:
		case StateMachineState::NoCrash:
		case StateMachineState::Stub:
		case StateMachineState::Unreached:
			/* These have no outgoing edges, so need no rewriting. */
			break;
		}
	}

	/* The state machine proper has now been fully rewritten.  All
	   that remains is to transform the free variable map and
	   return. */
	FreeVariableMap fvm = sm->freeVariables;
	bool b = false;
	transformFreeVariables(&fvm, &b);
	*done_something |= b;

	StateMachineState *newRoot;
	if (stateRewrites.count(sm->root))
		newRoot = stateRewrites[sm->root];
	else
		newRoot = sm->root;

	if (!b && newRoot == sm->root && fvDelta.size() == 0) {
		/* All transformations are in-place */
		return sm;
	}

	/* Construct new machine */
	for (auto it = fvDelta.begin(); it != fvDelta.end(); it++)
		fvm.content->set(it->first, it->second);
	return new StateMachine(newRoot, sm->origin, fvm, sm->tid);
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

