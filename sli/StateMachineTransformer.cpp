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
		return new StateMachineSideEffectAssertFalse(v);
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
#undef do_type
	}
	abort();
}

StateMachineNdChoice *
StateMachineTransformer::transformOneState(StateMachineNdChoice *s, bool *done_something)
{
	bool b = false;
	StateMachineState *trans;
	unsigned firstTransformed;
	for (firstTransformed = 0;
	     !b && firstTransformed < s->successors.size();
	     firstTransformed++) {
		trans = transformState(s->successors[firstTransformed], &b);
	}
	if (!b)
		return NULL;
	*done_something = true;
	std::vector<StateMachineState *> newSucc(s->successors);
	newSucc[firstTransformed] = trans;
	for (unsigned x = firstTransformed + 1; x < newSucc.size(); x++)
		newSucc[x] = transformState(newSucc[x], &b);
	return new StateMachineNdChoice(s->origin, newSucc);
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
	enumStates(sm, &allStates);

	/* Step 1: walk over the state machine states and figure out
	   which ones need to be changed due to the actual
	   transformation. */
	std::map<StateMachineState *, StateMachineState *> stateRewrites; /* From old state to new state */

	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		StateMachineState *s = *it;
		StateMachineState *res = transformState(s, done_something);
		if (res != NULL && res != s) {
			/* This one got rewritten */
			stateRewrites[s] = res;
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
			std::vector<StateMachineState *> edges;
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
									      NULL);
					break;
				}
				case StateMachineState::Bifurcate: {
					StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
					stateRewrites[s] =
						new StateMachineBifurcate(smb->origin,
									  smb->condition,
									  NULL,
									  NULL);
					break;
				}
				case StateMachineState::NdChoice: {
					StateMachineNdChoice *smnd = (StateMachineNdChoice *)s;
					stateRewrites[s] =
						new StateMachineNdChoice(smnd->origin);
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
		StateMachineState *old = it->first;
		StateMachineState *replacement = it->second;

		struct {
			void operator()(StateMachineState *&target, StateMachineState *o,
					std::map<StateMachineState *, StateMachineState *> &edgeRewrites) {
				StateMachineState *oldTarget = target;
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
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)old;
			assert(replacement->type == StateMachineState::Bifurcate);
			StateMachineBifurcate *repl = (StateMachineBifurcate *)replacement;
			doEdge(repl->trueTarget, smb->trueTarget, stateRewrites);
			doEdge(repl->falseTarget, smb->falseTarget, stateRewrites);
			break;
		}
		case StateMachineState::SideEffecting: {
			StateMachineSideEffecting *smp = (StateMachineSideEffecting *)old;
			assert(replacement->type == StateMachineState::SideEffecting);
			StateMachineSideEffecting *repl = (StateMachineSideEffecting *)replacement;
			doEdge(repl->target, smp->target, stateRewrites);
			break;
		}
		case StateMachineState::NdChoice: {
			StateMachineNdChoice *smnd = (StateMachineNdChoice *)old;
			assert(replacement->type == StateMachineState::NdChoice);
			StateMachineNdChoice *repl = (StateMachineNdChoice *)replacement;
			repl->successors.resize(smnd->successors.size());
			for (unsigned x = 0; x < smnd->successors.size(); x++)
				doEdge(repl->successors[x], smnd->successors[x], stateRewrites);
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

