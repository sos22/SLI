#include "sli.h"
#include "offline_analysis.hpp"

static void
enumStatesAndEdges(StateMachine *sm, std::set<StateMachineState *> &outStates,
		   std::set<StateMachineEdge *> &outEdges)
{
	std::vector<StateMachineState *> toVisitStates;
	std::vector<StateMachineEdge *> toVisitEdges;

	toVisitStates.push_back(sm->root);
	while (!toVisitStates.empty() || !toVisitEdges.empty()) {
		while (!toVisitStates.empty()) {
			StateMachineState *s = toVisitStates.back();
			toVisitStates.pop_back();
			if (!s || outStates.count(s))
				continue;
			outStates.insert(s);
			
			toVisitEdges.push_back(s->target0());
			toVisitEdges.push_back(s->target1());
		}
		while (!toVisitEdges.empty()) {
			StateMachineEdge *e = toVisitEdges.back();
			toVisitEdges.pop_back();
			if (!e || outEdges.count(e))
				continue;
			outEdges.insert(e);

			toVisitStates.push_back(e->target);
		}
	}
}

StateMachineSideEffectLoad *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectLoad *l, bool *)
{
	bool b = false;
	IRExpr *a = transformIRExpr(l->addr, &b);
	if (b)
		return new StateMachineSideEffectLoad(l->target, a, l->rip);
	else
		return NULL;
}

StateMachineSideEffectStore *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectStore *s, bool *)
{
	bool b = false;
	IRExpr *a = transformIRExpr(s->addr, &b), *d = transformIRExpr(s->data, &b);
	if (b)
		return new StateMachineSideEffectStore(a, d, s->rip);
	else
		return NULL;
}

StateMachineSideEffectAssertFalse *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectAssertFalse *a, bool *)
{
	bool b = false;
	IRExpr *v = transformIRExpr(a->value, &b);
	if (b)
		return new StateMachineSideEffectAssertFalse(v);
	else
		return NULL;
}

StateMachineSideEffectCopy *
StateMachineTransformer::transformOneSideEffect(StateMachineSideEffectCopy *c, bool *)
{
	bool b = false;
	IRExpr *v = transformIRExpr(c->value, &b);
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
	unsigned firstTransformed;
	firstTransformed = 0;
	StateMachineSideEffect *trans;
	while (firstTransformed < edge->sideEffects.size()) {
		StateMachineSideEffect *old = edge->sideEffects[firstTransformed];
		trans = transformSideEffect(old, done_something);
		if (trans && trans != old)
			break;
		firstTransformed++;
	}
	if (firstTransformed == edge->sideEffects.size())
		return NULL;
	StateMachineEdge *res = new StateMachineEdge(NULL);
	res->sideEffects.resize(edge->sideEffects.size());
	std::copy(edge->sideEffects.begin(),
		  edge->sideEffects.begin() + firstTransformed,
		  res->sideEffects.begin());
	res->sideEffects[firstTransformed] = trans;
	for (unsigned x = firstTransformed + 1; x < edge->sideEffects.size(); x++) {
		StateMachineSideEffect *old = edge->sideEffects[x];
		trans = transformSideEffect(old, done_something);
		if (!trans)
			trans = old;
		res->sideEffects[x] = trans;
	}
	return res;
}

StateMachineState *
StateMachineTransformer::transformState(StateMachineState *s, bool *done_something)
{
	if (StateMachineTerminal *t = dynamic_cast<StateMachineTerminal *>(s)) {
		if (StateMachineUnreached *a = dynamic_cast<StateMachineUnreached *>(t)) {
			return transformOneState(a, done_something);
		} else if (StateMachineCrash *b = dynamic_cast<StateMachineCrash *>(t)) {
			return transformOneState(b, done_something);
		} else if (StateMachineNoCrash *c = dynamic_cast<StateMachineNoCrash *>(t)) {
			return transformOneState(c, done_something);
		} else if (StateMachineStub *d = dynamic_cast<StateMachineStub *>(t)) {
			return transformOneState(d, done_something);
		} else {
			abort();
		}
	} else if (StateMachineProxy *p = dynamic_cast<StateMachineProxy *>(s)) {
		return transformOneState(p, done_something);
	} else if (StateMachineBifurcate *b = dynamic_cast<StateMachineBifurcate *>(s)) {
		return transformOneState(b, done_something);
	} else {
		abort();
	}
}

StateMachine *
StateMachineTransformer::transform(StateMachine *sm, bool *done_something)
{
	bool _b;
	if (!done_something) done_something = &_b;
	std::set<StateMachineState *> allStates;
	std::set<StateMachineEdge *> allEdges;
	enumStatesAndEdges(sm, allStates, allEdges);

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
			if ((s->target0() && edgeRewrites.count(s->target0())) ||
			    (s->target1() && edgeRewrites.count(s->target1()))) {
				/* Need to rewrite this one as well. */
				progress = true;

				/* Because terminals don't have targets. */
				assert(!dynamic_cast<StateMachineTerminal *>(s));

				if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(s)) {
					stateRewrites[s] =
						new StateMachineProxy(smp->origin,
								      (StateMachineEdge *)NULL);
				} else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(s)) {
					stateRewrites[s] =
						new StateMachineBifurcate(smb->origin,
									  smb->condition,
									  (StateMachineEdge *)NULL,
									  (StateMachineEdge *)NULL);
				} else {
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
				StateMachineEdge *n = new StateMachineEdge(NULL);
				n->sideEffects = e->sideEffects;
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

		if (dynamic_cast<StateMachineTerminal *>(old)) {
			/* These have no outgoing edges, so need no rewriting. */
		} else if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(old)) {
			StateMachineProxy *repl = dynamic_cast<StateMachineProxy *>(replacement);
			assert(repl);
			doEdge(repl->target, smp->target, edgeRewrites);
		} else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(old)) {
			StateMachineBifurcate *repl = dynamic_cast<StateMachineBifurcate *>(replacement);
			assert(repl);
			doEdge(repl->trueTarget, smb->trueTarget, edgeRewrites);
			doEdge(repl->falseTarget, smb->falseTarget, edgeRewrites);
		} else {
			abort();
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
