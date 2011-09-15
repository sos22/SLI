/* Conversion to static single assignment form */
#include "sli.h"
#include "state_machine.hpp"
#include "ssa.hpp"
#include "offline_analysis.hpp"

namespace SSA {

/* Unconfuse emacs indent */
#if 0
}
#endif

template <typename t> t
pop(std::set<t> &x)
{
	auto it = x.begin();
	t res = *it;
	x.erase(it);
	return res;
}

template <class Body> void
iterate_states(StateMachine *inp, Body &b)
{
	std::set<StateMachineState *> toVisit;
	std::set<StateMachineState *> visited;
	toVisit.insert(inp->root);
	while (!toVisit.empty()) {
		auto it = toVisit.begin();
		StateMachineState *s = *it;
		toVisit.erase(it);
		if (visited.count(s))
			continue;
		visited.insert(s);
		
		b(s, toVisit);
	}
}

static bool
sideEffectDefinesReg(const StateMachineSideEffect *se, const threadAndRegister &reg)
{
	switch (se->type) {
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)se;
		return threadAndRegister::partialEq(l->target, reg);
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *l = (StateMachineSideEffectCopy *)se;
		return threadAndRegister::partialEq(l->target, reg);
	}
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *l = (StateMachineSideEffectPhi *)se;
		return threadAndRegister::partialEq(l->reg, reg);
	}
	case StateMachineSideEffect::AssertFalse:
	case StateMachineSideEffect::Unreached:
	case StateMachineSideEffect::Store:
		return false;
	}
	return true;
}

template <typename t> void
operator |=(std::set<t> &out, const std::set<t> &inp)
{
	for (auto it = inp.begin(); it != inp.end(); it++)
		out.insert(*it);
}

/* Possibly reaching map.  This tells us, for each side effect in a
   state machine, the set of side effects which might conceivably
   reach it. */
class PossiblyReaching {
	void updateStateReaching(StateMachineState *state,
				 std::set<StateMachineEdge *> &edgesToUpdate);
	void updateEdgeReaching(StateMachineEdge *edge,
				std::set<StateMachineState *> &needsUpdate);
	void buildSideEffectTable(StateMachineEdge *edge);
	std::map<StateMachineState *, std::set<StateMachineSideEffect *> > stateTable;
	std::map<StateMachineSideEffect *, std::set<StateMachineSideEffect *> > effectTable;
	std::map<StateMachineEdge *, std::set<StateMachineSideEffect *> > edgeTable;
public:
	std::set<StateMachineSideEffect *> &effectsReachingState(StateMachineState *state) {
		return stateTable[state];
	}
	std::set<StateMachineSideEffect *> &effectsReachingSideEffect(StateMachineSideEffect *effect) {
		return effectTable[effect];
	}
	std::set<StateMachineSideEffect *> &effectsReachingEdge(StateMachineEdge *edge) {
		return edgeTable[edge];
	}
	void findReachingGenerations(StateMachineState *e,
				     const threadAndRegister &r,
				     std::vector<unsigned> &out);
	void findReachingGenerations(StateMachineSideEffect *e,
				     const threadAndRegister &r,
				     std::vector<unsigned> &out);
	PossiblyReaching(StateMachine *inp);
};

static void
enumAllStates(StateMachine *sm, std::set<StateMachineState *> &out)
{
	std::set<StateMachineState *> toVisit;
	toVisit.insert(sm->root);
	while (!toVisit.empty()) {
		StateMachineState *s = pop(toVisit);
		if (out.count(s))
			continue;
		out.insert(s);
		if (s->target0())
			toVisit.insert(s->target0()->target);
		if (s->target1())
			toVisit.insert(s->target1()->target);
	}
}

static void
enumAllEdges(StateMachine *sm, std::set<StateMachineEdge *> &out)
{
	std::set<StateMachineState *> toVisit;
	toVisit.insert(sm->root);
	while (!toVisit.empty()) {
		StateMachineState *s = pop(toVisit);
		if (s->target0()) {
			if (!out.count(s->target0())) {
				toVisit.insert(s->target0()->target);
				out.insert(s->target0());
			}
		}
		if (s->target1()) {
			if (!out.count(s->target1())) {
				toVisit.insert(s->target1()->target);
				out.insert(s->target1());
			}
		}
	}
}

PossiblyReaching::PossiblyReaching(StateMachine *inp)
{
	std::set<StateMachineState *> statesNeedingUpdate;
	std::set<StateMachineEdge *> edgesNeedingUpdate;
	enumAllStates(inp, statesNeedingUpdate);
	enumAllEdges(inp, edgesNeedingUpdate);
	while (!statesNeedingUpdate.empty() ||
	       !edgesNeedingUpdate.empty()) {
		while (!statesNeedingUpdate.empty()) {
			auto it = statesNeedingUpdate.begin();
			auto s = *it;
			statesNeedingUpdate.erase(it);
			updateStateReaching(s, edgesNeedingUpdate);
		}
		while (!edgesNeedingUpdate.empty()) {
			auto it = edgesNeedingUpdate.begin();
			auto e = *it;
			edgesNeedingUpdate.erase(it);
			updateEdgeReaching(e, statesNeedingUpdate);
		}
	}

	/* Now build the reaching-side-effect table */
	std::set<StateMachineState *> toVisit;
	std::set<StateMachineState *> visited;
	toVisit.insert(inp->root);
	while (!toVisit.empty()) {
		StateMachineState *s = pop(toVisit);
		if (visited.count(s))
			continue;
		visited.insert(s);
		if (s->target0()) {
			buildSideEffectTable(s->target0());
			toVisit.insert(s->target0()->target);
		}
		if (s->target1()) {
			buildSideEffectTable(s->target1());
			toVisit.insert(s->target1()->target);
		}
	}
}

void
PossiblyReaching::updateStateReaching(StateMachineState *state, std::set<StateMachineEdge *> &needsUpdate)
{
	struct {
		void operator()(StateMachineEdge *edge,
				const std::set<StateMachineSideEffect *> &inp,
				std::set<StateMachineEdge *> &needsUpdate,
				PossiblyReaching *_this) {
			std::set<StateMachineSideEffect *> &reachingThisEdge(_this->effectsReachingEdge(edge));
			if (reachingThisEdge != inp) {
				reachingThisEdge |= inp;
				needsUpdate.insert(edge);
			}
		}
	} updateEdge;
	std::set<StateMachineSideEffect *> &reachingThisState(effectsReachingState(state));
	if (state->target0())
		updateEdge(state->target0(), reachingThisState, needsUpdate, this);
	if (state->target1())
		updateEdge(state->target1(), reachingThisState, needsUpdate, this);
}

static void
sideEffectSetToGenerationSet(const std::set<StateMachineSideEffect *> &effects,
			     const threadAndRegister &reg,
			     std::vector<unsigned> &out)
{
	struct _ {
		std::vector<unsigned> &out;
		_(std::vector<unsigned> &_out)
			: out(_out)
		{}
		void operator()(unsigned r) {
			for (auto it = out.begin(); it != out.end(); it++)
				if (*it == r)
					return;
			out.push_back(r);
		}
	} addItem(out);
	for (auto it = effects.begin(); it != effects.end(); it++) {
		StateMachineSideEffect *se = *it;
		switch (se->type) {
		case StateMachineSideEffect::Load: {
			StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)se;
			if (threadAndRegister::partialEq(l->target, reg))
				addItem(l->target.gen());
			break;
		}
		case StateMachineSideEffect::Copy: {
			StateMachineSideEffectCopy *l = (StateMachineSideEffectCopy *)se;
			if (threadAndRegister::partialEq(l->target, reg))
				addItem(l->target.gen());
			break;
		}
		case StateMachineSideEffect::Phi: {
			StateMachineSideEffectPhi *l = (StateMachineSideEffectPhi *)se;
			if (threadAndRegister::partialEq(l->reg, reg))
				addItem(l->reg.gen());
			break;
		}
		case StateMachineSideEffect::AssertFalse:
		case StateMachineSideEffect::Unreached:
		case StateMachineSideEffect::Store:
			break;
		}
	}
}

void
PossiblyReaching::findReachingGenerations(StateMachineState *e,
					  const threadAndRegister &reg,
					  std::vector<unsigned> &out)
{
	std::set<StateMachineSideEffect *> &effects(effectsReachingState(e));
	sideEffectSetToGenerationSet(effects, reg, out);
}

void
PossiblyReaching::findReachingGenerations(StateMachineSideEffect *e,
					  const threadAndRegister &reg,
					  std::vector<unsigned> &out)
{
	std::set<StateMachineSideEffect *> &effects(effectsReachingSideEffect(e));
	sideEffectSetToGenerationSet(effects, reg, out);
}

static void
updateReachingSetForSideEffect(StateMachineSideEffect *smse, std::set<StateMachineSideEffect *> *out)
{
	class _ {
	public:
		std::set<StateMachineSideEffect *> *out;
		void operator()(threadAndRegister reg) {
			for (auto it = out->begin(); it != out->end(); ) {
				StateMachineSideEffect *o = *it;
				if (sideEffectDefinesReg(o, reg))
					out->erase(it++);
				else
					it++;
			}
		}
		_(std::set<StateMachineSideEffect *> *_out)
			: out(_out)
		{}
	} defineReg(out);
	switch (smse->type) {
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel = (StateMachineSideEffectLoad *)smse;
		defineReg(smsel->target);
		out->insert(smse);
		return;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec = (StateMachineSideEffectCopy *)smse;
		defineReg(smsec->target);
		out->insert(smse);
		return;
	}
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *smsep = (StateMachineSideEffectPhi *)smse;
		defineReg(smsep->reg);
		out->insert(smse);
		return;
	}
	case StateMachineSideEffect::AssertFalse:
	case StateMachineSideEffect::Unreached:
	case StateMachineSideEffect::Store:
		return;
	}
	abort();
}

void
PossiblyReaching::buildSideEffectTable(StateMachineEdge *e)
{
	std::set<StateMachineSideEffect *> reaching(effectsReachingEdge(e));
	for (auto it = e->sideEffects.begin(); it != e->sideEffects.end(); it++) {
		effectsReachingSideEffect(*it) |= reaching;
		updateReachingSetForSideEffect(*it, &reaching);
	}
}

void
PossiblyReaching::updateEdgeReaching(StateMachineEdge *edge,
				std::set<StateMachineState *> &needsUpdate)
{
	std::set<StateMachineSideEffect *> reachesEnd(effectsReachingEdge(edge));
	for (auto it = edge->sideEffects.begin();
	     it != edge->sideEffects.end();
	     it++)
		updateReachingSetForSideEffect(*it, &reachesEnd);
	std::set<StateMachineSideEffect *> &old(effectsReachingState(edge->target));
	if (old != reachesEnd) {
		old |= reachesEnd;
		needsUpdate.insert(edge->target);
	}
}

/* Assert that the machine does not currently reference and tAR
   structures with non-zero generation number. */
static void
assertNonSsa(StateMachine *inp)
{
#ifndef NDEBUG
	class : public StateMachineTransformer {
		IRExpr *transformIex(IRExprGet *g) {
			assert(g->reg.gen() == 0);
			return NULL;
		}
		StateMachineSideEffectLoad *transformOneSideEffect(StateMachineSideEffectLoad *l, bool *done_something) {
			assert(l->target.gen() == 0);
			return StateMachineTransformer::transformOneSideEffect(l, done_something);
		}
		StateMachineSideEffectCopy *transformOneSideEffect(StateMachineSideEffectCopy *l, bool *done_something) {
			assert(l->target.gen() == 0);
			return StateMachineTransformer::transformOneSideEffect(l, done_something);
		}
		StateMachineSideEffectPhi *transformOneSideEffect(StateMachineSideEffectPhi *, bool *) {
			abort();
		}
	} t;
	t.StateMachineTransformer::transform(inp);
#endif
}

class AllocateSsaVariable {
	std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &lastGeneration;
	PossiblyReaching &reaching;
public:
	threadAndRegister operator()(const threadAndRegister &orig)
	{
		assert(orig.gen() == 0);
		return orig.setGen( ++lastGeneration[orig] );
	}
	StateMachineSideEffectPhi *newPhi(const threadAndRegister &r, const std::vector<unsigned> &generations)
	{
		return new StateMachineSideEffectPhi(
			r.setGen(++lastGeneration[r]),
			generations);
	}
	StateMachineSideEffectPhi *newPhi(const threadAndRegister &r, StateMachineState *e)
	{
		std::vector<unsigned> generations;
		reaching.findReachingGenerations(e, r, generations);
		return newPhi(r, generations);
	}
	StateMachineSideEffectPhi *newPhi(const threadAndRegister &r, StateMachineSideEffect *e)
	{
		std::vector<unsigned> generations;
		reaching.findReachingGenerations(e, r, generations);
		return newPhi(r, generations);
	}
	AllocateSsaVariable(std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &_lastGeneration,
			    PossiblyReaching &_reaching)
		: lastGeneration(_lastGeneration), reaching(_reaching)
	{}
};

static StateMachine *
introduceSsaVars(StateMachine *inp,
		 PossiblyReaching &reaching,
		 std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &lastGeneration)
{
	AllocateSsaVariable allocateSsaVariable(lastGeneration, reaching);
	class _ : public StateMachineTransformer {
		std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &lastGeneration;
		AllocateSsaVariable &allocateSsaVariable;
		StateMachineSideEffectLoad *transformOneSideEffect(StateMachineSideEffectLoad *l, bool *) {
			assert(l->target.gen() == 0);
			return new StateMachineSideEffectLoad(
				l->target.setGen(++lastGeneration[l->target]),
				l->addr,
				l->rip);
		}
		StateMachineSideEffectCopy *transformOneSideEffect(StateMachineSideEffectCopy *c, bool *) {
			assert(c->target.gen() == 0);
			return new StateMachineSideEffectCopy(
				c->target.setGen(++lastGeneration[c->target]),
				c->value);
		}
		StateMachineSideEffectPhi *transformOneSideEffect(StateMachineSideEffectPhi *p, bool *) {
			assert(p->reg.gen() == 0);
			return allocateSsaVariable.newPhi(p->reg, p);
		}
		IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
			return e;
		}
	public:
		_(std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &_lastGeneration,
		  AllocateSsaVariable &_allocateSsaVariable)
			: lastGeneration(_lastGeneration), allocateSsaVariable(_allocateSsaVariable)
		{}
	} t(lastGeneration, allocateSsaVariable);
	return t.StateMachineTransformer::transform(inp);
}

/* Transform references to non-SSA variables into SSA ones wherever
   possible, without introducing any additional Phi nodes. */
static void
useSsaVars(StateMachine *inp, PossiblyReaching &reaching, bool *needPhiEdges,
	   bool *needPhiStates)
{
	std::set<StateMachineState *> visited;
	std::set<StateMachineState *> toVisit;

	class _ {
		bool *needPhiEdges;
		bool *needPhiStates;
		class exp_transformer : public IRExprTransformer {
			bool *needPhis;
			const std::set<StateMachineSideEffect *> &reaching;
			IRExpr *transformIex(IRExprGet *e) {
				if (e->reg.gen() != 0) {
					/* Already done */
					return NULL;
				}
				StateMachineSideEffect *se = NULL;
				for (auto it = reaching.begin();
				     it != reaching.end();
				     it++) {
					if (sideEffectDefinesReg(*it, e->reg)) {
						if (se) {
							/* Multiple
							 * relevant
							 * effects
							 * reach us ->
							 * need a phi
							 * node. */
							*needPhis = true;
							return NULL;
						} else {
							se = *it;
						}
					}
				}
				if (!se) {
					/* There are no reaching
					   assignments at all for this
					   variable.  That means it
					   doesn't matter what
					   generation we give it.
					   Just assign generation -1
					   and have done with it. */
					return IRExpr_Get(
						e->reg.setGen(-1),
						e->ty);
				}
				/* This is definitely the right side effect. */
				threadAndRegister r(threadAndRegister::invalid());
				if (StateMachineSideEffectCopy *c =
				    dynamic_cast<StateMachineSideEffectCopy *>(se)) {
					r = e->reg.setGen(c->target.gen());
					assert(threadAndRegister::fullEq(r, c->target));
				} else if (StateMachineSideEffectLoad *l =
					   dynamic_cast<StateMachineSideEffectLoad *>(se)) {
					r = e->reg.setGen(l->target.gen());
					assert(threadAndRegister::fullEq(r, l->target));
				} else if (StateMachineSideEffectPhi *p =
					   dynamic_cast<StateMachineSideEffectPhi *>(se)) {
					r = e->reg.setGen(p->reg.gen());
					assert(threadAndRegister::fullEq(r, p->reg));
				} else {
					abort();
				}
				return IRExpr_Get(r, e->ty);
			}
		public:
			exp_transformer(bool *_needPhis,
					const std::set<StateMachineSideEffect *> &_reaching)
				: needPhis(_needPhis), reaching(_reaching)
			{}
		};
	public:
		IRExpr * operator()(const std::set<StateMachineSideEffect *> &reaching,
				    IRExpr *e) {
			exp_transformer t(needPhiStates, reaching);
			return t.transformIRExpr(e);
		}
		void operator()(std::set<StateMachineSideEffect *> reaching,
				StateMachineEdge *edge)
		{
			exp_transformer t(needPhiEdges, reaching);
			for (auto it = edge->sideEffects.begin();
			     it != edge->sideEffects.end();
			     it++) {
				StateMachineSideEffect *e = *it;
				switch (e->type) {
				case StateMachineSideEffect::Store: {
					StateMachineSideEffectStore *ss =
						dynamic_cast<StateMachineSideEffectStore *>(e);
					ss->addr = t.transformIRExpr(ss->addr);
					ss->data = t.transformIRExpr(ss->data);
					break;
				}
				case StateMachineSideEffect::Load: {
					StateMachineSideEffectLoad *l =
						dynamic_cast<StateMachineSideEffectLoad *>(e);
					l->addr = t.transformIRExpr(l->addr);
					break;
				}
				case StateMachineSideEffect::Copy: {
					StateMachineSideEffectCopy *c =
						dynamic_cast<StateMachineSideEffectCopy *>(e);
					c->value = t.transformIRExpr(c->value);
					break;
				}
				case StateMachineSideEffect::AssertFalse: {
					StateMachineSideEffectAssertFalse *a =
						dynamic_cast<StateMachineSideEffectAssertFalse *>(e);
					a->value = t.transformIRExpr(a->value);
					break;
				}
				case StateMachineSideEffect::Unreached:
				case StateMachineSideEffect::Phi:
					break;
				}
				updateReachingSetForSideEffect(e, &reaching);
			}
		}
		_(bool *_needPhiEdges, bool *_needPhiStates)
			: needPhiEdges(_needPhiEdges), needPhiStates(_needPhiStates)
		{}
	} doit(needPhiEdges, needPhiStates);
	toVisit.insert(inp->root);
	while (!toVisit.empty()) {
		auto it = toVisit.begin();
		StateMachineState *s = *it;
		toVisit.erase(it);
		if (visited.count(s))
			continue;
		visited.insert(s);

		if (StateMachineStub *sms = dynamic_cast<StateMachineStub *>(s))
			sms->target = doit(reaching.effectsReachingState(s), sms->target);
		else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(s))
			smb->condition = doit(reaching.effectsReachingState(s), smb->condition);

		if (s->target0()) {
			doit(reaching.effectsReachingEdge(s->target0()),
			     s->target0());
			toVisit.insert(s->target0()->target);
		}
		if (s->target1()) {
			doit(reaching.effectsReachingEdge(s->target1()),
			     s->target1());
			toVisit.insert(s->target1()->target);
		}
	}
}

static void
findNeededRegisters(IRExpr *e, std::set<threadAndRegister, threadAndRegister::partialCompare> &out)
{
	class _ : public IRExprTransformer {
		std::set<threadAndRegister, threadAndRegister::partialCompare> &out;
		IRExpr *transformIex(IRExprGet *e) {
			if (e->reg.gen() == 0)
				out.insert(e->reg);
			return NULL;
		}
	public:
		_(std::set<threadAndRegister, threadAndRegister::partialCompare> &_out)
			: out(_out)
		{}
	} trans(out);
	trans.transformIRExpr(e);
}
static void 
findNeededRegisters(StateMachineSideEffect *smse, std::set<threadAndRegister, threadAndRegister::partialCompare> &out)
{
	switch (smse->type) {
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)smse;
		findNeededRegisters(l->addr, out);
		break;
	}
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectStore *l = (StateMachineSideEffectStore *)smse;
		findNeededRegisters(l->addr, out);
		findNeededRegisters(l->data, out);
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *l = (StateMachineSideEffectCopy *)smse;
		findNeededRegisters(l->value, out);
		break;
	}
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *l = (StateMachineSideEffectAssertFalse *)smse;
		findNeededRegisters(l->value, out);
		break;
	}
	case StateMachineSideEffect::Unreached:
	case StateMachineSideEffect::Phi:
		break;
	}
}

static void
introducePhiEdges(StateMachine *inp,
		  PossiblyReaching &reaching,
		  std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &lastGeneration)
{
	AllocateSsaVariable allocateSsaVariable(lastGeneration, reaching);
	std::set<threadAndRegister, threadAndRegister::partialCompare> introduced;
	std::set<StateMachineEdge *> visitedEdges;
	std::set<StateMachineEdge *> toVisitEdges;
	std::set<StateMachineState *> visitedStates;
	std::set<StateMachineState *> toVisitStates;

	toVisitStates.insert(inp->root);
	while (!toVisitStates.empty() ||
	       !toVisitEdges.empty()) {
		while (!toVisitStates.empty()) {
			StateMachineState *s = pop(toVisitStates);
			if (visitedStates.count(s))
				continue;
			visitedStates.insert(s);
			if (s->target0())
				toVisitEdges.insert(s->target0());
			if (s->target1())
				toVisitEdges.insert(s->target1());
		}
		while (!toVisitEdges.empty()) {
			StateMachineEdge *e = pop(toVisitEdges);
			for (unsigned x = 0; x < e->sideEffects.size(); x++) {
				std::set<threadAndRegister, threadAndRegister::partialCompare> needed;
				findNeededRegisters(e->sideEffects[x], needed);
				if (needed.empty())
					continue;
				for (auto it2 = needed.begin();
				     it2 != needed.end();
				     it2++) {
					if (introduced.count(*it2))
						continue;
					e->sideEffects.insert(
						e->sideEffects.begin() + x,
						allocateSsaVariable.newPhi(*it2, e->sideEffects[x]));
					x++;
					introduced.insert(*it2);
				}
			}
			toVisitStates.insert(e->target);
		}
	}
}

static void
introducePhiStates(StateMachine *inp,
		   PossiblyReaching &reaching,
		   std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &lastGeneration)
{
	AllocateSsaVariable allocateSsaVariable(lastGeneration, reaching);

	/* This is a lot easier if the root is a proxy node. */
	if (!dynamic_cast<StateMachineProxy *>(inp->root))
		inp->root = new StateMachineProxy(inp->origin, inp->root);

	class PredecessorMap : public std::map<StateMachineState *, StateMachineEdge *> {
		void discoverEdge(StateMachineEdge *e) {
			auto it = find(e->target);
			if (it == end()) {
				insert(std::pair<StateMachineState *, StateMachineEdge *>
				       (e->target, e));
			} else if (it->second == e) {
				/* do nothing */
			} else {
				/* This state has multiple
				 * predecessors. :( */
				it->second = NULL;
			}
		}
	public:
		PredecessorMap(StateMachine *inp) {
			std::set<StateMachineState *> visited;
			std::set<StateMachineState *> toVisit;
			toVisit.insert(inp->root);
			while (!toVisit.empty()) {
				StateMachineState *s = pop(toVisit);
				if (visited.count(s))
					continue;
				visited.insert(s);
				if (s->target0()) {
					discoverEdge(s->target0());
					toVisit.insert(s->target0()->target);
				}
				if (s->target1()) {
					discoverEdge(s->target1());
					toVisit.insert(s->target1()->target);
				}
			}
		}
	} predecessorMap(inp);
	
	std::set<threadAndRegister, threadAndRegister::partialCompare> introduced;
	std::set<StateMachineState *> needPredecessors;

	class _ {
		AllocateSsaVariable &allocateSsaVariable;
		PredecessorMap &predecessorMap;
		std::set<threadAndRegister, threadAndRegister::partialCompare> &introduced;
		std::set<StateMachineState *> &needPredecessors;
	public:
		void operator()(IRExpr *e, StateMachineState *sm) {
			/* It's pretty bad if the state is
			 * unreachable. */
			assert(predecessorMap.count(sm));
			StateMachineEdge *predecessor = predecessorMap[sm];
			std::set<threadAndRegister, threadAndRegister::partialCompare> needed;
			findNeededRegisters(e, needed);
			for (auto it = needed.begin(); it != needed.end(); it++) {
				if (introduced.count(*it))
					continue;
				if (!predecessor) {
					needPredecessors.insert(sm);
					break;
				}
				predecessor->sideEffects.push_back(
					allocateSsaVariable.newPhi(*it, sm));
				introduced.insert(*it);
			}
		}
		_(AllocateSsaVariable &_allocateSsaVariable,
		  PredecessorMap &_predecessorMap,
		  std::set<threadAndRegister, threadAndRegister::partialCompare> &_introduced,
		  std::set<StateMachineState *> &_needPredecessors)
			: allocateSsaVariable(_allocateSsaVariable),
			  predecessorMap(_predecessorMap),
			  introduced(_introduced),
			  needPredecessors(_needPredecessors)
		{}
	} addPhiNodes(allocateSsaVariable, predecessorMap, introduced, needPredecessors);

	/* Figure out where we need to put our Phi nodes.  If the
	   state has a well-defined predecessor, insert it; otherwise,
	   add it to needPredecessors. */
	std::set<StateMachineState *> visited;
	std::set<StateMachineState *> toVisit;
	toVisit.insert(inp->root);
	while (!toVisit.empty()) {
		StateMachineState *s = pop(toVisit);
		if (visited.count(s))
			continue;
		visited.insert(s);

		if (StateMachineStub *sms = dynamic_cast<StateMachineStub *>(s))
			addPhiNodes(sms->target, sms);
		else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(s))
			addPhiNodes(smb->condition, smb);
		if (s->target0())
			toVisit.insert(s->target0()->target);
		if (s->target1())
			toVisit.insert(s->target1()->target);
	}

	if (introduced.empty()) {
		/* We didn't manage to introduce any new phis.  That
		   had better be because we need some more
		   intermediate states. */
		assert(!needPredecessors.empty());
		StateMachineState *existing = pop(needPredecessors);
		StateMachineState *replacement =
			new StateMachineProxy(existing->origin, existing);
		/* And now iterate to insert that state. */
		visited.clear();
		visited.insert(replacement);
		toVisit.insert(inp->root);
		while (!toVisit.empty()) {
			StateMachineState *s = pop(toVisit);
			if (visited.count(s))
				continue;
			visited.insert(s);
			if (s->target0()) {
				toVisit.insert(s->target0()->target);
				if (s->target0()->target == existing)
					s->target0()->target = replacement;
			}
			if (s->target1()) {
				toVisit.insert(s->target1()->target);
				if (s->target1()->target == existing)
					s->target1()->target = replacement;
			}
		}
	}
}

static bool
useSsaVarsAndIntroducePhis(StateMachine *inp,
			   PossiblyReaching &reaching,
			   std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &lastGeneration)
{
	bool needPhiEdges;
	bool needPhiStates;

	useSsaVars(inp, reaching, &needPhiEdges, &needPhiStates);
	if (needPhiEdges)
		introducePhiEdges(inp, reaching, lastGeneration);
	else if (needPhiStates)
		introducePhiStates(inp, reaching, lastGeneration);
	return needPhiEdges || needPhiStates;
}

class duplication_context {
	typedef void *duplicator_t(duplication_context &ctxt,
				   const void *old);

	struct reloc_t {
		void **ptr;
		const void *old;
		duplicator_t *f;
	};
		
	std::map<const void *, void *> transTable;
	std::vector<reloc_t> relocs;

public:
	template <typename t> void operator()(t **out, const t *inp,
					      t *(*rawDupe)(duplication_context &ctxt,
							    const t *old))
	{
		reloc_t r;
		r.ptr = (void **)out;
		r.old = (const void *)inp;
		r.f = (duplicator_t *)rawDupe;
		relocs.push_back(r);
	}

	void doit(void)
	{
		while (!relocs.empty()) {
			reloc_t r = relocs.back();
			relocs.pop_back();
			auto it = transTable.find(r.old);
			if (it != transTable.end()) {
				*r.ptr = it->second;
				continue;
			}
			void *res = r.f(*this, r.old);
			transTable[r.old] = res;
			*r.ptr = res;
		}
	}
};

static IRRegArray *rawDupe(duplication_context &ctxt, const IRRegArray *inp)
{
	IRRegArray *res = new IRRegArray();
	res->base = inp->base;
	res->elemTy = inp->elemTy;
	res->nElems = inp->nElems;
	return res;
}

static IRConst *rawDupe(duplication_context &ctxt, const IRConst *inp)
{
	IRConst *res = new IRConst();
	res->tag = inp->tag;
	res->Ico = inp->Ico;
	return res;
}

static IRCallee *rawDupe(duplication_context &ctxt, const IRCallee *inp)
{
	IRCallee *res = new IRCallee();
	res->regparms = inp->regparms;
	res->name = inp->name;
	res->addr = inp->addr;
	res->mcx_mask = inp->mcx_mask;
	return res;
}

static IRExpr *rawDupe(duplication_context &ctxt, const IRExpr *inp)
{
	switch (inp->tag) {
	case Iex_Get: {
		const IRExprGet *i = (const IRExprGet *)inp;
		return new IRExprGet(i->reg, i->ty);
	}
	case Iex_GetI: {
		const IRExprGetI *i = (const IRExprGetI *)inp;
		IRExprGetI *res = new IRExprGetI();
		ctxt(&res->descr, i->descr, rawDupe);
		ctxt(&res->ix, i->ix, rawDupe);
		res->bias = i->bias;
		res->tid = i->tid;
		return res;
	}
	case Iex_Qop: {
		const IRExprQop *i = (const IRExprQop *)inp;
		IRExprQop *res = new IRExprQop();
		res->op = i->op;
		ctxt(&res->arg1, i->arg1, rawDupe);
		ctxt(&res->arg2, i->arg2, rawDupe);
		ctxt(&res->arg3, i->arg3, rawDupe);
		ctxt(&res->arg4, i->arg4, rawDupe);
		return res;
	}
	case Iex_Triop: {
		const IRExprTriop *i = (const IRExprTriop *)inp;
		IRExprTriop *res = new IRExprTriop();
		res->op = i->op;
		ctxt(&res->arg1, i->arg1, rawDupe);
		ctxt(&res->arg2, i->arg2, rawDupe);
		ctxt(&res->arg3, i->arg3, rawDupe);
		return res;
	}
	case Iex_Binop: {
		const IRExprBinop *i = (const IRExprBinop *)inp;
		IRExprBinop *res = new IRExprBinop();
		res->op = i->op;
		ctxt(&res->arg1, i->arg1, rawDupe);
		ctxt(&res->arg2, i->arg2, rawDupe);
		return res;
	}
	case Iex_Unop: {
		const IRExprUnop *i = (const IRExprUnop *)inp;
		IRExprUnop *res = new IRExprUnop();
		res->op = i->op;
		ctxt(&res->arg, i->arg, rawDupe);
		return res;
	}
	case Iex_Load: {
		const IRExprLoad *i = (const IRExprLoad *)inp;
		IRExprLoad *res = new IRExprLoad();
		res->ty = i->ty;
		ctxt(&res->addr, i->addr, rawDupe);
		res->rip = i->rip;
		return res;
	}
	case Iex_Const: {
		const IRExprConst *i = (const IRExprConst *)inp;
		IRExprConst *res = new IRExprConst();
		ctxt(&res->con, i->con, rawDupe);
		return res;
	}
	case Iex_CCall: {
		const IRExprCCall *i = (const IRExprCCall *)inp;
		IRExprCCall *res = new IRExprCCall();
		ctxt(&res->cee, i->cee, rawDupe);
		res->retty = i->retty;
		int nr_args;
		for (nr_args = 0; i->args[nr_args]; nr_args++)
			;
		res->args = alloc_irexpr_array(nr_args + 1);
		for (nr_args = 0; i->args[nr_args]; nr_args++)
			ctxt(&res->args[nr_args], i->args[nr_args], rawDupe);
		res->args[nr_args] = NULL;
		return res;
	}
	case Iex_Mux0X: {
		const IRExprMux0X *i = (const IRExprMux0X *)inp;
		IRExprMux0X *res = new IRExprMux0X();
		ctxt(&res->cond, i->cond, rawDupe);
		ctxt(&res->expr0, i->expr0, rawDupe);
		ctxt(&res->exprX, i->exprX, rawDupe);
		return res;
	}
	case Iex_Associative: {
		const IRExprAssociative *i = (const IRExprAssociative *)inp;
		IRExprAssociative *res = new IRExprAssociative();
		res->op = i->op;
		res->nr_arguments = i->nr_arguments;
		res->nr_arguments_allocated = i->nr_arguments;
		static libvex_allocation_site __las = {0, __FILE__, __LINE__};		
		res->contents =
			(IRExpr **)__LibVEX_Alloc_Bytes(&ir_heap,
							sizeof(res->contents[0]) * res->nr_arguments,
							&__las);
		for (int j = 0; j < res->nr_arguments; j++)
			ctxt(&res->contents[j], i->contents[j], rawDupe);
		return res;
	}
	case Iex_FreeVariable: {
		const IRExprFreeVariable *i = (const IRExprFreeVariable *)inp;
		IRExprFreeVariable *res = new IRExprFreeVariable();
		res->key = i->key;
		return res;
	}
	case Iex_ClientCall: {
		const IRExprClientCall *i = (const IRExprClientCall *)inp;
		IRExprClientCall *res = new IRExprClientCall();
		res->calledRip = i->calledRip;
		res->callSite = i->callSite;
		int nr_args;
		for (nr_args = 0; i->args[nr_args]; nr_args++)
			;
		res->args = alloc_irexpr_array(nr_args + 1);
		for (nr_args = 0; i->args[nr_args]; nr_args++)
			ctxt(&res->args[nr_args], i->args[nr_args], rawDupe);
		res->args[nr_args] = NULL;
		return res;
	}
	case Iex_ClientCallFailed: {
		const IRExprClientCallFailed *i = (const IRExprClientCallFailed *)inp;
		IRExprClientCallFailed *res = new IRExprClientCallFailed();
		ctxt(&res->target, i->target, rawDupe);
		return res;
	}
	case Iex_HappensBefore: {
		const IRExprHappensBefore *i = (const IRExprHappensBefore *)inp;
		IRExprHappensBefore *res = new IRExprHappensBefore();
		res->before = i->before;
		res->after = i->after;
		return res;
	}
	}
	abort();
}

static StateMachineSideEffectLoad *
rawDupe(duplication_context &ctxt, const StateMachineSideEffectLoad *l)
{
	StateMachineSideEffectLoad *res = new StateMachineSideEffectLoad(l->target,
									 NULL,
									 l->rip);
	ctxt(&res->addr, l->addr, rawDupe);
	return res;
}

static StateMachineSideEffectStore *
rawDupe(duplication_context &ctxt, const StateMachineSideEffectStore *l)
{
	StateMachineSideEffectStore *res = new StateMachineSideEffectStore(NULL,
									   NULL,
									   l->rip);
	ctxt(&res->addr, l->addr, rawDupe);
	ctxt(&res->data, l->data, rawDupe);
	return res;
}

static StateMachineSideEffectUnreached *
rawDupe(duplication_context &ctxt, const StateMachineSideEffectUnreached *l)
{
	return StateMachineSideEffectUnreached::get();
}

static StateMachineSideEffectAssertFalse *
rawDupe(duplication_context &ctxt, const StateMachineSideEffectAssertFalse *l)
{
	StateMachineSideEffectAssertFalse *res = new StateMachineSideEffectAssertFalse(NULL);
	ctxt(&res->value, l->value, rawDupe);
	return res;
}

static StateMachineSideEffectCopy *
rawDupe(duplication_context &ctxt, const StateMachineSideEffectCopy *l)
{
	StateMachineSideEffectCopy *res = new StateMachineSideEffectCopy(l->target,
									 NULL);
	ctxt(&res->value, l->value, rawDupe);
	return res;
}

static StateMachineSideEffectPhi *
rawDupe(duplication_context &ctxt, const StateMachineSideEffectPhi *l)
{
	return new StateMachineSideEffectPhi(l->reg, l->generations);
}

static StateMachineSideEffect *
rawDupe(duplication_context &ctxt, const StateMachineSideEffect *smse)
{
	switch (smse->type) {
#define do_case(n)							\
		case StateMachineSideEffect::n:				\
			return rawDupe(ctxt,				\
				       (const StateMachineSideEffect ## n *)smse)
		do_case(Load);
		do_case(Store);
		do_case(Unreached);
		do_case(AssertFalse);
		do_case(Copy);
		do_case(Phi);
	}
	abort();
}

static StateMachineState *rawDupe(duplication_context &ctxt, const StateMachineState *inp);

static StateMachineEdge *
rawDupe(duplication_context &ctxt, const StateMachineEdge *inp)
{
	StateMachineEdge *res = new StateMachineEdge(NULL);
	res->sideEffects.resize(inp->sideEffects.size());
	/* We deliberately unshare side effects, so that each one
	   appears in the machine in precisely one place.  This makes
	   the which-side-effects-reach-here calculation a lot
	   easier. */
	for (unsigned x = 0; x < res->sideEffects.size(); x++)
		res->sideEffects[x] = rawDupe(ctxt, inp->sideEffects[x]);
	ctxt(&res->target, inp->target, rawDupe);
	return res;
}

static StateMachineState *
rawDupe(duplication_context &ctxt, const StateMachineState *inp)
{
	if (const StateMachineProxy *smp = dynamic_cast<const StateMachineProxy *>(inp)) {
		StateMachineProxy *res = new StateMachineProxy(smp->origin, (StateMachineEdge *)NULL);
		ctxt(&res->target, smp->target, rawDupe);
		return res;
	} else if (const StateMachineBifurcate *smb = dynamic_cast<const StateMachineBifurcate *>(inp)) {
		StateMachineBifurcate *res = new StateMachineBifurcate(smb->origin, NULL, (StateMachineEdge *)NULL, NULL);
		ctxt(&res->condition, smb->condition, rawDupe);
		ctxt(&res->trueTarget, smb->trueTarget, rawDupe);
		ctxt(&res->falseTarget, smb->falseTarget, rawDupe);
		return res;
	} else if (dynamic_cast<const StateMachineUnreached *>(inp)) {
		return StateMachineUnreached::get();
	} else if (dynamic_cast<const StateMachineCrash *>(inp)) {
		return StateMachineCrash::get();
	} else if (dynamic_cast<const StateMachineNoCrash *>(inp)) {
		return StateMachineNoCrash::get();
	} else if (const StateMachineStub *sms = dynamic_cast<const StateMachineStub *>(inp)) {
		StateMachineStub *res = new StateMachineStub(sms->origin, NULL);
		ctxt(&res->target, sms->target, rawDupe);
		return res;
	} else {
		abort();
	}

}

static StateMachine *
rawDupe(duplication_context &ctxt, const StateMachine *inp)
{
	assert(inp->freeVariables.empty());
	FreeVariableMap fv;
	StateMachine *res = new StateMachine(
		NULL,
		inp->origin,
		fv,
		inp->tid);
	ctxt(&res->root, inp->root, rawDupe);
	return res;
}

static StateMachine *
duplicateStateMachine(const StateMachine *inp)
{
	duplication_context ctxt;
	assert(inp->freeVariables.empty());
	StateMachine *res;
	ctxt(&res, inp, rawDupe);
	ctxt.doit();
	return res;
}

static StateMachine *
convertToSSA(StateMachine *inp)
{
	assertNonSsa(inp);

	inp = duplicateStateMachine(inp);

	std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> lastGeneration;
	{
		PossiblyReaching reaching(inp);
		inp = introduceSsaVars(inp, reaching, lastGeneration);
	}
	PossiblyReaching reaching(inp);
	if (useSsaVarsAndIntroducePhis(inp, reaching, lastGeneration)) {
		bool progress;
		do {
			PossiblyReaching r(inp);
			progress = useSsaVarsAndIntroducePhis(inp, r, lastGeneration);
		} while (progress);
	}
	
	return inp;
}

static StateMachine *
deSSA(StateMachine *inp)
{
	class : public StateMachineTransformer {
		IRExpr *transformIex(IRExprGet *g) {
			if (g->reg.gen() != 0)
				return new IRExprGet(g->reg.setGen(0), g->ty);
			return StateMachineTransformer::transformIex(g);
		}
		StateMachineSideEffectLoad *transformOneSideEffect(StateMachineSideEffectLoad *l, bool *b) {
			if (l->target.gen() != 0) {
				l->target = l->target.setGen(0);
				*b = true;
			}
			return StateMachineTransformer::transformOneSideEffect(l, b);
		}
		StateMachineSideEffectCopy *transformOneSideEffect(StateMachineSideEffectCopy *l, bool *b) {
			if (l->target.gen() != 0) {
				l->target = l->target.setGen(0);
				*b = true;
			}
			return StateMachineTransformer::transformOneSideEffect(l, b);
		}
		StateMachineSideEffectPhi *transformOneSideEffect(StateMachineSideEffectPhi *, bool *) {
			abort(); /* Should have been dropped before gettign here */
		}
		StateMachineEdge *transformOneEdge(StateMachineEdge *edge, bool *done_something) {
			for (unsigned x = 0; x < edge->sideEffects.size(); ) {
				if (edge->sideEffects[x]->type == StateMachineSideEffect::Phi) {
					edge->sideEffects.erase(edge->sideEffects.begin() + x);
					*done_something = true;
				} else {
					x++;
				}
			}
			return StateMachineTransformer::transformOneEdge(edge, done_something);
		}
	} t;
	return t.transform(inp);
}

class optimiseSSATransformer : public StateMachineTransformer {
	PossiblyReaching reaching;

	StateMachineSideEffectPhi *transformOneSideEffect(StateMachineSideEffectPhi *phi,
							  bool *done_something)
	{
		std::vector<unsigned> generations;
		reaching.findReachingGenerations(phi, phi->reg, generations);
		if (generations != phi->generations) {
			*done_something = true;
			phi->generations = generations;
		}
		return phi;
	}
	IRExpr *transformIRExpr(IRExpr *e, bool *b) { return NULL; }
public:
	optimiseSSATransformer(StateMachine *inp)
		: reaching(inp)
	{}
};

/* Other optimisations can sometimes lead to the set of assignments
   which might reach a Phi node shrinking.  This pass goes through and
   fixes things up so that the reaching set in the Phi node
   accurately reflects this. */
static StateMachine *
optimiseSSA(StateMachine *inp, bool *done_something)
{
	optimiseSSATransformer t(inp);
	return t.transform(inp, done_something);
}

/* End of namespace SSA */
}

StateMachine *
convertToSSA(StateMachine *inp)
{
	return SSA::convertToSSA(inp);
}

StateMachine *
deSSA(StateMachine *inp)
{
	return SSA::deSSA(inp);
}

StateMachine *
optimiseSSA(StateMachine *inp, bool *done_something)
{
	return SSA::optimiseSSA(inp, done_something);
}

StateMachineSideEffect *
StateMachineSideEffectPhi::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
{
	if (generations.size() == 1) {
		*done_something = true;
		return new StateMachineSideEffectCopy(
			reg,
			new IRExprGet(reg.setGen(*generations.begin()),
				      Ity_INVALID));
	}
	return this;
}

