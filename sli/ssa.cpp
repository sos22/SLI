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

#ifdef NDEBUG
#define debug_dump_reaching_table 0
#else
static int debug_dump_reaching_table = 0;
#endif

/* Assert that the machine does not currently reference and tAR
   structures with non-zero generation number. */
static void
assertNonSsa(StateMachine *
#ifndef NDEBUG
	     inp
#endif
	)
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
		bool rewriteNewStates() const {
			return false;
		}
	} t;
	t.StateMachineTransformer::transform(inp);
#endif
}

static StateMachine *
assignLabelsToDefinitions(StateMachine *sm,
			  std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &lastGeneration)
{
	struct _ : public StateMachineTransformer {
		std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &lastGeneration;
		StateMachineSideEffect *transformSideEffect(StateMachineSideEffect *se,
							    bool *done_something) {
			threadAndRegister tr(threadAndRegister::invalid());
			if (se->type == StateMachineSideEffect::PointerAliasing) {
				StateMachineSideEffectPointerAliasing *smsespas =
					(StateMachineSideEffectPointerAliasing *)se;
				se = new StateMachineSideEffectPointerAliasing(
					smsespas->reg.setGen(-1),
					smsespas->set);
				*done_something = true;
			} else if (se->definesRegister(tr)) {
				/* Shouldn't be processing the same
				 * side effect multiple times. */
				switch (se->type) {
				case StateMachineSideEffect::Load: {
					StateMachineSideEffectLoad *smsel =
						(StateMachineSideEffectLoad *)se;
					assert(tr.gen() == 0);
					tr = tr.setGen(++lastGeneration[tr]);
					se = new StateMachineSideEffectLoad(
						smsel,
						tr);
					*done_something = true;
					break;
				}
				case StateMachineSideEffect::Copy: {
					StateMachineSideEffectCopy *smsec =
						(StateMachineSideEffectCopy *)se;
					tr = tr.setGen(++lastGeneration[tr]);
					se = new StateMachineSideEffectCopy(
						tr,
						smsec->value);
					*done_something = true;
					break;
				}
				case StateMachineSideEffect::PointerAliasing:
					/* Already handled */
					abort();
				case StateMachineSideEffect::Phi:
					/* Shouldn't be in SSA form yet */
					abort();
				case StateMachineSideEffect::Store:
				case StateMachineSideEffect::AssertFalse:
				case StateMachineSideEffect::Unreached:
				case StateMachineSideEffect::StartAtomic:
				case StateMachineSideEffect::EndAtomic:
				case StateMachineSideEffect::StartFunction:
				case StateMachineSideEffect::EndFunction:
				case StateMachineSideEffect::StackLayout:
					/* These shouldn't define registers */
					abort();
				}
			}
			return se;
		}
		_(std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &_lastGeneration)
			: lastGeneration(_lastGeneration)
		{}
		bool rewriteNewStates() const {
			return false;
		}
	} doit(lastGeneration);
	return doit.transform(sm);
}

/* A map from registers to sets of generations, telling us precisely
   which generations can reach a particular state. */
class ReachingEntry : public std::map<threadAndRegister, std::set<unsigned>, threadAndRegister::partialCompare> {
public:
	bool merge(const ReachingEntry &other);
	const std::set<unsigned> &get(const threadAndRegister &tr) const {
		auto it = find(tr);
		assert(it != end());
		return it->second;
	}
	void print(FILE *f) const {
		for (auto it = begin(); it != end(); it++) {
			if (it != begin())
				fprintf(f, "; ");
			fprintf(f, "%s: (", it->first.name());
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				if (it2 != it->second.begin())
					fprintf(f, ",");
				fprintf(f, "%d", *it2);
			}
			fprintf(f, ")");
		}
	}
};

bool
ReachingEntry::merge(const ReachingEntry &other)
{
	/* Could make this faster by taking advantage of the fact that
	   both maps are sorted in the same order, and the fact that
	   all the sets are sorted in the same order. */
	bool res = false;
	for (auto it = other.begin(); it != other.end(); it++) {
		auto localIt = find(it->first);
		if (localIt == end()) {
			insert(*it);
			res = true;
		} else {
			for (auto genIt = it->second.begin();
			     genIt != it->second.end();
			     genIt++)
				res |= localIt->second.insert(*genIt).second;
		}
	}
	return res;
}

class ReachingTable {
	std::map<const StateMachineState *, ReachingEntry> content;

	/* If we're building a reaching table as part of converting a
	   machine to SSA form, the reaching set is the set of
	   registers for foo is the set of things which foo:0 might
	   resolve to.  Otherwise, it's the set of generations which
	   might be selected by a Phi expression.  The two types of
	   table are generated in almost exactly the same way, except
	   that the former considers any assignment to register foo to
	   kill every other generation of foo in the current reaching
	   set, and the other one doesn't.

	   In other words, the former mode effectively moves the
	   generation number in an assignment from the target register
	   to the assignment itself, erases all of the generation
	   numbers, and computes which assignments might reach each
	   node.  The latter mode which assignments might reach a
	   given node without erasing the labels.

	   Set buildReachingForSSAErasure to true to select the first
	   mode, or false to select the second one.
	*/
	bool buildReachingForSSAErasure;

	ReachingEntry initialReachingSet(const StateMachine *);
	ReachingEntry getExitReaching(const StateMachineState *);
public:
	const ReachingEntry &getEntryReaching(const StateMachineState *sm) const {
		auto it = content.find(sm);
		assert(it != content.end());
		return it->second;
	}
	ReachingTable(const StateMachine *, bool considerErasure);
	void print(FILE *f, std::map<const StateMachineState *, int> &labels) const;
};

ReachingTable::ReachingTable(const StateMachine *inp, bool considerErasure)
	: buildReachingForSSAErasure(considerErasure)
{
	std::queue<const StateMachineState *> toProcess;
	std::vector<const StateMachineState *> states;
	enumStates(inp, &states);

	/* Initial value of the root is the import of all of the
	   registers which might possibly be relevant.  Initial value
	   of everything else is empty. */
	for (auto it = states.begin(); it != states.end(); it++) {
		if (*it == inp->root)
			content[*it] = initialReachingSet(inp);
		else
			content[*it] = ReachingEntry();
		toProcess.push(*it);
	}

	/* Iterate to a fixed point. */
	while (!toProcess.empty()) {
		const StateMachineState *s = toProcess.front();
		toProcess.pop();
		ReachingEntry exitReaching(getExitReaching(s));
		std::vector<const StateMachineState *> exits;
		s->targets(exits);
		for (auto it = exits.begin(); it != exits.end(); it++) {
			if (content[*it].merge(exitReaching))
				toProcess.push(*it);
		}
	}
}

ReachingEntry
ReachingTable::initialReachingSet(const StateMachine *sm)
{
	struct : public StateMachineTransformer {
		ReachingEntry res;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (ieg->reg.isReg())
				res[ieg->reg].insert((unsigned)-1);
			return IRExprTransformer::transformIex(ieg);
		}
		bool rewriteNewStates() const { return false; }
	} doit;
	doit.transform(const_cast<StateMachine *>(sm));
	return doit.res;
}

ReachingEntry
ReachingTable::getExitReaching(const StateMachineState *s)
{
	const StateMachineSideEffect *se = s->getSideEffect();
	threadAndRegister definedHere(threadAndRegister::invalid());
	if (!se || !se->definesRegister(definedHere))
		return content[s];
	ReachingEntry res(content[s]);
	std::set<unsigned> &gens(res[definedHere]);
	if (buildReachingForSSAErasure)
		gens.clear();
	gens.insert(definedHere.gen());
	return res;
}

void
ReachingTable::print(FILE *f, std::map<const StateMachineState *, int> &labels) const
{
	for (auto it = content.begin(); it != content.end(); it++) {
		fprintf(f, "l%d: ", labels[it->first]);
		it->second.print(f);
		fprintf(f, "\n");
	}
}

static StateMachine *
resolveDependencies(StateMachine *sm,
		    ReachingTable &reachingTable,
		    StateMachineState **needsPhi)
{
	struct _ : public StateMachineTransformer {
		const ReachingTable &reachingTable;
		StateMachineState **needsPhi;

		const ReachingEntry *currentStateReaching;
		StateMachineState *currentState;

		IRExpr *transformIex(IRExprGet *ieg) {
			assert(currentStateReaching);
			assert(currentState);
			if (ieg->reg.gen() == 0) {
				const std::set<unsigned> &gen(currentStateReaching->get(ieg->reg));
				assert(gen.size() != 0);
				if (gen.size() == 1) {
					return IRExpr_Get(
						ieg->reg.setGen(*gen.begin()),
						ieg->ty);
				} else {
					*needsPhi = currentState;
					return NULL;
				}
			} else {
				return NULL;
			}
		}
		StateMachineState *transformState(StateMachineState *sms,
						  bool *done_something)
		{
			assert(!currentState);
			assert(!currentStateReaching);
			if (sms->type == StateMachineState::Bifurcate ||
			    sms->type == StateMachineState::SideEffecting)
				currentStateReaching = &reachingTable.getEntryReaching(sms);
			currentState = sms;
			StateMachineState *res =
				StateMachineTransformer::transformState(sms, done_something);
			assert(currentState == sms);
			currentState = NULL;
			currentStateReaching = NULL;
			return res;
		}
		_(ReachingTable &_reachingTable, StateMachineState **_needsPhi)
			: reachingTable(_reachingTable),
			  needsPhi(_needsPhi),
			  currentStateReaching(NULL),			  
			  currentState(NULL)
		{}
		bool rewriteNewStates() const { return false; }
	} doit(reachingTable, needsPhi);
	return doit.transform(sm);
}

class unresolvedRefCmp {
public:
	bool operator()(const std::pair<threadAndRegister, IRType> &a,
			const std::pair<threadAndRegister, IRType> &b) {
		if (a.second < b.second)
			return true;
		if (a.second > b.second)
			return false;
		return threadAndRegister::partialCompare()(a.first, b.first);
	}
};

static void
findUnresolvedReferences(StateMachineState *s, std::set<std::pair<threadAndRegister, IRType>, unresolvedRefCmp> &out)
{
	struct _ : public StateMachineTransformer {
		std::set<std::pair<threadAndRegister, IRType>, unresolvedRefCmp> &out;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (ieg->reg.gen() == 0)
				out.insert(std::pair<threadAndRegister, IRType>(ieg->reg, ieg->ty));
			return NULL;
		}
		_(
			std::set<std::pair<threadAndRegister, IRType>, unresolvedRefCmp> &_out)
			: out(_out)
		{}
		bool rewriteNewStates() const { return false; }
	} t(out);
	bool d;
	t.transformState(s, &d);
}

static StateMachineSideEffecting *
findPredecessor(StateMachine *sm, StateMachineState *s)
{
	if (s->type == StateMachineState::SideEffecting)
		return (StateMachineSideEffecting *)s;
	/* This algorithm doesn't work for finding the predecessor of
	 * the root state, so make sure we don't have to. */
	if (sm->root == s)
		sm->root = new StateMachineSideEffecting(s->dbg_origin, NULL, s);
	std::set<StateMachineState *> allStates;
	enumStates(sm, &allStates);
	StateMachineState *found = NULL;
	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		std::vector<StateMachineState *> successors;
		(*it)->targets(successors);
		for (auto it2 = successors.begin(); it2 != successors.end(); it2++) {
			if (*it2 == s) {
				if (found == NULL) {
					found = *it;
				} else {
					goto insert_new_predecessor;
				}
			}
		}
	}
	if (found && found->type == StateMachineState::SideEffecting)
		return (StateMachineSideEffecting *)found;

insert_new_predecessor:
	StateMachineSideEffecting *res = new StateMachineSideEffecting(s->dbg_origin, NULL, s);
	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		StateMachineState *st = *it;
		std::vector<StateMachineState **> targets;
		st->targets(targets);
		for (auto it = targets.begin(); it != targets.end(); it++)
			if (**it == s)
				**it = res;
	}

	return res;
}

static StateMachine *
convertToSSA(StateMachine *inp)
{
	assertNonSsa(inp);

	inp = duplicateStateMachine(inp);

	std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> lastGeneration;
	inp = assignLabelsToDefinitions(inp, lastGeneration);

	while (1) {
		if (TIMEOUT)
			return NULL;

		ReachingTable reaching(inp, true);
		if (debug_dump_reaching_table) {
			std::map<const StateMachineState *, int> stateLabels;
			printf("At start of SSA conversion iteration:\n");
			printStateMachine(inp, stdout, stateLabels);
			printf("Reaching table:\n");
			reaching.print(stdout, stateLabels);
		}

		StateMachineState *needsPhi = NULL;
		inp = resolveDependencies(inp, reaching, &needsPhi);
		if (!needsPhi) {
			/* We're done */
			break;
		}

		/* We can only introduce one phi node for each
		   register each time around, because every time we do
		   we invalidate the reaching map.  We simplify
		   further by just only resolving one state each
		   time around. */
		std::set<std::pair<threadAndRegister, IRType>, unresolvedRefCmp> needed;
		StateMachineSideEffecting *insertAt;

		findUnresolvedReferences(needsPhi, needed);
		insertAt = findPredecessor(inp, needsPhi);
		for (auto it = needed.begin();
		     it != needed.end();
		     it++)
			insertAt->prependSideEffect(
					new StateMachineSideEffectPhi(
						it->first.setGen(++lastGeneration[it->first]),
						it->second,
						reaching.getEntryReaching(needsPhi).get(it->first)));
	}

	inp->assertSSA();

	return inp;
}

/* End of namespace SSA */
}

StateMachine *
convertToSSA(StateMachine *inp)
{
	return SSA::convertToSSA(inp);
}

StateMachineSideEffect *
StateMachineSideEffectPhi::optimise(const AllowableOptimisations &, bool *done_something)
{
	if (generations.size() == 0 ||
	    generations[0].val == NULL)
		return this;
	IRExpr *v = generations[0].val;
	for (unsigned x = 1; x < generations.size(); x++) {
		if (generations[x].val != v) {
			if (v->tag == Iex_Get &&
			    ((IRExprGet *)v)->reg == generations[x].reg)
				continue;
			return this;
		}
	}
	*done_something = true;
	return new StateMachineSideEffectCopy(reg, v);
}

