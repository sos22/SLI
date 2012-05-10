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

static StateMachine *
assignLabelsToDefinitions(StateMachine *sm,
			  std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &lastGeneration)
{
	struct _ : public StateMachineTransformer {
		std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &lastGeneration;
		StateMachineSideEffect *transformSideEffect(StateMachineSideEffect *se,
							    bool *done_something) {
			threadAndRegister tr(threadAndRegister::invalid());
			if (se->definesRegister(tr)) {
				/* Shouldn't be processing the same
				 * side effect multiple times. */
				assert(tr.gen() == 0);
				tr = tr.setGen(++lastGeneration[tr]);
				switch (se->type) {
				case StateMachineSideEffect::Load: {
					StateMachineSideEffectLoad *smsel =
						(StateMachineSideEffectLoad *)se;
					se = new StateMachineSideEffectLoad(
						tr,
						smsel->addr,
						smsel->rip,
						smsel->type);
					*done_something = true;
					break;
				}
				case StateMachineSideEffect::Copy: {
					StateMachineSideEffectCopy *smsec =
						(StateMachineSideEffectCopy *)se;
					se = new StateMachineSideEffectCopy(
						tr,
						smsec->value);
					*done_something = true;
					break;
				}
				case StateMachineSideEffect::Phi:
					/* Shouldn't be in SSA form yet */
					abort();
				case StateMachineSideEffect::Store:
				case StateMachineSideEffect::AssertFalse:
				case StateMachineSideEffect::Unreached:
					/* These shouldn't define registers */
					abort();
				}
			}
			return se;
		}
		_(std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> &_lastGeneration)
			: lastGeneration(_lastGeneration)
		{}
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
	ReachingEntry initialReachingSet(const StateMachine *);
	ReachingEntry getExitReaching(const StateMachineState *);
public:
	const ReachingEntry &getEntryReaching(const StateMachineState *sm) const {
		auto it = content.find(sm);
		assert(it != content.end());
		return it->second;
	}
	ReachingTable(const StateMachine *);
	void print(FILE *f, std::map<const StateMachineState *, int> &labels) const;
};

ReachingTable::ReachingTable(const StateMachine *inp)
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
		    std::set<StateMachineState *> &failedStates)
{
	struct _ : public StateMachineTransformer {
		const ReachingTable &reachingTable;
		std::set<StateMachineState *> &failedStates;

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
					failedStates.insert(currentState);
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
		_(ReachingTable &_reachingTable,
		  std::set<StateMachineState *> &_failedStates)
			: reachingTable(_reachingTable),
			  failedStates(_failedStates),
			  currentStateReaching(NULL),
			  currentState(NULL)
		{}
	} doit(reachingTable, failedStates);
	return doit.transform(sm);
}

static void
findUnresolvedReferences(StateMachineState *s, std::set<threadAndRegister, threadAndRegister::partialCompare> &out)
{
	struct _ : public StateMachineTransformer {
		std::set<threadAndRegister, threadAndRegister::partialCompare> &out;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (ieg->reg.gen() == 0)
				out.insert(ieg->reg);
			return NULL;
		}
		_(
			std::set<threadAndRegister, threadAndRegister::partialCompare> &_out)
			: out(_out)
		{}
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
		sm->root = new StateMachineSideEffecting(s->origin, NULL, s);
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
	StateMachineSideEffecting *res = new StateMachineSideEffecting(s->origin, NULL, s);
	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		StateMachineState *st = *it;
		switch (st->type) {
		case StateMachineState::SideEffecting: {
			StateMachineSideEffecting *se = (StateMachineSideEffecting *)st;
			if (se->target == s)
				se->target = res;
			break;
		}
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *se = (StateMachineBifurcate *)st;
			if (se->trueTarget == s)
				se->trueTarget = res;
			if (se->falseTarget == s)
				se->falseTarget = res;
			break;
		}
		case StateMachineState::NdChoice: {
			StateMachineNdChoice *smnd = (StateMachineNdChoice *)st;
			for (auto it = smnd->successors.begin(); it != smnd->successors.end(); it++) {
				if (*it == s)
					*it = res;
			}
			break;
		}
		case StateMachineState::Unreached:
		case StateMachineState::Crash:
		case StateMachineState::NoCrash:
		case StateMachineState::Stub:
			break;
		}
	}

	return res;
}

static StateMachine *
convertToSSA(StateMachine *inp)
{
	inp->sanityCheck();
	assertNonSsa(inp);

	inp = duplicateStateMachine(inp);

	std::map<threadAndRegister, unsigned, threadAndRegister::partialCompare> lastGeneration;
	inp = assignLabelsToDefinitions(inp, lastGeneration);

	std::set<StateMachineState *> pendingStates;
	enumStates(inp, &pendingStates);

	while (1) {
		if (TIMEOUT)
			return NULL;

		ReachingTable reaching(inp);
		if (debug_dump_reaching_table) {
			std::map<const StateMachineState *, int> stateLabels;
			printf("At start of SSA conversion iteration:\n");
			printStateMachine(inp, stdout, stateLabels);
			printf("Reaching table:\n");
			reaching.print(stdout, stateLabels);
		}

		std::set<StateMachineState *> newPendingStates;
		inp = resolveDependencies(inp, reaching, newPendingStates);
		if (newPendingStates.empty()) {
			/* We're done */
			break;
		}

		/* We can only introduce one phi node for each
		   register each time around, because every time we do
		   we invalidate the reaching map.  We simplify
		   further by just only resolving one state each
		   time around. */
		StateMachineState *s;
		{
			auto it = newPendingStates.begin();
			s = *it;
			it++;
			pendingStates.clear();
			pendingStates.insert(it, newPendingStates.end());
		}

		std::set<threadAndRegister, threadAndRegister::partialCompare> needed;
		StateMachineSideEffecting *insertAt;

		findUnresolvedReferences(s, needed);
		insertAt = findPredecessor(inp, s);
		for (auto it = needed.begin();
		     it != needed.end();
		     it++)
			insertAt->prependSideEffect(
					new StateMachineSideEffectPhi(
						it->setGen(++lastGeneration[*it]),
						reaching.getEntryReaching(s).get(*it)));
	}

	inp->assertSSA();
	inp->sanityCheck();

	return inp;
}

class optimiseSSATransformer : public StateMachineTransformer {
	ReachingTable reaching;

	StateMachineSideEffecting *transformOneState(StateMachineSideEffecting *smse,
						     bool *done_something)
	{
		StateMachineSideEffect *se = smse->getSideEffect();
		if (se && se->type == StateMachineSideEffect::Phi) {
			StateMachineSideEffectPhi *phi =
				(StateMachineSideEffectPhi *)se;
			const std::set<unsigned> &generations(reaching.getEntryReaching(smse).get(phi->reg));
			std::vector<std::pair<unsigned, IRExpr *> > newGenerations;
			newGenerations.reserve(phi->generations.size());
			for (auto it = phi->generations.begin();
			     it != phi->generations.end();
			     it++) {
				if (generations.count(it->first))
					newGenerations.push_back(*it);
			}
			if (newGenerations.size() < phi->generations.size()) {
				*done_something = true;
				return new StateMachineSideEffecting(
					smse->origin,
					new StateMachineSideEffectPhi(
						phi->reg,
						newGenerations),
					smse->target);
			}
		}
		return smse;
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
	if (TIMEOUT)
		return inp;
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
optimiseSSA(StateMachine *inp, bool *done_something)
{
	return SSA::optimiseSSA(inp, done_something);
}

StateMachineSideEffect *
StateMachineSideEffectPhi::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
{
	if (generations.size() == 0 ||
	    generations[0].second == NULL)
		return this;
	IRExpr *v = generations[0].second;
	for (unsigned x = 1; x < generations.size(); x++) {
		if (generations[x].second != v)
			return this;
	}
	*done_something = true;
	return new StateMachineSideEffectCopy(reg, v);
}

