/* Try to identify states which are bisimilar, and then go and merge
 * them.  This is in-place, so should really be part of ::optimise();
 * nevermind. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "libvex_prof.hpp"

namespace _bisimilarity {
/* Unconfuse emacs */
#if 0
}
#endif

typedef std::pair<StateMachineState *, StateMachineState *> st_pair_t;

static StateMachineState *
rewriteStateMachine(StateMachineState *sm,
		    std::map<StateMachineState *, StateMachineState *> &rules,
		    std::set<StateMachineState *> &memo);

static StateMachineState *
rewriteStateMachine(StateMachineState *sm,
		    std::map<StateMachineState *, StateMachineState *> &rules,
		    std::set<StateMachineState *> &memo)
{
	if (memo.count(sm))
		return sm;

	if (rules.count(sm) && rules[sm] != sm) {
		memo.insert(rules[sm]);
		return rewriteStateMachine(rules[sm], rules, memo);
	}
	memo.insert(sm);
	std::vector<StateMachineState **> targets;
	sm->targets(targets);
	for (auto it = targets.begin(); it != targets.end(); it++)
		**it = rewriteStateMachine(**it, rules, memo);
	return sm;
}

template <typename t> void
assert_mapping_acyclic(std::map<t, t> &m)
{
	std::set<t> clean;

	for (typename std::map<t, t>::const_iterator it = m.begin();
	     it != m.end();
	     it++) {
		if (clean.count(it->first))
			continue;
		t fastIterator;
		t slowIterator;
		bool cycle;
		slowIterator = fastIterator = it->first;
		while (1) {
			clean.insert(fastIterator);
			fastIterator = m[fastIterator];
			if (fastIterator == slowIterator) {
				cycle = true;
				break;
			}
			if (!m.count(fastIterator)) {
				cycle = false;
				break;
			}

			clean.insert(fastIterator);
			fastIterator = m[fastIterator];
			if (fastIterator == slowIterator) {
				cycle = true;
				break;
			}
			if (!m.count(fastIterator)) {
				cycle = false;
				break;
			}

			assert(m.count(slowIterator));
			slowIterator = m[slowIterator];
		}
		assert(!cycle);
	}
}

static StateMachineState *
rewriteStateMachine(StateMachineState *sm, std::map<StateMachineState *, StateMachineState *> &rules)
{
	/* Cyclies make this work badly. */
	assert_mapping_acyclic(rules);

	std::set<StateMachineState *> memo;

	return rewriteStateMachine(sm, rules, memo);
}

static StateMachine *
rewriteStateMachine(StateMachine *sm, std::map<StateMachineState *, StateMachineState *> &rules)
{
	sm->root = rewriteStateMachine(sm->root, rules);
	return sm;
}

static bool
statesLocallyBisimilar(StateMachineState *sm1,
		       StateMachineState *sm2,
		       const std::set<st_pair_t> &edges,
		       const AllowableOptimisations &opt)
{
	if (sm1 == sm2)
		return true;

	if (sm1->type != sm2->type)
		return false;

	std::vector<StateMachineState *> smTarg1;
	std::vector<StateMachineState *> smTarg2;
	sm1->targets(smTarg1);
	sm2->targets(smTarg2);
	if (smTarg1.size() != smTarg2.size())
		return false;
	for (unsigned x = 0; x < smTarg1.size(); x++) {
		if (!edges.count(st_pair_t(smTarg1[x], smTarg2[x])))
			return false;
	}
	switch (sm1->type) {
		/* These have no data, so if they're the same type it's fine */
	case StateMachineState::Unreached:
	case StateMachineState::Crash:
	case StateMachineState::NoCrash:
	case StateMachineState::NdChoice:
		return true;

	case StateMachineState::Stub: {
		StateMachineStub *sms1 = (StateMachineStub *)sm1;
		StateMachineStub *sms2 = (StateMachineStub *)sm2;
		return sms1->target == sms2->target;
	}

	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme1 = (StateMachineSideEffecting *)sm1;
		StateMachineSideEffecting *sme2 = (StateMachineSideEffecting *)sm2;
		return sideEffectsBisimilar(sme1->sideEffect, sme2->sideEffect, opt);
	}

	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb1 = (StateMachineBifurcate *)sm1;
		StateMachineBifurcate *smb2 = (StateMachineBifurcate *)sm2;
		return definitelyEqual(smb1->condition, smb2->condition, opt);
	}
	}
	abort();
}

static void
buildStateMachineBisimilarityMap(StateMachine *sm, std::set<st_pair_t> &bisimilarStates,
				 const std::set<StateMachineState *> *allStates,
				 const AllowableOptimisations &opt)
{
	/* We start by assuming that all states are bisimilar to each
	   other, and then use Tarski iteration to eliminate the
	   contradictions.  That allows us to build up maximal sets of
	   states such that the states in the sets are bisimilar to
	   each other.  Once we've got that, we pick one of the states
	   as being representative of the set, and then use it in
	   place of the other states. */
	std::set<StateMachineState *> _allStates;
	if (!allStates) {
		allStates = &_allStates;
		findAllStates(sm, _allStates);
	}

	/* Initially, everything is bisimilar to everything else. */
	for (std::set<StateMachineState *>::const_iterator it = allStates->begin();
	     !TIMEOUT && it != allStates->end();
	     it++)
		for (std::set<StateMachineState *>::const_iterator it2 = allStates->begin();
		     !TIMEOUT && it2 != allStates->end();
		     it2++)
			bisimilarStates.insert(st_pair_t(*it, *it2));

	bool progress;
	do {
		progress = false;

		if (TIMEOUT)
			return;
		/* Iterate over every suspected bisimilarity pair and
		   check for ``local bisimilarity''.  Once we're
		   consistent with the local bisimilarity
		   relationship, we will also be consistent with
		   global bismilarity. */
		for (std::set<st_pair_t>::iterator it = bisimilarStates.begin();
		     it != bisimilarStates.end();
			) {
			if (statesLocallyBisimilar(it->first, it->second, bisimilarStates, opt)) {
				it++;
			} else {
				bisimilarStates.erase(it++);
				progress = true;
			}
		}
	} while (progress);
}

static StateMachine *
bisimilarityReduction(StateMachine *sm, const AllowableOptimisations &opt)
{
	__set_profiling(bisimilarityReduction);
	std::set<st_pair_t> bisimilarStates;
	std::set<StateMachineState *> allStates;

	findAllStates(sm, allStates);
	buildStateMachineBisimilarityMap(sm, bisimilarStates, &allStates, opt);

	if (TIMEOUT)
		return sm;

	std::map<StateMachineState *, StateMachineState *> canonMap;

	/* Now build a mapping from states to canonical states, using
	   the bisimilarity information, such that two states map to
	   the same canonical state iff they are bisimilar. */
	/* The canonMap effectively forms an inverted forest.  Each
	   tree in the forest represents some set of bisimilar nodes,
	   and each node's entry points at its parent in the tree, if
	   it has one.  The canonical representation of each set is
	   the root of its corresponding tree.  We advance by merging
	   sets, by inserting one as a child of the root of the other,
	   in response to bisimilar state entries. */

	for (std::set<st_pair_t>::iterator it = bisimilarStates.begin();
	     it != bisimilarStates.end();
	     it++) {
		StateMachineState *s1 = it->first;
		StateMachineState *s2 = it->second;

		/* Map the two nodes to their canonicalisations, if
		 * they have them. */
		while (canonMap.count(s1))
			s1 = canonMap[s1];
		while (canonMap.count(s2))
			s2 = canonMap[s2];
		/* This is more subtle than it looks.  It might appear
		   that we should be able to pick pretty much
		   arbitrarily which way round we perform the mapping
		   (s2 -> s1 or s1 -> s2).  Not so: the mapping we
		   build has to respect a depth-first ordering of the
		   graph, or you risk introducing loops.  This way
		   around does respect that ordering, whereas the
		   other way around wouldn't. */
		/* XXX I'm not entirely convinced I believe that
		 * explanation. */
		if (s1 != s2)
			canonMap[s2] = s1;
	}

	/* Perform the rewrite.  We do this in-place, because it's not
	   context-dependent. */
	return rewriteStateMachine(sm, canonMap);
}

/* end of namespace */
}

StateMachine *
bisimilarityReduction(StateMachine *sm, const AllowableOptimisations &opt)
{
	return _bisimilarity::bisimilarityReduction(sm, opt);
}

