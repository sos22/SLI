/* Try to identify states which are bisimilar, and then go and merge
 * them.  This is in-place, so should really be part of ::optimise();
 * nevermind. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "libvex_prof.hpp"
#include "maybe.hpp"
#include "hash_table.hpp"
#include "allowable_optimisations.hpp"

#ifndef NDEBUG
static bool debug_bisimilarity = false;
#else
#define debug_bisimilarity false
#endif

namespace _bisimilarity {
/* Unconfuse emacs */
#if 0
}
#endif

class st_pair_t: public  std::pair<StateMachineState *, StateMachineState *> {
public:
	st_pair_t(StateMachineState *a, StateMachineState *b)
		: std::pair<StateMachineState *, StateMachineState *>(a, b)
	{}
	st_pair_t() {}
	unsigned long hash() const {
		return (unsigned long)first * 3 + (unsigned long)second * 5;
	}
};

static StateMachineState *
rewriteStateMachine(StateMachineState *sm,
		    HashedMap<HashedPtr<StateMachineState>, StateMachineState *> &rules,
		    HashedSet<HashedPtr<StateMachineState> > &memo);

static StateMachineState *
rewriteStateMachine(StateMachineState *sm,
		    HashedMap<HashedPtr<StateMachineState>, StateMachineState *> &rules,
		    HashedSet<HashedPtr<StateMachineState> > &memo)
{
	if (memo.contains(sm))
		return sm;

	Maybe<StateMachineState *> r = rules.get(sm);
	if (r.valid && r.content != sm) {
		memo.insert(r.content);
		return r.content;
	}
	memo.insert(sm);
	std::vector<StateMachineState **> targets;
	sm->targets(targets);
	for (auto it = targets.begin(); it != targets.end(); it++)
		**it = rewriteStateMachine(**it, rules, memo);
	return sm;
}

static StateMachineState *
rewriteStateMachine(StateMachineState *sm, HashedMap<HashedPtr<StateMachineState>, StateMachineState *> &rules)
{
	HashedSet<HashedPtr<StateMachineState> > memo;

	return rewriteStateMachine(sm, rules, memo);
}

static StateMachine *
rewriteStateMachine(StateMachine *sm, HashedMap<HashedPtr<StateMachineState>, StateMachineState *> &rules)
{
	sm->root = rewriteStateMachine(sm->root, rules);
	return sm;
}

static bool
statesLocallyBisimilar(StateMachineState *sm1,
		       StateMachineState *sm2,
		       const HashedSet<st_pair_t> &edges)
{
	assert(sm1 != sm2);
	assert(sm1->type == sm2->type);

	std::vector<StateMachineState *> smTarg1;
	std::vector<StateMachineState *> smTarg2;
	sm1->targets(smTarg1);
	sm2->targets(smTarg2);
	assert(smTarg1.size() == smTarg2.size());
	for (unsigned x = 0; x < smTarg1.size(); x++) {
		if (smTarg1[x] != smTarg2[x] &&
		    !edges.contains(st_pair_t(smTarg1[x], smTarg2[x])))
			return false;
	}
	return true;
}

static bool
statesMightBeBisimilar(StateMachineState *sm1,
		       StateMachineState *sm2,
		       const AllowableOptimisations &opt)
{
	assert(sm1 != sm2);
	if (sm1->type != sm2->type)
		return false;

	std::vector<StateMachineState *> smTarg1;
	std::vector<StateMachineState *> smTarg2;
	sm1->targets(smTarg1);
	sm2->targets(smTarg2);
	if (smTarg1.size() != smTarg2.size())
		return false;
	switch (sm1->type) {
		/* These have no data, so if they're the same type it's fine */
	case StateMachineState::Unreached:
	case StateMachineState::Crash:
	case StateMachineState::NoCrash:
		return true;

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
buildStateMachineBisimilarityMap(HashedSet<st_pair_t> &bisimilarStates,
				 const std::set<StateMachineState *> &allStates,
				 const AllowableOptimisations &opt,
				 const std::map<const StateMachineState *, int> &labels)
{
	/* We start by assuming that all states are bisimilar to each
	   other, and then use Tarski iteration to eliminate the
	   contradictions.  That allows us to build up maximal sets of
	   states such that the states in the sets are bisimilar to
	   each other.  Once we've got that, we pick one of the states
	   as being representative of the set, and then use it in
	   place of the other states. */

	/* Initially, everything is bisimilar to everything else. */
	for (auto it = allStates.begin();
	     !TIMEOUT && it != allStates.end();
	     it++)
		for (auto it2 = allStates.begin();
		     !TIMEOUT && it2 != allStates.end();
		     it2++)
			if (*it != *it2 && statesMightBeBisimilar(*it, *it2, opt))
				bisimilarStates.insert(st_pair_t(*it, *it2));

	if (debug_bisimilarity) {
		printf("Initial bisimilarity map:\n");
		for (auto it = bisimilarStates.begin(); !it.finished(); it.advance()) {
			auto it1 = labels.find(it->first);
			auto it2 = labels.find(it->second);
			assert(it1 != labels.end());
			assert(it2 != labels.end());
			printf("\tl%d <-> l%d\n", it1->second, it2->second);
		}
		for (auto it = labels.begin(); it != labels.end(); it++)
			printf("\tl%d -> %p\n", it->second, it->first);
	}

	bool progress;
	do {
		progress = false;

		if (TIMEOUT)
			return;
		if (debug_bisimilarity)
			printf("Start Tarski iteration\n");
		/* Iterate over every suspected bisimilarity pair and
		   check for ``local bisimilarity''.  Once we're
		   consistent with the local bisimilarity
		   relationship, we will also be consistent with
		   global bismilarity. */
		for (auto it = bisimilarStates.begin(); !it.finished(); ) {
			if (statesLocallyBisimilar(it->first, it->second, bisimilarStates)) {
				if (debug_bisimilarity) {
					auto it1 = labels.find(it->first);
					auto it2 = labels.find(it->second);
					assert(it1 != labels.end());
					assert(it2 != labels.end());
					printf("\tPreserve l%d <-> l%d\n",
					       it1->second, it2->second);
				}
				it.advance();
			} else {
				if (debug_bisimilarity) {
					auto it1 = labels.find(it->first);
					auto it2 = labels.find(it->second);
					assert(it1 != labels.end());
					assert(it2 != labels.end());
					printf("\tErase l%d <-> l%d\n",
					       it1->second, it2->second);
				}
				it.erase();
				progress = true;
			}
		}
	} while (progress);

	if (debug_bisimilarity) {
		printf("Final bisimilarity map:\n");
		for (auto it = bisimilarStates.begin(); !it.finished(); it.advance()) {
			auto it1 = labels.find(it->first);
			auto it2 = labels.find(it->second);
			assert(it1 != labels.end());
			assert(it2 != labels.end());
			printf("\tl%d <-> l%d\n", it1->second, it2->second);
		}
	}
}

static StateMachine *
bisimilarityReduction(StateMachine *sm, const AllowableOptimisations &opt)
{
	std::map<const StateMachineState *, int> stateLabels;

	__set_profiling(bisimilarityReduction);
	HashedSet<st_pair_t> bisimilarStates;
	std::set<StateMachineState *> allStates;

	findAllStates(sm, allStates);

	if (debug_bisimilarity) {
		printf("%s(..., %s):\n", __func__, opt.name());
		printf("SM = \n");
		printStateMachine(sm, stdout, stateLabels);
	}
	buildStateMachineBisimilarityMap(bisimilarStates, allStates, opt, stateLabels);

	if (TIMEOUT)
		return sm;

	HashedMap<HashedPtr<StateMachineState>, StateMachineState *> canonMap;

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

	for (auto it = bisimilarStates.begin(); !it.finished(); it.advance()) {
		StateMachineState *s1 = it->first;
		StateMachineState *s2 = it->second;

		/* Map the two nodes to their canonicalisations, if
		 * they have them. */
		while (1) {
			Maybe<StateMachineState *> r = canonMap.get(s1);
			if (!r.valid)
				break;
			s1 = r.content;
		}
		while (1) {
			Maybe<StateMachineState *> r = canonMap.get(s2);
			if (!r.valid)
				break;
			s2 = r.content;
		}
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
			canonMap.set(s2, s1);
	}

	if (debug_bisimilarity) {
		printf("Canonicalisation map:\n");
		for (auto it = canonMap.begin(); !it.finished(); it.advance())
			printf("\tl%d -> l%d\n",
			       stateLabels[it.key()],
			       stateLabels[it.value()]);
	}

	/* Perform the rewrite.  We do this in-place, because it's not
	   context-dependent. */
	StateMachine *res = rewriteStateMachine(sm, canonMap);
	if (debug_bisimilarity) {
		printf("Rewritten machine:\n");
		printStateMachine(res, stdout);
	}
	return res;
}

/* end of namespace */
}

StateMachine *
bisimilarityReduction(StateMachine *sm, const AllowableOptimisations &opt)
{
	return _bisimilarity::bisimilarityReduction(sm, opt);
}

