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
typedef std::pair<StateMachineEdge *, StateMachineEdge *> st_edge_pair_t;

static StateMachineState *
rewriteStateMachine(StateMachineState *sm,
		    std::map<StateMachineState *, StateMachineState *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules,
		    std::set<StateMachineState *> &memo,
		    std::set<StateMachineEdge *> &edgeMemo);

static StateMachineEdge *
rewriteStateMachineEdge(StateMachineEdge *sme,
			std::map<StateMachineState *, StateMachineState *> &rules,
			std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules,
			std::set<StateMachineState *> &memo,
			std::set<StateMachineEdge *> &edgeMemo)
{
	if (edgeMemo.count(sme))
		return sme;

	if (edgeRules.count(sme)) {
		edgeMemo.insert(edgeRules[sme]);
		return rewriteStateMachineEdge(edgeRules[sme], rules, edgeRules, memo, edgeMemo);
	}
	if (TIMEOUT)
		return sme;
	edgeMemo.insert(sme);
	sme->target = rewriteStateMachine(sme->target,
					  rules,
					  edgeRules,
					  memo,
					  edgeMemo);
	return sme;
}

static StateMachineState *
rewriteStateMachine(StateMachineState *sm,
		    std::map<StateMachineState *, StateMachineState *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules,
		    std::set<StateMachineState *> &memo,
		    std::set<StateMachineEdge *> &edgeMemo)
{
	if (memo.count(sm))
		return sm;

	if (rules.count(sm) && rules[sm] != sm) {
		memo.insert(rules[sm]);
		return rewriteStateMachine(rules[sm], rules, edgeRules, memo, edgeMemo);
	}
	memo.insert(sm);
	switch (sm->type) {
	case StateMachineState::Crash:
	case StateMachineState::NoCrash:
	case StateMachineState::Stub:
	case StateMachineState::Unreached:
		return sm;
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)sm;
		smb->trueTarget = rewriteStateMachineEdge(
			smb->trueTarget,
			rules,
			edgeRules,
			memo,
			edgeMemo);
		smb->falseTarget = rewriteStateMachineEdge(
			smb->falseTarget,
			rules,
			edgeRules,
			memo,
			edgeMemo);
		return sm;
	}
	case StateMachineState::Proxy: {
		StateMachineProxy *smp = (StateMachineProxy *)sm;
		smp->target = rewriteStateMachineEdge(
			smp->target,
			rules,
			edgeRules,
			memo,
			edgeMemo);
		return sm;
	}
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *smp = (StateMachineSideEffecting *)sm;
		smp->target = rewriteStateMachineEdge(
			smp->target,
			rules,
			edgeRules,
			memo,
			edgeMemo);
		return sm;
	}
	}
	abort();
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
rewriteStateMachine(StateMachineState *sm, std::map<StateMachineState *, StateMachineState *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules)
{
	/* Cyclies make this work badly. */
	assert_mapping_acyclic(rules);
	assert_mapping_acyclic(edgeRules);

	std::set<StateMachineState *> memo;
	std::set<StateMachineEdge *> edgeMemo;

	return rewriteStateMachine(sm, rules, edgeRules, memo, edgeMemo);
}

static StateMachine *
rewriteStateMachine(StateMachine *sm, std::map<StateMachineState *, StateMachineState *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules)
{
	sm->root = rewriteStateMachine(sm->root, rules, edgeRules);
	return sm;
}

static bool
edgesLocallyBisimilar(StateMachineEdge *sme1,
		      StateMachineEdge *sme2,
		      const std::set<st_pair_t> &states,
		      const AllowableOptimisations &opt)
{
	if (!states.count(st_pair_t(sme1->target, sme2->target)))
		return false;
	if (!!sme1->sideEffect != !!sme2->sideEffect)
		return false;
	if (!sme1->sideEffect)
		return true;
	return sideEffectsBisimilar(sme1->sideEffect, sme2->sideEffect, opt);
}

static bool
statesLocallyBisimilar(StateMachineState *sm1,
		       StateMachineState *sm2,
		       const std::set<st_edge_pair_t> &edges,
		       const AllowableOptimisations &opt)
{
	if (sm1 == sm2)
		return true;

	if (sm1->type != sm2->type)
		return false;

	switch (sm1->type) {
		/* These have no data, so if they're the same type it's fine */
	case StateMachineState::Unreached:
	case StateMachineState::Crash:
	case StateMachineState::NoCrash:
		return true;

	case StateMachineState::Stub: {
		StateMachineStub *sms1 = (StateMachineStub *)sm1;
		StateMachineStub *sms2 = (StateMachineStub *)sm2;
		return sms1->target == sms2->target;
	}

	case StateMachineState::Proxy: {
		StateMachineProxy *smp1 = (StateMachineProxy *)sm1;
		StateMachineProxy *smp2 = (StateMachineProxy *)sm2;
		return edges.count(st_edge_pair_t(smp1->target, smp2->target));
	}

	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme1 = (StateMachineSideEffecting *)sm1;
		StateMachineSideEffecting *sme2 = (StateMachineSideEffecting *)sm2;
		return edges.count(st_edge_pair_t(sme1->target, sme2->target)) &&
			sideEffectsBisimilar(sme1->sideEffect, sme2->sideEffect, opt);
	}

	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb1 = (StateMachineBifurcate *)sm1;
		StateMachineBifurcate *smb2 = (StateMachineBifurcate *)sm2;
		return edges.count(st_edge_pair_t(smb1->trueTarget, smb2->trueTarget)) &&
			edges.count(st_edge_pair_t(smb1->falseTarget, smb2->falseTarget)) &&
			definitelyEqual(smb1->condition, smb2->condition, opt);
	}
	}
	abort();
}

static void
buildStateMachineBisimilarityMap(StateMachine *sm, std::set<st_pair_t> &bisimilarStates,
				 std::set<st_edge_pair_t> &bisimilarEdges,
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

	std::set<StateMachineEdge *> allEdges;
	findAllEdges(sm, allEdges);	

	/* Initially, everything is bisimilar to everything else. */
	for (std::set<StateMachineState *>::const_iterator it = allStates->begin();
	     !TIMEOUT && it != allStates->end();
	     it++)
		for (std::set<StateMachineState *>::const_iterator it2 = allStates->begin();
		     !TIMEOUT && it2 != allStates->end();
		     it2++)
			bisimilarStates.insert(st_pair_t(*it, *it2));
	for (std::set<StateMachineEdge *>::iterator it = allEdges.begin();
	     !TIMEOUT && it != allEdges.end();
	     it++)
		for (std::set<StateMachineEdge *>::iterator it2 = allEdges.begin();
		     !TIMEOUT && it2 != allEdges.end();
		     it2++)
			bisimilarEdges.insert(st_edge_pair_t(*it, *it2));

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
			if (statesLocallyBisimilar(it->first, it->second, bisimilarEdges, opt)) {
				it++;
			} else {
				bisimilarStates.erase(it++);
				progress = true;
			}
		}
		for (std::set<st_edge_pair_t>::iterator it = bisimilarEdges.begin();
		     it != bisimilarEdges.end();
			) {
			if (edgesLocallyBisimilar(it->first, it->second, bisimilarStates, opt)) {
				it++;
			} else {
				bisimilarEdges.erase(it++);
				progress = true;
			}
		}
	} while (progress);
}

static StateMachine *
bisimilarityReduction(StateMachine *sm, const AllowableOptimisations &opt)
{
	__set_profiling(bisimilarityReduction);
	std::set<st_edge_pair_t> bisimilarEdges;
	std::set<st_pair_t> bisimilarStates;
	std::set<StateMachineState *> allStates;

	findAllStates(sm, allStates);
	buildStateMachineBisimilarityMap(sm, bisimilarStates, bisimilarEdges, &allStates, opt);

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

	/* Do the same thing for edges */
	std::map<StateMachineEdge *, StateMachineEdge *> canonEdgeMap;
	for (std::set<st_edge_pair_t>::iterator it = bisimilarEdges.begin();
	     it != bisimilarEdges.end();
	     it++) {
		StateMachineEdge *s1 = it->first;
		StateMachineEdge *s2 = it->second;
		while (canonEdgeMap.count(s1))
			s1 = canonEdgeMap[s1];
		while (canonEdgeMap.count(s2))
			s2 = canonEdgeMap[s2];
		if (s1 != s2)
			canonEdgeMap[s2] = s1;
	}

	/* Perform the rewrite.  We do this in-place, because it's not
	   context-dependent. */
	return rewriteStateMachine(sm, canonMap, canonEdgeMap);
}

/* end of namespace */
}

StateMachine *
bisimilarityReduction(StateMachine *sm, const AllowableOptimisations &opt)
{
	return _bisimilarity::bisimilarityReduction(sm, opt);
}

