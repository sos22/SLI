#include <map>

#include "sli.h"
#include "oracle.hpp"
#include "cfgnode.hpp"
#include "hash_table.hpp"
#include "stacked_cdf.hpp"

#include "cfgnode_tmpl.cpp"

namespace _getProbeCFGs {

#ifdef NDEBUG
#define debug_exploration 0
#define debug_trim 0
#define debug_find_roots 0
#else
static int debug_exploration = 0, debug_trim = 0, debug_find_roots = 0;
#endif

static void
debug_dump(const VexRip &vr)
{
	printf("%s", vr.name());
}

static void
debug_dump(const CFGNode *n)
{
	printCFG(n, stdout);
}

template <typename k, typename v> static void
debug_dump(const std::map<k, v> &what, const char *prefix)
{
	for (auto it = what.begin(); it != what.end(); it++) {
		printf("%s", prefix);
		debug_dump(it->first);
		printf(" -> ");
		debug_dump(it->second);
		printf("\n");
	}
}

template <typename t> static void
debug_dump(const HashedSet<t> &what, const char *prefix)
{
	for (auto it = what.begin(); !it.finished(); it.advance()) {
		printf("%s", prefix);
		debug_dump(*it);
		printf("\n");
	}
}

/* We always backtrack to at least maxPathLength1, and can backtrack
   up to maxPathLength2 provided that doing so doesn't cross any
   function heads. */
static bool
exploreForStartingRip(CfgLabelAllocator &allocLabel,
		      Oracle *oracle,
		      const VexRip &startingVexRip,
		      std::map<VexRip, CFGNode *> &out,
		      HashedSet<HashedPtr<const CFGNode> > &targetNodes,
		      std::set<VexRip> &newStartingRips,
		      CfgSuccMap<VexRip, VexRip> &succMap,
		      unsigned maxPathLength)
{
	std::vector<VexRip> pendingAtCurrentDepth;
	std::vector<VexRip> neededAtNextDepth;
	std::map<VexRip, std::set<VexRip> > neededRelocs;
	unsigned depth;
	bool firstInstr = true;

	if (debug_exploration)
		printf("Exploring from %s...\n", startingVexRip.name());
	pendingAtCurrentDepth.push_back(startingVexRip);
	depth = 0;
	while (depth < maxPathLength) {
		if (debug_exploration)
			printf("\tAt depth %d/%d\n", depth, maxPathLength);
		while (!pendingAtCurrentDepth.empty()) {
			VexRip vr(pendingAtCurrentDepth.back());
			pendingAtCurrentDepth.pop_back();
			if (out.count(vr))
				continue;
			CFGNode *node = CfgNodeForRip<VexRip>(allocLabel(), oracle, vr, vr, succMap);
			if (firstInstr)
				targetNodes.insert(node);
			firstInstr = false;
			if (!node) {
				if (debug_exploration)
					printf("\t\t%s doesn't exist?\n", vr.name());
				continue;
			}
			if (debug_exploration) {
				printf("\t\t");
				node->prettyPrint(stdout);
			}

			out[vr] = node;
			if (vr.stack.size() <= (unsigned)DynAnalysisRip::DATABASE_RIP_DEPTH &&
			    oracle->isFunctionHead(vr)) {
				/* Tricky case: we need to extend
				   @vr's stack backwards a bit in
				   order to get enough context to
				   complete the operation.  That in
				   practice means starting again with
				   a more complete starting RIP. */
				if (debug_exploration)
					printf("Need to backtrack further up the stack to get predecessors of %s\n",
					       vr.name());
				std::vector<unsigned long> callers;
				oracle->getPossibleStackTruncations(vr, callers);
				if (callers.size() != 0) {
					for (auto it = callers.begin();
					     it != callers.end();
					     it++) {
						VexRip newStart(startingVexRip);
						newStart.prepend(*it);
						newStartingRips.insert(newStart);
						if (debug_exploration)
							printf("\tCaller %lx -> new starting RIP %s\n",
							       *it, newStart.name());
					}
					return true;
				} else {
					/* Can't find any more
					   predecessors, just have to
					   make do with what we've
					   got. */
					if (debug_exploration)
						printf("Couldn't find any callers for %s?\n",
						       vr.name());
				}
			}
			oracle->findPredecessors(vr, true,
						 neededAtNextDepth);
		}
		depth++;
		pendingAtCurrentDepth = neededAtNextDepth;
		neededAtNextDepth.clear();
	}

	if (debug_exploration)
		printf("Done exploration from %s\n", startingVexRip.name());

	return false;
}

static void
initialExploration(CfgLabelAllocator &allocLabel,
		   Oracle *oracle,
		   const VexRip &targetRip,
		   std::map<VexRip, CFGNode *> &out,
		   HashedSet<HashedPtr<const CFGNode> > &targetInstrs,
		   unsigned maxPathLength)
{
	std::set<VexRip> startingRips;
	startingRips.insert(targetRip);
	CfgSuccMap<VexRip, VexRip> succMap;
	while (1) {
		out.clear();
		targetInstrs.clear();
		allocLabel.reset();
		succMap.clear();
		std::set<VexRip> newStartingRips;
		bool failed = false;
		if (debug_exploration)
			printf("initialExploration with %zd RIPs available\n",
			       startingRips.size());
		for (auto it = startingRips.begin(); it != startingRips.end(); it++) {
			if (exploreForStartingRip(allocLabel,
						  oracle,
						  *it,
						  out,
						  targetInstrs,
						  newStartingRips,
						  succMap,
						  maxPathLength)) {
				failed = true;
			} else {
				newStartingRips.insert(*it);
			}
		}
		if (!failed) {
			resolveReferences(succMap, out);
			return;
		}
		startingRips = newStartingRips;
	}
}

static bool
selectEdgeForCycleBreak(const CFGNode *start,
			std::map<const CFGNode *, std::set<std::pair<CFGNode *, int> > > &predecessorMap,
			HashedSet<HashedPtr<const CFGNode> > &cycle_free,
			const CFGNode **edge_start,
			int *edge_idx,
			int *discoveryDepth,
			HashedSet<HashedPtr<const CFGNode> > &clean,
			HashedSet<HashedPtr<const CFGNode> > &path)
{
	if (clean.contains(start) || cycle_free.contains(start))
		return false;
	assert(!path.contains(start));
	clean.insert(start);
	path.insert(start);
	std::set<std::pair<CFGNode *, int> > &predecessors(predecessorMap[start]);
	for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
		CFGNode *pred = it->first;
		assert(it->second < (int)pred->successors.size());
		CFGNode::successor_t *predEdge = &pred->successors[it->second];
		assert(predEdge->instr == start);
		if (path.contains(pred)) {
			*edge_start = pred;
			*edge_idx = it->second;
			*discoveryDepth = path.size();
			return true;
		}
		if (selectEdgeForCycleBreak(pred,
					    predecessorMap,
					    cycle_free,
					    edge_start,
					    edge_idx,
					    discoveryDepth,
					    clean,
					    path))
			return true;
	}
	path.erase(start);
	cycle_free.insert(start);
	return false;
}
static bool
selectEdgeForCycleBreak(const CFGNode *start,
			std::map<const CFGNode *, std::set<std::pair<CFGNode *, int> > > &predecessors,
			HashedSet<HashedPtr<const CFGNode> > &cycle_free,
			const CFGNode **cycle_edge_start,
			int *cycle_edge_end,
			int *discoveryDepth)
{
	HashedSet<HashedPtr<const CFGNode> > clean;
	HashedSet<HashedPtr<const CFGNode> > path;
	return selectEdgeForCycleBreak(start, predecessors, cycle_free,
				       cycle_edge_start, cycle_edge_end,
				       discoveryDepth,
				       clean, path);
}

static void
unrollAndCycleBreak(CfgLabelAllocator &allocLabel,
		    HashedSet<HashedPtr<CFGNode> > &instrs,
		    const HashedSet<HashedPtr<const CFGNode> > &targetInstrs,
		    HashedSet<HashedPtr<CFGNode> > &roots,
		    int maxPathLength)
{
	std::map<const CFGNode *, std::set<std::pair<CFGNode *, int> > > predecessorMap;

	for (auto it = instrs.begin(); !it.finished(); it.advance()) {
		CFGNode *n = *it;
		for (unsigned x = 0; x < n->successors.size(); x++)
			if (n->successors[x].instr)
				predecessorMap[n->successors[x].instr].insert(
					std::pair<CFGNode *, int>(n, x));
	}

	for (auto it = targetInstrs.begin(); !it.finished(); it.advance()) {
		const CFGNode *targetInstr = *it;
		HashedSet<HashedPtr<const CFGNode> > cycle_free;

		while (1) {
			CFGNode *cycle_edge_start;
			int cycle_edge_idx;
			int discoveryDepth;
			if (!selectEdgeForCycleBreak(targetInstr,
						     predecessorMap,
						     cycle_free,
						     (const CFGNode **)&cycle_edge_start,
						     &cycle_edge_idx,
						     &discoveryDepth)) {
				/* No cycles left in the graph.  Yay. */
				break;
			}
			assert(cycle_edge_idx < (int)cycle_edge_start->successors.size());
			CFGNode *cycle_edge_end = cycle_edge_start->successors[cycle_edge_idx].instr;
			assert(cycle_edge_end);
		
			/* Remove the dead edge before we duplicate incoming
			 * edges.  This only makes a difference for
			 * self-edges.  In the case of self-edges, it's to not
			 * duplicate the edge we just killed into the new
			 * node, because that leads to an exponential blow-up
			 * in edges which are just going to get removed later
			 * on anyway. */
			predecessorMap[cycle_edge_end].erase(std::pair<CFGNode *, int>(cycle_edge_start, cycle_edge_idx));
			cycle_edge_start->successors[cycle_edge_idx].instr = NULL;

			if (discoveryDepth < maxPathLength) {
				/* The edge from cycle_edge_start to
				   cycle_edge_end closes a cycle, and we want
				   to get rid of that cycle.  We do so by
				   duplicating cycle_edge_start along with all
				   of its *incoming* edges, plus the one edge
				   to cycle_edge_end.  We then remove
				   cycle_edge_end from the old node's outgoing
				   list.  The effect is that the old node is
				   no longer on the cycle.  The new node is
				   part of a cycle, but it's a cycle further
				   from the start node, and so if we iterate
				   long enough the cycle will eventually be
				   broken by maxPathLength. */
				CFGNode *new_node;
				/* Create new node */
				new_node = new CFGNode(cycle_edge_start, allocLabel());
			
				/* Maintain only edge to cycle_edge_end */
				new_node->successors.clear();
				CFGNode::successor_t succ = cycle_edge_start->successors[cycle_edge_idx];
				succ.instr = cycle_edge_end;
				new_node->successors.push_back(succ);
				predecessorMap[cycle_edge_end].insert(std::pair<CFGNode *, int>(new_node, 0));
			
				/* Clone all the incoming edges */
				std::set<std::pair<CFGNode *, int> > &oldNodePredecessors(predecessorMap[cycle_edge_start]);
				std::set<std::pair<CFGNode *, int> > &newNodePredecessors(predecessorMap[new_node]);
				for (auto it = oldNodePredecessors.begin();
				     it != oldNodePredecessors.end();
				     it++) {
					CFGNode *pred = it->first;
					pred->successors.push_back(
						CFGNode::successor_t::unroll(new_node));
					newNodePredecessors.insert(
						std::pair<CFGNode *, int>(
							pred,
							pred->successors.size() - 1));
				}
		
				instrs.insert(new_node);
			} else {
				roots.insert(cycle_edge_end);
			}
		}
	}
}

/* Find any nodes in @nodes which:

   a) Aren't reachable from a function head in @nodes, and
   b) Aren't followed by a true_target_instr within @maxPathLength
      nodes.

   And then go and remove them.  The idea is that the exploration has
   gone past @maxPathLength, and we want to keep any nodes past that
   depth which look like they might make the analysis easier and
   discard anything which looks like it'll make it more difficult.
*/
static void
trimExcessNodes(Oracle *oracle,
		HashedSet<HashedPtr<CFGNode> > &nodes,
		const HashedSet<HashedPtr<const CFGNode> > &targetInstrs,
		int maxPathLength)
{
	/* This is not an efficient algorithm for doing this.
	   Nevermind; this isn't exactly a hotspot. */
	std::map<CFGNode *, int> distanceToTargetInstr;
	for (auto it = nodes.begin(); !it.finished(); it.advance()) {
		CFGNode *n = *it;
		int v;
		if (targetInstrs.contains(n))
			v = 0;
		else
			v = nodes.size();
		distanceToTargetInstr[n] = v;
	}
	bool progress = true;
	while (progress) {
		progress = false;
		for (auto it = nodes.begin(); !it.finished(); it.advance()) {
			CFGNode *n = *it;
			int distance;
			distance = distanceToTargetInstr[n];
			for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++)
				if ( it2->instr &&
				     distance > distanceToTargetInstr[it2->instr] + 1)
					distance = distanceToTargetInstr[it2->instr] + 1;
			if (!progress && distanceToTargetInstr[n] != distance)
				progress = true;
			distanceToTargetInstr[n] = distance;
		}
	}

	HashedSet<HashedPtr<CFGNode> > reachableFromFunctionHead;
	HashedSet<HashedPtr<CFGNode> > pending;
	for (auto it = nodes.begin(); !it.finished(); it.advance()) {
		CFGNode *n = *it;
		if (oracle->isFunctionHead(n->rip))
			pending.insert(n);
	}
	while (!pending.empty()) {
		HashedSet<HashedPtr<CFGNode> > newPending;
		for (auto it = pending.begin(); !it.finished(); it.advance()) {
			CFGNode *n = *it;
			if (reachableFromFunctionHead._insert(n)) {
				for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++)
					if (it2->instr)
						newPending.insert(it2->instr);
			}
		}
		pending = newPending;
	}

	HashedSet<HashedPtr<CFGNode> > nodesToKill;
	for (auto it = nodes.begin(); !it.finished(); it.advance()) {
		/* We keep the node if either it's reachable from the
		 * function head or a root... */
		if (reachableFromFunctionHead.contains(*it)) {
			if (debug_trim) {
				printf("Preserve due to reachability from head %p ", &**it);
				(*it)->prettyPrint(stdout);
			}
			continue;
		}
		/* ...or it's within the threshold of a target
		 * instruction. */
		auto it2 = distanceToTargetInstr.find(*it);
		if (it2 != distanceToTargetInstr.end() &&
		    it2->second < maxPathLength) {
			if (debug_trim) {
				printf("Preserve at distance %d(< %d) %p ",
				       it2->second, maxPathLength, &**it);
				(*it)->prettyPrint(stdout);
			}
			continue;
		}
		/* Otherwise, we have to kill it. */
		if (debug_trim) {
			printf("Kill node %p ", &**it);
			(*it)->prettyPrint(stdout);
		}
		nodesToKill.insert(*it);
	}

	if (nodesToKill.empty())
		return;

	/* Now go back and remove all the nodes in nodesToKill. */
	for (auto it = nodes.begin(); !it.finished(); ) {
		CFGNode *n = *it;
		if (nodesToKill.contains(n)) {
			it.erase();
		} else {
			for (auto it2 = n->successors.begin();
			     it2 != n->successors.end();
			     it2++) {
				if (it2->instr && nodesToKill.contains(it2->instr))
					it2->instr = NULL;
			}
			it.advance();
		}
	}
}

static int
distanceToTrueInstr(const CFGNode *n, const HashedSet<HashedPtr<const CFGNode> > &targetInstr, int dflt)
{
	HashedSet<HashedPtr<const CFGNode> > successors;
	std::queue<const CFGNode *> pendingAtCurrentDepth;
	int depth = 0;
	pendingAtCurrentDepth.push(n);
	while (!pendingAtCurrentDepth.empty()) {
		std::queue<const CFGNode *> pendingAtNextDepth;
		while (!pendingAtCurrentDepth.empty()) {
			const CFGNode *n = pendingAtCurrentDepth.front();
			pendingAtCurrentDepth.pop();
			if (targetInstr.contains(n))
				return depth;
			if (!successors._insert(n))
				continue;
			for (auto it = n->successors.begin(); it != n->successors.end(); it++)
				if (it->instr)
					pendingAtNextDepth.push(it->instr);
		}
		pendingAtCurrentDepth = pendingAtNextDepth;
		depth++;
	}
	/* Can't reach any true instructions -> return default. */
	return dflt;
}

static void
removeReachable(HashedSet<HashedPtr<CFGNode> > &out, const CFGNode *n)
{
	std::vector<const CFGNode *> pending;
	pending.push_back(n);
	while (!pending.empty()) {
		const CFGNode *n = pending.back();
		pending.pop_back();
		if (!out.erase(const_cast<CFGNode *>(n))) {
			/* Already not-present */
			continue;
		}
		for (auto it = n->successors.begin(); it != n->successors.end(); it++)
			if (it->instr)
				pending.push_back(it->instr);
	}
}

static void
removeReachable(HashedSet<HashedPtr<CFGNode> > &out, const HashedSet<HashedPtr<CFGNode> > &roots)
{
	for (auto it = roots.begin(); !it.finished(); it.advance())
		removeReachable(out, *it);
}

/* Populate @roots with nodes such that, for every node in @m, there
   is a path from something in @roots which reaches @m.  We try to
   make @roots as small as possible, but ony guarantee to produce a
   minimal result if @m is acyclic. */
static void
findRoots(const HashedSet<HashedPtr<CFGNode> > &allNodes,
	  const HashedSet<HashedPtr<const CFGNode> > &targetInstrs,
	  HashedSet<HashedPtr<CFGNode> > &roots,
	  bool allow_cycles)
{
	HashedSet<HashedPtr<CFGNode> > currentlyUnrooted(allNodes);

	if (debug_find_roots) {
		printf("findRoots():\n");
		for (auto it = allNodes.begin(); !it.finished(); it.advance()) {
			printf("\t%p -> ", &**it);
			for (auto it2 = (*it)->successors.begin();
			     it2 != (*it)->successors.end();
			     it2++)
				printf("%p, ", it2->instr);
			printf("\n");
		}
	}

	/* First rule: if something in @currentlyUnrooted cannot be
	   reached from any node in @currentlyUnrooted then that node
	   should definitely be a root. */
	HashedSet<HashedPtr<CFGNode> > newRoots(currentlyUnrooted);
	for (auto it = allNodes.begin(); !it.finished(); it.advance()) {
		CFGNode *n = *it;
		for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++)
			if (it2->instr) {
				if (debug_find_roots)
					printf("%p is not a root because of %p\n",
					       it2->instr, n);
				newRoots.erase(it2->instr);
			}
	}

	if (debug_find_roots) {
		printf("Basic root set: ");
		for (auto it = newRoots.begin(); !it.finished(); it.advance())
			printf("%p, ", &**it);
		printf("\n");
	}

	removeReachable(currentlyUnrooted, newRoots);
	roots.extend(newRoots);

	if (!allow_cycles && !currentlyUnrooted.empty()) {
		printf("Unexpected cycle in CFG!\n");
		abort();
	}
	while (!currentlyUnrooted.empty()) {
		/* Nasty case: everything in @currentlyUnrooted is
		   part of a cycle in @currentlyUnrooted.  Try to grab
		   something which is as far as possible away from the
		   first true-flavoured instruction.  That tends to
		   give us the most useful information. */
		CFGNode *best_node;
		int best_distance;
		best_node = NULL;
		best_distance = -1;
		for (auto it = currentlyUnrooted.begin(); !it.finished(); it.advance()) {
			int n = distanceToTrueInstr(*it, targetInstrs, currentlyUnrooted.size());
			if (n > best_distance) {
				best_distance = n;
				best_node = *it;
			}
		}

		if (debug_find_roots)
			printf("Selected cycle-breaking root %p (%d)\n",
			       best_node, best_distance);
		assert(best_node != NULL);
		roots.insert(best_node);
		removeReachable(currentlyUnrooted, best_node);
	}
}

static void
trimUninterestingCFGNodes(std::map<VexRip, CFGNode *> &m,
			  const HashedSet<HashedPtr<const CFGNode> > &roots)
{
	/* First, figure out which nodes are interesting. */
	HashedSet<HashedPtr<const CFGNode> > interesting(roots);

	/* Anything which can reach an interesting node is itself
	 * interesting. */
	bool progress = true;
	while (progress) {
		progress = false;
		for (auto it = m.begin(); it != m.end(); it++) {
			const CFGNode *n = it->second;
			assert(n);
			if (interesting.contains(n))
				continue;
			bool isInteresting = false;
			for (auto it = n->successors.begin(); !isInteresting && it != n->successors.end(); it++)
				if (it->instr && interesting.contains(it->instr))
					isInteresting = true;
			if (isInteresting) {
				interesting.insert(n);
				progress = true;
			}
		}
	}

	/* So now we know which nodes we want to keep.  Go through and
	   remove all the ones which we don't want. */
	for (auto it = m.begin(); it != m.end(); ) {
		CFGNode *n = it->second;
		if (!interesting.contains(n)) {
			m.erase(it++);
			continue;
		}
		for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++)
			if (it2->instr && !interesting.contains(it2->instr))
				it2->instr = NULL;
		it++;
	}
}

static bool
getProbeCFG(CfgLabelAllocator &allocLabel,
	    Oracle *oracle,
	    const VexRip &targetInstr,
	    HashedSet<HashedPtr<CFGNode> > &out,
	    HashedSet<HashedPtr<const CFGNode> > &targetNodes,
	    unsigned maxPathLength)
{
	std::map<VexRip, CFGNode *> ripsToCFGNodes;
	initialExploration(allocLabel, oracle, targetInstr, ripsToCFGNodes, targetNodes, maxPathLength);

	if (debug_exploration) {
		printf("Initial ripsToCFGNodes table:\n");
		debug_dump(ripsToCFGNodes, "\t");
	}

	trimUninterestingCFGNodes(ripsToCFGNodes, targetNodes);

	HashedSet<HashedPtr<CFGNode> > nodes;
	for (auto it = ripsToCFGNodes.begin(); it != ripsToCFGNodes.end(); it++)
		nodes.insert(it->second);

	findRoots(nodes, targetNodes, out, true);
	if (debug_exploration) {
		printf("Roots before loop unrolling:\n");
		debug_dump(out, "\t");
	}

	unrollAndCycleBreak(allocLabel, nodes, targetNodes, out, maxPathLength);

	if (debug_exploration) {
		printf("Before trimming:\n");
		debug_dump(out, "\t");
	}

	trimExcessNodes(oracle, nodes, targetNodes, maxPathLength);

	findRoots(nodes, targetNodes, out, false);
	if (debug_exploration) {
		printf("After trimming:\n");
		debug_dump(out, "\t");
	}

	return true;
}

/* End of namespace */
};

bool
getProbeCFGs(CfgLabelAllocator &allocLabel, Oracle *oracle, const VexRip &vr, HashedSet<HashedPtr<CFGNode> > &out,
	     HashedSet<HashedPtr<const CFGNode> > &targetNodes, int threshold)
{
	bool res;
	stackedCdf::startGetProbeCFGs();
	res = _getProbeCFGs::getProbeCFG(allocLabel, oracle, vr, out, targetNodes, threshold);
	stackedCdf::stopGetProbeCFGs();
	return res;
}

bool
getProbeCFGs(CfgLabelAllocator &allocLabel, Oracle *oracle, const VexRip &vr, HashedSet<HashedPtr<CFGNode> > &out,
	     HashedSet<HashedPtr<const CFGNode> > &targetNodes)
{
	return getProbeCFGs(allocLabel, oracle, vr, out, targetNodes, PROBE_CLUSTER_THRESHOLD);
}

