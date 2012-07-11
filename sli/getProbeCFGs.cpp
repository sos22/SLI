#include <map>

#include "sli.h"
#include "oracle.hpp"
#include "cfgnode.hpp"

#include "cfgnode_tmpl.cpp"

namespace _getProbeCFGs {

#ifdef NDEBUG
#define debug_exploration 0
#define debug_trim 0
#define debug_find_roots 0
#else
static int debug_exploration = 0, debug_trim = 0, debug_find_roots = 0;
#endif

enum cfgflavour_probe_t { cfgp_flavour_true, cfgp_flavour_ordinary };

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
debug_dump(const std::set<t> &what, const char *prefix)
{
	for (auto it = what.begin(); it != what.end(); it++) {
		printf("%s", prefix);
		debug_dump(*it);
		printf("\n");
	}
}

/* We always backtrack to at least maxPathLength1, and can backtrack
   up to maxPathLength2 provided that doing so doesn't cross any
   function heads. */
static bool
exploreForStartingRip(Oracle *oracle,
		      const VexRip &startingVexRip,
		      std::map<VexRip, CFGNode *> &out,
		      std::map<const CFGNode *, cfgflavour_probe_t> &cfgFlavours,
		      std::set<VexRip> &newStartingRips,
		      unsigned maxPathLength1,
		      unsigned maxPathLength2)
{
	std::vector<VexRip> pendingAtCurrentDepth;
	std::vector<VexRip> neededAtNextDepth;
	std::map<VexRip, std::set<VexRip> > neededRelocs;
	unsigned depth;

	if (debug_exploration)
		printf("Exploring from %s...\n", startingVexRip.name());
	cfgflavour_probe_t flavour = cfgp_flavour_true;
	pendingAtCurrentDepth.push_back(startingVexRip);
	depth = 0;
	while (depth < maxPathLength2) {
		if (debug_exploration)
			printf("\tAt depth %d/(%d,%d)\n", depth, maxPathLength1, maxPathLength2);
		while (!pendingAtCurrentDepth.empty()) {
			VexRip vr(pendingAtCurrentDepth.back());
			pendingAtCurrentDepth.pop_back();
			if (out.count(vr))
				continue;
			CFGNode *node = CFGNode::forRip(oracle, vr);
			cfgFlavours[node] = flavour;
			flavour = cfgp_flavour_ordinary;
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
			bool isLibraryCall = node->libraryFunction != LibraryFunctionTemplate::none;
			if (depth < maxPathLength1) {
				oracle->findPredecessors(vr, true,
							 isLibraryCall,
							 neededAtNextDepth);
			} else {
				std::vector<VexRip> pred;
				oracle->findPredecessors(vr, true,
							 isLibraryCall,
							 pred);
				/* If we're past the intended max
				   depth then we only consider
				   unambiguous non-call
				   predecessors. */
				if (pred.size() == 1 &&
				    pred[0].stack.size() == vr.stack.size())
					neededAtNextDepth.push_back(pred[0]);
			}
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
initialExploration(Oracle *oracle, const DynAnalysisRip &targetRip,
		   std::map<VexRip, CFGNode *> &out,
		   std::map<const CFGNode *, cfgflavour_probe_t> &cfgFlavours,
		   unsigned maxPathLength1, unsigned maxPathLength2)
{
	std::set<VexRip> startingRips;
	startingRips.insert(targetRip.toVexRip());
	while (1) {
		out.clear();
		cfgFlavours.clear();
		std::set<VexRip> newStartingRips;
		bool failed = false;
		if (debug_exploration)
			printf("initialExploration with %zd RIPs available\n",
			       startingRips.size());
		for (auto it = startingRips.begin(); it != startingRips.end(); it++) {
			if (exploreForStartingRip(oracle, *it, out,
						  cfgFlavours,
						  newStartingRips,
						  maxPathLength1,
						  maxPathLength2)) {
				failed = true;
			} else {
				newStartingRips.insert(*it);
			}
		}
		if (!failed)
			return;
		startingRips = newStartingRips;
	}
}

static bool
selectEdgeForCycleBreak(CFGNode *start,
			std::map<CFGNode *, std::set<CFGNode *> > &predecessorMap,
			std::set<CFGNode *> &cycle_free,
			CFGNode **edge_start, CFGNode **edge_end,
			int *discoveryDepth,
			std::set<CFGNode *> &clean, std::set<CFGNode *> &path)
{
	if (clean.count(start) || cycle_free.count(start))
		return false;
	assert(!path.count(start));
	clean.insert(start);
	path.insert(start);
	std::set<CFGNode *> &predecessors(predecessorMap[start]);
	for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
		if (path.count(*it)) {
			*edge_start = *it;
			*edge_end = start;
			*discoveryDepth = path.size();
			return true;
		}
		if (selectEdgeForCycleBreak(*it, predecessorMap, cycle_free,
					    edge_start, edge_end, discoveryDepth,
					    clean, path))
			return true;
	}
	path.erase(start);
	cycle_free.insert(start);
	return false;
}
static bool
selectEdgeForCycleBreak(CFGNode *start,
			std::map<CFGNode *, std::set<CFGNode *> > &predecessors,
			std::set<CFGNode *> &cycle_free,
			CFGNode **cycle_edge_start,
			CFGNode **cycle_edge_end,
			int *discoveryDepth)
{
	std::set<CFGNode *> clean;
	std::set<CFGNode *> path;
	return selectEdgeForCycleBreak(start, predecessors, cycle_free,
				       cycle_edge_start, cycle_edge_end,
				       discoveryDepth,
				       clean, path);
}

static void
unrollAndCycleBreak(std::set<CFGNode *> &instrs,
		    std::map<const CFGNode *, cfgflavour_probe_t> &cfgFlavours,
		    int maxPathLength)
{
	std::map<CFGNode *, std::set<CFGNode *> > predecessorMap;
	std::set<CFGNode *> startNodes;

	for (auto it = instrs.begin(); it != instrs.end(); it++) {
		CFGNode *n = *it;
		if (n->fallThrough.second)
			predecessorMap[n->fallThrough.second].insert(n);
		for (auto it = n->branches.begin();
		     it != n->branches.end();
		     it++)
			if (it->second)
				predecessorMap[it->second].insert(n);
		auto it_fl = cfgFlavours.find(n);
		assert(it_fl != cfgFlavours.end());
		if (it_fl->second == cfgp_flavour_true)
			startNodes.insert(n);
	}
	assert(!startNodes.empty());

	for (auto it = startNodes.begin(); it != startNodes.end(); it++) {
		CFGNode *startNode = *it;
		std::set<CFGNode *> cycle_free;
		while (1) {
			CFGNode *cycle_edge_start, *cycle_edge_end;
			int discoveryDepth;
			if (!selectEdgeForCycleBreak(startNode,
						     predecessorMap,
						     cycle_free,
						     &cycle_edge_start,
						     &cycle_edge_end,
						     &discoveryDepth)) {
				/* No cycles left in the graph.  Yay. */
				break;
			}
			if (cycle_edge_start->my_rip == cycle_edge_end->my_rip)
				dbg_break("break self-edge");

			/* Remove the dead edge before we duplicate
			 * incoming edges.  This only makes a
			 * difference for self-edges.  In the case of
			 * self-edges, it's to not duplicate the edge
			 * we just killed into the new node, because
			 * that leads to an exponential blow-up in
			 * edges which are just going to get removed
			 * later on anyway. */
			if (cycle_edge_start->fallThrough.second == cycle_edge_end) {
				cycle_edge_start->fallThrough.second = NULL;
			} else {
				for (auto it = cycle_edge_start->branches.begin();
				     it != cycle_edge_start->branches.end();
				     it++) {
					if (it->second == cycle_edge_end) {
						it->second = NULL;
						break;
					}
				}
			}
			predecessorMap[cycle_edge_end].erase(cycle_edge_start);

			if (discoveryDepth < maxPathLength) {
				/* The edge from cycle_edge_start to
				   cycle_edge_end closes a cycle, and
				   we want to get rid of that cycle.
				   We do so by duplicating
				   cycle_edge_start along with all of
				   its *incoming* edges, plus the one
				   edge to cycle_edge_end.  We then
				   remove cycle_edge_end from the old
				   node's outgoing list.  The effect
				   is that the old node is no longer
				   on the cycle.  The new node is part
				   of a cycle, but it's a cycle
				   further from the start node, and so
				   if we iterate long enough the cycle
				   will eventually be broken by
				   maxPathLength. */
				CFGNode *new_node;
				/* Create new node */
				new_node = new CFGNode(cycle_edge_start->my_rip,
						       cycle_edge_start->libraryFunction);
				cfgFlavours[new_node] = cfgp_flavour_ordinary;
				/* Maintain the edge to cycle_edge_end */
				new_node->fallThrough.first = cycle_edge_end->my_rip;
				new_node->fallThrough.second = cycle_edge_end;
				predecessorMap[cycle_edge_end].insert(new_node);

				/* Clone all the incoming edges */
				std::set<CFGNode *> &oldNodePredecessors(predecessorMap[cycle_edge_start]);
				std::set<CFGNode *> &newNodePredecessors(predecessorMap[new_node]);
				for (auto it = oldNodePredecessors.begin();
				     it != oldNodePredecessors.end();
				     it++) {
					CFGNode *pred = *it;
					pred->branches.push_back(
						CFGNode::successor_t(new_node->my_rip, new_node));
					newNodePredecessors.insert(pred);
				}

				instrs.insert(new_node);
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
		std::set<CFGNode *> &nodes,
		const std::map<const CFGNode *, cfgflavour_probe_t> &cfgFlavours,
		int maxPathLength)
{
	/* This is not an efficient algorithm for doing this.
	   Nevermind; this isn't exactly a hotspot. */
	std::map<CFGNode *, int> distanceToTargetInstr;
	for (auto it = nodes.begin(); it != nodes.end(); it++) {
		CFGNode *n = *it;
		int v;
		auto it_fl = cfgFlavours.find(n);
		assert(it_fl != cfgFlavours.end());
		if (it_fl->second == cfgp_flavour_true)
			v = 0;
		else
			v = nodes.size();
		distanceToTargetInstr[n] = v;
	}
	bool progress = true;
	while (progress) {
		progress = false;
		for (auto it = nodes.begin(); it != nodes.end(); it++) {
			CFGNode *n = *it;
			int distance;
			distance = distanceToTargetInstr[n];
			if (n->fallThrough.second &&
			    distance > distanceToTargetInstr[n->fallThrough.second] + 1)
				distance = distanceToTargetInstr[n->fallThrough.second] + 1;
			for (auto it2 = n->branches.begin(); it2 != n->branches.end(); it2++)
				if ( it2->second &&
				     distance > distanceToTargetInstr[it2->second] + 1)
					distance = distanceToTargetInstr[it2->second] + 1;
			if (!progress && distanceToTargetInstr[n] != distance)
				progress = true;
			distanceToTargetInstr[n] = distance;
		}
	}

	std::set<CFGNode *> reachableFromFunctionHead;
	std::set<CFGNode *> pending;
	for (auto it = nodes.begin(); it != nodes.end(); it++) {
		CFGNode *n = *it;
		if (oracle->isFunctionHead(n->my_rip))
			pending.insert(n);
	}
	while (!pending.empty()) {
		std::set<CFGNode *> newPending;
		for (auto it = pending.begin(); it != pending.end(); it++) {
			CFGNode *n = *it;
			if (reachableFromFunctionHead.insert(n).second) {
				if (n->fallThrough.second)
					newPending.insert(n->fallThrough.second);
				for (auto it2 = n->branches.begin(); it2 != n->branches.end(); it2++)
					if (it2->second)
						newPending.insert(it2->second);
			}
		}
		pending = newPending;
	}

	std::set<CFGNode *> nodesToKill;
	for (auto it = nodes.begin(); it != nodes.end(); it++) {
		/* We keep the node if either it's reachable from the
		 * function head or a root... */
		if (reachableFromFunctionHead.count(*it)) {
			if (debug_trim) {
				printf("Preserve due to reachability from head %p ", *it);
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
				       it2->second, maxPathLength, *it);
				(*it)->prettyPrint(stdout);
			}
			continue;
		}
		/* Otherwise, we have to kill it. */
		if (debug_trim) {
			printf("Kill node %p ", *it);
			(*it)->prettyPrint(stdout);
		}
		nodesToKill.insert(*it);
	}

	if (nodesToKill.empty())
		return;

	/* Now go back and remove all the nodes in nodesToKill. */
	for (auto it = nodes.begin(); it != nodes.end(); ) {
		CFGNode *n = *it;
		if (nodesToKill.count(n)) {
			nodes.erase(it++);
		} else {
			if (n->fallThrough.second && nodesToKill.count(n->fallThrough.second))
				n->fallThrough.second = NULL;
			for (auto it2 = n->branches.begin();
			     it2 != n->branches.end();
			     it2++) {
				if (it2->second && nodesToKill.count(it2->second))
					it2->second = NULL;
			}
			it++;
		}
	}
}

template <typename t> static int
distanceToTrueInstr(const _CFGNode<t> *n, const std::map<const _CFGNode<t> *, cfgflavour_probe_t> &flavours)
{
	std::set<const _CFGNode<t> *> successors;
	std::queue<const _CFGNode<t> *> pendingAtCurrentDepth;
	int depth = 0;
	pendingAtCurrentDepth.push(n);
	while (1) {
		std::queue<const _CFGNode<t> *> pendingAtNextDepth;
		assert(pendingAtNextDepth.empty());
		while (!pendingAtCurrentDepth.empty()) {
			const _CFGNode<t> *n = pendingAtCurrentDepth.front();
			pendingAtCurrentDepth.pop();
			auto it = flavours.find(n);
			assert(it != flavours.end());
			if (it->second == cfgp_flavour_true)
				return depth;
			if (!successors.insert(n).second)
				continue;
			for (auto it = n->branches.begin(); it != n->branches.end(); it++)
				if (it->second)
					pendingAtNextDepth.push(it->second);
			if (n->fallThrough.second)
				pendingAtNextDepth.push(n->fallThrough.second);
		}
		pendingAtCurrentDepth = pendingAtNextDepth;
		depth++;
	}
	/* Can't reach any true instructions -> shouldn't happen. */
	abort();
}

template <typename t> static void
removeReachable(std::set<_CFGNode<t> *> &out, const _CFGNode<t> *n)
{
	std::vector<const _CFGNode<t> *> pending;
	pending.push_back(n);
	while (!pending.empty()) {
		const _CFGNode<t> *n = pending.back();
		pending.pop_back();
		if (TIMEOUT)
			return;
		if (!out.erase(const_cast<CFGNode *>(n))) {
			/* Already not-present */
			continue;
		}
		if (n->fallThrough.second)
			pending.push_back(n->fallThrough.second);
		for (auto it = n->branches.begin(); it != n->branches.end(); it++)
			if (it->second)
				pending.push_back(it->second);
	}
}

template <typename t> static void
removeReachable(std::set<_CFGNode<t> *> &out, const std::set<_CFGNode<t> *> &roots)
{
	for (auto it = roots.begin(); it != roots.end(); it++)
		removeReachable(out, *it);
}

template <typename t> static void
operator|=(std::set<t> &a, const std::set<t> &b)
{
	for (auto it = b.begin(); it != b.end(); it++)
		a.insert(*it);
}

/* Populate @roots with nodes such that, for every node in @m, there
   is a path from something in @roots which reaches @m.  We try to
   make @roots as small as possible, but ony guarantee to produce a
   minimal result if @m is acyclic. */
template <typename t> static void
findRoots(const std::set<_CFGNode<t> *> &allNodes,
	  const std::map<const _CFGNode<t> *, cfgflavour_probe_t> &cfgFlavours,
	  std::set<_CFGNode<t> *> &roots)
{
	std::set<_CFGNode<t> *> currentlyUnrooted(allNodes);

	if (debug_find_roots) {
		printf("findRoots():\n");
		for (auto it = allNodes.begin(); it != allNodes.end(); it++) {
			printf("\t%p -> ", *it);
			if ((*it)->fallThrough.second)
				printf("%p, ", (*it)->fallThrough.second);
			for (auto it2 = (*it)->branches.begin();
			     it2 != (*it)->branches.end();
			     it2++)
				printf("%p, ", it2->second);
			printf("\n");
		}
	}

	/* First rule: if something in @currentlyUnrooted cannot be
	   reached from any node in @currentlyUnrooted then that node
	   should definitely be a root. */
	std::set<_CFGNode<t> *> newRoots = currentlyUnrooted;
	for (auto it = allNodes.begin();
	     it != allNodes.end();
	     it++) {
		_CFGNode<t> *n = *it;
		if (n->fallThrough.second) {
			newRoots.erase(n->fallThrough.second);
			if (debug_find_roots)
				printf("%p is not a root because of %p\n", n->fallThrough.second,
				       n);
		}
		for (auto it2 = n->branches.begin(); it2 != n->branches.end(); it2++)
			if (it2->second) {
				if (debug_find_roots)
					printf("%p is not a root because of %p\n",
					       it2->second, n);
				newRoots.erase(it2->second);
			}
	}

	if (debug_find_roots) {
		printf("Basic root set: ");
		for (auto it = newRoots.begin(); it != newRoots.end(); it++)
			printf("%p, ", *it);
		printf("\n");
	}

	removeReachable(currentlyUnrooted, newRoots);
	roots |= newRoots;
	while (!TIMEOUT && !currentlyUnrooted.empty()) {
		/* Nasty case: everything in @currentlyUnrooted is
		   part of a cycle in @currentlyUnrooted.  Try to grab
		   something which is as far as possible away from the
		   first true-flavoured instruction.  That tends to
		   give us the most useful information. */
		_CFGNode<t> *best_node;
		int best_distance;
		best_node = NULL;
		best_distance = -1;
		for (auto it = currentlyUnrooted.begin(); it != currentlyUnrooted.end(); it++) {
			int n = distanceToTrueInstr(*it, cfgFlavours);
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

static bool
getProbeCFG(Oracle *oracle, const DynAnalysisRip &targetInstr,
	    std::set<CFGNode *> &out, unsigned maxPathLength1,
	    unsigned maxPathLength2)
{
	/* Step one: build a CFG backwards from @targetInstr until the
	   shortest path from any root to @vr is at least
	   @maxPathLength */
	VexRip dominator;

	std::map<VexRip, CFGNode *> ripsToCFGNodes;
	std::map<const CFGNode *, cfgflavour_probe_t> cfgFlavours;
	initialExploration(oracle, targetInstr, ripsToCFGNodes, cfgFlavours, maxPathLength1, maxPathLength2);

	if (debug_exploration) {
		printf("Initial ripsToCFGNodes table:\n");
		debug_dump(ripsToCFGNodes, "\t");
	}

	resolveReferences(ripsToCFGNodes);
	trimUninterestingCFGNodes(ripsToCFGNodes, targetInstr);

	std::set<CFGNode *> nodes;
	for (auto it = ripsToCFGNodes.begin(); it != ripsToCFGNodes.end(); it++)
		nodes.insert(it->second);

	if (debug_exploration) {
		std::set<CFGNode *> roots;
		findRoots(nodes, cfgFlavours, roots);
		printf("Roots before loop unrolling:\n");
		debug_dump(roots, "\t");
	}

	unrollAndCycleBreak(nodes, cfgFlavours, maxPathLength2);

	if (debug_exploration) {
		std::set<CFGNode *> initialRoots;
		findRoots(nodes, cfgFlavours, initialRoots);
		printf("Before trimming:\n");
		debug_dump(initialRoots, "\t");
	}

	trimExcessNodes(oracle, nodes, cfgFlavours, maxPathLength1);

	findRoots(nodes, cfgFlavours, out);
	if (debug_exploration) {
		printf("After trimming:\n");
		debug_dump(out, "\t");
	}

	return true;
}

/* End of namespace */
};

bool
getProbeCFGs(Oracle *oracle, const DynAnalysisRip &vr, std::set<CFGNode *> &out)
{
	return _getProbeCFGs::getProbeCFG(oracle, vr, out, PROBE_CLUSTER_THRESHOLD1, PROBE_CLUSTER_THRESHOLD2);
}
