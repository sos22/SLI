#include <map>

#include "sli.h"
#include "oracle.hpp"
#include "cfgnode.hpp"

#include "cfgnode_tmpl.cpp"

namespace _getProbeCFGs {

#ifdef NDEBUG
#define debug_exploration 0
#define debug_trim 0
#else
static int debug_exploration = 0, debug_trim = 0;
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
	CFGNode::flavour_t flavour = CFGNode::true_target_instr;
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
			CFGNode *node = CFGNode::forRip(oracle, vr, flavour);
			flavour = CFGNode::ordinary_instr;
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
		   unsigned maxPathLength1, unsigned maxPathLength2)
{
	std::set<VexRip> startingRips;
	startingRips.insert(targetRip.toVexRip());
	while (1) {
		out.clear();
		std::set<VexRip> newStartingRips;
		bool failed = false;
		if (debug_exploration)
			printf("initialExploration with %zd RIPs available\n",
			       startingRips.size());
		for (auto it = startingRips.begin(); it != startingRips.end(); it++) {
			if (exploreForStartingRip(oracle, *it, out,
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
unrollAndCycleBreak(std::set<CFGNode *> &instrs, int maxPathLength)
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
		if (n->flavour == CFGNode::true_target_instr)
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
						       CFGNode::ordinary_instr,
						       cycle_edge_start->libraryFunction);
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
		int maxPathLength)
{
	/* This is not an efficient algorithm for doing this.
	   Nevermind; this isn't exactly a hotspot. */
	std::map<CFGNode *, int> distanceToTargetInstr;
	for (auto it = nodes.begin(); it != nodes.end(); it++) {
		CFGNode *n = *it;
		int v;
		if (n->flavour == CFGNode::true_target_instr)
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
	initialExploration(oracle, targetInstr, ripsToCFGNodes, maxPathLength1, maxPathLength2);

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
		findRoots(nodes, roots);
		printf("Roots before loop unrolling:\n");
		debug_dump(roots, "\t");
	}

	unrollAndCycleBreak(nodes, maxPathLength2);

	if (debug_exploration) {
		std::set<CFGNode *> initialRoots;
		findRoots(nodes, initialRoots);
		printf("Before trimming:\n");
		debug_dump(initialRoots, "\t");
	}

	trimExcessNodes(oracle, nodes, maxPathLength1);

	findRoots(nodes, out);
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
