#include <map>

#include "sli.h"
#include "oracle.hpp"
#include "cfgnode.hpp"

namespace _getProbeCFGs {

#ifdef NDEBUG
#define debug_exploration 0
#else
static int debug_exploration = 1;
#endif

static void
debug_dump(const VexRip &vr)
{
	printf("%s", vr.name());
}

static void
debug_dump(const CFGNode *n)
{
	printCFG(n, "\t", stdout);
}

static void
debug_dump(int x)
{
	printf("%d", x);
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

					
static bool
exploreForStartingRip(Oracle *oracle,
		      const VexRip &startingVexRip,
		      std::map<VexRip, CFGNode *> &out,
		      std::set<VexRip> &newStartingRips,
		      unsigned maxPathLength)
{
	std::vector<VexRip> pendingAtCurrentDepth;
	std::vector<VexRip> neededAtNextDepth;
	std::map<VexRip, std::set<VexRip> > neededRelocs;

	if (debug_exploration)
		printf("Exploring from %s...\n", startingVexRip.name());
	CFGNode::flavour_t flavour = CFGNode::true_target_instr;
	pendingAtCurrentDepth.push_back(startingVexRip);
	while (maxPathLength != 0) {
		if (debug_exploration)
			printf("\tAt depth %d\n", maxPathLength);
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
				dbg_break("Need to backtrack further up the stack");
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
			oracle->findPredecessors(vr, neededAtNextDepth);
		}
		maxPathLength--;
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
		   unsigned maxPathLength)
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
						  maxPathLength)) {
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
			CFGNode **edge_start, CFGNode **edge_end,
			int *discoveryDepth,
			std::set<CFGNode *> &clean, std::set<CFGNode *> &path)
{
	if (clean.count(start))
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
		if (selectEdgeForCycleBreak(*it, predecessorMap, edge_start, edge_end,
					    discoveryDepth, clean, path))
			return true;
	}
	path.erase(start);
	return false;
}
static bool
selectEdgeForCycleBreak(CFGNode *start,
			std::map<CFGNode *, std::set<CFGNode *> > &predecessors,
			CFGNode **cycle_edge_start,
			CFGNode **cycle_edge_end,
			int *discoveryDepth)
{
	std::set<CFGNode *> clean;
	std::set<CFGNode *> path;
	return selectEdgeForCycleBreak(start, predecessors,
				       cycle_edge_start, cycle_edge_end,
				       discoveryDepth,
				       clean, path);
}

static void
unrollAndCycleBreak(std::set<CFGNode *> &instrs, int maxPathLength)
{
	std::map<CFGNode *, std::set<CFGNode *> > predecessorMap;
	CFGNode *startNode;

	startNode = NULL;
	for (auto it = instrs.begin(); it != instrs.end(); it++) {
		CFGNode *n = *it;
		if (n->fallThrough.second)
			predecessorMap[n->fallThrough.second].insert(n);
		for (auto it = n->branches.begin();
		     it != n->branches.end();
		     it++)
			if (it->second)
				predecessorMap[it->second].insert(n);
		if (n->flavour == CFGNode::true_target_instr) {
			assert(startNode == NULL);
			startNode = n;
		}
	}
	assert(startNode);

	while (1) {
		CFGNode *cycle_edge_start, *cycle_edge_end;
		int discoveryDepth;
		if (!selectEdgeForCycleBreak(startNode,
					     predecessorMap,
					     &cycle_edge_start,
					     &cycle_edge_end,
					     &discoveryDepth)) {
			/* No cycles left in the graph.  Yay. */
			break;
		}

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
			new_node = new CFGNode(cycle_edge_start->my_rip, CFGNode::ordinary_instr);
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

		/* Remove the edge we just killed. */
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
	}
		
}
		    
static bool
getProbeCFG(Oracle *oracle, const DynAnalysisRip &targetInstr,
	    std::set<CFGNode *> &out, unsigned maxPathLength)
{
	/* Step one: build a CFG backwards from @targetInstr until the
	   shortest path from any root to @vr is at least
	   @maxPathLength */
	VexRip dominator;

	std::map<VexRip, CFGNode *> ripsToCFGNodes;
	initialExploration(oracle, targetInstr, ripsToCFGNodes, maxPathLength);

	if (debug_exploration) {
		printf("Initial ripsToCFGNodes table:\n");
		debug_dump(ripsToCFGNodes, "\t");
	}

	resolveReferences(ripsToCFGNodes);
	trimUninterestingCFGNodes(ripsToCFGNodes, targetInstr);

	std::set<CFGNode *> nodes;
	for (auto it = ripsToCFGNodes.begin(); it != ripsToCFGNodes.end(); it++)
		nodes.insert(it->second);
	unrollAndCycleBreak(nodes, maxPathLength);

	findRoots(nodes, out);
	if (debug_exploration) {
		printf("Roots:\n");
		debug_dump(out, "\t");
	}

	return true;
}

/* End of namespace */
};

bool
getProbeCFGs(Oracle *oracle, const DynAnalysisRip &vr, std::set<CFGNode *> &out)
{
	return _getProbeCFGs::getProbeCFG(oracle, vr, out, PROBE_CLUSTER_THRESHOLD);
}
