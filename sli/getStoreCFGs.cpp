#include "sli.h"
#include "cfgnode.hpp"
#include "typesdb.hpp"
#include "oracle.hpp"

#include <map>
#include <queue>
#include <set>

namespace _getStoreCFGs {

#define debug_flags(f)				\
	f(debug_initial_exploration)		\
	f(debug_trim_uninteresting)		\
	f(debug_find_roots)			\
	f(debug_remove_redundant_roots)		\
	f(debug_unroll_and_cycle_break)		\
	f(debug_top_level)
#ifdef NDEBUG
#define mk_debug_flag(name)			\
	static const bool name = false;
#else
#define mk_debug_flag(name)			\
	static bool name = false;
#endif
debug_flags(mk_debug_flag)
#undef debug_flags
#undef mk_debug_flag

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

static void
initialExploration(const std::set<DynAnalysisRip> &roots,
		   unsigned maxPathLength,
		   Oracle *oracle,
		   std::map<VexRip, CFGNode *> &results)
{
	/* We want to find all instructions which either roots
	   themselves or part of paths between roots which have a
	   length of @maxPathLength or less. */

	/* Start by enumerating all static paths of length
	   @maxPathLength or less starting from a root. */
	/* First argument is number of instructions left for paths
	   from this instruction. */
	std::queue<std::pair<unsigned, VexRip> > pending;

	std::map<VexRip, std::pair<unsigned, CFGNode *> > doneSoFar;

	std::set<VexRip> vr_roots;
	for (auto it = roots.begin(); it != roots.end(); it++)
		vr_roots.insert(it->toVexRip());

	for (auto it = vr_roots.begin(); it != vr_roots.end(); it++)
		pending.push(std::pair<unsigned, VexRip>(maxPathLength, *it));
top_exploration_iter:
	while (!pending.empty()) {
		if (TIMEOUT)
			return;
		std::pair<unsigned, VexRip> item(pending.front());
		pending.pop();

		assert(item.first > 0);

		auto it = doneSoFar.find(item.second);
		if (it != doneSoFar.end()) {
			if (item.first > it->second.first) {
				/* We've already explored this once,
				   but at a worse depth.  Fix it
				   up. */
				CFGNode *n = it->second.second;
				for (auto it2 = n->branches.begin();
				     it2 != n->branches.end();
				     it2++)
					pending.push(std::pair<unsigned, VexRip>(
							     item.first - 1,
							     it2->first));
				if (n->fallThrough.first.isValid())
					pending.push(std::pair<unsigned, VexRip>(
							     item.first - 1,
							     n->fallThrough.first));
				it->second.first = item.first;

				if (item.first == maxPathLength)
					n->flavour = CFGNode::true_target_instr;
			} else {
				/* We've already explored this at
				   a better depth, so don't need to
				   do anything. */
			}
			continue;
		}

		CFGNode::flavour_t flavour =
			item.first == maxPathLength ? CFGNode::true_target_instr : CFGNode::ordinary_instr;
		CFGNode *work = CFGNode::forRip(oracle, item.second, flavour);
		if (!work) {
			if (debug_initial_exploration)
				printf("Cannot get IRSB for %s\n", item.second.name());
			continue;
		}
		if (item.first != 1) {
			if (work->fallThrough.first.isValid())
				pending.push(std::pair<unsigned, VexRip>(
						     item.first - 1,
						     work->fallThrough.first));
			for (auto it = work->branches.begin();
			     it != work->branches.end();
			     it++)
				pending.push(std::pair<unsigned, VexRip>(
						     item.first - 1,
						     it->first));
		}

		doneSoFar[item.second] = std::pair<unsigned, CFGNode *>(item.first, work);
	}

	/* Now we need to try to stitch together CFGs wherever we can.
	   The problem is that DynamicAnalysisRips truncate the call
	   stack, whereas VexRips don't, so if you want to cluster
	   across function calls things are a bit tricky.

	   e.g. suppose we have something like this:

	   a() {
	   l1: x = 5;
	       b();
           }
	   b() {
	   l2: y = 7;
           }

	   And we want to cluster the two assignments.  The dynamic
	   analysis RIPs will look something like this:

	   1: X Y Z l1
	   2: Y Z a l2

	   When we explore from 1, we'll find l2 as ``X Y Z a l2'',
	   which doesn't match up, so we won't merge the two nodes.
	   The fix is just to add X Y Z a l2 as a new root when we're
	   done with the initial exploration.

	   The obvious alternative way of doing this is just to
	   explore everything using DynamicAnalysisRip rather than
	   VexRip.  That doesn't work, for two reasons.  First,
	   DynamicAnalysisRips don't contain enough information to
	   correctly handle ret instructions.  More subtly, b() might
	   also be called from some other function, c() say, with a
	   completely different call context.  We don't really want to
	   merge a() and c() (and even if we did want to, it's not
	   obvious how we'd do so consistently), which means we really
	   want to duplicate c().  Using full VexRips makes that
	   trivial, but using DynamicAnalysisRips makes it really
	   hard. */
	std::set<VexRip> new_roots;
	for (auto it = doneSoFar.begin(); !TIMEOUT && it != doneSoFar.end(); it++) {
		const VexRip &discoveredRip(it->first);
		if (TIMEOUT)
			return;
		if (vr_roots.count(discoveredRip))
			continue;
		for (auto it2 = vr_roots.begin(); !TIMEOUT && it2 != vr_roots.end(); it2++) {
			const VexRip &rootRip(*it2);

			/* We create a new root for @discoveredRip if
			   there is any @rootRip which is a truncation
			   of it. */
			if (rootRip.isTruncationOf(discoveredRip)) {
				if (debug_initial_exploration) {
					printf("Need a new root, %s, because %s doesn't quite match up\n",
					       discoveredRip.name(),
					       rootRip.name());
				}
				new_roots.insert(discoveredRip);
				/* You might think that we should
				   erase @rootRip from new_roots at
				   this point, because @discoveredRip
				   will subsume it.  Not so.  We might
				   have to iterate multiple times, in
				   which case a future iteration might
				   pick up @rootRip and perform
				   further merging later on. */
			}
		}
	}

	if (!new_roots.empty()) {
		for (auto it = new_roots.begin(); it != new_roots.end(); it++) {
			vr_roots.insert(*it);
			pending.push(std::pair<unsigned, VexRip>(maxPathLength, *it));
		}
		if (debug_initial_exploration)
			printf("Explore %zd additional roots\n",
			       pending.size());
		goto top_exploration_iter;
	}

	for (auto it = doneSoFar.begin(); it != doneSoFar.end(); it++) {
		assert(it->second.second);
		results.insert(std::pair<VexRip, CFGNode *>(it->first, it->second.second));
	}
}

/* Sometimes we end up generating redundant roots i.e. roots for
   machines which are themselves part of other machines.  The reason
   for this is the way we do merges.  If we have something like this:

   a() {
   1:  store1();
   2:  b();
   3:
   }

   b() {
   4:  store2();
   5:
   }

   and store1 and store2 are both interesting then we'll create one
   root at 1 and one at 4.  From 1, we'll explore VexRips
   {1},{2},{4,3},{5,3},{3}.  From 4, we'll explore {4} and {5}.  The
   RIPs don't strictly match up, so there's some sense in which the
   two CFGs are disjoint, but the machine we generate from root 4 will
   be a subset of the machine we generate from root 1, and therefore
   useless.  In particular, if a root is itself a non-equal truncation
   of a VexRip then that root is redundant and most be removed.

   Return true if we do anything, and false otherwise. */
/* Note that we only remove the root; we don't remove the
   now-redundant parts of @m. */
static bool
removeRedundantRoots(const std::map<VexRip, CFGNode *> &m,
		     std::set<CFGNode *> &roots)
{
	bool res = false;
	for (auto it = roots.begin(); !TIMEOUT && it != roots.end(); ) {
		const VexRip &rootRip((*it)->my_rip);
		bool redundant = false;
		for (auto it2 = m.begin(); !redundant && it2 != m.end(); it2++) {
			if (rootRip.isTruncationOf(it2->first))
				redundant = true;
		}
		if (redundant) {
			roots.erase(it++);
			res = true;
		} else {
			it++;
		}
	}
	return res;
}

/* Remove any nodes in @m which aren't reachable from a root in
 * @roots */
static void
removeUnreachableCFGNodes(std::map<VexRip, CFGNode *> &m, const std::set<CFGNode *> &roots)
{
	std::set<CFGNode *> reachable(roots);
	std::vector<CFGNode *> pending;
	pending.reserve(roots.size() * 2);
	for (auto it = roots.begin(); it != roots.end(); it++) {
		CFGNode *n = *it;
		if (n->fallThrough.second) pending.push_back(n->fallThrough.second);
		for (auto it = n->branches.begin(); it != n->branches.end(); it++)
			if (it->second)
				pending.push_back(it->second);
	}
	while (!pending.empty()) {
		if (TIMEOUT)
			return;
		CFGNode *n = pending.back();
		pending.pop_back();
		assert(n);
		if (!reachable.insert(n).second)
			continue;
		if (n->fallThrough.second) pending.push_back(n->fallThrough.second);
		for (auto it = n->branches.begin(); it != n->branches.end(); it++)
			if (it->second)
				pending.push_back(it->second);
	}
	for (auto it = m.begin(); it != m.end(); ) {
		if (reachable.count(it->second))
			it++;
		else
			m.erase(it++);
	}
}

/* The node labelling map tells you how far each node is from each
 * root.  We find all of the nodes of flavour true_target_instr and
 * call them true targets.  Then, for each true target T and node N,
 * we find the length of the shortest path from T to N. */
class nodeLabelling : public std::map<CFGNode *, unsigned> {
public:
	bool merge(nodeLabelling &other);
	void successor(unsigned maxPathLength);
};
class nodeLabellingMap : public std::map<CFGNode *, nodeLabelling> {
public:
	nodeLabellingMap(std::set<CFGNode *> &roots, unsigned maxPathLength);
};

void
debug_dump(const nodeLabelling &nl)
{
	for (auto it = nl.begin(); it != nl.end(); it++)
		printf("%p -> %d, ", it->first, it->second);
}

bool
nodeLabelling::merge(nodeLabelling &other)
{
	bool did_something = false;
	for (auto it = other.begin(); it != other.end(); it++) {
		auto it_did_insert = insert(std::pair<CFGNode *, unsigned>(it->first, it->second));
		auto it2 = it_did_insert.first;
		bool did_insert = it_did_insert.second;

		if (did_insert) {
			/* Easy case: there are currently no paths
			   from this true target to this node, so can
			   just use the path we found. */
			did_something = true;
		} else if (it2->second <= it->second) {
			/* We already have a path which is better than
			   the one we just found -> do nothing. */
		} else {
			/* New path is better than currently best
			   known one -> take new one. */
			it2->second = it->second;
			did_something = true;
		}
	}
	return did_something;
}

void
nodeLabelling::successor(unsigned maxPathLength)
{
	for (auto it = begin(); it != end(); ) {
		it->second++;
		if (it->second > maxPathLength)
			erase(it++);
		else
			it++;
	}
}

nodeLabellingMap::nodeLabellingMap(std::set<CFGNode *> &roots, unsigned maxPathLength)
{
	std::queue<CFGNode *> pending;
	CFGNode *root;

	for (auto it = roots.begin(); it != roots.end(); it++) {
		root = *it;
		pending.push(root);
		while (!pending.empty()) {
			CFGNode *n = pending.front();
			pending.pop();
			if (n->flavour == CFGNode::true_target_instr)
				(*this)[n][n] = 0;
			if (!n->fallThrough.second && n->branches.empty())
				continue;
			nodeLabelling exitMap((*this)[n]);
			exitMap.successor(maxPathLength);
			if (n->fallThrough.second && (*this)[n->fallThrough.second].merge(exitMap))
				pending.push(n->fallThrough.second);
			for (auto it2 = n->branches.begin(); it2 != n->branches.end(); it2++)
				if (it2->second && (*this)[it2->second].merge(exitMap))
					pending.push(it2->second);			
		}
	}
}

/* Look through @root until we find a cycle.  Report the edge which
   completes the cycle in *@edge_start and *@edge_end. */
static bool
selectEdgeForCycleBreak(CFGNode *root, CFGNode **edge_start, CFGNode **edge_end,
			std::set<CFGNode *> &clean, std::set<CFGNode *> &path)
{
	if (!root->fallThrough.second && root->branches.empty())
		return false;
	if (clean.count(root))
		return false;
	assert(!path.count(root));
	clean.insert(root);
	path.insert(root);
	if (root->fallThrough.second) {
		if (path.count(root->fallThrough.second)) {
			*edge_start = root;
			*edge_end = root->fallThrough.second;
			return true;
		}
		if (selectEdgeForCycleBreak(root->fallThrough.second, edge_start, edge_end, clean,
					    path))
			return true;
	}
	for (auto it = root->branches.begin(); it != root->branches.end(); it++) {
		if (it->second) {
			if (path.count(it->second)) {
				*edge_start = root;
				*edge_end = it->second;
				return true;
			}
			if (selectEdgeForCycleBreak(it->second, edge_start, edge_end, clean,
						    path))
				return true;
		}
	}
	path.erase(root);
	return false;
}
static bool
selectEdgeForCycleBreak(CFGNode *root, CFGNode **edge_start, CFGNode **edge_end)
{
	std::set<CFGNode *> clean; /* Anything in here definitely
				      cannot reach a cycle. */
	std::set<CFGNode *> path; /* All the nodes between @root and
				     the node we're currently looking
				     at. */
	return selectEdgeForCycleBreak(root, edge_start, edge_end, clean, path);
}

/* Take the graph represented by @roots and transform it so that it is
   acyclic, whilst still maintaining all paths up to length
   @maxPathLength which start and end with a true_target_instr node.
   This will usually involve duplicating some nodes, and the duplicate
   of a true_target_instr is a dupe_target_instr, so this does
   actually terminate. */
static void
performUnrollAndCycleBreak(std::set<CFGNode *> &roots, unsigned maxPathLength)
{
	nodeLabellingMap nlm(roots, maxPathLength);

	for (auto it = roots.begin(); it != roots.end(); it++) {
		while (!TIMEOUT) {
			CFGNode *cycle_edge_start, *cycle_edge_end;
			if (!selectEdgeForCycleBreak(*it, &cycle_edge_start, &cycle_edge_end)) {
				/* No cycles left in the graph rooted
				 * at *it.  Yay. */
				break;
			}
			nodeLabelling label(nlm[cycle_edge_start]);
			CFGNode *new_node;
			label.successor(maxPathLength);
			if (label.size() == 0) {
				new_node = NULL;
			} else {
				new_node = cycle_edge_end->dupe();
				nlm[new_node] = label;
			}
			if (cycle_edge_start->fallThrough.second == cycle_edge_end) {
				cycle_edge_start->fallThrough.second = new_node;
			} else {
				bool found_it = false;
				for (auto it = cycle_edge_start->branches.begin();
				     !found_it && it != cycle_edge_start->branches.end();
				     it++) {
					if (it->second == cycle_edge_end) {
						it->second = new_node;
						found_it = true;
					}
				}
				assert(found_it);
			}
		}
	}
}

static void
backtrackWhereUnambiguous(std::map<VexRip, CFGNode *> &ripsToCFGNodes,
			  Oracle *oracle)
{
	std::set<CFGNode *> roots;
	findRoots(ripsToCFGNodes, roots);
	std::set<CFGNode *> newNodes;
	for (auto it = roots.begin(); it != roots.end(); it++) {
		CFGNode *n = *it;
		for (unsigned cntr = 0; cntr < CONFIG_MAX_STORE_BACKTRACK; cntr++) {
			std::vector<VexRip> predecessors;
			oracle->findPredecessors(n->my_rip, true,
						 n->libraryFunction != LibraryFunctionTemplate::none,
						 predecessors);
			if (predecessors.size() != 1)
				break;
			if (predecessors[0].stack.size() != n->my_rip.stack.size())
				break;
			VexRip &predecessor(predecessors[0]);
			if (ripsToCFGNodes.count(predecessor))
				break;
			CFGNode *work = CFGNode::forRip(oracle, predecessor, CFGNode::ordinary_instr);
			if (!work)
				break;
			ripsToCFGNodes[predecessor] = work;
			newNodes.insert(work);
			n = work;
		}
	}
	for (auto it = newNodes.begin(); it != newNodes.end(); it++)
		resolveReferences(ripsToCFGNodes, *it);
}

static void
buildCFG(const std::set<DynAnalysisRip> &dyn_roots, unsigned maxPathLength,
	 Oracle *oracle, std::set<CFGNode *> &roots)
{
	std::map<VexRip, CFGNode *> ripsToCFGNodes;
	initialExploration(dyn_roots, maxPathLength, oracle, ripsToCFGNodes);
	if (TIMEOUT)
		return;
	resolveReferences(ripsToCFGNodes);

	if (debug_initial_exploration) {
		printf("Results of initial exploration:\n");
		debug_dump(ripsToCFGNodes, "\t");
	}

	trimUninterestingCFGNodes(ripsToCFGNodes, dyn_roots);
	if (debug_trim_uninteresting) {
		printf("After removing uninteresting nodes:\n");
		debug_dump(ripsToCFGNodes, "\t");
	}

	backtrackWhereUnambiguous(ripsToCFGNodes, oracle);

	findRoots(ripsToCFGNodes, roots);
	if (debug_find_roots) {
		printf("After backtracking:\n");
		debug_dump(roots, "\t");
	}
	if (removeRedundantRoots(ripsToCFGNodes, roots)) {
		if (debug_remove_redundant_roots) {
			printf("after removing redundant roots:\n");
			debug_dump(roots, "\t");
		}
		removeUnreachableCFGNodes(ripsToCFGNodes, roots);
		if (debug_trim_uninteresting) {
			printf("after removing unreachable nodes:\n");
			debug_dump(roots, "\t");
		}
	}

	/* Okay, so we've now successfully built the entire CFG for
	   the relevant fragment of program.  Now we need to perform
	   cycle-breaking and unrolling so that:

	   a) The graph is acyclic, and
	   b) all paths up to length maxPathLength are still
	   represented.

	   Note that, for b, ``paths'' includes all of the
	   instructions in dyn_roots (i.e. those with is_root set)
	   even if they aren't roots of the static graph.  What that
	   means in practice is that we stop unrolling if, for every
	   dynamic root D, every path from D to the current
	   instruction is at least $N instructions long.
	*/
	performUnrollAndCycleBreak(roots, maxPathLength);
	if (debug_unroll_and_cycle_break) {
		printf("after unrolling and cycle breaking:\n");
		debug_dump(roots, "\t");
	}

	/* That might have duplicated up a few more nodes than we
	   really need due to partly unrolling a cycle and then
	   hitting the path limit.  Trim them out again. */
	trimUninterestingCFGNodes(roots);
	if (debug_trim_uninteresting) {
		printf("after final uninteresting trim:\n");
		debug_dump(roots, "\t");
	}
}

/* Build all of the store machines */
static void
getStoreCFGs(const std::set<DynAnalysisRip> &conflictingStores,
	     Oracle *oracle,
	     CFGNode ***roots,
	     int *nr_roots)
{
	std::set<CFGNode *> cfgRoots;
	buildCFG(conflictingStores, STORE_CLUSTER_THRESHOLD, oracle, cfgRoots);

	/* Need to copy that out to something in the IR heap, so that
	   we can do garbage collection. */
	*roots = (CFGNode **)__LibVEX_Alloc_Ptr_Array(&ir_heap, cfgRoots.size());
	unsigned nrCfgRoots = 0;
	for (auto it = cfgRoots.begin(); it != cfgRoots.end(); it++) {
		(*roots)[nrCfgRoots] = *it;
		nrCfgRoots++;
	}
	*nr_roots = nrCfgRoots;
}

/* End of namespace */
}

void
getStoreCFGs(const std::set<DynAnalysisRip> &conflictingStores,
	     Oracle *oracle,
	     CFGNode ***roots,
	     int *nr_roots)
{
	if (_getStoreCFGs::debug_top_level) {
		printf("getStoreCFGs, input ");
		for (auto it = conflictingStores.begin(); it != conflictingStores.end(); it++)
			printf("%s, ", it->name());
		printf("\n");
	}

	_getStoreCFGs::getStoreCFGs(conflictingStores, oracle, roots, nr_roots);

	if (!TIMEOUT && _getStoreCFGs::debug_top_level) {
		printf("Results:\n");
		for (int x = 0; x < *nr_roots; x++) {
			printf("%d/%d:\n", x, *nr_roots);
			printCFG( (*roots)[x], "\t", stdout);
		}
	}
}
