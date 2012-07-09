/* Careful: this gets #include'd into store_unroll_cycle_break.cpp so
 * that we can unit test some static functions. */
#include "sli.h"
#include "cfgnode.hpp"
#include "typesdb.hpp"
#include "oracle.hpp"

#include <map>
#include <queue>
#include <set>

#include "cfgnode_tmpl.cpp"

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

/* The node labelling map tells you where nodes can occur on paths.
   The idea is that we only need to care about paths which start on a
   true target instruction, end on a true or dupe target instruction,
   and which contain at most @depth instructions.  We therefore
   track, for each pair of (instruction, true target instruction):

   -- The minimum distance from the true target to the instruction of
      interest.  This is the from distance.
   -- The minimum distance from the instruction of interest to the
      true target or any dupes of it.  This is the to distance.

   In both cases, distance is measured as the number of edges on the
   path (so the distance from a target to itself is zero).  Either
   entry in the label might be empty, if we there are no paths of the
   right type.
*/
template <typename t>
class nodeLabellingComponent : public std::map<_CFGNode<t> *, int>, public Named {
	char *mkName() const {
		std::vector<char *> v;
		for (auto it = this->begin(); it != this->end(); it++) {
			if (it != this->begin())
				v.push_back(strdup(", "));
			v.push_back(my_asprintf("%p -> %d", it->first, it->second));
		}
		size_t sz = 0;
		for (auto it = v.begin(); it != v.end(); it++)
			sz += strlen(*it);
		char *res = (char *)malloc(sz + 1);
		res[0] = 0;
		for (auto it = v.begin(); it != v.end(); it++) {
			strcat(res, *it);
			free(*it);
		}
		return res;
	}
public:
	void successor(int maxDepth);
	bool merge(nodeLabellingComponent<t> &other);
};
template <typename t>
class nodeLabelling : public Named {
	char *mkName() const {
		return my_asprintf("{from = %s, to = %s}",
				   min_from.name(), min_to.name());
	}
public:
	nodeLabellingComponent<t> min_from;
	nodeLabellingComponent<t> min_to;
	bool dead(int maxDepth) const;
};
template <typename t>
class nodeLabellingMap : public std::map<_CFGNode<t> *, nodeLabelling<t> > {
public:
	nodeLabellingMap(std::set<_CFGNode<t> *> &roots, int maxPathLength);
	void prettyPrint(FILE *f) const;
};
template <typename t> void
nodeLabellingMap<t>::prettyPrint(FILE *f) const
{
	for (auto it = this->begin(); it != this->end(); it++)
		fprintf(f, "%p -> %s\n", it->first, it->second.name());
}

template <typename t> bool
nodeLabellingComponent<t>::merge(nodeLabellingComponent<t> &other)
{
	bool did_something = false;
	for (auto it = other.begin(); it != other.end(); it++) {
		auto it_did_insert = insert(std::pair<_CFGNode<t> *, unsigned>(it->first, it->second));
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

template <typename t> void
nodeLabellingComponent<t>::successor(int maxDepth)
{
	for (auto it = this->begin(); it != this->end(); ) {
		it->second++;
		if (it->second > maxDepth)
			this->erase(it++);
		else
			it++;
	}
}

template <typename t> bool
nodeLabelling<t>::dead(int maxDepth) const
{
	if (min_from.empty() || min_to.empty())
		return true;
	int min_from_true_target = maxDepth + 1;
	int min_to_dupe_target = maxDepth + 1;
	for (auto it = min_from.begin(); it != min_from.end(); it++)
		if (it->second < min_from_true_target)
			min_from_true_target = it->second;
	for (auto it = min_to.begin(); it != min_to.end(); it++)
		if (it->second < min_from_true_target)
			min_to_dupe_target = it->second;
	return min_from_true_target + min_to_dupe_target > maxDepth;
}

template <typename t>
nodeLabellingMap<t>::nodeLabellingMap(std::set<_CFGNode<t> *> &roots, int maxPathLength)
{
	std::queue<_CFGNode<t> *> pending;

	/* Initial pending set is all of the true target instructions. */
	std::set<_CFGNode<t> *> visited;
	for (auto it = roots.begin(); it != roots.end(); it++) {
		std::queue<_CFGNode<t> *> p2;
		p2.push(*it);
		while (!p2.empty()) {
			_CFGNode<t> *n = p2.front();
			p2.pop();
			if (!visited.insert(n).second)
				continue;
			if (n->flavour == _CFGNode<t>::true_target_instr)
				pending.push(n);
			if (n->fallThrough.second)
				p2.push(n->fallThrough.second);
			for (auto it2 = n->branches.begin();
			     it2 != n->branches.end();
			     it2++) {
				if (it2->second)
					p2.push(it2->second);
			}
		}
	}

	while (!pending.empty()) {
		_CFGNode<t> *n = pending.front();
		pending.pop();
		if (n->flavour == _CFGNode<t>::true_target_instr)
			(*this)[n].min_to[n] = 0;
		assert(n->flavour != _CFGNode<t>::dupe_target_instr);
		if (!n->fallThrough.second && n->branches.empty())
			continue;
		nodeLabellingComponent<t> exitMap((*this)[n].min_to);
		exitMap.successor(maxPathLength);
		if (n->fallThrough.second && (*this)[n->fallThrough.second].min_to.merge(exitMap))
			pending.push(n->fallThrough.second);
		for (auto it2 = n->branches.begin(); it2 != n->branches.end(); it2++)
			if (it2->second && (*this)[it2->second].min_to.merge(exitMap))
				pending.push(it2->second);			
	}
	bool progress = true;
	while (progress) {
		progress = false;
		for (auto it = this->begin(); it != this->end(); it++) {
			nodeLabellingComponent<t> &entryMap(it->second.min_from);
			_CFGNode<t> *n = it->first;
			if (n->flavour == _CFGNode<t>::true_target_instr) {
				if (!entryMap.count(n)) {
					progress = true;
					entryMap[n] = 0;
				} else {
					assert(entryMap[n] == 0);
				}
			}
			if (n->fallThrough.second) {
				nodeLabellingComponent<t> m((*this)[n->fallThrough.second].min_from);
				m.successor(maxPathLength);
				progress |= entryMap.merge(m);
			}
			for (auto it2 = n->branches.begin(); it2 != n->branches.end(); it2++) {
				if (it2->second) {
					nodeLabellingComponent<t> m ((*this)[it2->second].min_from);
					m.successor(maxPathLength);
					progress |= entryMap.merge(m);
				}
			}
		}
	}
}

/* Look through @root until we find a cycle.  Report the edge which
   completes the cycle in *@edge_start and *@edge_end. */
template <typename t> static bool
selectEdgeForCycleBreak(_CFGNode<t> *root,
			_CFGNode<t> **edge_start,
			_CFGNode<t> **edge_end,
			std::set<_CFGNode<t> *> &clean, std::set<_CFGNode<t> *> &path)
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
template <typename t> static bool
selectEdgeForCycleBreak(_CFGNode<t> *root, _CFGNode<t> **edge_start, _CFGNode<t> **edge_end)
{
	std::set<_CFGNode<t> *> clean; /* Anything in here definitely
				      cannot reach a cycle. */
	std::set<_CFGNode<t> *> path; /* All the nodes between @root and
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
template <typename t> static void
performUnrollAndCycleBreak(std::set<_CFGNode<t> *> &roots, unsigned maxPathLength)
{
	nodeLabellingMap<t> nlm(roots, maxPathLength);

	for (auto it = roots.begin(); it != roots.end(); it++) {
		while (!TIMEOUT) {
			_CFGNode<t> *cycle_edge_start, *cycle_edge_end;
			if (!selectEdgeForCycleBreak(*it, &cycle_edge_start, &cycle_edge_end)) {
				/* No cycles left in the graph rooted
				 * at *it.  Yay. */
				break;
			}
			nodeLabelling<t> label(nlm[cycle_edge_start]);
			_CFGNode<t> *new_node;
			label.min_from.successor(maxPathLength);
			label.min_to = nlm[cycle_edge_end].min_to;
			if (label.dead(maxPathLength)) {
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

/* The roots of the graph start off as the true target instructions,
   and then we move them backwards a little bit as long as that's
   unambiguous.  The idea is that including a bit more context can
   give the later analysis phases a bit more information, and it's
   safe as long as you know that you really did go down that path,
   which means its safe as long as you only ever backtrack
   instructions which have a unique predecessor. */
static void
findRootsAndBacktrack(std::map<VexRip, CFGNode *> &ripsToCFGNodes,
		      std::set<CFGNode *> &roots,
		      Oracle *oracle)
{
	std::set<CFGNode *> targetInstrs;
	for (auto it = ripsToCFGNodes.begin(); it != ripsToCFGNodes.end(); it++)
		if ( it->second->flavour == CFGNode::true_target_instr )
			targetInstrs.insert(it->second);
	std::set<CFGNode *> newNodes;
	for (auto it = targetInstrs.begin(); it != targetInstrs.end(); it++) {
		CFGNode *n = *it;
		for (unsigned cntr = 0; cntr < CONFIG_MAX_STORE_BACKTRACK; cntr++) {
			std::vector<VexRip> predecessors;
			oracle->findPredecessors(n->my_rip,
						 n->my_rip.stack.size() != 1,
						 n->libraryFunction != LibraryFunctionTemplate::none,
						 predecessors);
			if (predecessors.size() != 1)
				break;
			VexRip &predecessor(predecessors[0]);
			/* The starts and ends of functions are often
			   nice places to analyse, so stop
			   backtracking if it looks like we've reached
			   one. */
			if (predecessor.stack.size() != n->my_rip.stack.size())
				break;
			if (ripsToCFGNodes.count(predecessor))
				break;
			CFGNode *work = CFGNode::forRip(oracle, predecessor, CFGNode::ordinary_instr);
			if (!work)
				break;
			ripsToCFGNodes[predecessor] = work;
			newNodes.insert(work);
			n = work;
		}
		roots.insert(n);
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

	findRootsAndBacktrack(ripsToCFGNodes, roots, oracle);
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
			printCFG( (*roots)[x], stdout);
		}
	}
}
