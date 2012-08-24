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
	f(debug_top_level)			\
	f(debug_backtrack_roots)
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

enum cfgflavour_store_t { cfgs_flavour_true, cfgs_flavour_dupe, cfgs_flavour_ordinary };

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

static void
initialExploration(const std::set<DynAnalysisRip> &roots,
		   std::map<const CFGNode *, cfgflavour_store_t> &flavours,
		   CfgLabelAllocator &allocLabel,
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

	for (auto it = vr_roots.begin(); it != vr_roots.end(); it++) {
		assert(it->isValid());
		pending.push(std::pair<unsigned, VexRip>(maxPathLength, *it));
	}
top_exploration_iter:
	while (!pending.empty()) {
		if (TIMEOUT)
			return;
		std::pair<unsigned, VexRip> item(pending.front());
		pending.pop();

		assert(item.second.isValid());
		assert(item.first > 0);

		auto it = doneSoFar.find(item.second);
		if (it != doneSoFar.end()) {
			if (item.first > it->second.first) {
				/* We've already explored this once,
				   but at a worse depth.  Fix it
				   up. */
				CFGNode *n = it->second.second;
				for (auto it2 = n->successors.begin();
				     it2 != n->successors.end();
				     it2++) {
					if (it2->rip.isValid())
						pending.push(std::pair<unsigned, VexRip>(
								     item.first - 1,
								     it2->rip));
				}
				it->second.first = item.first;

				if (item.first == maxPathLength)
					flavours[n] = cfgs_flavour_true;
			} else {
				/* We've already explored this at
				   a better depth, so don't need to
				   do anything. */
			}
			continue;
		}

		assert(item.second.isValid());

		CFGNode *work = CfgNodeForRip<VexRip>(allocLabel(), oracle, item.second);
		if (!work) {
			if (debug_initial_exploration)
				printf("Cannot get IRSB for %s\n", item.second.name());
			continue;
		}
		if (item.first == maxPathLength)
			flavours[work] = cfgs_flavour_true;
		else
			flavours[work] = cfgs_flavour_ordinary;
		if (item.first != 1) {
			for (auto it = work->successors.begin();
			     it != work->successors.end();
			     it++)
				if (it->rip.isValid())
					pending.push(std::pair<unsigned, VexRip>(
							     item.first - 1,
							     it->rip));
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
			assert(it->isValid());
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
		     HashedSet<HashedPtr<CFGNode> > &roots)
{
	bool res = false;
	for (auto it = roots.begin(); !TIMEOUT && !it.finished(); ) {
		const VexRip &rootRip((*it)->rip);
		bool redundant = false;
		for (auto it2 = m.begin(); !redundant && it2 != m.end(); it2++) {
			if (rootRip.isTruncationOf(it2->first))
				redundant = true;
		}
		if (redundant) {
			it.erase();
			res = true;
		} else {
			it.advance();
		}
	}
	return res;
}

/* Remove any nodes in @m which aren't reachable from a root in
 * @roots */
static void
removeUnreachableCFGNodes(std::map<VexRip, CFGNode *> &m, const HashedSet<HashedPtr<CFGNode> > &roots)
{
	HashedSet<HashedPtr<CFGNode> > reachable(roots);
	std::vector<CFGNode *> pending;
	pending.reserve(roots.size() * 2);
	for (auto it = roots.begin(); !it.finished(); it.advance()) {
		CFGNode *n = *it;
		for (auto it = n->successors.begin(); it != n->successors.end(); it++)
			if (it->instr)
				pending.push_back(it->instr);
	}
	while (!pending.empty()) {
		if (TIMEOUT)
			return;
		CFGNode *n = pending.back();
		pending.pop_back();
		assert(n);
		if (!reachable.insert(n))
			continue;
		for (auto it = n->successors.begin(); it != n->successors.end(); it++)
			if (it->instr)
				pending.push_back(it->instr);
	}
	for (auto it = m.begin(); it != m.end(); ) {
		if (reachable.contains(it->second))
			it++;
		else
			m.erase(it++);
	}
}

template <typename t>
class predecessorMap {
public:
	std::map<Instruction<t> *, HashedSet<HashedPtr<Instruction<t> > > > content;
	predecessorMap(const HashedSet<HashedPtr<Instruction<t> > > &roots);
	void erase_edge(Instruction<t> *src, Instruction<t> *dest) {
		assert(content.count(dest));
		assert(content.count(src));
		assert(content[dest].contains(src));
		content[dest].erase(src);
	}
	void insert_edge(Instruction<t> *src, Instruction<t> *dest) {
		assert(content.count(dest));
		assert(content.count(src));
		assert(!content[dest].contains(src));
		content[dest].insert(src);
	}
	void new_node(Instruction<t> *n) {
		assert(!content.count(n));
		content[n].clear(); /* kind of a no-op, but makes sure
				       that the slot in content is
				       actually allocated. */
		for (auto it = n->successors.begin(); it != n->successors.end(); it++) {
			if (it->instr) {
				assert(content.count(it->instr));
				content[it->instr].insert(n);
			}
		}
	}
	void findPredecessors(Instruction<t> *n, HashedSet<HashedPtr<Instruction<t> > > &out) {
		assert(content.count(n));
		out = content[n];
	}
};

template <typename t>
predecessorMap<t>::predecessorMap(const HashedSet<HashedPtr<Instruction<t> > > &roots)
{
	std::queue<Instruction<t> *> pending;
	for (auto it = roots.begin(); !it.finished(); it.advance()) {
		content[*it].clear();
		pending.push(*it);
	}
	while (!pending.empty()) {
		Instruction<t> *n = pending.front();
		pending.pop();
		for (auto it = n->successors.begin(); it != n->successors.end(); it++) {
			if (it->instr && content[it->instr].insert(n))
				pending.push(it->instr);
		}
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
class nodeLabellingComponent : public std::map<Instruction<t> *, int>, public Named {
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
class nodeLabellingMap : public std::map<Instruction<t> *, nodeLabelling<t> > {
	predecessorMap<t> &predecessors;
	const std::map<const Instruction<t> *, cfgflavour_store_t> &cfgFlavours;
	int maxDepth;
public:
	nodeLabellingMap(HashedSet<HashedPtr<Instruction<t> > > &roots,
			 predecessorMap<t> &predecessors,
			 const std::map<const Instruction<t> *, cfgflavour_store_t> &cfgFlavours,
			 int maxPathLength);
	void recalculate_min_from(Instruction<t> *n);
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
		auto it_did_insert = insert(std::pair<Instruction<t> *, unsigned>(it->first, it->second));
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
nodeLabellingMap<t>::nodeLabellingMap(HashedSet<HashedPtr<Instruction<t> > > &roots,
				      predecessorMap<t> &_predecessors,
				      const std::map<const Instruction<t> *, cfgflavour_store_t> &_cfgFlavours,
				      int maxPathLength)
	: predecessors(_predecessors), cfgFlavours(_cfgFlavours),
	  maxDepth(maxPathLength)
{
	/* Initial pending set is all of the true target instructions,
	 * for both min_to and min_from calculations. */
	std::queue<Instruction<t> *> initial_pending;
	HashedSet<HashedPtr<Instruction<t> > > visited;
	for (auto it = roots.begin(); !it.finished(); it.advance()) {
		std::queue<Instruction<t> *> p2;
		p2.push(*it);
		while (!p2.empty()) {
			Instruction<t> *n = p2.front();
			p2.pop();
			if (!visited.insert(n))
				continue;
			auto it_fl = cfgFlavours.find(n);
			assert(it_fl != cfgFlavours.end());
			if (it_fl->second == cfgs_flavour_true)
				initial_pending.push(n);
			for (auto it2 = n->successors.begin();
			     it2 != n->successors.end();
			     it2++) {
				if (it2->instr)
					p2.push(it2->instr);
			}
		}
	}

	std::queue<Instruction<t> *> pending(initial_pending);

	/* First we calculate min_to */
	while (!pending.empty()) {
		Instruction<t> *n = pending.front();
		pending.pop();

		auto it_fl = cfgFlavours.find(n);
		assert(it_fl != cfgFlavours.end());
		if (it_fl->second == cfgs_flavour_true)
			(*this)[n].min_to[n] = 0;
		assert(it_fl->second != cfgs_flavour_dupe);

		if (n->successors.empty())
			continue;

		nodeLabellingComponent<t> exitMap((*this)[n].min_to);
		exitMap.successor(maxPathLength);
		for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++)
			if (it2->instr && (*this)[it2->instr].min_to.merge(exitMap))
				pending.push(it2->instr);			
	}

	/* Now we calculate min_from using essentially the same
	 * algorithm, but using predecessors rather than
	 * successors. */
	pending = initial_pending;
	while (!pending.empty()) {
		Instruction<t> *n = pending.front();
		pending.pop();

		auto it_fl = cfgFlavours.find(n);
		assert(it_fl != cfgFlavours.end());
		if (it_fl->second == cfgs_flavour_true)
			(*this)[n].min_from[n] = 0;
		assert(it_fl->second != cfgs_flavour_dupe);

		HashedSet<HashedPtr<Instruction<t> > > pred;
		predecessors.findPredecessors(n, pred);
		if (pred.empty())
			continue;

		nodeLabellingComponent<t> entryMap((*this)[n].min_from);
		entryMap.successor(maxPathLength);
		for (auto it2 = pred.begin(); !it2.finished(); it2.advance())
			if ( (*this)[*it2].min_from.merge(entryMap) )
				pending.push(*it2);
	}
}

/* One of the edges to @node was just broken and replaced by something.
   That might change the minimum distance from a root to @n.
   Recalculate min_from as appropriate. */
template <typename t> void
nodeLabellingMap<t>::recalculate_min_from(Instruction<t> *node)
{
	std::queue<Instruction<t> *> pending;
	pending.push(node);
	while (!pending.empty()) {
		Instruction<t> *p = pending.front();
		pending.pop();

		/* This is a bit fiddly.  Because the label on the
		   node may have increased, we can't rely on our usual
		   merge operation (which works when things are
		   monotone descending) and have to recompute the
		   label on the node starting from just its
		   predecessor nodes, without reference to the node's
		   own label. */
		HashedSet<HashedPtr<Instruction<t> > > pred;
		nodeLabellingComponent<t> newEntryMap;
		predecessors.findPredecessors(p, pred);
		for (auto it = pred.begin(); !it.finished(); it.advance())
			newEntryMap.merge((*this)[*it].min_from);
		nodeLabellingComponent<t> newExitMap(newEntryMap);
		newExitMap.successor(maxDepth);
		auto it_fl = cfgFlavours.find(p);
		assert(it_fl != cfgFlavours.end());
		if (it_fl->second == cfgs_flavour_true)
			newExitMap[p] = 0;
		if (newExitMap != (*this)[p].min_from) {
			/* The min_from label on this node has
			 * changed.  Set the new label and propagate
			 * it to successors. */
			(*this)[p].min_from = newExitMap;
			for (auto it = p->successors.begin(); it != p->successors.end(); it++)
				if (it->instr)
					pending.push(it->instr);
		}
	}
}

/* Look through @root until we find a cycle.  Report the edge which
   completes the cycle in *@edge_start and *@edge_end. */
template <typename t> static bool
selectEdgeForCycleBreak(Instruction<t> *root,
			Instruction<t> **edge_start,
			Instruction<t> **edge_end,
			HashedSet<HashedPtr<Instruction<t> > > &clean,
			HashedSet<HashedPtr<Instruction<t> > > &path)
{
	if (root->successors.empty())
		return false;
	if (clean.contains(root))
		return false;
	assert(!path.contains(root));
	clean.insert(root);
	path.insert(root);
	for (auto it = root->successors.begin(); it != root->successors.end(); it++) {
		if (it->instr) {
			if (path.contains(it->instr)) {
				*edge_start = root;
				*edge_end = it->instr;
				return true;
			}
			if (selectEdgeForCycleBreak(it->instr, edge_start, edge_end, clean,
						    path))
				return true;
		}
	}
	path.erase(root);
	return false;
}
template <typename t> static bool
selectEdgeForCycleBreak(Instruction<t> *root, Instruction<t> **edge_start, Instruction<t> **edge_end)
{
	HashedSet<HashedPtr<Instruction<t> > > clean; /* Anything in here definitely
				      cannot reach a cycle. */
	HashedSet<HashedPtr<Instruction<t> > > path; /* All the nodes between @root and
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
performUnrollAndCycleBreak(CfgLabelAllocator &allocLabel,
			   HashedSet<HashedPtr<Instruction<t> > > &roots,
			   std::map<const Instruction<t> *, cfgflavour_store_t> &cfgFlavours,
			   unsigned maxPathLength)
{
	predecessorMap<t> pred(roots);
	nodeLabellingMap<t> nlm(roots, pred, cfgFlavours, maxPathLength);

	for (auto it = roots.begin(); !it.finished(); it.advance()) {
		while (!TIMEOUT) {
			Instruction<t> *cycle_edge_start, *cycle_edge_end;
			if (!selectEdgeForCycleBreak(&**it, &cycle_edge_start, &cycle_edge_end)) {
				/* No cycles left in the graph rooted
				 * at *it.  Yay. */
				break;
			}
			nodeLabelling<t> label(nlm[cycle_edge_start]);
			Instruction<t> *new_node;
			label.min_from.successor(maxPathLength);
			label.min_to = nlm[cycle_edge_end].min_to;
			if (label.dead(maxPathLength)) {
				new_node = NULL;
			} else {
				new_node = cycle_edge_end->dupe(allocLabel());
				auto it_fl = cfgFlavours.find(cycle_edge_end);
				assert(it_fl != cfgFlavours.end());
				if (it_fl->second == cfgs_flavour_true || it_fl->second == cfgs_flavour_dupe)
					cfgFlavours[new_node] = cfgs_flavour_dupe;
				else
					cfgFlavours[new_node] = cfgs_flavour_ordinary;
				pred.new_node(new_node);
				nlm[new_node] = label;
			}
			bool found_it = false;
			for (auto it = cycle_edge_start->successors.begin();
			     !found_it && it != cycle_edge_start->successors.end();
			     it++) {
				if (it->instr == cycle_edge_end) {
					it->instr = new_node;
					found_it = true;
				}
			}
			assert(found_it);
			pred.erase_edge(cycle_edge_start, cycle_edge_end);
			if (new_node)
				pred.insert_edge(cycle_edge_start, new_node);
			nlm.recalculate_min_from(cycle_edge_end);
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
findRootsAndBacktrack(CfgLabelAllocator &allocLabel,
		      std::map<VexRip, CFGNode *> &ripsToCFGNodes,
		      std::map<const CFGNode *, cfgflavour_store_t> &flavours,
		      HashedSet<HashedPtr<CFGNode> > &roots,
		      Oracle *oracle)
{
	if (debug_backtrack_roots)
		printf("%s:\n", __func__);
	HashedSet<HashedPtr<CFGNode> > targetInstrs;
	for (auto it = ripsToCFGNodes.begin(); it != ripsToCFGNodes.end(); it++) {
		auto it_fl = flavours.find(it->second);
		assert(it_fl != flavours.end());
		if (it_fl->second == cfgs_flavour_true) {
			if (debug_backtrack_roots) {
				printf("Initial root %p: ", it->second);
				it->second->prettyPrint(stdout);
			}
			targetInstrs.insert(it->second);
		}
	}
	HashedSet<HashedPtr<CFGNode> > newNodes;
	for (auto it = targetInstrs.begin(); !it.finished(); it.advance()) {
		CFGNode *start = *it;
		CFGNode *n = start;
		if (debug_backtrack_roots) {
			printf("Consider backtracking %p: ", n);
			n->prettyPrint(stdout);
		}
		for (unsigned cntr = 0; cntr < CONFIG_MAX_STORE_BACKTRACK; cntr++) {
			std::vector<VexRip> predecessors;
			bool isLibraryCall = false;
			for (auto it = n->successors.begin(); it != n->successors.end(); it++)
				if (it->calledFunction != LibraryFunctionTemplate::none)
					isLibraryCall = true;
			oracle->findPredecessors(n->rip,
						 n->rip.stack.size() != 1,
						 isLibraryCall,
						 predecessors);
			if (predecessors.size() != 1) {
				if(debug_backtrack_roots)
					printf("\tFailed; %zd predecessors\n", predecessors.size());
				break;
			}
			VexRip &predecessor(predecessors[0]);
			if (debug_backtrack_roots)
				printf("\tPredecessor %s\n", predecessor.name());
			/* The starts and ends of functions are often
			   nice places to analyse, so stop
			   backtracking if it looks like we've reached
			   one. */
			if (predecessor.stack.size() != n->rip.stack.size()) {
				if (debug_backtrack_roots)
					printf("\tFailed: stack size %zd != %zd\n",
					       predecessor.stack.size(),
					       n->rip.stack.size());
				break;
			}
			if (ripsToCFGNodes.count(predecessor)) {
				n = ripsToCFGNodes[predecessor];
				if (debug_backtrack_roots) {
					printf("\tFinished backtracking at %p: ", n);
					n->prettyPrint(stdout);
				}
				break;
			} else {
				CFGNode *work = CfgNodeForRip<VexRip>(allocLabel(), oracle, predecessor);
				if (!work) {
					if (debug_backtrack_roots)
						printf("\tFailed: no decode\n");
					break;
				}
				flavours[work] = cfgs_flavour_ordinary;
				ripsToCFGNodes[predecessor] = work;
				newNodes.insert(work);
				n = work;
				if (debug_backtrack_roots) {
					printf("\tBacktracked to new %p: ", n);
					n->prettyPrint(stdout);
				}
			}
		}
		roots.insert(n);
	}
	for (auto it = newNodes.begin(); !it.finished(); it.advance())
		resolveReferences(ripsToCFGNodes, &**it);

	for (auto it = roots.begin(); !it.finished(); ) {
		CFGNode *n = *it;
		/* Walk back up the unique predecessor chain for @n.
		   If we encounter any other roots then this root is
		   redundant. */
		bool redundant = false;
		if (debug_backtrack_roots) {
			printf("Check redundancy of root %p: ", n);
			n->prettyPrint(stdout);
		}
		while (1) {
			std::vector<VexRip> predecessors;
			bool isLibraryCall = false;
			for (auto it = n->successors.begin(); it != n->successors.end(); it++)
				if (it->calledFunction != LibraryFunctionTemplate::none)
					isLibraryCall = true;
			oracle->findPredecessors(n->rip,
						 n->rip.stack.size() != 1,
						 isLibraryCall,
						 predecessors);
			if (predecessors.size() != 1)
				break;
			VexRip &predecessor(predecessors[0]);
			auto it2 = ripsToCFGNodes.find(predecessor);
			if (it2 == ripsToCFGNodes.end())
				break;
			CFGNode *pred = it2->second;
			if (pred == n)
				break;
			if (roots.contains(pred)) {
				redundant = true;
				if (debug_backtrack_roots) {
					printf("\tRedundant with %p: ", pred);
					pred->prettyPrint(stdout);
				}
				break;
			}
			n = pred;
		}

		if (redundant) {
			it.erase();
		} else {
			if (debug_backtrack_roots)
				printf("\tNot redundant\n");
			it.advance();
		}
	}
}

template <typename t> static void
trimUninterestingCFGNodes(HashedSet<HashedPtr<Instruction<t> > > &roots,
			  const std::map<const Instruction<t> *, cfgflavour_store_t> &flavours)
{
	HashedSet<HashedPtr<Instruction<t> > > interesting(roots);
	HashedSet<HashedPtr<Instruction<t> > > allCFGNodes;
	for (auto it = roots.begin(); !TIMEOUT && !it.finished(); it.advance())
		cfgnode_tmpl::enumerateCFG(&**it, allCFGNodes);
	bool progress = true;
	while (!TIMEOUT && progress) {
		progress = false;
		for (auto it = allCFGNodes.begin(); !it.finished(); it.advance()) {
			Instruction<t> *n = *it;
			if (interesting.contains(n))
				continue;
			bool isInteresting = false;
			auto fl_it = flavours.find(n);
			assert(fl_it != flavours.end());
			if ( fl_it->second == cfgs_flavour_true ||
			     fl_it->second == cfgs_flavour_dupe )
				isInteresting = true;
			for (auto it2 = n->successors.begin(); !isInteresting && it2 != n->successors.end(); it2++)
				if (it2->instr && interesting.contains(it2->instr))
					isInteresting = true;
			if (isInteresting) {
				interesting.insert(n);
				progress = true;
			}
		}
	}
	if (debug_trim_uninteresting) {
		for (auto it = allCFGNodes.begin(); !it.finished(); it.advance()) {
			if (!interesting.contains(*it)) {
				printf("Trim uninteresting: %p ", &**it);
				(*it)->prettyPrint(stdout);
			}
		}
	}

	for (auto it = allCFGNodes.begin(); !TIMEOUT && !it.finished(); it.advance()) {
		Instruction<t> *n = *it;
		for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++)
			if (it2->instr && !interesting.contains(it2->instr))
				it2->instr = NULL;
	}
}

static void
buildCFG(CfgLabelAllocator &allocLabel, const std::set<DynAnalysisRip> &dyn_roots,
	 unsigned maxPathLength, Oracle *oracle, HashedSet<HashedPtr<CFGNode> > &roots)
{
	std::map<VexRip, CFGNode *> ripsToCFGNodes;
	std::map<const CFGNode *, cfgflavour_store_t> cfgFlavours;
	initialExploration(dyn_roots, cfgFlavours, allocLabel, maxPathLength, oracle, ripsToCFGNodes);
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

	findRootsAndBacktrack(allocLabel, ripsToCFGNodes, cfgFlavours, roots, oracle);
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
	performUnrollAndCycleBreak(allocLabel, roots, cfgFlavours, maxPathLength);
	if (debug_unroll_and_cycle_break) {
		printf("after unrolling and cycle breaking:\n");
		debug_dump(roots, "\t");
	}

	/* That might have duplicated up a few more nodes than we
	   really need due to partly unrolling a cycle and then
	   hitting the path limit.  Trim them out again. */
	trimUninterestingCFGNodes(roots, cfgFlavours);
	if (debug_trim_uninteresting) {
		printf("after final uninteresting trim:\n");
		debug_dump(roots, "\t");
	}
}

class SortByRipComp {
public:
	bool operator()(CFGNode *a, CFGNode *b) {
		return a->rip < b->rip;
	}
};
static void
sortByRip(CFGNode **roots, int nr_roots)
{
	std::sort(&roots[0], &roots[nr_roots], SortByRipComp());
}

/* Build all of the store machines */
static void
getStoreCFGs(CfgLabelAllocator &allocLabel,
	     const std::set<DynAnalysisRip> &conflictingStores,
	     Oracle *oracle,
	     CFGNode ***roots,
	     int *nr_roots)
{
	HashedSet<HashedPtr<CFGNode> > cfgRoots;
	buildCFG(allocLabel, conflictingStores, STORE_CLUSTER_THRESHOLD, oracle, cfgRoots);

	/* Need to copy that out to something in the IR heap, so that
	   we can do garbage collection. */
	*roots = (CFGNode **)__LibVEX_Alloc_Ptr_Array(&ir_heap, cfgRoots.size());
	unsigned nrCfgRoots = 0;
	for (auto it = cfgRoots.begin(); !it.finished(); it.advance()) {
		(*roots)[nrCfgRoots] = *it;
		nrCfgRoots++;
	}

	/* For sanity reasons, we want to process the store CFG roots
	   in a deterministic order (because otherwise performance
	   tuning is just too hard).  They're currently in pointer
	   order, which is non-deterministic.  Sort by RIP to make it
	   deterministic. */
	sortByRip((*roots), nrCfgRoots);

	*nr_roots = nrCfgRoots;
}

/* End of namespace */
}

void
getStoreCFGs(CfgLabelAllocator &allocLabel,
	     const std::set<DynAnalysisRip> &conflictingStores,
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

	_getStoreCFGs::getStoreCFGs(allocLabel, conflictingStores, oracle, roots, nr_roots);

	if (!TIMEOUT && _getStoreCFGs::debug_top_level) {
		printf("Results:\n");
		for (int x = 0; x < *nr_roots; x++) {
			printf("%d/%d:\n", x, *nr_roots);
			printCFG( (*roots)[x], stdout);
		}
	}
}
