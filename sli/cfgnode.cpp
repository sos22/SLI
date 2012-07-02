#include "sli.h"
#include "cfgnode.hpp"
#include "oracle.hpp"

#ifdef NDEBUG
#define debug_find_roots 0
#else
static int debug_find_roots = 0;
#endif

CFGNode *
CFGNode::forRip(Oracle *oracle, const VexRip &vr, CFGNode::flavour_t flavour)
{
	IRSB *irsb = oracle->getIRSBForRip(vr);
	if (!irsb)
		return NULL;
	CFGNode *work = new CFGNode(vr, flavour, LibraryFunctionTemplate::none);
	int x;
	for (x = 1; x < irsb->stmts_used && irsb->stmts[x]->tag != Ist_IMark; x++) {
		if (irsb->stmts[x]->tag == Ist_Exit)
			work->branches.push_back(
				CFGNode::successor_t(((IRStmtExit *)irsb->stmts[x])->dst.rip,
						     NULL));
	}
	if (x == irsb->stmts_used) {
		if (irsb->jumpkind == Ijk_Ret) {
			work->fallThrough.first = vr;
			work->fallThrough.first.rtrn();
		} else if (irsb->jumpkind == Ijk_Call) {
			if (irsb->next_is_const) {
				if (oracle->isPltCall(irsb->next_const.rip)) {
					work->libraryFunction = oracle->identifyLibraryCall(irsb->next_const.rip);
					work->fallThrough.first = extract_call_follower(irsb);
				} else {
					work->branches.push_back(
						CFGNode::successor_t(irsb->next_const.rip,
								     NULL));
				}
			} else {
				std::vector<VexRip> b;
				oracle->getInstrCallees(vr, b);
				for (auto it = b.begin(); it != b.end(); it++)
					work->branches.push_back(
						CFGNode::successor_t(*it, NULL));
			}
		} else if (irsb->next_is_const) {
			work->fallThrough.first = irsb->next_const.rip;
		} else {
			/* Note that the oracle has a slightly
			   different idea of fall-throughs to
			   us: it considers the targets of a
			   dynamic branch to be fall-through
			   targets, whereas we consider them
			   to be branch targets. */
			std::vector<VexRip> b;
			oracle->getInstrFallThroughs(vr, b);
			for (auto it = b.begin(); it != b.end(); it++)
				work->branches.push_back(
					CFGNode::successor_t(*it, NULL));
		}
	} else {
		assert(irsb->stmts[x]->tag == Ist_IMark);
		work->fallThrough.first = ((IRStmtIMark *)irsb->stmts[x])->addr.rip;
	}
	return work;
}

void
resolveReferences(const std::map<VexRip, CFGNode *> &m, CFGNode *what)
{
	assert(what);

	struct {
		const std::map<VexRip, CFGNode *> *m;
		CFGNode *operator()(const VexRip &vr) {
			if (!vr.isValid())
				return NULL;
			auto it = m->find(vr);
			if (it != m->end())
				return it->second;
			else
				return NULL;
		}
	} resolveBranch = {&m};

	what->fallThrough.second = resolveBranch(what->fallThrough.first);
	for (auto it = what->branches.begin(); it != what->branches.end(); it++)
		it->second = resolveBranch(it->first);
}

void
resolveReferences(std::map<VexRip, CFGNode *> &m)
{
	if (TIMEOUT)
		return;
	for (auto it = m.begin(); it != m.end(); it++)
		resolveReferences(m, it->second);
}

static void
enumerateCFG(CFGNode *start, std::set<CFGNode *> &out)
{
	std::vector<CFGNode *> pending;
	pending.push_back(start);
	while (!pending.empty()) {
		CFGNode *n = pending.back();
		pending.pop_back();
		if (!out.insert(n).second)
			continue;
		if (n->fallThrough.second)
			pending.push_back(n->fallThrough.second);
		for (auto it = n->branches.begin(); it != n->branches.end(); it++)
			if (it->second)
				pending.push_back(it->second);
	}
}

/* Remove any nodes in @m which cannot ever reach something in
 * @roots. */
void
trimUninterestingCFGNodes(std::map<VexRip, CFGNode *> &m,
			  const std::set<DynAnalysisRip> &roots)
{
	/* First, figure out which nodes are interesting. */
	std::set<CFGNode *> interesting;
	/* Anything in @roots is interesting. */
	for (auto it = m.begin(); !TIMEOUT && it != m.end(); it++) {
		const VexRip &vr(it->first);
		for (auto it2 = roots.begin(); !TIMEOUT && it2 != roots.end(); it2++) {
			const DynAnalysisRip &dr(*it2);
			if (dr == DynAnalysisRip(vr)) {
				interesting.insert(it->second);
				break;
			}
		}
	}
	/* Anything which can reach an interesting node is itself
	 * interesting. */
	bool progress = true;
	while (progress) {
		if (TIMEOUT)
			return;
		progress = false;
		for (auto it = m.begin(); it != m.end(); it++) {
			CFGNode *n = it->second;
			assert(n);
			if (interesting.count(n))
				continue;
			bool isInteresting = false;
			if ( n->fallThrough.second && interesting.count(n->fallThrough.second) )
				isInteresting = true;
			for (auto it = n->branches.begin(); !isInteresting && it != n->branches.end(); it++)
				if (it->second && interesting.count(it->second))
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
		if (!interesting.count(n)) {
			m.erase(it++);
			continue;
		}
		if (n->fallThrough.second && !interesting.count(n->fallThrough.second))
			n->fallThrough.second = NULL;
		for (auto it2 = n->branches.begin(); it2 != n->branches.end(); it2++)
			if (it2->second && !interesting.count(it2->second))
				it2->second = NULL;
		it++;
	}
}

void
trimUninterestingCFGNodes(std::map<VexRip, CFGNode *> &m,
			  const DynAnalysisRip &root)
{
	std::set<DynAnalysisRip> roots;
	roots.insert(root);
	trimUninterestingCFGNodes(m, roots);
}

void
trimUninterestingCFGNodes(std::set<CFGNode *> &roots)
{
	std::set<CFGNode *> interesting(roots);
	std::set<CFGNode *> allCFGNodes;
	for (auto it = roots.begin(); !TIMEOUT && it != roots.end(); it++)
		enumerateCFG(*it, allCFGNodes);
	bool progress = true;
	while (!TIMEOUT && progress) {
		progress = false;
		for (auto it = allCFGNodes.rbegin(); it != allCFGNodes.rend(); it++) {
			CFGNode *n = *it;
			if (interesting.count(n))
				continue;
			bool isInteresting = false;
			if ( n->flavour == CFGNode::true_target_instr ||
			     n->flavour == CFGNode::dupe_target_instr ||
			     (n->fallThrough.second && interesting.count(n->fallThrough.second)))
				isInteresting = true;
			for (auto it2 = n->branches.begin(); !isInteresting && it2 != n->branches.end(); it2++)
				if (it2->second && interesting.count(it2->second))
					isInteresting = true;
			if (isInteresting) {
				interesting.insert(n);
				progress = true;
			}
		}
	}
	for (auto it = allCFGNodes.begin(); !TIMEOUT && it != allCFGNodes.end(); it++) {
		CFGNode *n = *it;
		if (n->fallThrough.second && !interesting.count(n->fallThrough.second))
			n->fallThrough.second = NULL;
		for (auto it2 = n->branches.begin(); it2 != n->branches.end(); it2++)
			if (it2->second && !interesting.count(it2->second))
				it2->second = NULL;
	}
}

static void
removeReachable(std::set<CFGNode *> &out, const CFGNode *n)
{
	std::vector<const CFGNode *> pending;
	pending.push_back(n);
	while (!pending.empty()) {
		const CFGNode *n = pending.back();
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

static void
removeReachable(std::set<CFGNode *> &out, const std::set<CFGNode *> &roots)
{
	for (auto it = roots.begin(); it != roots.end(); it++)
		removeReachable(out, *it);
}

static int
nrSuccessors(const std::set<CFGNode *> &interesting, const CFGNode *n)
{
	std::set<const CFGNode *> successors;
	std::queue<const CFGNode *> pending;
	pending.push(n);
	while (!pending.empty()) {
		const CFGNode *n = pending.front();
		pending.pop();
		if (!interesting.count(const_cast<CFGNode *>(n)))
			continue;
		if (!successors.insert(n).second)
			continue;
		for (auto it = n->branches.begin(); it != n->branches.end(); it++)
			if (it->second)
				pending.push(it->second);
		if (n->fallThrough.second)
			pending.push(n->fallThrough.second);
	}
	return successors.size();
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
void
findRoots(const std::set<CFGNode *> &allNodes, std::set<CFGNode *> &roots)
{
	std::set<CFGNode *> currentlyUnrooted(allNodes);

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
	std::set<CFGNode *> newRoots = currentlyUnrooted;
	for (auto it = allNodes.begin();
	     it != allNodes.end();
	     it++) {
		CFGNode *n = *it;
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
		   part of a cycle in @currentlyUnrooted.  Grab
		   whichever node reaches the largest number of
		   successor nodes, breaking ties by according to the
		   node flavour. */
		/* (i.e. if we have a choice, we prefer to take
		   true_target_instr nodes as roots in preference to
		   ordinary_instr ones) */
		CFGNode *best_node;
		int best_nr_succ;
		best_node = NULL;
		best_nr_succ = -1;
		for (auto it = currentlyUnrooted.begin(); it != currentlyUnrooted.end(); it++) {
			/* Shouldn't be any dupe nodes at this stage of the pipeline. */
			assert((*it)->flavour != CFGNode::dupe_target_instr);

			int n = nrSuccessors(currentlyUnrooted, *it);
			if (n > best_nr_succ ||
			    (n == best_nr_succ &&
			     best_node->flavour == CFGNode::ordinary_instr &&
			     (*it)->flavour == CFGNode::true_target_instr)) {
				best_nr_succ = n;
				best_node = *it;
			}
		}

		if (debug_find_roots)
			printf("Selected cycle-breaking root %p (%d)\n",
			       best_node, best_nr_succ);
		assert(best_node != NULL);
		roots.insert(best_node);
		removeReachable(currentlyUnrooted, best_node);
	}
}

void
findRoots(const std::map<VexRip, CFGNode *> &m, std::set<CFGNode *> &roots)
{
	std::set<CFGNode *> allNodes;
	for (auto it = m.begin(); it != m.end(); it++)
		allNodes.insert(it->second);
	findRoots(allNodes, roots);
}

void
dumpCFGToDot(const std::set<CFGNode *> &roots, FILE *f)
{
	std::set<CFGNode *> allNodes;
	for (auto it = roots.begin(); it != roots.end(); it++)
		enumerateCFG(*it, allNodes);

	fprintf(f, "digraph {\n");
	for (auto it = allNodes.begin(); it != allNodes.end(); it++) {
		CFGNode *n = *it;
		fprintf(f, "n%p [label=\"%p\"", n, n);
		if (roots.count(n))
			fprintf(f, ", shape=box");
		switch (n->flavour) {
		case CFGNode::true_target_instr:
			fprintf(f, ", color=green");
			break;
		case CFGNode::dupe_target_instr:
			fprintf(f, ", color=yellow");
			break;
		case CFGNode::ordinary_instr:
			break;
		}
		fprintf(f, "]\n");
		if (n->fallThrough.second)
			fprintf(f, "n%p -> n%p [color=blue]\n", n, n->fallThrough.second);
		for (auto it = n->branches.begin();
		     it != n->branches.end();
		     it++)
			if (it->second)
				fprintf(f, "n%p -> n%p [color=red]\n", n, it->second);
	}
	fprintf(f, "}\n");
}

/* This is mostly intended to be called from the debugger. */
void
dumpCFGToDot(const std::set<CFGNode *> &allNodes, const char *fname, bool useTheseRoots)
{
	FILE *f = fopen(fname, "w");
	if (!f) {
		printf("can't open %s\n", fname);
		return;
	}
	if (useTheseRoots) {
		dumpCFGToDot(allNodes, f);
	} else {
		std::set<CFGNode *> roots;
		findRoots(allNodes, roots);
		dumpCFGToDot(roots, f);
	}
	fclose(f);
}
