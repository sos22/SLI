#include "sli.h"
#include "cfgnode.hpp"
#include "oracle.hpp"

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

#include "cfgnode_tmpl.cpp"

template <typename t> static void
dumpCFGToDot(const std::set<_CFGNode<t> *> &roots, FILE *f)
{
	std::set<_CFGNode<t> *> allNodes;
	for (auto it = roots.begin(); it != roots.end(); it++)
		enumerateCFG(*it, allNodes);

	fprintf(f, "digraph {\n");
	for (auto it = allNodes.begin(); it != allNodes.end(); it++) {
		_CFGNode<t> *n = *it;
		fprintf(f, "n%p [label=\"%p\"", n, n);
		if (roots.count(n))
			fprintf(f, ", shape=box");
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

template <typename t> static void
dumpCFGToDot(const std::set<_CFGNode<t> *> &allNodes, const char *fname)
{
	FILE *f = fopen(fname, "w");
	if (!f) {
		printf("can't open %s\n", fname);
		return;
	}
	dumpCFGToDot(allNodes, f);
	fclose(f);
}

void
dumpCFGToDot(const std::set<CFGNode *> &allNodes, const char *fname)
{
	dumpCFGToDot(allNodes, fname);
}


