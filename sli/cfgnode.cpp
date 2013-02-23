#include "sli.h"
#include "cfgnode.hpp"
#include "oracle.hpp"

#include "cfgnode_tmpl.cpp"

template <typename t> static void
dumpCFGToDot(const HashedSet<HashedPtr<_CFGNode<t> > > &roots, FILE *f)
{
	std::set<_CFGNode<t> *> allNodes;
	for (auto it = roots.begin(); !it.finished(); it.advance())
		enumerateCFG(*it, allNodes);

	fprintf(f, "digraph {\n");
	for (auto it = allNodes.begin(); it != allNodes.end(); it++) {
		auto *n = *it;
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
dumpCFGToDot(const HashedSet<HashedPtr<_CFGNode<t> > > &allNodes, const char *fname)
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
dumpCFGToDot(const HashedSet<HashedPtr<CFGNode> > &allNodes, const char *fname)
{
	dumpCFGToDot(allNodes, fname);
}

void
____force_compile()
{
	printCFG<VexRip>(NULL, NULL);
}
