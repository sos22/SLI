#include "sli.h"
#include "oracle.hpp"
#include "cfgnode.hpp"

#include "cfgnode_tmpl.cpp"

int
main(int argc, char *argv[])
{
	init_sli();

	MachineState *ms = MachineState::readELFExec(argv[1]);
	Oracle *oracle = new Oracle(ms, NULL, NULL);

	std::map<DynAnalysisRip, IRType> input;

	for (int x = 2; x < argc; x++) {
		DynAnalysisRip r;
		const char *leftovers;
		if (!parseDynAnalysisRip(&r, argv[x], &leftovers) ||
		    *leftovers != 0)
			errx(1, "expected dyn analysis rip as argument, got %s",
			     argv[x]);
		input[r] = Ity_I64;
	}
	
	CFGNode **roots;
	int nr_roots;
	CfgLabelAllocator alloc;
	getStoreCFGs(alloc, input, oracle, &roots, &nr_roots);

	printf("Results:\n");
	for (int x = 0; x < nr_roots; x++) {
		printf("%d/%d:\n", x, nr_roots);
		printCFG(roots[x], stdout);
	}

	return 0;
}
