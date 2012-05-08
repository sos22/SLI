#include "sli.h"
#include "oracle.hpp"
#include "cfgnode.hpp"
#include "typesdb.hpp"

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	DynAnalysisRip vr;
	const char *suffix;
	if (!parseDynAnalysisRip(&vr, argv[4], &suffix) || *suffix)
		err(1, "cannot parse %s as VexRip", argv[4]);
	std::set<CFGNode *> roots;
	if (!getProbeCFGs(oracle, vr, roots))
		err(1, "cannot build root set");

	int cntr = 0;
	for (auto it = roots.begin(); it != roots.end(); it++) {
		printf("Root %d/%zd:\n", cntr, roots.size());
		printCFG(*it, "\t", stdout);
		cntr++;
	}

	FILE *f = fopen("probecfg.dot", "w");
	dumpCFGToDot(roots, f);
	fclose(f);

	return 0;
}
