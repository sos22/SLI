#include <err.h>

#include "sli.h"
#include "oracle.hpp"
#include "cfgnode.hpp"
#include "typesdb.hpp"

#include "cfgnode.hpp"
#include "cfgnode_tmpl.cpp"

int
main(int argc, char *argv[])
{
	if (argc < 5)
		errx(1, "not enough arguments");

	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], argv[4], ALLOW_GC);

	VexRip vr;
	const char *suffix;
	if (!parseVexRip(&vr, argv[4], &suffix) || *suffix)
		err(1, "cannot parse %s as VexRip", argv[5]);
	HashedSet<HashedPtr<CFGNode> > roots;
	HashedSet<HashedPtr<const CFGNode> > targets;
	CfgLabelAllocator allocLabel;
	if (!getProbeCFGs(allocLabel, oracle, vr, roots, targets))
		err(1, "cannot build root set");

	int cntr = 0;
	for (auto it = roots.begin(); !it.finished(); it.advance()) {
		printf("Root %d/%zd:\n", cntr, roots.size());
		printCFG(it->get(), stdout);
		cntr++;
	}

	dumpCFGToDot(roots, "probecfg.dot");

	return 0;
}
