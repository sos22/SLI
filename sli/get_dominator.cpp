#include "sli.h"
#include "oracle_rip.hpp"

int
main(int argc, char *argv[])
{
	if (argc < 2)
		errx(1, "need coredump filename");
	init_sli();
	MachineState *ms = MachineState::readCoredump(argv[1]);
	Thread *thr = ms->findThread(ThreadId(1));

	std::vector<VexRip> dominators;
	std::vector<VexRip> fheads;
	getDominators(thr, ms, dominators, fheads);

	for (auto it = dominators.begin();
	     it != dominators.end();
	     it++) {
		printf("%s\n", it->name());
	}

	return 0;
}
