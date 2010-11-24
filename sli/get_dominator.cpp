#include "sli.h"

int
main(int argc, char *argv[])
{
	init_sli();
	MachineState *ms = MachineState::readCoredump(argv[1]);
	Thread *thr = ms->findThread(ThreadId(1));

	std::vector<unsigned long> dominators;
	getDominators(thr, ms, dominators);

	for (std::vector<unsigned long>::iterator it = dominators.begin();
	     it != dominators.end();
	     it++) {
		printf("%lx\n", *it);
	}

	return 0;
}
