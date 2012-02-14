#include "sli.h"
#include "oracle_rip.hpp"

int
main(int argc, char *argv[])
{
	init_sli();
	MachineState *ms = MachineState::readCoredump(argv[1]);
	Thread *thr = ms->findThread(ThreadId(1));

	std::vector<OracleRip> dominators;
	std::vector<OracleRip> fheads;
	getDominators(thr, ms, dominators, fheads);

	for (auto it = dominators.begin();
	     it != dominators.end();
	     it++) {
		printf("%s\n", it->name());
	}

	return 0;
}
