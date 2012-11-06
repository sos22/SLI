#include "sli.h"
#include "oracle.hpp"

int
main(int argc, char *argv[])
{
	init_sli();

	const char *binary = argv[1];
	const char *types = argv[2];
	const char *callgraph = argv[3];
	const char *staticdb = argv[4];

	MachineState *ms = MachineState::readELFExec(binary);
	Thread *thr = ms->findThread(ThreadId(1));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, types));
	Oracle::loadCallGraph(oracle, callgraph, staticdb, ALLOW_GC);

	return 0;
}
