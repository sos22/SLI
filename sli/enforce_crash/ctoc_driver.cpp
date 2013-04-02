#include "sli.h"
#include "enforce_crash.hpp"

int
main(int argc, char *argv[])
{
	const char *binary = argv[1];
	const char *ced_path = argv[2];
	const char *types = argv[3];
	const char *callgraph = argv[4];
	const char *staticdb = argv[5];
	const char *output = argv[6];

	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(binary));
	VexPtr<Oracle> oracle(new Oracle(ms, ms->findThread(ThreadId(1)), types));
	oracle->loadCallGraph(oracle, callgraph, staticdb, ALLOW_GC);

	return ced_to_cep(ced_path, ms, output, binary, oracle);
}
