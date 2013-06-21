/* Silly little thing which reads in a static DB and compares it to
   the types table, making sure that every typed instruction is in a
   function. */
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

	auto instrIterator = oracle->type_db->enumerateAllInstructions();
	while (!instrIterator->finished()) {
		DynAnalysisRip dr;
		instrIterator->fetch(&dr);
		StaticRip fh(oracle->functionHeadForInstruction(StaticRip(dr)));
		if (fh.rip == 0) {
			printf("%s is missing from instruction table!\n", dr.name());
		}
		instrIterator->advance();
	}
	return 0;
}
