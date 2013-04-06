#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "crashcfg.hpp"

int
main(int argc, char *const argv[])
{
	if (argc < 7)
		errx(1, "need at least six arguments: binary, types table, callgraph, static db, output filename, and at least one summary");

	const char *binary = argv[1];
	const char *types_table = argv[2];
	const char *callgraph = argv[3];
	const char *staticdb = argv[4];
	const char *output_fname = argv[5];
	const char *const *summary_fnames = argv + 6;
	int nr_summaries = argc - 6;

	init_sli();

	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(binary);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, types_table);
	}
	oracle->loadCallGraph(oracle, callgraph, staticdb, ALLOW_GC);

	std::map<SummaryId, CrashSummary *> summaries;
	SMScopes scopes;
	for (int i = 0; i < nr_summaries; i++) {
		summaries[SummaryId(i + 1)] = readBugReport(&scopes, summary_fnames[i], NULL);
	}

	char *patch = buildPatchForCrashSummary(NULL, oracle, summaries);
	printf("Patch is:\n%s\n", patch);

	writePatchToFile(output_fname, binary, summaries, patch);

	return 0;
}
