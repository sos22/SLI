#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "crashcfg.hpp"
#include "timers.hpp"

int
main(int argc, char *const argv[])
{
	if (argc < 7)
		errx(1, "need at least six arguments: binary, types table, callgraph, static db, output filename, and at least one summary");

	const char *binary = argv[1];
	const char *types_table = argv[2];
	const char *callgraph = argv[3];
	const char *staticdb = argv[4];
	const char *slidir = argv[5];
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

	FILE *logfile = fopen("s2f_perf.log", "w");
	for (int i = 0; i < nr_summaries; i++) {
		fflush(0);
		std::map<SummaryId, CrashSummary *> summaries;
		SMScopes scopes;
		summaries[SummaryId(1)] = readBugReport(&scopes, summary_fnames[i], NULL);

		fprintf(logfile, "%f: start %s\n", now(), summary_fnames[i]);
		char *patch = buildPatchForCrashSummary(logfile, oracle, summaries);

		fprintf(logfile, "%f: start system compile\n", now());
		writePatchToFile("s2f_perf.genfix.c", binary, summaries, patch);
		my_system("gcc", "-Wall", "-O", "-shared", "-fPIC", "-I", slidir, "s2f_perf.genfix.c", "-o", "s2f_perf.genfix.so", NULL);
		fprintf(logfile, "%f: stop system compile\n", now());

		fprintf(logfile, "%f: stop\n", now());

		unlink("s2f_perf.genfix.c");
		unlink("s2f_perf.genfix.so");
	}

	return 0;
}

