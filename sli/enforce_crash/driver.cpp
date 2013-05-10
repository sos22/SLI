#include <sys/types.h>
#include <dirent.h>
#include <err.h>
#include <errno.h>
#include "sli.h"
#include "enforce_crash.hpp"
#include "canon.hpp"
#include "timers.hpp"
#include "allowable_optimisations.hpp"
#include "patch_strategy.hpp"

extern FILE *bubble_plot_log;

int
main(int argc, char *argv[])
{
	const char *binary = argv[1];
	const char *types = argv[2];
	const char *callgraph = argv[3];
	const char *staticdb = argv[4];
	const char *topdir = argv[5];
	const char *summarydir = argv[6];

	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(binary));
	VexPtr<Oracle> oracle(new Oracle(ms, ms->findThread(ThreadId(1)), types));
	VexPtr<OracleInterface> oracleI(oracle);
	oracle->loadCallGraph(oracle, callgraph, staticdb, ALLOW_GC);

	unlink("enf_bubble.log");
	bubble_plot_log = fopen("enf_bubble.log", "a");
	if (!bubble_plot_log) {
		err(1, "opening bubble log");
	}
	setlinebuf(bubble_plot_log);

	const char *inc_dir = my_asprintf("-I%s/sli/enforce_crash", topdir);
	const char *interpreter = my_asprintf("%s/cep_interpreter.o", topdir);

	DIR *d = opendir(summarydir);
	if (!d) {
		err(1, "opendir(%s)", summarydir);
	}
	while (1) {
		fflush(0);

		/* Force a GC, for sanity */
		LibVEX_gc(ALLOW_GC);

		errno = 0;
		auto de = readdir(d);
		if (!de) {
			if (errno) {
				err(1, "readdir(%s)", summarydir);
			}
			break;
		}
		if (!strcmp(".", de->d_name) || !strcmp("..", de->d_name)) {
			continue;
		}

		if (run_in_child(bubble_plot_log)) {
			continue;
		}

		const char *summary_fname = my_asprintf("%s/%s", summarydir, de->d_name);
		char *first_line;
		SMScopes scopes;
		VexPtr<CrashSummary, &ir_heap> summary(readBugReport(&scopes, summary_fname, &first_line));

		fprintf(bubble_plot_log, "%f: start build enforcer %s\n", now(), summary_fname);
		fprintf(bubble_plot_log, "%f: start canonicalise\n", now());
		summary = optimise_crash_summary(summary, oracleI, ALLOW_GC);
		summary = canonicalise_crash_summary(summary, oracleI,
						     AllowableOptimisations::defaultOptimisations.
							enableassumePrivateStack().
							enablenoExtend(),
						     ALLOW_GC);
		summary = optimise_crash_summary(summary, oracleI, ALLOW_GC);

		ThreadAbstracter abs;
		int next_hb_id = 10000;
		fprintf(bubble_plot_log, "%f: stop canonicalise\n", now());
		crashEnforcementData acc = enforceCrashForMachine(SummaryId(1), summary,
								  oracle, abs, next_hb_id);

		fprintf(bubble_plot_log, "%f: start simplify plan\n", now());		
		optimiseHBEdges(acc);
		optimiseStashPoints(acc, oracle);
		optimiseCfg(acc);
		fprintf(bubble_plot_log, "%f: stop simplify plan\n", now());

		{
			fprintf(bubble_plot_log, "%f: start build strategy\n", now());		
			TimeoutTimer tmr;
			tmr.timeoutAfterSeconds(TIMEOUT_EC_STRATEGY);
			printf("Build patch strategy for %s\n", summary_fname);
			buildPatchStrategy(acc.roots, acc.crashCfg, oracle,
					   acc.patchPoints, acc.interpretInstrs);
			tmr.cancel();
			fprintf(bubble_plot_log, "%f: stop build strategy\n", now());		
		}

		fprintf(bubble_plot_log, "%f: start compile\n", now());		
		ced_to_cep(acc, "temp.cep.c", binary, oracle);
		fprintf(bubble_plot_log, "%f: stop compile\n", now());		

		printf("Invoking gcc for %s\n", summary_fname);
		fprintf(bubble_plot_log, "%f: start gcc\n", now());
		my_system("gcc", "-ldl", inc_dir, "-shared", interpreter, "-x", "c", "temp.cep.c", "-o", "temp.interp.so", NULL);
		fprintf(bubble_plot_log, "%f: stop gcc\n", now());

		fprintf(bubble_plot_log, "%f: stop build enforcer\n", now());

		free((void *)summary_fname);
		unlink("temp.cep.c");
		unlink("temp.interp.so");

		exit(0);
	}

	return 0;
}
