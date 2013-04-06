#include "sli.h"
#include "enforce_crash.hpp"
#include "timers.hpp"
#include "patch_strategy.hpp"

extern FILE *bubble_plot_log;

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], argv[4], ALLOW_GC);

	int next_hb_id = 0xaabb;

	SMScopes scopes;
	ThreadAbstracter abs;
	crashEnforcementData accumulator;

	bubble_plot_log = fopen("ec_driver_bubbles.log", "w");

	timeout_means_death = true;

	TimeoutTimer tt;
	tt.timeoutAfterSeconds(60);
	for (int i = 6; i < argc; i++) {
		CrashSummary *summary;

		if (i == 6) {
			summary = readBugReport(&scopes, argv[i], NULL);
		} else {
			SMScopes _scopes;
			summary = readBugReport(&_scopes, argv[i], NULL);
			summary = rewriteSummaryCrossScope(summary, &scopes);
		}
		crashEnforcementData acc = enforceCrashForMachine(SummaryId(i - 5), summary, oracle, abs, next_hb_id);
		optimiseHBEdges(acc);
		optimiseStashPoints(acc, oracle);
		optimiseCfg(acc);
		accumulator |= acc;
	}

	buildPatchStrategy(accumulator.roots, accumulator.crashCfg, oracle,
			   accumulator.patchPoints, accumulator.interpretInstrs);

	FILE *f = fopen(argv[5], "w");
	accumulator.prettyPrint(&scopes, f);
	accumulator.prettyPrint(&scopes, stdout);
	fclose(f);

	return 0;
}
