/* Like canonicalise_crash_summary, but use some more aggressive
   canonicalisations which are more computationally expensive. */
#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "intern.hpp"
#include "allowable_optimisations.hpp"
#include "offline_analysis.hpp"

static CrashSummary *
canonicalise_crash_summary(VexPtr<CrashSummary, &ir_heap> input,
			   VexPtr<Oracle> oracle,
			   const AllowableOptimisations &optIn,
			   GarbageCollectionToken token)
{
	input->loadMachine = removeAssertions(input->loadMachine, optIn, oracle, false, token);
	input->storeMachine = removeAssertions(input->storeMachine, optIn, oracle, false, token);

	return input;
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(argv[1]);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, argv[2]);
	}

	VexPtr<CrashSummary, &ir_heap> summary;
	char *first_line;

	summary = readBugReport(argv[3], &first_line);

	summary = canonicalise_crash_summary(
		summary,
		oracle,
		AllowableOptimisations::defaultOptimisations.
			enableassumePrivateStack().
			enablenoExtend(),
		ALLOW_GC);

	FILE *f = fopen(argv[4], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);

	return 0;
}
