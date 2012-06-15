/* Like canonicalise_crash_summary, but use some more aggressive
   canonicalisations which are more computationally expensive. */
#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "intern.hpp"
#include "allowable_optimisations.hpp"
#include "offline_analysis.hpp"

static StateMachine *
removeMarkers(VexPtr<StateMachine, &ir_heap> sm,
	      const AllowableOptimisations &opt,
	      VexPtr<Oracle> &oracle,
	      GarbageCollectionToken token)
{
	std::vector<StateMachineSideEffecting *> states;
	enumStates(sm, &states);
	for (auto it = states.begin(); it != states.end(); it++) {
		auto s = *it;
		if (s->sideEffect &&
		    (s->sideEffect->type == StateMachineSideEffect::StartFunction ||
		     s->sideEffect->type == StateMachineSideEffect::EndFunction))
			s->sideEffect = NULL;
	}
	return optimiseStateMachine(sm, opt, oracle, false, token);
}

static CrashSummary *
canonicalise_crash_summary(VexPtr<CrashSummary, &ir_heap> input,
			   VexPtr<Oracle> oracle,
			   const AllowableOptimisations &optIn,
			   GarbageCollectionToken token)
{
	VexPtr<StateMachine, &ir_heap> sm(input->loadMachine);
	input->loadMachine = removeMarkers(sm, optIn, oracle, token);
	input->loadMachine = removeAssertions(input->loadMachine, optIn, oracle, false, token);
	sm = input->storeMachine;
	input->storeMachine = removeAssertions(input->storeMachine, optIn, oracle, false, token);
	input->storeMachine = removeMarkers(sm, optIn, oracle, token);

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
