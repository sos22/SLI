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
	internStateMachineTable t;
	input->loadMachine = internStateMachine(input->loadMachine, t);
	input->storeMachine = internStateMachine(input->storeMachine, t);
	input->verificationCondition = internIRExpr(input->verificationCondition, t);

	std::set<DynAnalysisRip> nonLocalLoads;
	{
		std::set<StateMachineSideEffectLoad *> loads;
		std::set<StateMachineSideEffectStore *> stores;
		enumSideEffects(input->loadMachine, loads);
		enumSideEffects(input->storeMachine, loads);
		enumSideEffects(input->storeMachine, stores);

		for (auto it = loads.begin(); it != loads.end(); it++) {
			StateMachineSideEffectLoad *smsel = *it;
			if (nonLocalLoads.count(DynAnalysisRip(smsel->rip.rip.rip)))
				continue;
			for (auto it2 = stores.begin(); it2 != stores.end(); it2++) {
				StateMachineSideEffectStore *smses = *it2;
				if (oracle->memoryAccessesMightAliasCrossThread(
					    smsel->rip.rip.rip,
					    smses->rip.rip.rip)) {
					nonLocalLoads.insert(DynAnalysisRip(smsel->rip.rip.rip));
					break;
				}
			}
		}
	}

	AllowableOptimisations opt = optIn.setnonLocalLoads(&nonLocalLoads);
	VexPtr<StateMachine, &ir_heap> sm(input->loadMachine);
	input->loadMachine = optimiseStateMachine(sm,
						  opt,
						  oracle,
						  false,
						  token);
	sm = input->storeMachine;
	input->storeMachine = 
		optimiseStateMachine(sm,
				     opt,
				     oracle,
				     false,
				     token);
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
