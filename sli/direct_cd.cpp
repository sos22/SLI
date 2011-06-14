/* Re-implementation of direct which tries to work off of just a core
   dump, rather than needing the full trace. */
#include <err.h>

#include <algorithm>
#include <queue>
#include <map>
#include <set>

#include "sli.h"
#include "nd_chooser.h"
#include "range_tree.h"
#include "pickle.hpp"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "simplify_irexpr.hpp"
#include "eval_state_machine.hpp"
#include "crash_reason.hpp"
#include "inferred_information.hpp"
#include "offline_analysis.hpp"

static FILE *
fopenf(const char *mode, const char *fmt, ...)
{
	va_list args;
	char *path;
	FILE *res;

	va_start(args, fmt);
	vasprintf(&path, fmt, args);
	va_end(args);

	res = fopen(path, mode);
	free(path);
	return res;
}

class DumpFix : public FixConsumer {
public:
	void operator()(VexPtr<CrashSummary, &ir_heap> &summary, GarbageCollectionToken token);
};

void
DumpFix::operator()(VexPtr<CrashSummary, &ir_heap> &summary, GarbageCollectionToken token)
{
	printf("Load machine:\n");
	printStateMachine(summary->loadMachine, stdout);

	for (std::vector<CrashSummary::StoreMachineData *>::iterator it = summary->storeMachines.begin();
	     it != summary->storeMachines.end();
	     it++) {
		CrashSummary::StoreMachineData *smd = *it;
		printf("Store machine:\n");
		printStateMachine(smd->machine, stdout);
		printf("Remote macro sections:\n");
		for (std::vector<CrashSummary::StoreMachineData::macroSectionT>::iterator it2 = 
			     smd->macroSections.begin();
		     it2 != smd->macroSections.end();
		     it2++) {
			printf("\t");
			it2->first->prettyPrint(stdout);
			printf(" -> ");
			it2->second->prettyPrint(stdout);
			printf("\n");
		}
	}
	dbg_break("Have remote critical sections");
}

int
main(int argc, char *argv[])
{
	if (argc <= 1)
		errx(1, "need at least one argument");

	init_sli();

	if (!strcmp(argv[1], "--check-sorter")) {
		sanity_check_irexpr_sorter();
		return 0;
	}
	if (!strcmp(argv[1], "--check-optimiser")) {
		sanity_check_optimiser();
		return 0;
	}

	VexPtr<MachineState> ms(MachineState::readCoredump(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(CRASHED_THREAD)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));

	VexPtr<CrashReason, &ir_heap> proximal(getProximalCause(ms, thr->regs.rip(), thr));
	if (!proximal)
		errx(1, "cannot get proximal cause of crash");
	proximal = backtrackToStartOfInstruction(CRASHING_THREAD, proximal, ms->addressSpace);

	VexPtr<InferredInformation> ii(new InferredInformation(oracle));
	ii->addCrashReason(proximal);

	std::vector<unsigned long> previousInstructions;
	oracle->findPreviousInstructions(previousInstructions);

	DumpFix df;
	considerInstructionSequence(previousInstructions,
				    ii,
				    oracle,
				    proximal->rip.rip,
				    ms,
				    df,
				    ALLOW_GC);

	return 0;
}
