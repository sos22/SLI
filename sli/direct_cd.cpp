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
#include "genfix.hpp"

class DumpFix : public FixConsumer {
public:
	VexPtr<Oracle> &oracle;
	void operator()(VexPtr<CrashSummary, &ir_heap> &summary, GarbageCollectionToken token);
	DumpFix(VexPtr<Oracle> &_oracle)
		: oracle(_oracle)
	{}
};

void
DumpFix::operator()(VexPtr<CrashSummary, &ir_heap> &summary, GarbageCollectionToken token)
{
	printCrashSummary(summary, stdout);
	char *s = buildPatchForCrashSummary(oracle, summary,
					    "patch");
	if (s)
		printf("Generates patch:\n#include \"patch_head.h\"\n\n%s\n\n#include \"patch_skeleton.c\"\n", s);
	else
		printf("Patch generation fails\n");
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

	DumpFix df(oracle);
	considerInstructionSequence(previousInstructions,
				    ii,
				    oracle,
				    proximal->rip.rip,
				    ms,
				    df,
				    true,
				    ALLOW_GC);

	return 0;
}
