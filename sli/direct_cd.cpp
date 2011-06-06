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

static bool
instructionIsInteresting(const InstructionSet &i, unsigned long r)
{
	return i.rips.count(r) != 0;
}

static unsigned long
wrappedRipToRip(unsigned long r)
{
	return r;
}

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

	considerInstructionSequence(previousInstructions,
				    ii,
				    oracle,
				    proximal->rip.rip,
				    ms);

	return 0;
}
