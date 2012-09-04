#include <sys/fcntl.h>
#include <err.h>
#include <unistd.h>

#include "sli.h"
#include "oracle.hpp"
#include "state_machine.hpp"
#include "eval_state_machine.hpp"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"
#include "alloc_mai.hpp"

int
main(int argc, char *argv[])
{
	if (argc < 4)
		errx(1, "not enough arguments");

	init_sli();

	VexPtr<StateMachine, &ir_heap> sm(readStateMachine(0));

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);
	VexPtr<MaiMap, &ir_heap> mai(MaiMap::fromFile(sm, argv[4]));

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack();
	sm = optimiseStateMachine(mai, sm, opt, oracle, true, ALLOW_GC);
	printStateMachine(sm, stdout);

	return 0;
}
