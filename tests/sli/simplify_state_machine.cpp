#include <sys/fcntl.h>
#include <unistd.h>

#include "sli.h"
#include "oracle.hpp"
#include "state_machine.hpp"
#include "eval_state_machine.hpp"
#include "offline_analysis.hpp"

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<StateMachine, &ir_heap> sm(readStateMachine(0));

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack();
	sm = optimiseStateMachine(sm, opt, oracle, true, true, ALLOW_GC);
	printStateMachine(sm, stdout);

	return 0;
}
