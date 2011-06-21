#include <sys/fcntl.h>
#include <unistd.h>

#include "sli.h"
#include "oracle.hpp"
#include "state_machine.hpp"
#include "eval_state_machine.hpp"

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<StateMachine> sm(readStateMachine(0));

	sm->sanity_check();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack();
	bool ignore;
	sm = sm->optimise(opt, oracle, &ignore);
	printStateMachine(sm, stdout);

	sm->sanity_check();

	return 0;
}
