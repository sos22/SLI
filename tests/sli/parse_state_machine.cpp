#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"
#include "state_machine.hpp"

int
main()
{
	StateMachine *sm;

	init_sli();
	sm = readStateMachine(0);
	printStateMachine(sm, stdout);

	return 0;
}
