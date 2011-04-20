#include <stdio.h>

#include "sli.h"
#include "state_machine.hpp"
#include "pickle.hpp"
int
main(int argc, char *argv[])
{
	init_sli();

	FILE *f = fopen(argv[1], "r");
	StateMachine *sm = unpickleStateMachine(f);

	printStateMachine(sm, stdout);

	return 0;
}
