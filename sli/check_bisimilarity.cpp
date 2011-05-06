#include <stdio.h>

#include "sli.h"
#include "state_machine.hpp"
#include "pickle.hpp"

int
main(int argc, char *argv[])
{
	init_sli();
	StateMachine *sm1 = unpickleStateMachine(fopen(argv[1], "r"));
	StateMachine *sm2 = unpickleStateMachine(fopen(argv[2], "r"));
	if (stateMachinesBisimilar(sm1, sm2))
		printf("similar\n");
	else
		printf("not similar\n");
	return 0;
}
