#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"
#include "state_machine.hpp"

int
main(int argc, char *argv[])
{
	StateMachine *sm;

	init_sli();
	SMScopes scopes;
	if (!scopes.read(argv[1]))
		err(1, "reading %s as scopes", argv[1]);
	sm = readStateMachine(&scopes, 0);
	printStateMachine(sm, stdout);

	return 0;
}
