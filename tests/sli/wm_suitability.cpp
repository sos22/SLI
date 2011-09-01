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

	VexPtr<Oracle> oracle(new Oracle(NULL, NULL, argv[1]));

	VexPtr<StateMachine, &ir_heap> readMachine(readStateMachine(open(argv[2], O_RDONLY)));
	VexPtr<StateMachine, &ir_heap> writeMachine(readStateMachine(open(argv[3], O_RDONLY)));
	VexPtr<IRExpr, &ir_heap> survive(readIRExpr(open(argv[4], O_RDONLY)));
	
	IRExpr *assumption = writeMachineSuitabilityConstraint(readMachine, writeMachine, survive, oracle,
							       AllowableOptimisations::defaultOptimisations,
							       ALLOW_GC);
	if (!assumption) {
		printf("<machine unsuitable>\n");
	} else {
		ppIRExpr(assumption, stdout);
		printf("\n");
	}

	return 0;
}
