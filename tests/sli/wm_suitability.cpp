#include <sys/fcntl.h>
#include <err.h>
#include <unistd.h>

#include "sli.h"
#include "oracle.hpp"
#include "state_machine.hpp"
#include "eval_state_machine.hpp"

int
main(int argc, char *argv[])
{
	if (argc < 4)
		errx(1, "not enough arguments");
	init_sli();

	VexPtr<Oracle> oracle(new Oracle(NULL, NULL, argv[1]));

	VexPtr<StateMachine, &ir_heap> readMachine(readStateMachine(open(argv[2], O_RDONLY)));
	VexPtr<StateMachine, &ir_heap> writeMachine(readStateMachine(open(argv[3], O_RDONLY)));
	VexPtr<IRExpr, &ir_heap> survive(readIRExpr(open(argv[4], O_RDONLY)));
	
	IRExpr *assumption = writeMachineCrashConstraint(writeMachine,
							 survive,
							 IRExpr_Const(IRConst_U1(1)),
							 IRExpr_Const(IRConst_U1(0)),
							 AllowableOptimisations::defaultOptimisations);
	if (!assumption) {
		printf("<machine unsuitable>\n");
	} else {
		ppIRExpr(assumption, stdout);
		printf("\n");
	}

	return 0;
}
