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

	VexPtr<Oracle> oracle(new Oracle(NULL, NULL, NULL));

	VexPtr<StateMachine, &ir_heap> sm(readStateMachine(open(argv[1], O_RDONLY)));
	VexPtr<IRExpr, &ir_heap> survive;
	
	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.enableignoreSideEffects();

	survive = survivalConstraintIfExecutedAtomically(sm, oracle, opt, ALLOW_GC);

	survive = simplifyIRExpr(survive, opt);

	ppIRExpr(survive, stdout);
	printf("\n");

	return 0;
}
