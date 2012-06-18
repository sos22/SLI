#include <sys/fcntl.h>
#include <err.h>
#include <unistd.h>

#include "sli.h"
#include "oracle.hpp"
#include "state_machine.hpp"
#include "eval_state_machine.hpp"
#include "allowable_optimisations.hpp"

int
main(int argc, char *argv[])
{
	if (argc < 1)
		errx(1, "need to know where to read the state machine from");

	init_sli();

	VexPtr<OracleInterface> oracle(new Oracle(NULL, NULL, NULL));

	VexPtr<StateMachine, &ir_heap> sm(readStateMachine(open(argv[1], O_RDONLY)));
	VexPtr<IRExpr, &ir_heap> survive;
	VexPtr<IRExpr, &ir_heap> nullExpr(NULL);

	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.enableignoreSideEffects();

	survive = survivalConstraintIfExecutedAtomically(sm, nullExpr, oracle, false, opt, ALLOW_GC);

	survive = simplifyIRExpr(survive, opt);

	ppIRExpr(survive, stdout);
	printf("\n");

	return 0;
}
