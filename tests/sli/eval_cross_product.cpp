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

	VexPtr<StateMachine, &ir_heap> readMachine(readStateMachine(open(argv[1], O_RDONLY)));
	VexPtr<StateMachine, &ir_heap> writeMachine(readStateMachine(open(argv[2], O_RDONLY)));
	VexPtr<IRExpr, &ir_heap> assumption(readIRExpr(open(argv[3], O_RDONLY)));
	
	bool mightCrash;
	bool mightSurvive;

	evalCrossProductMachine(readMachine, writeMachine, oracle, assumption,
				AllowableOptimisations::defaultOptimisations,
				&mightSurvive, &mightCrash, ALLOW_GC);
	printf("Might survive %d, might crash %d\n",
	       mightSurvive, mightCrash);

	return 0;
}
