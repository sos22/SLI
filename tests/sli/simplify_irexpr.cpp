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

	IRExpr *exp = readIRExpr(open(argv[1], O_RDONLY));
	
	AllowableOptimisations opt =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack()
		.enableignoreSideEffects();

	exp = simplifyIRExpr(exp, opt);

	ppIRExpr(exp, stdout);
	printf("\n");

	return 0;
}
