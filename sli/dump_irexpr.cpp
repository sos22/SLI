#include <stdio.h>

#include "sli.h"
#include "pickle.hpp"
int
main(int argc, char *argv[])
{
	init_sli();

	FILE *f = fopen(argv[1], "r");
	IRExpr *e = unpickleIRExpr(f);

	ppIRExpr(e, stdout);

	return 0;
}
