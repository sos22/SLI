#include <err.h>
#include <stdio.h>

#include "sli.h"
#include "oracle.hpp"
#include "allowable_optimisations.hpp"
#include "sat_checker.hpp"

int
main()
{
	init_sli();
	IRExpr *e = readIRExpr(0);
	if (satisfiable(e, AllowableOptimisations::defaultOptimisations)) {
		printf("Satisfiable\n");
		return 0;
	} else {
		printf("Not satisfiable\n");
		return 1;
	}
}
