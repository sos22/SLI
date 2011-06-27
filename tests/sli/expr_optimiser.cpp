#include "sli.h"
#include "simplify_irexpr.hpp"

int
main(int argc, char *argv[])
{
	init_sli();
	sanity_check_optimiser();
	return 0;
}
