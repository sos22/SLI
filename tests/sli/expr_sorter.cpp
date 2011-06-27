#include "sli.h"
#include "simplify_irexpr.hpp"

int
main(int argc, char *argv[])
{
	init_sli();
	sanity_check_irexpr_sorter();
	return 0;
}
