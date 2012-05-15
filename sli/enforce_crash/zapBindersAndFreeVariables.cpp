#include "sli.h"
#include "zapBindersAndFreeVariables.hpp"
#include "offline_analysis.hpp"

void
zapBindersAndFreeVariables(StateMachine *)
{
}

IRExpr *
zapFreeVariables(IRExpr *src)
{
	return src;
}
