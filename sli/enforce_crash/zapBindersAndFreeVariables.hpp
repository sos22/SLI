#ifndef zapBindersAndFreeVariables_hpp__
#define zapBindersAndFreeVariables_hpp__

#include "libvex_ir.h"

class StateMachine;

void zapBindersAndFreeVariables(StateMachine *sm);
IRExpr *zapFreeVariables(IRExpr *src);

#endif /* !zapBindersAndFreeVariables_hpp__ */
