#ifndef zapBindersAndFreeVariables_hpp__
#define zapBindersAndFreeVariables_hpp__

#include "libvex_ir.h"

class FreeVariableMap;
class StateMachine;

void zapBindersAndFreeVariables(FreeVariableMap &m, StateMachine *sm);
IRExpr *zapFreeVariables(IRExpr *src, FreeVariableMap &fv);

#endif /* !zapBindersAndFreeVariables_hpp__ */
