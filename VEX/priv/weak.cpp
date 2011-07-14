#include <stdio.h>

#include "libvex_ir.h"

void ppStateMachineSideEffectMemoryAccess(StateMachineSideEffectMemoryAccess *, FILE *) __attribute__((weak));
void
ppStateMachineSideEffectMemoryAccess(StateMachineSideEffectMemoryAccess *smsema, FILE *f)
{
	fprintf(f, "SMSEM{%p}", smsema);
}
