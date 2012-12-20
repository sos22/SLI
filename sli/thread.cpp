#include "sli.h"

const ThreadId ThreadId::invalidTid;

RegisterSet::RegisterSet(VexGuestAMD64State const&r)
{
	for (unsigned x = 0; x < NR_REGS; x++)
		registers[x] = ((unsigned long *)&r)[x];
}

void
Thread::pretty_print(void) const
{
	printf("Thread tid %d%s\n",
	       tid._tid(), crashed ? " crashed" : "");
}
