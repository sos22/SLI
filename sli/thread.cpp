#include "sli.h"

const ThreadId ThreadId::invalidTid;

RegisterSet::RegisterSet(VexGuestAMD64State const&r)
{
	for (unsigned x = 0; x < NR_REGS; x++)
		registers[x] = ((unsigned long *)&r)[x];
}

Thread *Thread::dupeSelf() const
{
	return new Thread(*this);
}

void
Thread::pretty_print(void) const
{
	printf("Thread tid %d, %s%s\n",
	       tid._tid(),
#define f(n) n ? "(" #n ")" : ""
	       f(exitted),
	       f(crashed));
#undef f
	if (currentIRSB) {
		printf("Current IRSB:\n");
		ppIRSB(currentIRSB, stdout);
		printf("Offset %d, origin %lx\n",
		       currentIRSBOffset,
		       currentIRSBRip);
	}
}
