#include "sli.h"

template<> unsigned long
load_ait(unsigned long x, unsigned long addr, EventTimestamp when, EventTimestamp store,
	 unsigned long storeAddr, unsigned size)
{
	return x;
}


#include "logwriter.cpp"
#include "thread.cpp"
#include "machinestate.cpp"
#include "logreader.cpp"
#include "syscalls.cpp"
#include "memlog.cpp"
#include "memtracepool.cpp"
#include "memorytrace.cpp"
#include "addressspace.cpp"
#include "pmap.cpp"
#include "vamap.cpp"

#define MK_INTERP(t)				\
	MK_MACHINE_STATE(t);			\
	MK_INTERPRETER(t);			\
	MK_THREAD(t);				\
	MK_MEM_LOG(t);				\
	MK_MEMTRACE_POOL(t);			\
	MK_MEMTRACE(t);				\
	MK_LOGWRITER(t);			\
	MK_ADDRESS_SPACE(t);			\
	MK_LOGREADER(t);                        \
        MK_PMAP(t);				\
	MK_VAMAP(t)


static unsigned long signed_shift_right(unsigned long x, unsigned long y)
{
	return (long)x >> y;
}

static unsigned long signed_le(unsigned long x, unsigned long y)
{
	return (long)x <= (long)y;
}
	
static unsigned long signed_l(unsigned long x, unsigned long y)
{
	return (long)x < (long)y;
}

static unsigned long operator ==(expression_result a, expression_result b)
{
	return a.lo == b.lo && a.hi == b.hi;
}

static unsigned long operator !=(expression_result a, expression_result b)
{
	return !(a == b);
}

#include "interpreter.cpp"
#include "replay.cpp"

MK_INTERP(unsigned long);

