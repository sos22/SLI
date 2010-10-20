#include "logwriter.cpp"
#include "replay.cpp"
#include "thread.cpp"
#include "machinestate.cpp"
#include "interpreter.cpp"
#include "syscalls.cpp"
#include "memlog.cpp"
#include "memtracepool.cpp"
#include "memorytrace.cpp"
#include "addressspace.cpp"
#include "logreader.cpp"
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

template <typename ait>
ait operator !=(expression_result<ait> a, expression_result<ait> b)
{
	return !(a == b);
}

template<typename ait>
ait operator ==(expression_result<ait> a, expression_result<ait> b)
{
	return a.lo == b.lo && a.hi == b.hi;
}

MK_INTERP(unsigned long);

