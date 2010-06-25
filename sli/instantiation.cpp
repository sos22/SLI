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

template <>
void mulls64(struct expression_result<abstract_interpret_value> *dest,
	     const struct expression_result<abstract_interpret_value> &src1,
	     const struct expression_result<abstract_interpret_value> &src2)
{
	expression_result<unsigned long> d, s1, s2;
	s1.lo = src1.lo.v;
	s1.hi = src1.hi.v;
	s2.lo = src2.lo.v;
	s2.hi = src2.hi.v;

	mulls64(&d, s1, s2);
	dest->lo.v = d.lo;
	dest->hi.v = d.hi;
}

template<>
RegisterSet<abstract_interpret_value>::RegisterSet(const VexGuestAMD64State &r)
{
	for (unsigned x = 0;
	     x < NR_REGS;
	     x++)
		registers[x] = mkConst<abstract_interpret_value>( ((unsigned long *)&r)[x] );
}

static inline abstract_interpret_value signed_shift_right(abstract_interpret_value x, abstract_interpret_value y)
{
	abstract_interpret_value v;
	memset(&v, 0, sizeof(v));
	v.v = (long)x.v >> y.v;
	v.origin = rshiftarith::get(x.origin, y.origin);
	sanity_check_ait(v);
	return v;
}

static inline abstract_interpret_value signed_le(abstract_interpret_value x, abstract_interpret_value y)
{
	abstract_interpret_value v;
	Expression *c = ConstExpression::get(0x8000000000000000ul);
	memset(&v, 0, sizeof(v));
	v.v = (long)x.v <= (long)y.v;
	v.origin = lessthanequals::get(plus::get(x.origin, c),
				       plus::get(y.origin, c));
	return v;
}
	
static inline abstract_interpret_value signed_l(abstract_interpret_value x, abstract_interpret_value y)
{
	abstract_interpret_value v;
	Expression *c = ConstExpression::get(0x8000000000000000ul);
	memset(&v, 0, sizeof(v));
	v.v = (long)x.v < (long)y.v;
	v.origin = lessthan::get(plus::get(x.origin, c),
				 plus::get(y.origin, c));
	return v;
}
	
MK_INTERP(abstract_interpret_value);


MK_MACH_CONVERTOR(unsigned long, abstract_interpret_value);
