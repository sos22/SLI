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

#define MK_INTERP(t)				\
	MK_MACHINE_STATE(t);			\
	MK_INTERPRETER(t);			\
	MK_THREAD(t);				\
	MK_MEM_LOG(t);				\
	MK_MEMTRACE_POOL(t);			\
	MK_MEMTRACE(t);				\
	MK_LOGWRITER(t);			\
	MK_ADDRESS_SPACE(t);			\
	MK_LOGREADER(t)

static unsigned long force(unsigned long x)
{
	return x;
}

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

template<>
unsigned long import_ait(unsigned long x)
{
	return x;
}

MK_INTERP(unsigned long);

static unsigned long force(abstract_interpret_value aiv)
{
	return aiv.v;
}

#define OP(x)								\
	static abstract_interpret_value operator x(const abstract_interpret_value &aiv, \
						   const abstract_interpret_value & cnt) \
	{								\
		abstract_interpret_value res;				\
		res.v = aiv.v x cnt.v;					\
		return res;						\
	}

OP(<<)
OP(>>)
OP(&)
OP(|)
OP(^)
OP(+)
OP(*)
OP(/)
OP(%)
OP(-)
OP(>=)
OP(<)
OP(<=)
OP(==)
OP(!=)
OP(||)
OP(&&)

static abstract_interpret_value operator !(const abstract_interpret_value &aiv)
{
	abstract_interpret_value res;
	res.v = !aiv.v;
	return res;
}

static abstract_interpret_value operator ~(const abstract_interpret_value &aiv)
{
	abstract_interpret_value res;
	res.v = ~aiv.v;
	return res;
}

static abstract_interpret_value signed_shift_right(abstract_interpret_value x, abstract_interpret_value y)
{
	abstract_interpret_value v;
	v.v = (long)x.v >> y.v;
	return v;
}

static abstract_interpret_value signed_le(abstract_interpret_value x, abstract_interpret_value y)
{
	abstract_interpret_value v;
	v.v = (long)x.v <= (long)y.v;
	return v;
}
	
static abstract_interpret_value signed_l(abstract_interpret_value x, abstract_interpret_value y)
{
	abstract_interpret_value v;
	v.v = (long)x.v < (long)y.v;
	return v;
}
	
static abstract_interpret_value operator &=(abstract_interpret_value &lhs,
					    const abstract_interpret_value &rhs)
{
	lhs.v &= rhs.v;
	return lhs;
}

static abstract_interpret_value operator |=(abstract_interpret_value &lhs,
					    const abstract_interpret_value &rhs)
{
	lhs.v |= rhs.v;
	return lhs;
}

static abstract_interpret_value operator ^=(abstract_interpret_value &lhs,
					    const abstract_interpret_value &rhs)
{
	lhs.v ^= rhs.v;
	return lhs;
}

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
		registers[x] = abstract_interpret_value( ((unsigned long *)&r)[x] );
}

template <>
abstract_interpret_value abstract_interpret_value::import(unsigned long x)
{
	abstract_interpret_value v;
	v.v = x;
	return v;
}

template<>
abstract_interpret_value import_ait(unsigned long x)
{
	return abstract_interpret_value::import(x);
}

template<>
unsigned long import_ait(abstract_interpret_value v)
{
	return v.v;
}

MK_INTERP(abstract_interpret_value);


MK_MACH_CONVERTOR(unsigned long, abstract_interpret_value);
