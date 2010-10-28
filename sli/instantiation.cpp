#include "sli.h"

#define MK_INTERP(t)				\
	MK_INTERPRETER(t);


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

