/* Debug break points.  These must be compiled with optimisations
 * off. */
#include "sli.h"

static void
dbg_brk(const char *msg)
{
}

void
dbg_break(const char *fmt, ...)
{
	va_list args;
	va_start(args, fmt);
	char *r;
	int x = vasprintf(&r, fmt, args);
	va_end(args);
	(void)x;

	dbg_brk(r);
}
