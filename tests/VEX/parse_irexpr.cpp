#include <err.h>

#include "libvex.h"
#include "libvex_ir.h"

static __attribute__ ((noreturn)) void
failure_exit(void)
{
	abort();
}

static void log_bytes(const char *buf, Int nbytes)
{
	fwrite(buf, nbytes, 1, stdout);
}

void dbg_break(const char *msg, ...) {}

int
main(int argc, char *argv[])
{
	VexControl vcon;
	IRExpr *ir;

	LibVEX_default_VexControl(&vcon);
	vcon.iropt_level = 0;
	vcon.iropt_unroll_thresh = 0;
	vcon.guest_chase_thresh = 0;
	LibVEX_Init(failure_exit, log_bytes, 0, 0, &vcon);

	const char *s;

	if (!parseIRExpr(&ir, argv[1], &s))
		errx(1, "parsing %s as IR expression", argv[1]);
	printf("Suffix: %s\n", s);
	ppIRExpr(ir, stdout);
	printf("\n");

	return 0;
}
