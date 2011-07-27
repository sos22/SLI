#include <err.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include "libvex.h"
#include "libvex_ir.h"
#include "libvex_emwarn.h"
#include "libvex_guest_amd64.h"
#include "guest_generic_bb_to_IR.h"
#include "guest_amd64_defs.h"

static __attribute__ ((noreturn)) void
failure_exit(void)
{
	abort();
}

static void log_bytes(const char *buf, Int nbytes)
{
	fwrite(buf, nbytes, 1, stdout);
}

static Bool chase_into_ok(void *ignore1, Addr64 ignore2)
{
	return False;
}

void fixup_expression_table(void)
{
}

void dbg_break(const char *msg, ...) {}

int
main()
{
	VexControl vcon;
	IRSB *irsb;
	VexArchInfo archinfo_guest;
	VexAbiInfo abiinfo_both;
	VexGuestExtents vge;

	LibVEX_default_VexControl(&vcon);
	vcon.iropt_level = 0;
	vcon.iropt_unroll_thresh = 0;
	vcon.guest_chase_thresh = 0;
	LibVEX_Init(failure_exit, log_bytes, 0, 0, &vcon);

	LibVEX_default_VexArchInfo(&archinfo_guest);
	LibVEX_default_VexAbiInfo(&abiinfo_both);
	abiinfo_both.guest_stack_redzone_size = 128;

	TrivMemoryFetcher tmf((const UChar *)main,
			      99,
			      128);
	irsb = bb_to_IR(97,
			&vge,
			NULL, /* Context for chase_into_ok */
			disInstr_AMD64,
			tmf,
			(Addr64)main, /* guest code original rip */
			chase_into_ok,
			False, /* host bigendian */
			VexArchAMD64,
			&archinfo_guest,
			&abiinfo_both,
			Ity_I64, /* guest word type */
			False, /* do_self_check */
			NULL, /* preamble */
			0, /* self check start */
			0); /* self check len */

	if (!irsb)
		errx(1, "decoding self");

	ppIRSB(irsb, stdout);

	return 0;
}
