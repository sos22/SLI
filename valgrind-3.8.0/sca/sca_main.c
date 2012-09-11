
/*--------------------------------------------------------------------*/
/*--- Nulgrind: The minimal Valgrind tool.               sca_main.c ---*/
/*--------------------------------------------------------------------*/

/*
  This file is part of Nulgrind, the minimal Valgrind tool,
  which does no instrumentation or analysis.

  Copyright (C) 2002-2012 Nicholas Nethercote
  njn@valgrind.org

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License as
  published by the Free Software Foundation; either version 2 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
  02111-1307, USA.

  The GNU General Public License is contained in the file COPYING.
*/

#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_vki.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_options.h"
#include "pub_tool_aspacemgr.h"
#include "vki/vki-scnums-amd64-linux.h"
#include "libvex_emwarn.h"
#include "libvex_guest_amd64.h"

static Long sca_db_size;
static unsigned long database;

#define DATABASE_MAGIC 0xbb8d4fde1557ab1ful
#define NR_HEADS 524243

struct hash_head {
	unsigned long offset;
	int nr_slots;
};
struct hash_entry {
	unsigned char aliases[16];
	unsigned char stackHasLeaked;
};

static void sca_post_clo_init(void)
{
	if (database == 0)
		VG_(tool_panic)("No database specified\n");
}

static int
hash_rip(unsigned long h)
{
	while (h >= NR_HEADS)
		h = (h / NR_HEADS) ^ (h % NR_HEADS);
	return h;
}

static VexEmWarn
sca_instr_cb(VexGuestAMD64State* vex_state)
{
	int h = hash_rip(vex_state->guest_RIP);
	const struct hash_head *hh = (const struct hash_head *)(database + 8 + 16 * h);
	int nr_slots = hh->nr_slots;
	const unsigned long *rip_area = (const unsigned long *)(database + hh->offset);
	int i;
	for (i = 0; i < nr_slots; i++) {
		if (rip_area[i] == 0)
			VG_(tool_panic)("Corrupt database\n");
		if (rip_area[i] == vex_state->guest_RIP)
			break;
	}
	if (i == nr_slots) {
		const NSegment *seg = VG_(am_find_nsegment)(vex_state->guest_RIP);
		HChar *n;
		n = VG_(am_get_filename)(seg);
		if (n && VG_(strncmp)(n, "/lib/", 5)) {
			VG_(printf)("WARNING: No database entry for RIP %llx (%s)\n", vex_state->guest_RIP, n);
		}
		return EmWarn_NONE;
	}
//	VG_(printf)("Found database entry for RIP %llx (%d, %d)\n", vex_state->guest_RIP, i, h);
	return EmWarn_NONE;
}

static IRSB *
sca_instrument ( VgCallbackClosure* closure,
		 IRSB* sbIn,
		 VexGuestLayout* layout, 
		 VexGuestExtents* vge,
		 IRType gWordTy, IRType hWordTy )
{
	IRSB *sbOut = deepCopyIRSBExceptStmts(sbIn);
	int i;
	IRCallee *cee;
	IRDirty *d;
	IRStmt *stmt;
	cee = mkIRCallee(0, "sca_instr", sca_instr_cb);
	d = emptyIRDirty();
	d->cee = cee;
	d->guard = IRExpr_Const(IRConst_U1(1));
	d->args = mkIRExprVec_0();
	d->tmp = IRTemp_INVALID;
	d->mFx = Ifx_None;
	d->mAddr = NULL;
	d->mSize = 0;
	d->needsBBP = True;
	d->nFxState = 1;
	d->fxState[0].fx = Ifx_Read;
	d->fxState[0].offset = 0;
	d->fxState[0].size = sizeof(VexGuestAMD64State);
	d->fxState[0].nRepeats = 0;
	d->fxState[0].repeatLen = 0;
	stmt = IRStmt_Dirty(d);
	for (i = 0; i < sbIn->stmts_used; i++) {
		addStmtToIRSB(sbOut, sbIn->stmts[i]);
		if (sbIn->stmts[i]->tag == Ist_IMark)
			addStmtToIRSB(sbOut, stmt);
	}
	return sbOut;
}

static void sca_fini(Int exitcode)
{
}

static Bool
sca_process_command_line_option(Char *opt)
{
	Char *pathname;
	if (VG_STR_CLO(opt, "--database", pathname)) {
		int fd = VG_(fd_open)(pathname, VKI_O_RDONLY, 0);
		struct vg_stat s;
		unsigned long mmap_addr;
		register unsigned long r10 asm ("r10");
		register unsigned long r8 asm("r8");
		register unsigned long r9 asm("r9");
		if (fd < 0) {
			VG_(printf)("Cannot open %s\n", pathname);
			VG_(tool_panic)("Cannot open database");
		}
		if (VG_(fstat)(fd, &s) < 0)
			VG_(tool_panic)("Cannot stat database");
		sca_db_size = s.size;

		r10 = VKI_MAP_PRIVATE;
		r8 = fd;
		r9 = 0;
		asm ("syscall\n"
		     : "=a" (mmap_addr)
		     : "0" (__NR_mmap),
		       "D" (0),
		       "S" ((s.size + 4095ul) & ~4095ul),
		       "d" (VKI_PROT_READ),
		       "r" (r10),
		       "r" (r8),
		       "r" (r9)
		     : "memory", "flags");
		if ((long)mmap_addr < 0)
			VG_(tool_panic)("Cannot mmap database");
		if (*(unsigned long *)mmap_addr != DATABASE_MAGIC)
			VG_(tool_panic)("Database contains bad magic number");
		database = mmap_addr;
		VG_(close)(fd);
		return True;
	} else {
		return False;
	}
}

static void
sca_print_usage(void)
{
	VG_(printf)("Only tool argument is --database=..., the path to the database\n");
}

static void
sca_print_debug_usage(void)
{
}

static void
sca_pre_clo_init(void)
{
	VG_(details_name)            ("SCA");
	VG_(details_version)         (NULL);
	VG_(details_description)     ("the minimal Valgrind tool");
	VG_(details_copyright_author)(
		"Copyright (C) 2002-2012, and GNU GPL'd, by Nicholas Nethercote.");
	VG_(details_bug_reports_to)  (VG_BUGS_TO);

	VG_(details_avg_translation_sizeB) ( 275 );

	VG_(basic_tool_funcs)        (sca_post_clo_init,
				      sca_instrument,
				      sca_fini);

	VG_(needs_command_line_options) (sca_process_command_line_option,
					 sca_print_usage,
					 sca_print_debug_usage);
}

VG_DETERMINE_INTERFACE_VERSION(sca_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
