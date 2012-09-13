
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
#include "pub_tool_threadstate.h"
#include "pub_tool_mallocfree.h"
#include "vki/vki-scnums-amd64-linux.h"
#include "libvex_emwarn.h"
#include "libvex_guest_amd64.h"
#include "libvex_guest_offsets.h"

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

struct per_thread {
	struct per_thread *next;
	ThreadId tid;
	unsigned nr_stack_frames;
	unsigned stack_escape_flags[6];
	unsigned long frame_limit;
	unsigned long rip;
	const struct hash_entry *hash_entry;
};

#define THREAD_HASH_HEADS 31
static struct per_thread *
thread_heads[THREAD_HASH_HEADS];

static struct per_thread *
get_per_thread(void)
{
	ThreadId t = VG_(get_running_tid)();
	unsigned h = t;
	struct per_thread *cursor;
	while (h >= THREAD_HASH_HEADS)
		h = (h / THREAD_HASH_HEADS) ^ (h % THREAD_HASH_HEADS);
	cursor = thread_heads[h];
	while (cursor && cursor->tid != t)
		cursor = cursor->next;
	if (!cursor) {
		VG_(printf)("Allocate per-thread struct for %d\n", t);
		cursor = VG_(malloc)("per_thread", sizeof(*cursor));
		cursor->tid = t;
		cursor->frame_limit = 0;
		cursor->nr_stack_frames = 0;
		cursor->next = thread_heads[h];
		thread_heads[h] = cursor;
	}
	return cursor;
}

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
	const struct hash_entry *he;
	struct per_thread *const pt = get_per_thread();

	pt->hash_entry = NULL;
	pt->rip = vex_state->guest_RIP;
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
		if (n && VG_(strncmp)(n, "/lib/", 5) && VG_(strncmp)(n, "/usr/lib/", 9)) {
			VG_(printf)("WARNING: No database entry for RIP %llx (%s)\n", vex_state->guest_RIP, n);
		}
		return EmWarn_NONE;
	}

	he = (const struct hash_entry *)(database + hh->offset + hh->nr_slots * 8 + i * (sizeof(struct hash_entry)));
	for (i = 0; i < 16; i++) {
		if (!(he->aliases[i] & 4)) {
			unsigned long reg;
			switch (i) {
#define do_idx(idx, name)						\
				case idx:				\
					reg = vex_state->guest_ ## name; \
					break;
				do_idx(0, RAX)
				do_idx(1, RCX)
				do_idx(2, RDX)
				do_idx(3, RBX)
				do_idx(4, RSP)
				do_idx(5, RBP)
				do_idx(6, RSI)
				do_idx(7, RDI)
				do_idx(8, R8)
				do_idx(9, R9)
				do_idx(10, R10)
				do_idx(11, R11)
				do_idx(12, R12)
				do_idx(13, R13)
				do_idx(14, R14)
				do_idx(15, R15)
#undef do_idx
			default:
				VG_(tool_panic)("Badness");
			}
			if (reg >= vex_state->guest_RSP - 128 && reg < pt->frame_limit)
				VG_(printf)("Failed: Register %d isn't supposed to point at the stack at %llx, but does (%lx vs (%llx,%lx))\n",
					    i, vex_state->guest_RIP,
					    reg,
					    vex_state->guest_RSP - 128,
					    pt->frame_limit);
		}
	}
	if (!he->stackHasLeaked) {
		if (pt->nr_stack_frames <= 32 * 6 &&
		    pt->nr_stack_frames > 0 &&
		    pt->stack_escape_flags[(pt->nr_stack_frames - 1)/32] & (1u << ((pt->nr_stack_frames - 1) % 32)))
			VG_(printf)("Failed: stack was supposed to be private at %llx, but was found to be public\n",
				    vex_state->guest_RIP);
	}
	pt->hash_entry = he;
	return EmWarn_NONE;
}

static VexEmWarn
sca_deref_cb(unsigned long rsp, unsigned long value, unsigned long reg)
{
	struct per_thread *pt = get_per_thread();
	if (pt->hash_entry == NULL)
		return EmWarn_NONE;
	if (value >= rsp - 128 && value < pt->frame_limit)
		return EmWarn_NONE;
	if (reg > OFFSET_amd64_R15 || reg < OFFSET_amd64_RAX) {
		VG_(printf)("sca_deref_cb called on bad reg %lx\n", reg);
		VG_(tool_panic)("Dead");
	}
	if (!(pt->hash_entry->aliases[ (reg - OFFSET_amd64_RAX) / 8] & 2))
		VG_(printf)("Failed: deref register %lx (-> %lx) which isn't supposed to be a pointer (stack %lx, %lx) at %lx\n",
			    reg, value, rsp - 128, pt->frame_limit, pt->rip);
	return EmWarn_NONE;
}

static VexEmWarn
sca_call_cb(unsigned long rsp)
{
	struct per_thread *pt = get_per_thread();
	pt->frame_limit = rsp;
	if (pt->nr_stack_frames < 32 * 6)
		pt->stack_escape_flags[pt->nr_stack_frames / 32] &= ~(1u << (pt->nr_stack_frames % 32));
	pt->nr_stack_frames++;
	return EmWarn_NONE;
}

static VexEmWarn
sca_ret_cb(unsigned long rsp)
{
	struct per_thread *pt = get_per_thread();
	pt->frame_limit = rsp;
	if (pt->nr_stack_frames == 0)
		VG_(printf)("Warning: thread %d returned from more functions than it called?\n",
			    VG_(get_running_tid)());
	else
		pt->nr_stack_frames--;
	return EmWarn_NONE;
}

static VexEmWarn
sca_store_cb(unsigned long rsp, unsigned long ptr, unsigned long data)
{
	struct per_thread *pt = get_per_thread();
	int f = pt->nr_stack_frames - 1;
	if (f < 32 * 6 &&
	    (ptr < rsp - 128 || ptr >= pt->frame_limit) &&
	    data > rsp - 128 &&
	    data < pt->frame_limit)
		pt->stack_escape_flags[f / 32] |= (1u << (f % 32));
	return EmWarn_NONE;
}

struct deref_collection {
	int nr_tmps;
	IRTemp tmp[8];
	int nr_regs;
	unsigned regs[2];
};

static void
dc_add_tmp(struct deref_collection *dc, IRTemp tmp)
{
	int i;
	for (i = 0; i < dc->nr_tmps; i++)
		if (dc->tmp[i] == tmp)
			return;
	if (dc->nr_tmps == 8)
		VG_(tool_panic)("Out of tmp slots in deref collection\n");
	dc->tmp[dc->nr_tmps] = tmp;
	dc->nr_tmps++;
}

static void
dc_add_reg(struct deref_collection *dc, unsigned offset)
{
	int i;
	if (offset < OFFSET_amd64_RAX || offset > OFFSET_amd64_R15)
		return;
	for (i = 0; i < dc->nr_regs; i++)
		if (dc->regs[i] == offset)
			return;
	if (dc->nr_regs == 8)
		VG_(tool_panic)("Out of reg slots in deref collection\n");
	dc->regs[dc->nr_regs] = offset;
	dc->nr_regs++;
}

static void
processDerefPtr(struct deref_collection *dc, IRExpr *derefPtr)
{
	if (derefPtr->tag == Iex_Const)
		return;
	if (derefPtr->tag != Iex_RdTmp) {
		ppIRExpr(derefPtr);
		VG_(tool_panic)("Bad derefPtr\n");
	}
	dc_add_tmp(dc, derefPtr->Iex.RdTmp.tmp);
}

static void
processLoadExpr(struct deref_collection *dc, IRExpr *e)
{
	int j;
	switch (e->tag) {
	case Iex_Binder:
		return;
	case Iex_Get:
		return;
	case Iex_GetI:
		processLoadExpr(dc, e->Iex.GetI.ix);
		return;
	case Iex_RdTmp:
		return;
	case Iex_Qop:
		processLoadExpr(dc, e->Iex.Qop.details->arg4);
	case Iex_Triop:
		processLoadExpr(dc, e->Iex.Qop.details->arg1);
		processLoadExpr(dc, e->Iex.Qop.details->arg2);
		processLoadExpr(dc, e->Iex.Qop.details->arg3);
		return;
	case Iex_Binop:
		processLoadExpr(dc, e->Iex.Binop.arg2);
	case Iex_Unop:
		processLoadExpr(dc, e->Iex.Binop.arg1);
		return;
	case Iex_Load:
		processDerefPtr(dc, e->Iex.Load.addr);
		processLoadExpr(dc, e->Iex.Load.addr);
		return;
	case Iex_Const:
		return;
	case Iex_CCall:
		for (j = 0; e->Iex.CCall.args[j]; j++)
			processLoadExpr(dc, e->Iex.CCall.args[j]);
		return;
	case Iex_Mux0X:
		processLoadExpr(dc, e->Iex.Mux0X.cond);
		processLoadExpr(dc, e->Iex.Mux0X.expr0);
		processLoadExpr(dc, e->Iex.Mux0X.exprX);
		return;
	}
	VG_(tool_panic)("badness");
}

static void
addDependency(struct deref_collection *dc, IRExpr *iex, IRSB *sb)
{
	switch (iex->tag) {
	case Iex_Get:
		dc_add_reg(dc, iex->Iex.Get.offset);
		return;
	case Iex_RdTmp:
		dc_add_tmp(dc, iex->Iex.RdTmp.tmp);
		return;
	case Iex_Const:
		return;
	case Iex_Binop:
		switch (iex->Iex.Binop.op) {
		case Iop_Add64:
			addDependency(dc, iex->Iex.Binop.arg1, sb);
			addDependency(dc, iex->Iex.Binop.arg2, sb);
			return;
		case Iop_Sub64:
			addDependency(dc, iex->Iex.Binop.arg1, sb);
			return;
		case Iop_Shl64:
		case Iop_Sar64:
			return;
		default:
			break;
		}
		break;
	}
	ppIRExpr(iex);
	ppIRSB(sb);
	VG_(tool_panic)("Missing case in addDependency!");
}

static void
rewriteDcForStatement(struct deref_collection *dc, IRStmt *stmt, IRSB *sb)
{
	int i;

	switch (stmt->tag) {
	case Ist_NoOp:
		break;
	case Ist_IMark:
		break;
	case Ist_AbiHint:
		break;
	case Ist_Put:
		for (i = 0; i < dc->nr_regs; i++)
			if (dc->regs[i] == stmt->Ist.Put.offset)
				VG_(tool_panic)("Overly complex data flow in rewriteDcForStatement\n");
		break;
	case Ist_PutI:
		break;
	case Ist_WrTmp:
		for (i = 0; i < dc->nr_tmps; ) {
			if (dc->tmp[i] == stmt->Ist.WrTmp.tmp) {
				VG_(memmove)(dc->tmp + i, dc->tmp + i + 1, sizeof(IRTemp) * (dc->nr_tmps - i - 1));
				dc->nr_tmps--;
				addDependency(dc, stmt->Ist.WrTmp.data, sb);
			} else {
				i++;
			}
		}
		break;
	case Ist_Store:
		break;
	case Ist_CAS:
		break;
	case Ist_LLSC:
		break;
	case Ist_Dirty:
		for (i = 0; i < dc->nr_tmps; i++) {
			if (dc->tmp[i] == stmt->Ist.WrTmp.tmp) {
				ppIRStmt(stmt);
				VG_(tool_panic)("DC depends on dirty call!\n");
			}
		}
		break;
	case Ist_MBE:
		break;
	case Ist_Exit:
		break;
	}
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
	for (i = 0; i < sbIn->stmts_used && sbIn->stmts[i]->tag == Ist_NoOp; i++)
		;
	for (i = 0; i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark; i++)
		addStmtToIRSB(sbOut, sbIn->stmts[i]);
	if (i >= sbIn->stmts_used) {
		VG_(printf)("Huh? Block starts without an IMark?\n");
		ppIRSB(sbIn);
	}
	while (i < sbIn->stmts_used) {
		if (sbIn->stmts[i]->tag != Ist_IMark) {
			ppIRSB(sbIn);
			VG_(printf)("i = %d\n", i);
			VG_(tool_panic)("Dead99");
		}
		addStmtToIRSB(sbOut, sbIn->stmts[i]);
		addStmtToIRSB(sbOut, stmt);
		i++;
		while (i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark) {
			IRTemp rsp = Ity_INVALID;
			int j;
			struct deref_collection dc;

			VG_(memset)(&dc, 0, sizeof(dc));

			addStmtToIRSB(sbOut, sbIn->stmts[i]);

			/* Collect up all the derefed temporaries. */
			switch (sbIn->stmts[i]->tag) {
			case Ist_NoOp:
				break;
			case Ist_IMark:
				break;
			case Ist_AbiHint:
				processLoadExpr(&dc, sbIn->stmts[i]->Ist.AbiHint.base);
				processLoadExpr(&dc, sbIn->stmts[i]->Ist.AbiHint.nia);
				break;
			case Ist_Put:
				processLoadExpr(&dc, sbIn->stmts[i]->Ist.Put.data);
				break;
			case Ist_PutI:
				processLoadExpr(&dc, sbIn->stmts[i]->Ist.PutI.details->ix);
				processLoadExpr(&dc, sbIn->stmts[i]->Ist.PutI.details->data);
				break;
			case Ist_WrTmp:
				processLoadExpr(&dc, sbIn->stmts[i]->Ist.WrTmp.data);
				break;
			case Ist_Store:
				processDerefPtr(&dc, sbIn->stmts[i]->Ist.Store.addr);
				processLoadExpr(&dc, sbIn->stmts[i]->Ist.Store.addr);
				processLoadExpr(&dc, sbIn->stmts[i]->Ist.Store.data);
				break;
			case Ist_CAS:
				processDerefPtr(&dc, sbIn->stmts[i]->Ist.CAS.details->addr);
				processLoadExpr(&dc, sbIn->stmts[i]->Ist.CAS.details->expdLo);
				processLoadExpr(&dc, sbIn->stmts[i]->Ist.CAS.details->dataLo);
				break;
			case Ist_LLSC:
				VG_(tool_panic)("LLSC on amd64?");
			case Ist_Dirty:
				processLoadExpr(&dc, sbIn->stmts[i]->Ist.Dirty.details->guard);
				for (j = 0; sbIn->stmts[i]->Ist.Dirty.details->args[j]; j++)
					processLoadExpr(&dc, sbIn->stmts[i]->Ist.Dirty.details->args[j]);
				break;
			case Ist_MBE:
				break;
			case Ist_Exit:
				processLoadExpr(&dc, sbIn->stmts[i]->Ist.Exit.guard);
				break;
			}

			/* Now walk backwards from here to translate
			 * the derefed temporaries into derefed
			 * registers. */
			for (j = i - 1; sbIn->stmts[j]->tag != Ist_IMark && dc.nr_tmps != 0; j--)
				rewriteDcForStatement(&dc, sbIn->stmts[j], sbIn);
			if (dc.nr_tmps != 0) {
				ppIRSB(sbIn);
				VG_(printf)("DC:\n");
				for (j = 0; j < dc.nr_tmps; j++) {
					VG_(printf)("\t");
					ppIRTemp(dc.tmp[j]);
					VG_(printf)("\n");
				}
				VG_(printf)("i = %d\n", i);
				VG_(tool_panic)("Failed to reduce all temporaries!\n");
			}
			for (j = 0; j < dc.nr_regs; j++) {
				IRTemp t;
				if (rsp == Ity_INVALID) {
					rsp = newIRTemp(sbOut->tyenv, Ity_I64);
					addStmtToIRSB(
						sbOut,
						IRStmt_WrTmp(
							rsp,
							IRExpr_Get(OFFSET_amd64_RSP, Ity_I64)));
				}
				t = newIRTemp(sbOut->tyenv, Ity_I64);
				addStmtToIRSB(
					sbOut,
					IRStmt_WrTmp(t, IRExpr_Get(dc.regs[j], Ity_I64)));
				addStmtToIRSB(
					sbOut,
					IRStmt_Dirty(
						unsafeIRDirty_0_N(
							0,
							"sca_deref",
							sca_deref_cb,
							mkIRExprVec_3(
								IRExpr_RdTmp(rsp),
								IRExpr_RdTmp(t),
								IRExpr_Const(
									IRConst_U64(dc.regs[j]))))));
			}
			if (sbIn->stmts[i]->tag == Ist_Store &&
			    typeOfIRExpr(sbIn->tyenv, sbIn->stmts[i]->Ist.Store.data) == Ity_I64) {
				if (rsp == Ity_INVALID) {
					rsp = newIRTemp(sbOut->tyenv, Ity_I64);
					addStmtToIRSB(
						sbOut,
						IRStmt_WrTmp(
							rsp,
							IRExpr_Get(OFFSET_amd64_RSP, Ity_I64)));
				}
				addStmtToIRSB(
					sbOut,
					IRStmt_Dirty(
						unsafeIRDirty_0_N(
							0,
							"sca_store",
							sca_store_cb,
							mkIRExprVec_3(
								IRExpr_RdTmp(rsp),
								sbIn->stmts[i]->Ist.Store.addr,
								sbIn->stmts[i]->Ist.Store.data))));
			}

			i++;
		}
	}
	if (sbIn->jumpkind == Ijk_Call ||
	    sbIn->jumpkind == Ijk_Ret) {
		void *cb;
		HChar *label;
		IRTemp t;

		if (sbIn->jumpkind == Ijk_Call) {
			cb = sca_call_cb;
			label = "sca_call_cb";
		} else {
			cb = sca_ret_cb;
			label = "sca_ret_cb";
		}
		t = newIRTemp(sbOut->tyenv, Ity_I64);
		addStmtToIRSB(
			sbOut,
			IRStmt_WrTmp(
				t,
				IRExpr_Get(OFFSET_amd64_RSP, Ity_I64)));
		addStmtToIRSB(
			sbOut,
			IRStmt_Dirty(
				unsafeIRDirty_0_N(
					0,
					label,
					cb,
					mkIRExprVec_1(
						IRExpr_RdTmp(t)))));
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
