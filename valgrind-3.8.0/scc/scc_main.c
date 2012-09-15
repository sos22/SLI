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

#define THREAD_HASH_HEADS 31
#define OUTPUT_BUF_SIZE 131072
#define NR_BLOOM_COUNTERS 32771

/* 1/frequency for random sampling.  Must not exceed 65536, because we
   only have 16 bits of randomness available. */
#define SAMPLE_PERIOD 1024

struct output_file {
	int fd;
	unsigned buf_used;
	unsigned char buf[OUTPUT_BUF_SIZE];
};

struct per_thread {
	struct per_thread *next;
	ThreadId tid;
	int trace_ptr;
	unsigned long trace[0];
};

static unsigned
trace_length;
static struct output_file
output = { .fd = -1 };
static struct per_thread *
thread_heads[THREAD_HASH_HEADS];
static unsigned char
bloom_counters[NR_BLOOM_COUNTERS];

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
		cursor = VG_(malloc)("per_thread", sizeof(*cursor) + trace_length * 8);
		cursor->tid = t;
		cursor->trace_ptr = 0;
		thread_heads[h] = cursor;
	}
	return cursor;
}

static unsigned long
lc_random(void)
{
	/* Simple LC random number generator.  Parameters are from
	   Knuth, seed was randomly chosen.  Note that the low bits
	   will have very poor randomness.  The high ones are much
	   better. */
	static unsigned long state = 12821024184365607893ul;
	state =
		state * 6364136223846793005ul +
		1442695040888963407ul;
	return state;
}

static int
sample_this_access(void)
{
	return (lc_random() >> 48) % SAMPLE_PERIOD == 0;
}

static int
sample_this_trace(unsigned h)
{
	int freq = bloom_counters[h];
	unsigned r = lc_random() >> 50;
	return r % (freq+1) == 0;
}

static void
sampled_trace(unsigned h)
{
	if (bloom_counters[h] < 127)
		bloom_counters[h]++;
}

static unsigned
hash_current_trace(const struct per_thread *pt)
{
	int i;
	unsigned long acc = 0;
	for (i = pt->trace_ptr; i < pt->trace_ptr + trace_length; i++)
		acc = acc * 9490482695628177868ul + pt->trace[i & (trace_length - 1)];
	while (acc >= NR_BLOOM_COUNTERS)
		acc = (acc % NR_BLOOM_COUNTERS) % (acc / NR_BLOOM_COUNTERS);
	return acc;
}

static void
output_flush(struct output_file *of)
{
	if (of->buf_used > 0)
		VG_(write)(of->fd, of->buf, of->buf_used);
	of->buf_used = 0;
}

static void
output_write(struct output_file *of, const void *buf, unsigned buf_size)
{
	unsigned this_time;
	unsigned copied;

	for (copied = 0; copied < buf_size; copied += this_time) {
		this_time = buf_size - copied;
		if (this_time > OUTPUT_BUF_SIZE - of->buf_used)
			this_time = OUTPUT_BUF_SIZE - of->buf_used;
		VG_(memcpy)(of->buf + of->buf_used,
			    (const void *)((unsigned long)buf + copied),
			    this_time);
		of->buf_used += this_time;
		if (of->buf_used == OUTPUT_BUF_SIZE)
			output_flush(of);
	}
}

static VexEmWarn
scc_footstep_cb(unsigned long rip)
{
	struct per_thread *pt = get_per_thread();
	pt->trace[pt->trace_ptr] = rip;
	pt->trace_ptr = (pt->trace_ptr + 1) & (trace_length - 1);
	return EmWarn_NONE;
}

static VexEmWarn
scc_deref_cb(unsigned long addr, unsigned long rsp)
{
	struct per_thread *pt;
	unsigned h;
	const unsigned long *frag1, *frag2;
	unsigned len_frag1, len_frag2;
	unsigned long magic = 0xaabbccddeeff8844ul;

	if (addr >= rsp - 128 && addr < rsp + 32768)
		return EmWarn_NONE;

	if (!sample_this_access())
		return EmWarn_NONE;
	pt = get_per_thread();
	h = hash_current_trace(pt);
	if (!sample_this_trace(h))
		return EmWarn_NONE;

	frag1 = pt->trace + pt->trace_ptr;
	len_frag1 = trace_length - pt->trace_ptr;
	frag2 = pt->trace;
	len_frag2 = pt->trace_ptr;
	output_write(&output, &magic, sizeof(magic));
	output_write(&output, frag1, len_frag1 * 8);
	output_write(&output, frag2, len_frag2 * 8);
	sampled_trace(h);
	return EmWarn_NONE;
}

static void
addFootstep(IRSB *sb, unsigned long addr)
{
	addStmtToIRSB(
		sb,
		IRStmt_Dirty(
			unsafeIRDirty_0_N(
				0,
				"scc_footstep",
				scc_footstep_cb,
				mkIRExprVec_1(
					IRExpr_Const(IRConst_U64(addr))))));
}

static void
derefPointer(IRSB *sb, IRExpr *ptr)
{
	IRTemp rsp;
	if (ptr->tag != Iex_RdTmp && ptr->tag != Iex_Const) {
		IRTemp t = newIRTemp(sb->tyenv, Ity_I64);
		addStmtToIRSB(
			sb,
			IRStmt_WrTmp(t, ptr));
		ptr = IRExpr_RdTmp(t);
	}
	rsp = newIRTemp(sb->tyenv, Ity_I64);
	addStmtToIRSB(
		sb,
		IRStmt_WrTmp(rsp, IRExpr_Get(OFFSET_amd64_RSP, Ity_I64)));
	addStmtToIRSB(
		sb,
		IRStmt_Dirty(
			unsafeIRDirty_0_N(
				0,
				"scc_deref",
				scc_deref_cb,
				mkIRExprVec_2(
					ptr,
					IRExpr_RdTmp(rsp)
					))));
}

static void
checkForLoads(IRSB *sb, IRExpr *what)
{
	if (!what)
		return;
	switch (what->tag) {
	case Iex_Binder:
	case Iex_Get:
	case Iex_RdTmp:
		break;
	case Iex_GetI:
		checkForLoads(sb, what->Iex.GetI.ix);
		break;
	case Iex_Qop:
		checkForLoads(sb, what->Iex.Qop.details->arg4);
	case Iex_Triop:
		checkForLoads(sb, what->Iex.Qop.details->arg3);
		checkForLoads(sb, what->Iex.Qop.details->arg2);
		checkForLoads(sb, what->Iex.Qop.details->arg1);
		break;
	case Iex_Binop:
		checkForLoads(sb, what->Iex.Binop.arg2);
	case Iex_Unop:
		checkForLoads(sb, what->Iex.Binop.arg1);
		break;
	case Iex_Load:
		checkForLoads(sb, what->Iex.Load.addr);
		derefPointer(sb, what->Iex.Load.addr);
		break;
	case Iex_Const:
		break;
	case Iex_CCall: {
		int i;
		for (i = 0; what->Iex.CCall.args[i]; i++)
			checkForLoads(sb, what->Iex.CCall.args[i]);
		break;
	}
	case Iex_Mux0X:
		checkForLoads(sb, what->Iex.Mux0X.cond);
		checkForLoads(sb, what->Iex.Mux0X.expr0);
		checkForLoads(sb, what->Iex.Mux0X.exprX);
		break;
	}
}

static IRSB *
scc_instrument(VgCallbackClosure* closure,
	       IRSB* sbIn,
	       VexGuestLayout* layout,
	       VexGuestExtents* vge,
	       IRType gWordTy,
	       IRType hWordTy)
{
	IRSB *sbOut = deepCopyIRSBExceptStmts(sbIn);
	int i;
	IRStmt *stmt;

	for (i = 0; i < sbIn->stmts_used; i++) {
		stmt = sbIn->stmts[i];
		addStmtToIRSB(sbOut, stmt);
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			addFootstep(sbOut, stmt->Ist.IMark.addr);
			break;
		case Ist_AbiHint:
			checkForLoads(sbOut, stmt->Ist.AbiHint.base);
			checkForLoads(sbOut, stmt->Ist.AbiHint.nia);
			break;
		case Ist_Put:
			checkForLoads(sbOut, stmt->Ist.Put.data);
			break;
		case Ist_PutI:
			checkForLoads(sbOut, stmt->Ist.PutI.details->data);
			checkForLoads(sbOut, stmt->Ist.PutI.details->ix);
			break;
		case Ist_WrTmp:
			checkForLoads(sbOut, stmt->Ist.WrTmp.data);
			break;
		case Ist_Store:
			checkForLoads(sbOut, stmt->Ist.Store.data);
			checkForLoads(sbOut, stmt->Ist.Store.addr);
			derefPointer(sbOut, stmt->Ist.Store.addr);
			break;
		case Ist_CAS:
			checkForLoads(sbOut, stmt->Ist.CAS.details->dataLo);
			checkForLoads(sbOut, stmt->Ist.CAS.details->dataHi);
			checkForLoads(sbOut, stmt->Ist.CAS.details->expdLo);
			checkForLoads(sbOut, stmt->Ist.CAS.details->expdHi);
			checkForLoads(sbOut, stmt->Ist.CAS.details->addr);
			derefPointer(sbOut, stmt->Ist.CAS.details->addr);
			break;
		case Ist_LLSC:
			VG_(tool_panic)("LLSC on amd64?\n");
		case Ist_MBE:
			break;
		case Ist_Exit:
			checkForLoads(sbOut, stmt->Ist.Exit.guard);
			break;
		case Ist_Dirty: {
			int j;
			checkForLoads(sbOut, stmt->Ist.Dirty.details->guard);
			for (j = 0; stmt->Ist.Dirty.details->args[j]; j++)
				checkForLoads(sbOut, stmt->Ist.Dirty.details->args[j]);
			break;
		}
		}
	}
	return sbOut;
}

static void
scc_post_clo_init(void)
{
	if (trace_length == 0)
		VG_(tool_panic)("No trace length specified\n");
	if (trace_length & (trace_length - 1))
		VG_(tool_panic)("Trace length must be a power of two.\n");
	if (output.fd == -1)
		VG_(tool_panic)("No output file specified\n");
}

static void
scc_print_usage(void)
{
	VG_(printf)("\t--trace-length=<n>   How many instructions in each trace\n");
	VG_(printf)("\t--output=<fname>     Where to dump the traces\n");
}

static void
scc_print_debug_usage(void)
{
}

static Bool
scc_process_command_line_option(Char *opt)
{
	Char *pathname;
	if (VG_STR_CLO(opt, "--output", pathname)) {
		output.fd = VG_(fd_open)(pathname, VKI_O_WRONLY | VKI_O_CREAT | VKI_O_TRUNC, 0600);
		if (output.fd < 0) {
			VG_(printf)("Cannot open %s\n", pathname);
			VG_(tool_panic)("Cannot open database");
		}
		output.buf_used = 0;
		return True;
	} else if (VG_INT_CLO(opt, "--trace-length", trace_length)) {
		return True;
	} else {
		return False;
	}
}

static void
scc_fini(Int exitcode)
{
	output_flush(&output);
}

static void
sca_pre_clo_init(void)
{
	VG_(details_name)            ("SCC");
	VG_(details_version)         (NULL);
	VG_(details_description)     ("the minimal Valgrind tool");
	VG_(details_copyright_author)(
		"Copyright (C) 2002-2012, and GNU GPL'd, by Nicholas Nethercote.");
	VG_(details_bug_reports_to)  (VG_BUGS_TO);

	VG_(details_avg_translation_sizeB) ( 275 );

	VG_(basic_tool_funcs)        (scc_post_clo_init,
				      scc_instrument,
				      scc_fini);

	VG_(needs_command_line_options) (scc_process_command_line_option,
					 scc_print_usage,
					 scc_print_debug_usage);
}

VG_DETERMINE_INTERFACE_VERSION(sca_pre_clo_init)
