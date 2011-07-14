/* This gets #include'd into both the replay and record systems.  It
  contains all the gubbins needed to add the monitoring infrastructure
  to VEX IR. */
#include "libvex.h"
#include "libvex_ir.h"
#include "libvex_guest_offsets.h"
#include "sli.h"

#define FOOTSTEP_REGS_ONLY
#include "ppres.h"

#define load_worker_function load_event

#define mk_helper_load(typ, suffix)                            \
static typ                                                     \
 helper_load_ ## suffix (const typ *ptr, unsigned long rsp,    \
			 unsigned long rip)		       \
{							       \
	/* Placeholder, never actually called. */	       \
	abort();					       \
}

#define mk_helpers(typ, suffix)                        \
mk_helper_load(typ, suffix)

mk_helpers(unsigned char, 8)
mk_helpers(unsigned short, 16)
mk_helpers(unsigned, 32)
mk_helpers(unsigned long, 64)

typedef struct {
	unsigned long long a;
	unsigned long long b;
} ultralong_t;

mk_helpers(ultralong_t, 128)

static IRExpr *
log_reads_expr(unsigned tid, IRSB *sb, IRExpr *exp)
{
	if (!exp)
		return NULL;

	switch (exp->tag) {
	case Iex_Get:
	case Iex_Binder:
	case Iex_RdTmp:
	case Iex_FreeVariable:
		return exp;
	case Iex_GetI:
		return IRExpr_GetI(exp->Iex.GetI.descr,
				   log_reads_expr(tid, sb, exp->Iex.GetI.ix),
				   exp->Iex.GetI.bias,
				   exp->Iex.GetI.tid);
	case Iex_Qop:
		return IRExpr_Qop(exp->Iex.Qop.op,
				  log_reads_expr(tid, sb, exp->Iex.Qop.arg1),
				  log_reads_expr(tid, sb, exp->Iex.Qop.arg2),
				  log_reads_expr(tid, sb, exp->Iex.Qop.arg3),
				  log_reads_expr(tid, sb, exp->Iex.Qop.arg4));
	case Iex_Triop:
		return IRExpr_Triop(exp->Iex.Triop.op,
				    log_reads_expr(tid, sb, exp->Iex.Triop.arg1),
				    log_reads_expr(tid, sb, exp->Iex.Triop.arg2),
				    log_reads_expr(tid, sb, exp->Iex.Triop.arg3));
	case Iex_Binop:
		return IRExpr_Binop(exp->Iex.Binop.op,
				    log_reads_expr(tid, sb, exp->Iex.Binop.arg1),
				    log_reads_expr(tid, sb, exp->Iex.Binop.arg2));
	case Iex_Associative: {
		IRExpr *out = IRExpr_Associative(exp);
		for (int x = 0;
		     x < exp->Iex.Associative.nr_arguments;
		     x++)
			out->Iex.Associative.contents[x] =
				log_reads_expr(tid, sb, out->Iex.Associative.contents[x]);
		return out;
	}
	case Iex_Unop:
		return IRExpr_Unop(exp->Iex.Unop.op,
				   log_reads_expr(tid, sb, exp->Iex.Unop.arg));
	case Iex_Load: {
		IRExpr **args;
		void *helper;
		const char *helper_name;
		IRTemp dest;
		IRDirty *f;

#define HLP(x) helper_name = "helper_load_" #x ; helper = (void *)helper_load_ ## x ;
		switch (exp->Iex.Load.ty) {
		case Ity_INVALID:
			throw NotImplementedException("Bad type 1");
		case Ity_I1:
			throw NotImplementedException("Bad type 2");
		default:
			throw NotImplementedException("Bad type 3");
		case Ity_I8:
			HLP(8);
			break;
		case Ity_I16:
			HLP(16);
			break;
		case Ity_I32:
		case Ity_F32:
			HLP(32);
			break;
		case Ity_I64:
		case Ity_F64:
			HLP(64);
			break;
		case Ity_I128:
			HLP(128);
			break;
		case Ity_V128:
			HLP(128);
			break;
		}
#undef HLP

		args = mkIRExprVec_3(log_reads_expr(tid, sb, exp->Iex.Load.addr),
				     IRExpr_Get(OFFSET_amd64_RSP, Ity_I64, tid),
				     IRExpr_Get(OFFSET_amd64_RIP, Ity_I64, tid));
		dest = newIRTemp(sb->tyenv, exp->Iex.Load.ty);
		f = unsafeIRDirty_1_N(dest,
				      0,
				      helper_name,
				      helper,
				      args);
		addStmtToIRSB(sb, IRStmt_Dirty(f));
		return IRExpr_RdTmp(dest, tid);
	}
	case Iex_Const:
		return exp;
	case Iex_CCall: {
		IRExpr **args;
		unsigned x;

		args = shallowCopyIRExprVec(exp->Iex.CCall.args);
		for (x = 0; args[x]; x++)
			args[x] = log_reads_expr(tid, sb, args[x]);
		return IRExpr_CCall(exp->Iex.CCall.cee,
				    exp->Iex.CCall.retty,
				    args);
	}
	case Iex_Mux0X:
		return IRExpr_Mux0X(log_reads_expr(tid, sb, exp->Iex.Mux0X.cond),
				    log_reads_expr(tid, sb, exp->Iex.Mux0X.expr0),
				    log_reads_expr(tid, sb, exp->Iex.Mux0X.exprX));
	case Iex_ClientCall: /* There shouldn't be any of these at this stage */
	case Iex_ClientCallFailed:
		abort();
	}
	throw NotImplementedException("Something bad");
}

IRSB *
instrument_func(unsigned tid,
		void *closure,
		IRSB *sb_in,
		VexGuestLayout *layout,
		VexGuestExtents *vge,
		IRType gWordTy,
		IRType hWordTy)
{
	IRStmt **in_stmts = sb_in->stmts;
	int nr_in_stmts = sb_in->stmts_used;
	IRSB *sb_out;
	IRStmt *current_in_stmt;
	IRStmt *out_stmt;
	int i;

	sb_in->stmts = NULL;
	sb_in->stmts_used = 0;
	sb_in->stmts_size = 0;
	sb_out = sb_in;

	for (i = 0; i < nr_in_stmts; i++) {
		current_in_stmt = in_stmts[i];
		out_stmt = current_in_stmt;
		switch (current_in_stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			break;
		case Ist_AbiHint:
			break;
		case Ist_Put:
			out_stmt->Ist.Put.data = log_reads_expr(tid, sb_out, out_stmt->Ist.Put.data);
			break;
		case Ist_PutI:
			out_stmt->Ist.PutI.ix = log_reads_expr(tid, sb_out, out_stmt->Ist.PutI.ix);
			out_stmt->Ist.PutI.data = log_reads_expr(tid, sb_out, out_stmt->Ist.PutI.data);
			break;
		case Ist_WrTmp:
			out_stmt->Ist.WrTmp.data = log_reads_expr(tid, sb_out, out_stmt->Ist.WrTmp.data);
			break;
		case Ist_Store: {
			IRExpr *addr = current_in_stmt->Ist.Store.addr;
			IRExpr *data = current_in_stmt->Ist.Store.data;
			out_stmt->Ist.Store.addr = log_reads_expr(tid, sb_out, addr);
			out_stmt->Ist.Store.data = log_reads_expr(tid, sb_out, data);
			break;
		}
		case Ist_CAS:
			out_stmt->Ist.CAS.details->addr =
				log_reads_expr(tid, sb_out,
					       out_stmt->Ist.CAS.details->addr);
			out_stmt->Ist.CAS.details->expdHi =
				log_reads_expr(tid, sb_out,
					       out_stmt->Ist.CAS.details->expdHi);
			out_stmt->Ist.CAS.details->expdLo =
				log_reads_expr(tid, sb_out,
					       out_stmt->Ist.CAS.details->expdLo);
			out_stmt->Ist.CAS.details->dataHi =
				log_reads_expr(tid, sb_out,
					       out_stmt->Ist.CAS.details->dataHi);
			out_stmt->Ist.CAS.details->dataLo =
				log_reads_expr(tid, sb_out,
					       out_stmt->Ist.CAS.details->dataLo);
			break;
		case Ist_Dirty: {
			unsigned x;
			IRDirty *details;
			details = out_stmt->Ist.Dirty.details;
			details->guard = log_reads_expr(tid, sb_out, details->guard);
			for (x = 0; details->args[x]; x++)
				details->args[x] = log_reads_expr(tid, sb_out, details->args[x]);
			/* Not mAddr, because it's not actually read. */
			break;
		}
		case Ist_MBE:
			break;
		case Ist_Exit:
			out_stmt->Ist.Exit.guard =
				log_reads_expr(tid, sb_out, out_stmt->Ist.Exit.guard);
			break;
		}
		addStmtToIRSB(sb_out, out_stmt);
	}

	return sb_out;
}
