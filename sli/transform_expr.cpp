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
 helper_load_ ## suffix (const typ *, unsigned long ,	       \
			 unsigned long )		       \
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
	case Iex_FreeVariable:
	case Iex_EntryPoint:
	case Iex_ControlFlow:
		return exp;
	case Iex_GetI: {
		IRExprGetI *e = (IRExprGetI *)exp;
		return IRExpr_GetI(e->descr,
				   log_reads_expr(tid, sb, e->ix),
				   e->bias,
				   e->tid);
	}
	case Iex_Qop: {
		IRExprQop *e = (IRExprQop *)exp;
		return IRExpr_Qop(e->op,
				  log_reads_expr(tid, sb, e->arg1),
				  log_reads_expr(tid, sb, e->arg2),
				  log_reads_expr(tid, sb, e->arg3),
				  log_reads_expr(tid, sb, e->arg4));
	}
	case Iex_Triop: {
		IRExprTriop *e = (IRExprTriop *)exp;
		return IRExpr_Triop(e->op,
				    log_reads_expr(tid, sb, e->arg1),
				    log_reads_expr(tid, sb, e->arg2),
				    log_reads_expr(tid, sb, e->arg3));
	}
	case Iex_Binop: {
		IRExprBinop *e = (IRExprBinop *)exp;
		return IRExpr_Binop(e->op,
				    log_reads_expr(tid, sb, e->arg1),
				    log_reads_expr(tid, sb, e->arg2));
	}
	case Iex_Associative: {
		IRExprAssociative *e = (IRExprAssociative *)exp;
		IRExprAssociative *out = (IRExprAssociative *)IRExpr_Associative(e);
		for (int x = 0;
		     x < e->nr_arguments;
		     x++)
			out->contents[x] =
				log_reads_expr(tid, sb, out->contents[x]);
		return out;
	}
	case Iex_Unop: {
		IRExprUnop *e = (IRExprUnop *)exp;
		return IRExpr_Unop(e->op,
				   log_reads_expr(tid, sb, e->arg));
	}
	case Iex_Load: {
		IRExprLoad *e = (IRExprLoad *)exp;
		IRExpr **args;
		void *helper;
		const char *helper_name;
		IRTemp dest;
		IRDirty *f;

		assert(e->addr->type() == Ity_I64);

#define HLP(x) helper_name = "helper_load_" #x ; helper = (void *)helper_load_ ## x ;
		switch (e->ty) {
		case Ity_INVALID:
			abort();
		case Ity_I1:
			abort();
		case Ity_I8:
			HLP(8);
			break;
		case Ity_I16:
			HLP(16);
			break;
		case Ity_I32:
			HLP(32);
			break;
		case Ity_I64:
			HLP(64);
			break;
		case Ity_I128:
			HLP(128);
			break;
		}
#undef HLP

		args = mkIRExprVec_3(log_reads_expr(tid, sb, e->addr),
				     IRExpr_Get(OFFSET_amd64_RSP, Ity_I64, tid, 0),
				     IRExpr_Get(OFFSET_amd64_RIP, Ity_I64, tid, 0));
		dest = newIRTemp(sb->tyenv);
		f = unsafeIRDirty_1_N(threadAndRegister::temp(tid, dest, 0),
				      0,
				      helper_name,
				      helper,
				      args);
		addStmtToIRSB(sb, IRStmt_Dirty(f));
		return IRExpr_RdTmp(dest, e->ty, tid, 0);
	}
	case Iex_Const:
		return exp;
	case Iex_CCall: {
		IRExprCCall *e = (IRExprCCall *)exp;
		IRExpr **args;
		int x;
		int nr_args;
		for (nr_args = 0; e->args[nr_args]; nr_args++)
			;
		args = alloc_irexpr_array(nr_args + 1);
		args[nr_args] = NULL;
		for (x = 0; x < nr_args; x++)
			args[x] = log_reads_expr(tid, sb, e->args[x]);
		return IRExpr_CCall(e->cee,
				    e->retty,
				    args);
	}
	case Iex_Mux0X: {
		IRExprMux0X *e = (IRExprMux0X *)exp;
		return IRExpr_Mux0X(log_reads_expr(tid, sb, e->cond),
				    log_reads_expr(tid, sb, e->expr0),
				    log_reads_expr(tid, sb, e->exprX));
	}
	case Iex_HappensBefore:
		abort();
	}
	abort();
}

IRSB *
instrument_func(unsigned tid,
		void *,
		IRSB *sb_in,
		VexGuestLayout *,
		VexGuestExtents *,
		IRType ,
		IRType )
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
		case Ist_Put: {
			IRStmtPut *o = (IRStmtPut *)out_stmt;
			o->data = log_reads_expr(tid, sb_out, o->data);
			break;
		}
		case Ist_PutI: {
			IRStmtPutI *o = (IRStmtPutI *)out_stmt;
			o->ix = log_reads_expr(tid, sb_out, o->ix);
			o->data = log_reads_expr(tid, sb_out, o->data);
			break;
		}
		case Ist_Store: {
			IRStmtStore *o = (IRStmtStore *)out_stmt;
			IRExpr *addr = o->addr;
			IRExpr *data = o->data;
			o->addr = log_reads_expr(tid, sb_out, addr);
			o->data = log_reads_expr(tid, sb_out, data);
			break;
		}
		case Ist_CAS: {
			IRStmtCAS *o = (IRStmtCAS *)out_stmt;
			o->details->addr =
				log_reads_expr(tid, sb_out,
					       o->details->addr);
			o->details->expdHi =
				log_reads_expr(tid, sb_out,
					       o->details->expdHi);
			o->details->expdLo =
				log_reads_expr(tid, sb_out,
					       o->details->expdLo);
			o->details->dataHi =
				log_reads_expr(tid, sb_out,
					       o->details->dataHi);
			o->details->dataLo =
				log_reads_expr(tid, sb_out,
					       o->details->dataLo);
			break;
		}
		case Ist_Dirty: {
			IRStmtDirty *o = (IRStmtDirty *)out_stmt;
			unsigned x;
			IRDirty *details;
			details = o->details;
			details->guard = log_reads_expr(tid, sb_out, details->guard);
			for (x = 0; details->args[x]; x++)
				details->args[x] = log_reads_expr(tid, sb_out, details->args[x]);
			/* Not mAddr, because it's not actually read. */
			break;
		}
		case Ist_MBE:
			break;
		case Ist_Exit: {
			IRStmtExit *o = (IRStmtExit *)out_stmt;
			o->guard = log_reads_expr(tid, sb_out, o->guard);
			break;
		}
		case Ist_StartAtomic:
			break;
		case Ist_EndAtomic:
			break;
		}
		addStmtToIRSB(sb_out, out_stmt);
	}

	return sb_out;
}
