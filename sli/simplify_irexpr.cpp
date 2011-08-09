#include <time.h>

#include "sli.h"
#include "state_machine.hpp"

#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"
#include "cnf.hpp"

#include "libvex_guest_offsets.h"
#include "libvex_prof.hpp"
#include "../VEX/priv/guest_generic_bb_to_IR.h"
#include "../VEX/priv/guest_amd64_defs.h"

/* Returns true if the operation definitely commutes, or false if
 * we're not sure. */
static bool
operationCommutes(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) ||
		(op >= Iop_CmpEQ8 && op <= Iop_CmpEQ64) ||
		(op == Iop_And1) ||
		(op == Iop_Or1) ||
		(op == Iop_Xor1);
}

/* Returns true if the operation definitely associates in the sense
 * that (a op b) op c == a op (b op c), or false if we're not sure. */
static bool
operationAssociates(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) || (op == Iop_And1) ||
		(op >= Iop_And8 && op <= Iop_And64) || (op >= Iop_Xor8 && op <= Iop_Xor64) ||
		(op >= Iop_Or8 && op <= Iop_Or64) || (op == Iop_Or1) ||
		(op == Iop_Xor1)
		;
}

bool
physicallyEqual(const IRConst *a, const IRConst *b)
{
	if (a->tag != b->tag)
		return false;
	switch (a->tag) {
#define do_case(t)					\
		case Ico_ ## t:				\
			return a->Ico. t == b->Ico. t
		do_case(U1);
		do_case(U8);
		do_case(U16);
		do_case(U32);
		do_case(U64);
		do_case(F64);
		do_case(F64i);
		do_case(V128);
#undef do_case
	}
	abort();
}

static bool
physicallyEqual(const IRRegArray *a, const IRRegArray *b)
{
	return a->base == b->base && a->elemTy == b->elemTy && a->nElems == b->nElems;
}

static bool
physicallyEqual(const IRCallee *a, const IRCallee *b)
{
	return a->addr == b->addr;
}

static bool
physicallyEqual(const IRExpr *a, const IRExpr *b)
{
	if (a == b)
		return true;
	if (a->tag != b->tag)
		return false;
	switch (a->tag) {
	case Iex_Binder:
		return a->Iex.Binder.binder == b->Iex.Binder.binder;
	case Iex_Get:
		return a->Iex.Get.offset == b->Iex.Get.offset &&
			a->Iex.Get.ty == b->Iex.Get.ty;
	case Iex_GetI:
		return a->Iex.GetI.bias == b->Iex.GetI.bias &&
			physicallyEqual(a->Iex.GetI.descr,
					b->Iex.GetI.descr) &&
			physicallyEqual(a->Iex.GetI.ix,
					b->Iex.GetI.ix);
	case Iex_RdTmp:
		return a->Iex.RdTmp.tmp == b->Iex.RdTmp.tmp;

	case Iex_Qop:
		if (!physicallyEqual(a->Iex.Qop.arg4,
				     b->Iex.Qop.arg4))
			return false;
	case Iex_Triop:
		if (!physicallyEqual(a->Iex.Qop.arg3,
				     b->Iex.Qop.arg3))
			return false;
	case Iex_Binop:
		if (!physicallyEqual(a->Iex.Qop.arg2,
				     b->Iex.Qop.arg2))
			return false;
	case Iex_Unop:
		if (!physicallyEqual(a->Iex.Qop.arg1,
				     b->Iex.Qop.arg1))
			return false;
		return a->Iex.Qop.op == b->Iex.Qop.op;
	case Iex_Load:
		return a->Iex.Load.isLL == b->Iex.Load.isLL &&
			a->Iex.Load.end == b->Iex.Load.end &&
			a->Iex.Load.ty == b->Iex.Load.ty &&
			physicallyEqual(a->Iex.Load.addr, b->Iex.Load.addr);
	case Iex_Const:
		return physicallyEqual(a->Iex.Const.con, b->Iex.Const.con);
	case Iex_CCall: {
		if (a->Iex.CCall.retty != b->Iex.CCall.retty ||
		    !physicallyEqual(a->Iex.CCall.cee, b->Iex.CCall.cee))
			return false;
		int x;
		for (x = 0; a->Iex.CCall.args[x]; x++) {
			if (!b->Iex.CCall.args[x])
				return false;
			if (!physicallyEqual(a->Iex.CCall.args[x],
					     b->Iex.CCall.args[x]))
				return false;
		}
		if (b->Iex.CCall.args[x])
			return false;
		return true;
	}
	case Iex_Mux0X:
		return physicallyEqual(a->Iex.Mux0X.cond,
				       b->Iex.Mux0X.cond) &&
			physicallyEqual(a->Iex.Mux0X.expr0,
					b->Iex.Mux0X.expr0) &&
			physicallyEqual(a->Iex.Mux0X.exprX,
					b->Iex.Mux0X.exprX);
	case Iex_Associative:
		if (a->Iex.Associative.op != b->Iex.Associative.op ||
		    a->Iex.Associative.nr_arguments != b->Iex.Associative.nr_arguments)
			return false;
		for (int x = 0; x < a->Iex.Associative.nr_arguments; x++)
			if (!physicallyEqual(a->Iex.Associative.contents[x],
					     b->Iex.Associative.contents[x]))
				return false;
		return true;
	case Iex_FreeVariable:
		return a->Iex.FreeVariable.key == b->Iex.FreeVariable.key;
	case Iex_ClientCall:
		if (a->Iex.ClientCall.calledRip != b->Iex.ClientCall.calledRip ||
		    a->Iex.ClientCall.callSite != b->Iex.ClientCall.callSite)
			return false;
		for (int i = 0; ; i++) {
			if (!a->Iex.ClientCall.args[i]) {
				if (!b->Iex.ClientCall.args[i])
					return true;
				else
					return false;
			} else if (!b->Iex.ClientCall.args[i])
				return false;
			if (!physicallyEqual(a->Iex.ClientCall.args[i],
					     b->Iex.ClientCall.args[i]))
				return false;
		}
		abort();
	case Iex_ClientCallFailed:
		return physicallyEqual(a->Iex.ClientCallFailed.target,
				       b->Iex.ClientCallFailed.target);
	case Iex_HappensBefore:
		return a->Iex.HappensBefore.before == b->Iex.HappensBefore.before &&
			a->Iex.HappensBefore.after == b->Iex.HappensBefore.after;
	}
	abort();
}

static IRExpr *
optimise_condition_calculation(
	IRExpr *_cond,
	IRExpr *cc_op,
	IRExpr *dep1,
	IRExpr *dep2,
	IRExpr *ndep,
	const AllowableOptimisations &opt)
{
	unsigned long cond;
	IRExpr *res;
	bool invert;
	IRExpr *sf, *cf, *zf, *of;

	/* We only handle a few very special cases here. */
	if (_cond->tag != Iex_Const || cc_op->tag != Iex_Const)
		return NULL;
	cond = _cond->Iex.Const.con->Ico.U64;
	invert = cond & 1;
	cond &= ~1ul;
	res = NULL;
	sf = cf = zf = of = NULL;

	switch (cc_op->Iex.Const.con->Ico.U64) {
	case AMD64G_CC_OP_SUBB:
		zf = IRExpr_Binop(Iop_CmpEQ8, dep1, dep2);
		break;
	case AMD64G_CC_OP_SUBW:
		zf = IRExpr_Binop(Iop_CmpEQ16, dep1, dep2);
		break;
	case AMD64G_CC_OP_SUBL:
	case AMD64G_CC_OP_SUBQ:
		zf = IRExpr_Binop(
			Iop_CmpEQ64,
			dep1,
			dep2);
		cf = IRExpr_Binop(
			Iop_CmpLT64U,
			dep1,
			dep2);
		sf = IRExpr_Binop(
			Iop_CmpLT64S,
			dep1,
			dep2);
		of = IRExpr_Binop(
			Iop_CC_OverflowSub,
			dep1,
			dep2);
		break;
	case AMD64G_CC_OP_LOGICB:
	case AMD64G_CC_OP_LOGICL:
	case AMD64G_CC_OP_LOGICQ:
		zf = IRExpr_Binop(
			Iop_CmpEQ64,
			dep1,
			IRExpr_Const(IRConst_U64(0)));
		sf = IRExpr_Binop(
			Iop_CmpLT64S,
			dep1,
			IRExpr_Const(IRConst_U32(0)));
		of = IRExpr_Const(IRConst_U1(0));
		break;
	case AMD64G_CC_OP_ADDW:
		sf = IRExpr_Binop(
			Iop_CmpLT32S,
			IRExpr_Binop(
				Iop_Add16,
				dep1,
				dep2),
			IRExpr_Const(IRConst_U16(0)));
		break;
	default:
		printf("Unknown CC op %llx\n", cc_op->Iex.Const.con->Ico.U64);
		break;
	}

	switch (cond) {
	case AMD64CondZ:
		res = zf;
		break;
	case AMD64CondB:
		res = cf;
		break;
	case AMD64CondBE:
		if (cf && zf)
			res = IRExpr_Binop(
				Iop_Or1,
				cf,
				zf);
		break;
	case AMD64CondS:
		res = sf;
		break;
	case AMD64CondL:
		if (sf && of)
			res = IRExpr_Binop(
				Iop_Xor1,
				sf,
				of);
		else
			printf("CondL needs both sf and of; op %llx\n", cc_op->Iex.Const.con->Ico.U64);
		break;
	case AMD64CondLE:
		if (sf && of && zf)
			res = IRExpr_Binop(
				Iop_Or1,
				IRExpr_Binop(
					Iop_Xor1,
					sf,
					of),
				zf);
		else
			printf("CondLE needs sf, of, and zf; op %llx\n", cc_op->Iex.Const.con->Ico.U64);
		break;
	default:
		break;
	}
	if (!res)
		printf("Cannot handle CC condition %ld, op %lld\n",
		       cond, cc_op->Iex.Const.con->Ico.U64);
	if (res && invert)
		res = IRExpr_Unop(Iop_Not1, res);
	return res;
}

/* Wherever we have a choice as to the ordering of an expression's
   sub-expressions, we sort them into ascending order of complexity,
   where complexity is defined by this function.  The main requirement
   is that if both x and -x occur in the argument list, x will occur
   before -x. */
/* If two expressions have the same complexity, we use a lexicographic
   ordering to distinguish them. */
int
exprComplexity(const IRExpr *e)
{
	switch (e->tag) {
	case Iex_Binder:
		return 10;
	case Iex_Get:
		return 20;
	case Iex_GetI:
		return 20 + exprComplexity(e->Iex.GetI.ix);
	case Iex_RdTmp:
		return 30;
	case Iex_Qop:
		return 10 +
			exprComplexity(e->Iex.Qop.arg1) +
			exprComplexity(e->Iex.Qop.arg2) +
			exprComplexity(e->Iex.Qop.arg3) +
			exprComplexity(e->Iex.Qop.arg4);
	case Iex_Triop:
		return 10 +
			exprComplexity(e->Iex.Qop.arg1) +
			exprComplexity(e->Iex.Qop.arg2) +
			exprComplexity(e->Iex.Qop.arg3);
	case Iex_Binop:
		return 10 +
			exprComplexity(e->Iex.Qop.arg1) +
			exprComplexity(e->Iex.Qop.arg2);
	case Iex_Unop:
		return 10 + exprComplexity(e->Iex.Qop.arg1);
	case Iex_Load:
		return 10 + exprComplexity(e->Iex.Load.addr);
	case Iex_Const:
		return 0;
	case Iex_Mux0X:
		return 10 + exprComplexity(e->Iex.Mux0X.cond) +
			exprComplexity(e->Iex.Mux0X.expr0) +
			exprComplexity(e->Iex.Mux0X.exprX);
	case Iex_CCall: {
		int acc = 50;
		for (int x = 0; e->Iex.CCall.args[x]; x++)
			acc += exprComplexity(e->Iex.CCall.args[x]);
		return acc;
	}
	case Iex_Associative: {
		int acc = 10;
		for (int x = 0; x < e->Iex.Associative.nr_arguments; x++)
			acc += exprComplexity(e->Iex.Associative.contents[x]);
		return acc;
	}
	case Iex_FreeVariable:
		return 100;
	case Iex_ClientCall: {
		int acc = 100;
		for (int x = 0; e->Iex.ClientCall.args[x]; x++)
			acc += exprComplexity(e->Iex.ClientCall.args[x]);
		return acc;
	}
	case Iex_ClientCallFailed:
		return 1000 + exprComplexity(e->Iex.ClientCallFailed.target);
	case Iex_HappensBefore:
		return 100;
	}
	abort();
}

static int
ordering_iex_tag(IRExprTag a)
{
	switch (a) {
	case Iex_Const: return 0;
	case Iex_Binder: return 1;
	case Iex_Get: return 2;
	case Iex_GetI: return 3;
	case Iex_RdTmp: return 4;
	case Iex_FreeVariable: return 5;
	case Iex_Unop: return 6;
	case Iex_Binop: return 7;
	case Iex_Triop: return 8;
	case Iex_Qop: return 9;
	case Iex_Associative: return 10;
	case Iex_Mux0X: return 11;
	case Iex_Load: return 12;
	case Iex_CCall: return 13;
	case Iex_ClientCall: return 14;
	case Iex_ClientCallFailed: return 15;
	case Iex_HappensBefore: return 16;
	}
	abort();
}

static bool
IexTagLessThan(IRExprTag a, IRExprTag b)
{
	if (a == b)
		return false;

	int _a = ordering_iex_tag(a);
	int _b = ordering_iex_tag(b);
	return _a < _b;
}

static bool
sortIRConsts(IRConst *a, IRConst *b)
{
	if (a->tag < b->tag)
		return true;
	if (a->tag > b->tag)
		return false;
	switch (a->tag) {
#define do_type(t)					\
		case Ico_ ## t :			\
			return a->Ico. t < b->Ico. t
		do_type(U1);
		do_type(U8);
		do_type(U16);
		do_type(U32);
		do_type(U64);
		do_type(F64);
		do_type(F64i);
		do_type(V128);
#undef do_type
	}
	abort();
}

static bool
sortIRExprs(IRExpr *a, IRExpr *b)
{
	int ac = exprComplexity(a);
	int bc = exprComplexity(b);
	if (ac < bc)
		return true;
	if (ac > bc)
		return false;
	if (IexTagLessThan(a->tag, b->tag)) {
		return true;
	} else if (a->tag != b->tag) {
		return false;
	}
	
	switch (a->tag) {
	case Iex_Binder:
		return a->Iex.Binder.binder < b->Iex.Binder.binder;
	case Iex_Get:
		return a->Iex.Get.offset < b->Iex.Get.offset;
	case Iex_GetI:
		return sortIRExprs(a->Iex.GetI.ix, b->Iex.GetI.ix);
	case Iex_RdTmp:
		return a->Iex.RdTmp.tmp < b->Iex.RdTmp.tmp;
	case Iex_Qop:
		if (a->Iex.Qop.op < b->Iex.Qop.op)
			return true;
		if (a->Iex.Qop.op > b->Iex.Qop.op)
			return false;
		if (physicallyEqual(a->Iex.Qop.arg1, b->Iex.Qop.arg1)) {
			if (physicallyEqual(a->Iex.Qop.arg2,
					    b->Iex.Qop.arg2)) {
				if (physicallyEqual(a->Iex.Qop.arg3,
						    b->Iex.Qop.arg3))
					return sortIRExprs(a->Iex.Qop.arg4,
							   b->Iex.Qop.arg4);
				else
					return sortIRExprs(a->Iex.Qop.arg3,
							   b->Iex.Qop.arg3);
			} else
				return sortIRExprs(a->Iex.Qop.arg2,
						   b->Iex.Qop.arg2);
		} else {
			return sortIRExprs(a->Iex.Qop.arg1,
					   b->Iex.Qop.arg1);
		}
	case Iex_Triop:
		if (a->Iex.Qop.op < b->Iex.Qop.op)
			return true;
		if (a->Iex.Qop.op > b->Iex.Qop.op)
			return false;
		if (physicallyEqual(a->Iex.Qop.arg1, b->Iex.Qop.arg1)) {
			if (physicallyEqual(a->Iex.Qop.arg2,
					    b->Iex.Qop.arg2)) {
				return sortIRExprs(a->Iex.Qop.arg3,
						   b->Iex.Qop.arg3);
			} else
				return sortIRExprs(a->Iex.Qop.arg2,
						   b->Iex.Qop.arg2);
		} else {
			return sortIRExprs(a->Iex.Qop.arg1,
					   b->Iex.Qop.arg1);
		}
	case Iex_Binop:
		if (a->Iex.Qop.op < b->Iex.Qop.op)
			return true;
		if (a->Iex.Qop.op > b->Iex.Qop.op)
			return false;
		if (physicallyEqual(a->Iex.Qop.arg1, b->Iex.Qop.arg1)) {
			return sortIRExprs(a->Iex.Qop.arg2,
					   b->Iex.Qop.arg2);
		} else {
			return sortIRExprs(a->Iex.Qop.arg1,
					   b->Iex.Qop.arg1);
		}
	case Iex_Unop:
		if (a->Iex.Qop.op < b->Iex.Qop.op)
			return true;
		if (a->Iex.Qop.op > b->Iex.Qop.op)
			return false;
		return sortIRExprs(a->Iex.Qop.arg1,
				   b->Iex.Qop.arg1);
	case Iex_Load:
		return sortIRExprs(a->Iex.Load.addr, b->Iex.Load.addr);
	case Iex_Const:
		return sortIRConsts(a->Iex.Const.con, b->Iex.Const.con);
	case Iex_CCall: {
		int r = strcmp(a->Iex.CCall.cee->name,
			       b->Iex.CCall.cee->name);
		if (r < 0)
			return true;
		else if (r > 0)
			return false;
		for (int x = 0; 1; x++) {
			if (!a->Iex.CCall.args[x] &&
			    !b->Iex.CCall.args[x])
				return false;
			if (!a->Iex.CCall.args[x])
				return true;
			if (!b->Iex.CCall.args[x])
				return false;
			if (!physicallyEqual(a->Iex.CCall.args[x],
					     b->Iex.CCall.args[x]))
				return sortIRExprs(a->Iex.CCall.args[x],
						   b->Iex.CCall.args[x]);
		}
	}
	case Iex_Mux0X:
		if (!physicallyEqual(a->Iex.Mux0X.cond,
				     b->Iex.Mux0X.cond))
			return sortIRExprs(a->Iex.Mux0X.cond,
					   b->Iex.Mux0X.cond);
		if (!physicallyEqual(a->Iex.Mux0X.expr0,
				     b->Iex.Mux0X.expr0))
			return sortIRExprs(a->Iex.Mux0X.expr0,
					   b->Iex.Mux0X.expr0);
		return sortIRExprs(a->Iex.Mux0X.exprX,
				   b->Iex.Mux0X.exprX);
	case Iex_Associative: {
		if (a->Iex.Associative.op < b->Iex.Associative.op)
			return true;
		if (a->Iex.Associative.op > b->Iex.Associative.op)
			return false;
		int x;
		x = 0;
		while (1) {
			if (x == a->Iex.Associative.nr_arguments &&
			    x == b->Iex.Associative.nr_arguments)
				return false;
			if (x == a->Iex.Associative.nr_arguments)
				return true;
			if (x == b->Iex.Associative.nr_arguments)
				return false;
			if (!physicallyEqual( a->Iex.Associative.contents[x],
					      b->Iex.Associative.contents[x] ))
				return sortIRExprs( a->Iex.Associative.contents[x],
						    b->Iex.Associative.contents[x] );
			x++;
		}
	}
	case Iex_FreeVariable:
		return a->Iex.FreeVariable.key < b->Iex.FreeVariable.key;
	case Iex_ClientCall:
		if (a->Iex.ClientCall.callSite < b->Iex.ClientCall.callSite)
			return true;
		else if (a->Iex.ClientCall.callSite > b->Iex.ClientCall.callSite)
			return false;
		for (int x = 0; 1; x++) {
			if (!a->Iex.ClientCall.args[x] && !b->Iex.ClientCall.args[x])
				return false;
			if (!a->Iex.ClientCall.args[x])
				return true;
			if (!b->Iex.ClientCall.args[x])
				return false;
			if (!physicallyEqual(a->Iex.ClientCall.args[x],
					     b->Iex.ClientCall.args[x]))
				return sortIRExprs(a->Iex.ClientCall.args[x],
						   b->Iex.ClientCall.args[x]);
		}
	case Iex_ClientCallFailed:
		return sortIRExprs(a->Iex.ClientCallFailed.target,
				   b->Iex.ClientCallFailed.target);
	case Iex_HappensBefore:
		if (a->Iex.HappensBefore.before < b->Iex.HappensBefore.before)
			return true;
		if (a->Iex.HappensBefore.before > b->Iex.HappensBefore.before)
			return false;
		return a->Iex.HappensBefore.after < b->Iex.HappensBefore.after;
	}

	abort();
}

void
addArgumentToAssoc(IRExpr *e, IRExpr *arg)
{
	assert( (e->optimisationsApplied & ~arg->optimisationsApplied) == 0);
	if (e->Iex.Associative.nr_arguments == e->Iex.Associative.nr_arguments_allocated) {
		e->Iex.Associative.nr_arguments_allocated += 8;
		e->Iex.Associative.contents = (IRExpr **)
			LibVEX_realloc(&ir_heap,
				       e->Iex.Associative.contents,
				       sizeof(IRExpr *) * e->Iex.Associative.nr_arguments_allocated);
	}
	e->Iex.Associative.contents[e->Iex.Associative.nr_arguments] = arg;
	e->Iex.Associative.nr_arguments++;
}

static void
purgeAssocArgument(IRExpr *e, int idx)
{
	assert(e->tag == Iex_Associative);
	assert(idx < e->Iex.Associative.nr_arguments);
	memmove(e->Iex.Associative.contents + idx,
		e->Iex.Associative.contents + idx + 1,
		sizeof(IRExpr *) * (e->Iex.Associative.nr_arguments - idx - 1));
	e->Iex.Associative.nr_arguments--;
}

static IRExpr *optimiseIRExpr(IRExpr *src, const AllowableOptimisations &opt, bool *done_something);

IRExpr *
optimiseIRExprFP(IRExpr *e, const AllowableOptimisations &opt, bool *done_something)
{
#if MANUAL_PROFILING
	static ProfilingSite __site("optimiseIRExprFP");
	static bool live;
	bool do_profiling;
	do_profiling = !live;
	unsigned long s = do_profiling ? SetProfiling::rdtsc() : 0;
	live = true;
#endif

	bool progress;
	progress = false;
	e = optimiseIRExpr(e, opt, &progress);
	if (progress) {
		*done_something = true;
		while (progress) {
			if (TIMEOUT) {
#if MANUAL_PROFILING
				live = false;
#endif
				return e;
			}
			progress = false;
			e = optimiseIRExpr(e, opt, &progress);
		}
	}
	e->optimisationsApplied |= opt.asUnsigned();
#if MANUAL_PROFILING
	if (do_profiling) {
		__site.accumulated_ticks += SetProfiling::rdtsc() - s;
		__site.nr_sites++;
		live = false;
	}
#endif
	return e;
}

static IRExpr *
optimiseIRExpr(IRExpr *src, const AllowableOptimisations &opt, bool *done_something)
{
	if (TIMEOUT)
		return src;

	if (!(opt.asUnsigned() & ~src->optimisationsApplied))
		return src;
	/* First, recursively optimise our arguments. */
	switch (src->tag) {
	case Iex_Qop:
		src->Iex.Qop.arg4 = optimiseIRExprFP(src->Iex.Qop.arg4, opt, done_something);
	case Iex_Triop:
		src->Iex.Triop.arg3 = optimiseIRExprFP(src->Iex.Triop.arg3, opt, done_something);
	case Iex_Binop:
		src->Iex.Binop.arg2 = optimiseIRExprFP(src->Iex.Binop.arg2, opt, done_something);
	case Iex_Unop:
		src->Iex.Unop.arg = optimiseIRExprFP(src->Iex.Unop.arg, opt, done_something);
		break;
	case Iex_Load:
		src->Iex.Load.addr = optimiseIRExprFP(src->Iex.Load.addr, opt, done_something);
#if 0
		if (src->Iex.Load.addr->tag == Iex_Const &&
		    (long)src->Iex.Load.addr->Iex.Const.con->Ico.U64 < 4096)
			dbg_break("optimising load to load of strange constant address (IRExpr *)%p\n",
				  src);
#endif
		break;
	case Iex_CCall: {
		for (int x = 0; src->Iex.CCall.args[x]; x++) {
			src->Iex.CCall.args[x] =
				optimiseIRExprFP(src->Iex.CCall.args[x], opt, done_something);
		}
		/* Special cases for amd64g_calculate_condition. */
		if (!strcmp(src->Iex.CCall.cee->name,
			    "amd64g_calculate_condition")) {
			IRExpr *e;
			e = optimise_condition_calculation(
				src->Iex.CCall.args[0],
				src->Iex.CCall.args[1],
				src->Iex.CCall.args[2],
				src->Iex.CCall.args[3],
				src->Iex.CCall.args[4],
				opt);
			if (e) {
				*done_something = true;
				src = e;
			}
		}
		break;
	}
	case Iex_Mux0X:
		src->Iex.Mux0X.cond = optimiseIRExprFP(src->Iex.Mux0X.cond, opt, done_something);
		src->Iex.Mux0X.expr0 = optimiseIRExprFP(src->Iex.Mux0X.expr0, opt, done_something);
		src->Iex.Mux0X.exprX = optimiseIRExprFP(src->Iex.Mux0X.exprX, opt, done_something);
		break;
	case Iex_Associative:
		for (int x = 0; x < src->Iex.Associative.nr_arguments; x++)
			src->Iex.Associative.contents[x] =
				optimiseIRExprFP(src->Iex.Associative.contents[x], opt, done_something);
		break;
	case Iex_ClientCall:
		for (int x = 0; src->Iex.ClientCall.args[x]; x++)
			src->Iex.ClientCall.args[x] =
				optimiseIRExprFP(src->Iex.ClientCall.args[x], opt, done_something);
		break;
	case Iex_ClientCallFailed:
		src->Iex.ClientCallFailed.target =
			optimiseIRExprFP(src->Iex.ClientCallFailed.target, opt, done_something);
		break;
	case Iex_GetI:
		src->Iex.GetI.ix =
			optimiseIRExprFP(src->Iex.GetI.ix, opt, done_something);
		break;
	case Iex_Binder:
	case Iex_Get:
	case Iex_RdTmp:
	case Iex_Const:
	case Iex_FreeVariable:
	case Iex_HappensBefore:
		break;
	}

	if (src->tag == Iex_Associative) {
		__set_profiling(optimise_associative);

		/* Drag up nested associatives. */
		bool haveNestedAssocs = false;
		for (int x = 0; !haveNestedAssocs && x < src->Iex.Associative.nr_arguments; x++)
			if (src->Iex.Associative.contents[x]->tag == Iex_Associative &&
			    src->Iex.Associative.contents[x]->Iex.Associative.op ==
				src->Iex.Associative.op)
				haveNestedAssocs = true;
		if (haveNestedAssocs) {
			__set_profiling(pull_up_nested_associatives);
			IRExpr *e = IRExpr_Associative(src->Iex.Associative.op, NULL);
			for (int x = 0; x < src->Iex.Associative.nr_arguments; x++) {
				IRExpr *arg = src->Iex.Associative.contents[x];
				if (arg->tag == Iex_Associative &&
				    arg->Iex.Associative.op == src->Iex.Associative.op) {
					for (int y = 0; y < arg->Iex.Associative.nr_arguments; y++)
						addArgumentToAssoc(e, arg->Iex.Associative.contents[y]);
				} else {
					addArgumentToAssoc(e, arg);
				}
			}
			src = e;
			*done_something = true;
		}

		/* Sort IRExprs so that ``related'' expressions are likely to
		 * be close together. */
		if (operationCommutes(src->Iex.Associative.op)) {
			__set_profiling(sort_associative_arguments);
			std::sort(src->Iex.Associative.contents,
				  src->Iex.Associative.contents + src->Iex.Associative.nr_arguments,
				  sortIRExprs);
		}
		/* Fold together constants.  For commutative
		   operations they'll all be at the beginning, but
		   don't assume that associativity implies
		   commutativity. */
		{ __set_profiling(associative_constant_fold);
		for (int x = 0; x + 1 < src->Iex.Associative.nr_arguments; x++) {
			IRExpr *a, *b;
			a = src->Iex.Associative.contents[x];
			b = src->Iex.Associative.contents[x+1];
			if (a->tag == Iex_Const && b->tag == Iex_Const) {
				IRExpr *res;
				IRConst *l, *r;
				l = a->Iex.Const.con;
				r = b->Iex.Const.con;
				switch (src->Iex.Associative.op) {
				case Iop_Add8:
					res = IRExpr_Const(
						IRConst_U8((l->Ico.U8 + r->Ico.U8) & 0xff));
					break;
				case Iop_Add16:
					res = IRExpr_Const(
						IRConst_U16((l->Ico.U16 + r->Ico.U16) & 0xffff));
					break;
				case Iop_Add32:
					res = IRExpr_Const(
						IRConst_U32((l->Ico.U32 + r->Ico.U32) & 0xffffffff));
					break;
				case Iop_Add64:
					res = IRExpr_Const(IRConst_U64(l->Ico.U64 + r->Ico.U64));
					break;
				case Iop_And1:
					res = IRExpr_Const(IRConst_U1(l->Ico.U1 & r->Ico.U1));
					break;
				case Iop_Or1:
					res = IRExpr_Const(IRConst_U1(l->Ico.U1 | r->Ico.U1));
					break;
				case Iop_And8:
					res = IRExpr_Const(IRConst_U8(l->Ico.U8 & r->Ico.U8));
					break;
				case Iop_And16:
					res = IRExpr_Const(IRConst_U16(l->Ico.U16 & r->Ico.U16));
					break;
				case Iop_And32:
					res = IRExpr_Const(IRConst_U32(l->Ico.U32 & r->Ico.U32));
					break;
				case Iop_Or32:
					res = IRExpr_Const(IRConst_U32(l->Ico.U32 | r->Ico.U32));
					break;
				case Iop_And64:
					res = IRExpr_Const(IRConst_U64(l->Ico.U64 & r->Ico.U64));
					break;
				case Iop_Xor8:
					res = IRExpr_Const(IRConst_U32(l->Ico.U8 ^ r->Ico.U8));
					break;
				case Iop_Xor32:
					res = IRExpr_Const(IRConst_U32(l->Ico.U32 ^ r->Ico.U32));
					break;
				default:
					printf("Warning: can't constant-fold in ");
					ppIRExpr(src, stdout);
					printf("\n");
					res = NULL;
					break;
				}
				if (res) {
					res = optimiseIRExprFP(res, opt, done_something);
					memmove(src->Iex.Associative.contents + x + 1,
						src->Iex.Associative.contents + x + 2,
						sizeof(IRExpr *) * (src->Iex.Associative.nr_arguments - x - 2));
					src->Iex.Associative.nr_arguments--;
					src->Iex.Associative.contents[x] = res;
					x--;
					*done_something = true;
				}
			} else if (!operationCommutes(src->Iex.Associative.op)) {
				break;
			}
		}
		}
		/* Some special cases for And1: 1 & x -> x, 0 & x -> 0 */
		if (src->Iex.Associative.op == Iop_And1) {
			__set_profiling(optimise_assoc_and1);
			/* If there are any constants, they'll be at the start. */
			while (src->Iex.Associative.nr_arguments > 1 &&
			       src->Iex.Associative.contents[0]->tag == Iex_Const) {
				IRConst *c = src->Iex.Associative.contents[0]->Iex.Const.con;
				*done_something = true;
				if (c->Ico.U1) {
					purgeAssocArgument(src, 0);
				} else {
					return src->Iex.Associative.contents[0];
				}
			}
		}
		/* Likewise for Or1 */
		if (src->Iex.Associative.op == Iop_Or1) {
			__set_profiling(optimise_assoc_or1);
			while (src->Iex.Associative.nr_arguments > 1 &&
			       src->Iex.Associative.contents[0]->tag == Iex_Const) {
				IRConst *c = src->Iex.Associative.contents[0]->Iex.Const.con;
				*done_something = true;
				if (!c->Ico.U1) {
					purgeAssocArgument(src, 0);
				} else {
					return src->Iex.Associative.contents[0];
				}
			}
		}

		/* x & x -> x, for any and-like operator */
		if (src->Iex.Associative.op >= Iop_And8 && src->Iex.Associative.op <= Iop_And64) {
			__set_profiling(optimise_assoc_x_and_x);
			for (int it1 = 0;
			     it1 < src->Iex.Associative.nr_arguments;
			     it1++) {
				for (int it2 = it1 + 1;
				     it2 < src->Iex.Associative.nr_arguments;
					) {
					if (definitelyEqual(src->Iex.Associative.contents[it1],
							    src->Iex.Associative.contents[it2],
							    opt)) {
						*done_something = true;
						purgeAssocArgument(src, it2);
					} else {
						it2++;
					}
				}
			}
		}

		/* a <-< b || b <-< a is definitely true. */
		if (src->Iex.Associative.op == Iop_Or1) {
			__set_profiling(optimise_assoc_happens_before);
			for (int i1 = 0; i1 < src->Iex.Associative.nr_arguments; i1++) {
				IRExpr *a1 = src->Iex.Associative.contents[i1];
				if (a1->tag != Iex_HappensBefore)
					continue;
				for (int i2 = i1 + 1; i2 < src->Iex.Associative.nr_arguments; i2++) {
					IRExpr *a2 = src->Iex.Associative.contents[i2];
					if (a2->tag != Iex_HappensBefore)
						continue;
					if ( a1->Iex.HappensBefore.before == a2->Iex.HappensBefore.after &&
					     a1->Iex.HappensBefore.after == a2->Iex.HappensBefore.before ) {
						*done_something = true;
						return IRExpr_Const(IRConst_U1(1));
					}
				}
			}
		}

		/* x + -x -> 0, for any plus-like operator, so remove
		 * both x and -x from the list. */
		/* Also do x & ~x -> 0, x ^ x -> 0, while we're here. */
		if (opt.xPlusMinusX) {
			__set_profiling(optimise_assoc_xplusminusx);
			bool plus_like;
			bool and_like;
			bool xor_like;
			plus_like = src->Iex.Associative.op >= Iop_Add8 && src->Iex.Associative.op <= Iop_Add64;
			and_like = (src->Iex.Associative.op >= Iop_And8 && src->Iex.Associative.op <= Iop_And64) ||
				src->Iex.Associative.op == Iop_And1;
			xor_like = src->Iex.Associative.op >= Iop_Xor8 && src->Iex.Associative.op <= Iop_Xor64;
			if (plus_like || and_like || xor_like) {
				for (int it1 = 0;
				     it1 < src->Iex.Associative.nr_arguments;
					) {
					IRExpr *l = src->Iex.Associative.contents[it1];
					int it2;
					for (it2 = 0;
					     it2 < src->Iex.Associative.nr_arguments;
					     it2++) {
						if (it2 == it1)
							continue;
						IRExpr *r = src->Iex.Associative.contents[it2];
						bool purge;
						if (plus_like) {
							if (r->tag == Iex_Unop) {
								purge = r->Iex.Unop.op >= Iop_Neg8 &&
									r->Iex.Unop.op <= Iop_Neg64;
							} else {
								purge = false;
							}
							if (purge)
								purge = l == r->Iex.Unop.arg;
						} else if (and_like) {
							if (r->tag == Iex_Unop)
								purge = (r->Iex.Unop.op >= Iop_Not8 &&
									 r->Iex.Unop.op <= Iop_Not64) ||
									r->Iex.Unop.op == Iop_Not1;
							else
								purge = false;
							if (purge)
								purge = l == r->Iex.Unop.arg;
						} else {
							assert(xor_like);
							purge = l == r;
						}

						if (purge) {
							*done_something = true;
							if (and_like) {
								/* x & ~x -> 0 and eliminates the entire expression. */
								switch (src->Iex.Associative.op) {
								case Iop_And8:
									return IRExpr_Const(IRConst_U8(0));
								case Iop_And16:
									return IRExpr_Const(IRConst_U16(0));
								case Iop_And32:
									return IRExpr_Const(IRConst_U32(0));
								case Iop_And64:
									return IRExpr_Const(IRConst_U64(0));
								case Iop_And1:
									return IRExpr_Const(IRConst_U1(0));
								default:
									abort();
								}
							}

							/* Careful: do the largest index first so that the
							   other index remains valid. */
							if (it1 < it2) {
								purgeAssocArgument(src, it2);
								src->Iex.Associative.contents[it1] =
									IRExpr_Const(IRConst_U64(0));
							} else {
								purgeAssocArgument(src, it1);
								src->Iex.Associative.contents[it2] =
									IRExpr_Const(IRConst_U64(0));
							}
							break;
						}
					}
					if (it2 == src->Iex.Associative.nr_arguments)
						it1++;
				}
			}
			if (src->Iex.Associative.nr_arguments == 0) {
				*done_something = true;
				switch (src->Iex.Associative.op) {
				case Iop_Add8:
				case Iop_Xor8:
					return IRExpr_Const(IRConst_U8(0));
				case Iop_Add16:
				case Iop_Xor16:
					return IRExpr_Const(IRConst_U16(0));
				case Iop_Add32:
				case Iop_Xor32:
					return IRExpr_Const(IRConst_U32(0));
				case Iop_Add64:
				case Iop_Xor64:
					return IRExpr_Const(IRConst_U64(0));

				case Iop_And1:
					return IRExpr_Const(IRConst_U1(1));
				case Iop_And8:
					return IRExpr_Const(IRConst_U8(0xff));
				case Iop_And16:
					return IRExpr_Const(IRConst_U16(0xffff));
				case Iop_And32:
					return IRExpr_Const(IRConst_U32(0xffffffff));
				case Iop_And64:
					return IRExpr_Const(IRConst_U64(0xfffffffffffffffful));

				case Iop_Or1:
					return IRExpr_Const(IRConst_U1(0));

				default:
					abort();
				}
			}
		}

		/* If the size is reduced to one, eliminate the assoc list */
		if (src->Iex.Associative.nr_arguments == 1) {
			*done_something = true;
			return src->Iex.Associative.contents[0];
		}
	}

	/* Now use some special rules to simplify a few classes of binops and unops. */
	if (src->tag == Iex_Unop) {
		__set_profiling(optimise_unop);
		if (src->Iex.Unop.op == Iop_64to1 &&
		    ((src->Iex.Unop.arg->tag == Iex_Associative &&
		      (src->Iex.Unop.arg->Iex.Associative.op == Iop_And1 ||
		       src->Iex.Unop.arg->Iex.Associative.op == Iop_Or1)) ||
		     (src->Iex.Unop.arg->tag == Iex_Binop &&
		      ((src->Iex.Unop.arg->Iex.Binop.op >= Iop_CmpEQ8 &&
			src->Iex.Unop.arg->Iex.Binop.op <= Iop_CmpNE64) ||
		       (src->Iex.Unop.arg->Iex.Binop.op >= Iop_CmpLT32S &&
			src->Iex.Unop.arg->Iex.Binop.op <= Iop_CmpLE64U))))) {
			/* This can happen sometimes because of the
			   way we simplify condition codes.  Very easy
			   fix: strip off the outer 64to1. */
			*done_something = true;
			return src->Iex.Unop.arg;
		}

		if (src->Iex.Unop.op >= Iop_8Uto16 &&
		    src->Iex.Unop.op <= Iop_32Uto64) {
			/* Get rid of signed upcasts; they tend to
			   show up where you don't want them, and they
			   don't actually do anything useful. */
			*done_something = true;
			return src->Iex.Unop.arg;
		}

		if (src->Iex.Unop.op == Iop_Not1 &&
		    src->Iex.Unop.arg->tag == Iex_Unop &&
		    src->Iex.Unop.arg->Iex.Unop.op == src->Iex.Unop.op) {
			*done_something = true;
			return src->Iex.Unop.arg->Iex.Unop.arg;
		}

		if (src->Iex.Unop.op == Iop_Not1 &&
		    src->Iex.Unop.arg->tag == Iex_Associative &&
		    (src->Iex.Unop.arg->Iex.Associative.op == Iop_And1 ||
		     src->Iex.Unop.arg->Iex.Associative.op == Iop_Or1)) {
			/* Convert ~(x & y) to ~x | ~y */
			IRExpr *a = IRExpr_Associative(&src->Iex.Unop.arg->Iex.Associative);
			for (int i = 0;
			     i < a->Iex.Associative.nr_arguments;
			     i++) {
				a->Iex.Associative.contents[i] =
					optimiseIRExprFP(
						IRExpr_Unop(
							Iop_Not1,
							a->Iex.Associative.contents[i]),
						opt,
						done_something);
			}
			if (a->Iex.Associative.op == Iop_And1)
				a->Iex.Associative.op = Iop_Or1;
			else
				a->Iex.Associative.op = Iop_And1;
			*done_something = true;
			return a;
		}
		if (src->Iex.Unop.op == Iop_BadPtr) {
			if (src->Iex.Unop.arg->tag == Iex_Associative &&
			    src->Iex.Unop.arg->Iex.Associative.op == Iop_Add64 &&
			    src->Iex.Unop.arg->Iex.Associative.nr_arguments == 2 &&
			    src->Iex.Unop.arg->Iex.Associative.contents[0]->tag == Iex_Const) {
				/* BadPtr(k + x) -> BadPtr(x) if k is
				 * a constant.  That's not strictly
				 * speaking true, because it's always
				 * possible that k is enough to push
				 * you over the boundary between valid
				 * and invalid memory, but that's so
				 * rare that I'm willing to ignore
				 * it. */
				*done_something = true;
				src->Iex.Unop.arg = src->Iex.Unop.arg->Iex.Associative.contents[1];
				return src;
			}
			if (src->Iex.Unop.arg->tag == Iex_Get &&
			    src->Iex.Unop.arg->Iex.Get.offset == offsetof(VexGuestAMD64State, guest_FS_ZERO)) {
				/* The FS register is assumed to
				   always point at valid memory. */
				*done_something = true;
				return IRExpr_Const(IRConst_U1(0));
			}
		}
		if (src->Iex.Unop.arg->tag == Iex_Const) {
			IRConst *c = src->Iex.Unop.arg->Iex.Const.con;
			switch (src->Iex.Unop.op) {
			case Iop_Neg8:
				*done_something = true;
				return IRExpr_Const(IRConst_U8(-c->Ico.U8));
			case Iop_Neg16:
				*done_something = true;
				return IRExpr_Const(IRConst_U16(-c->Ico.U16));
			case Iop_Neg32:
				*done_something = true;
				return IRExpr_Const(IRConst_U32(-c->Ico.U32));
			case Iop_Neg64:
				*done_something = true;
				return IRExpr_Const(IRConst_U64(-c->Ico.U64));
			case Iop_Not1:
				*done_something = true;
				return IRExpr_Const(IRConst_U1(c->Ico.U1 ^ 1));
			case Iop_32Uto64:
				*done_something = true;
				return IRExpr_Const(IRConst_U64(c->Ico.U32));
			case Iop_32Sto64:
				*done_something = true;
				return IRExpr_Const(IRConst_U64((int)c->Ico.U32));
			case Iop_1Uto8:
				*done_something = true;
				return IRExpr_Const(IRConst_U8(c->Ico.U1));
			case Iop_64to1:
				*done_something = true;
				return IRExpr_Const(IRConst_U1(!!c->Ico.U64));
			case Iop_64to32:
				*done_something = true;
				return IRExpr_Const(IRConst_U32(c->Ico.U64));
			case Iop_BadPtr:
				if (c->Ico.U64 < 4096) {
					*done_something = true;
					return IRExpr_Const(IRConst_U1(1));
				}
				/* Could sensibly just check that the
				 * target address isn't mapped here,
				 * on the assumption that anything not
				 * in the binary won't have a fixed
				 * address, but that then depends on
				 * the machine state, and I don't want
				 * to make optimiseIRExpr depend on
				 * machine state just for that. */
				break;
			default:
				printf("Cannot constant fold ");
				ppIRExpr(src, stdout);
				printf("\n");
				break;
			}
		}
	} else if (src->tag == Iex_Binop) {
		__set_profiling(optimise_binop);
		IRExpr *l = src->Iex.Binop.arg1;
		IRExpr *r = src->Iex.Binop.arg2;
		if (src->Iex.Binop.op == Iop_Xor1) {
			/* Convert A ^ B to (A & ~B) | (~A & B).  It's
			   bigger, but it's worth it just normalise
			   things. */
			*done_something = true;
			return optimiseIRExpr(
				IRExpr_Associative(
					Iop_Or1,
					IRExpr_Associative(
						Iop_And1,
						l,
						IRExpr_Unop(Iop_Not1, r),
						NULL),
					IRExpr_Associative(
						Iop_And1,
						r,
						IRExpr_Unop(Iop_Not1, l),
						NULL),
					NULL),
				opt,
				done_something);
		}
		if (src->Iex.Binop.op >= Iop_Sub8 &&
		    src->Iex.Binop.op <= Iop_Sub64) {
			/* Replace a - b with a + (-b), so as to
			   eliminate binary -. */
			*done_something = true;
			src->Iex.Binop.op = (IROp)(src->Iex.Binop.op - Iop_Sub8 + Iop_Add8);
			r = src->Iex.Binop.arg2 =
				optimiseIRExprFP(
					IRExpr_Unop( (IROp)((src->Iex.Binop.op - Iop_Add8) + Iop_Neg8),
						     r ),
					opt,
					done_something);
		}
		if (operationAssociates(src->Iex.Binop.op)) {
			/* Convert to an associative operation. */
			*done_something = true;
			return optimiseIRExpr(
				IRExpr_Associative(
					src->Iex.Binop.op,
					l,
					r,
					NULL),
				opt,
				done_something);
		}
		/* If a op b commutes, sort the arguments. */
		if (operationCommutes(src->Iex.Binop.op) &&
		    sortIRExprs(r, l)) {
			src->Iex.Binop.arg1 = r;
			src->Iex.Binop.arg2 = l;
			l = src->Iex.Binop.arg1;
			r = src->Iex.Binop.arg2;
			*done_something = true;
		}

		/* x << 0 -> x */
		if (src->Iex.Binop.op >= Iop_Shl8 && src->Iex.Binop.op <= Iop_Shl64 &&
		    r->tag == Iex_Const &&
		    r->Iex.Const.con->Ico.U8 == 0) {
			*done_something = true;
			return l;
		}

		/* We simplify == expressions with sums on the left
		   and right by trying to move all of the constants to
		   the left and all of the non-constants to the
		   right. */
		if (src->Iex.Binop.op == Iop_CmpEQ64) {
			if (r->tag == Iex_Associative &&
			    r->Iex.Associative.op == Iop_Add64 &&
			    r->Iex.Associative.contents[0]->tag == Iex_Const) {
				assert(r->Iex.Associative.nr_arguments > 1);
				/* a == C + b -> -C + a == b */
				IRExpr *cnst = r->Iex.Associative.contents[0];
				IRExpr *newRight = IRExpr_Associative(&r->Iex.Associative);
				purgeAssocArgument(newRight, 0);
				IRExpr *newLeft = IRExpr_Associative(
					Iop_Add64,
					IRExpr_Unop(
						Iop_Neg64,
						cnst),
					l,
					NULL);
				l = src->Iex.Binop.arg1 = optimiseIRExprFP(newLeft, opt, done_something);
				r = src->Iex.Binop.arg2 = optimiseIRExprFP(newRight, opt, done_something);
				*done_something = true;
			}
			if (l->tag == Iex_Associative &&
			    l->Iex.Associative.op == Iop_Add64) {
				/* C + a == b -> C == b - a */
				assert(l->Iex.Associative.nr_arguments > 1);
				IRExpr *newR = IRExpr_Associative(Iop_Add64, r, NULL);
				for (int it = 1;
				     it < l->Iex.Associative.nr_arguments;
				     it++)
					addArgumentToAssoc(newR,
							   IRExpr_Unop(
								   Iop_Neg64,
								   l->Iex.Associative.contents[it]));
				IRExpr *cnst = l->Iex.Associative.contents[0];
				if (cnst->tag != Iex_Const) {
					addArgumentToAssoc(newR,
							   IRExpr_Unop(
								   Iop_Neg64,
								   cnst));
					cnst = IRExpr_Const(IRConst_U64(0));
				}
				l = src->Iex.Binop.arg1 = cnst;
				r = src->Iex.Binop.arg2 = optimiseIRExprFP(newR, opt, done_something);
				*done_something = true;
			}
			/* If, in a == b, a and b are physically
			 * identical, the result is a constant 1. */
			if (physicallyEqual(l, r)) {
				*done_something = true;
				return IRExpr_Const(IRConst_U1(1));
			}

			/* Otherwise, a == b -> 0 == b - a, provided that a is not a constant. */
			if (l->tag != Iex_Const) {
				src->Iex.Binop.arg1 = IRExpr_Const(IRConst_U64(0));
				src->Iex.Binop.arg2 =
					IRExpr_Binop(
						Iop_Add64,
						r,
						IRExpr_Unop(
							Iop_Neg64,
							l));
				*done_something = true;
				return optimiseIRExpr(src, opt, done_something);
			}
		}

		/* And another one: -x == c -> x == -c if c is a constant. */
		if (src->Iex.Binop.op == Iop_CmpEQ64 &&
		    l->tag == Iex_Unop &&
		    l->Iex.Unop.op == Iop_Neg64 &&
		    r->tag == Iex_Const) {
			src->Iex.Binop.arg1 = l->Iex.Unop.arg;
			src->Iex.Binop.arg2 = IRExpr_Const(
				IRConst_U64(-r->Iex.Const.con->Ico.U64));
			*done_something = true;
			return optimiseIRExpr(src, opt, done_something);
		}

		/* If enabled, assume that the stack is ``private'',
		   in the sense that it doesn't alias with any global
		   variables, and is therefore never equal to any
		   constants which are present in the machine code. */
		if (opt.assumePrivateStack &&
		    src->Iex.Binop.op == Iop_CmpEQ64 &&
		    r->tag == Iex_Get &&
		    r->Iex.Get.offset == OFFSET_amd64_RSP &&
		    l->tag == Iex_Const) {
			*done_something = true;
			return IRExpr_Const(IRConst_U1(0));
		}

		/* If both arguments are constant, try to constant
		 * fold everything away. */
		if (l->tag == Iex_Const &&
		    r->tag == Iex_Const) {
			switch (src->Iex.Binop.op) {
			case Iop_CmpEQ32:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U1(
						l->Iex.Const.con->Ico.U32 ==
						r->Iex.Const.con->Ico.U32));
			case Iop_CmpLT64S:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U1(
						(long)l->Iex.Const.con->Ico.U64 <
						(long)r->Iex.Const.con->Ico.U64));
			case Iop_CmpLT64U:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U1(
						l->Iex.Const.con->Ico.U64 <
						r->Iex.Const.con->Ico.U64));
			case Iop_CmpEQ8:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U1(
						l->Iex.Const.con->Ico.U8 ==
						r->Iex.Const.con->Ico.U8));
			case Iop_CmpEQ16:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U1(
						l->Iex.Const.con->Ico.U16 ==
						r->Iex.Const.con->Ico.U16));
			case Iop_CmpEQ64:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U1(
						l->Iex.Const.con->Ico.U64 ==
						r->Iex.Const.con->Ico.U64));
			case Iop_Sar32:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U32(
						    (int)l->Iex.Const.con->Ico.U32 >>
						    r->Iex.Const.con->Ico.U8));
			case Iop_Sar64:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U64(
						    (long)l->Iex.Const.con->Ico.U64 >>
						    r->Iex.Const.con->Ico.U8));
			case Iop_Shl64:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U64(
						    l->Iex.Const.con->Ico.U64 <<
						    r->Iex.Const.con->Ico.U8));
			case Iop_CC_OverflowSub: {
				unsigned long a = l->Iex.Const.con->Ico.U64;
				unsigned long b = r->Iex.Const.con->Ico.U64;
				return IRExpr_Const(
					IRConst_U1(
						((a ^ b) & (a ^ (a - b))) >> 63));
			}
			case Iop_32HLto64:
				return IRExpr_Const(
					IRConst_U64(
						((unsigned long)l->Iex.Const.con->Ico.U32 << 32) |
						r->Iex.Const.con->Ico.U32));
			default:
				printf("Cannot constant fold binop %d: ", src->Iex.Binop.op);
				ppIRExpr(src, stdout);
				printf("\n");
				break;
			}
		}

	} else if (src->tag == Iex_Mux0X) {
		if (src->Iex.Mux0X.cond->tag == Iex_Const) {
			*done_something = true;
			if (src->Iex.Mux0X.cond->Iex.Const.con->Ico.U1)
				return src->Iex.Mux0X.exprX;
			else
				return src->Iex.Mux0X.expr0;
		}
	}

	return src;
}

static IRExpr *
optimiseIRExpr(IRExpr *e, const AllowableOptimisations &opt)
{
	bool ign;
	ign = false;
	e = optimiseIRExprFP(e, opt, &ign);
	e = simplifyIRExprAsBoolean(e, &ign);
	e = optimiseIRExprFP(e, opt, &ign);
	return e;
}

IRExpr *
simplifyIRExpr(IRExpr *a, const AllowableOptimisations &opt)
{
	__set_profiling(simplifyIRExpr);
	bool done_something;

	do {
		done_something = false;
		if (TIMEOUT)
			return a;
		a = optimiseIRExpr(a, opt, &done_something);
		a = simplifyIRExprAsBoolean(a, &done_something);
	} while (done_something);

	return a;
}

bool
definitelyEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt)
{
	IRExpr *r = optimiseIRExpr(IRExpr_Binop(Iop_CmpEQ64, a, b), opt);
	return r->tag == Iex_Const && r->Iex.Const.con->Ico.U1;
}
bool
definitelyNotEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt)
{
	IRExpr *r = optimiseIRExpr(IRExpr_Binop(Iop_CmpEQ64, a, b), opt);
	return r->tag == Iex_Const && !r->Iex.Const.con->Ico.U1;
}

bool
isBadAddress(IRExpr *e, const AllowableOptimisations &opt, OracleInterface *oracle)
{
	return e->tag == Iex_Const &&
		(long)e->Iex.Const.con->Ico.U64 < 4096;
}

bool
definitelyUnevaluatable(IRExpr *e, const AllowableOptimisations &opt, OracleInterface *oracle)
{
	if (TIMEOUT)
		return false;
	switch (e->tag) {
	case Iex_Binder:
	case Iex_Get:
	case Iex_RdTmp:
	case Iex_Const:
	case Iex_FreeVariable:
	case Iex_HappensBefore:
		return false;
	case Iex_GetI:
		return definitelyUnevaluatable(e->Iex.GetI.ix, opt, oracle);
	case Iex_Qop:
		if (definitelyUnevaluatable(e->Iex.Qop.arg4, opt, oracle))
			return true;
	case Iex_Triop:
		if (definitelyUnevaluatable(e->Iex.Qop.arg3, opt, oracle))
			return true;
	case Iex_Binop:
		if (definitelyUnevaluatable(e->Iex.Qop.arg2, opt, oracle))
			return true;
	case Iex_Unop:
		if (definitelyUnevaluatable(e->Iex.Qop.arg1, opt, oracle))
			return true;
		return false;
	case Iex_CCall:
		for (int x = 0; e->Iex.CCall.args[x]; x++)
			if (definitelyUnevaluatable(e->Iex.CCall.args[x], opt, oracle))
				return true;
		return false;
	case Iex_Mux0X:
		return definitelyUnevaluatable(e->Iex.Mux0X.cond, opt, oracle);
	case Iex_Associative:
		for (int x = 0; x < e->Iex.Associative.nr_arguments; x++)
			if (definitelyUnevaluatable(e->Iex.Associative.contents[x], opt, oracle))
				return true;
		return false;
	case Iex_Load:
		return isBadAddress(e->Iex.Load.addr, opt, oracle) ||
			definitelyUnevaluatable(e->Iex.Load.addr, opt, oracle);
	case Iex_ClientCall:
		for (int x = 0; e->Iex.ClientCall.args[x]; x++)
			if (definitelyUnevaluatable(e->Iex.ClientCall.args[x], opt, oracle))
				return true;
		return false;
	case Iex_ClientCallFailed:
		return definitelyUnevaluatable(e->Iex.ClientCallFailed.target, opt, oracle);
	}
	abort();
}

static IRType
random_irtype(void)
{
       return (IRType)((unsigned long)Ity_I8 + random() % 7);
}

static IRConst *
random_irconst(void)
{
	switch (random_irtype()) {
	case Ity_I8:
		return IRConst_U8(random() % 256);
	case Ity_I16:
		return IRConst_U16(random() % 65536);
	case Ity_I32:
		return IRConst_U32(random());
	case Ity_I64:
		return IRConst_U64(random());
	case Ity_F32:
	case Ity_I128:
		return random_irconst();
	case Ity_F64:
		return IRConst_F64(random() / (double)random());
	case Ity_V128:
		return IRConst_V128(random());
	default:
		abort();
	}
}

/* The random IRexprs consist of a possible-empty layer of And1, Or1,
 * Xor1, and Not1 operations, followed by a layer of comparisons and
 * boolean functions, and then other stuff underneath. */

static IRExpr *random_irexpr1(unsigned depth);

/* Build arithmetic layer */
static IRExpr *
random_irexpr3(unsigned depth)
{
	if (!depth)
		return IRExpr_Const(IRConst_U64(random()));
	switch (random() % 12) {
	case 0:
		return IRExpr_Const(IRConst_U64(random()));
	case 1:
		return IRExpr_Mux0X(
			random_irexpr1(depth - 1),
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 2:
		return IRExpr_Binop(
			Iop_Add64,
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 3:
		return IRExpr_Binop(
			Iop_And64,
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 4:
		return IRExpr_Binop(
			Iop_Or64,
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 5:
		return IRExpr_Binop(
			Iop_Xor64,
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 6:
		return IRExpr_Unop(
			Iop_Neg64,
			random_irexpr3(depth - 1));
	case 7:
		return IRExpr_Unop(
			Iop_Not64,
			random_irexpr3(depth - 1));
	case 8:
		return IRExpr_Binop(
			Iop_Sub64,
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 9:
		return IRExpr_Binop(
			Iop_Sar64,
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 10:
		return IRExpr_Get(
			(random() % 40) * 8,
			Ity_I64,
			73);
	case 11:
		return IRExpr_RdTmp(random() % 16, 73);
	}
	abort();
}

/* Build comparator layer */
static IRExpr *
random_irexpr2(unsigned depth)
{
	if (!depth)
		return IRExpr_Const(IRConst_U1(random() % 2));
	switch (random() % 6) {
	case 0:
		return IRExpr_Unop(Iop_BadPtr, random_irexpr3(depth - 1));
	case 1:
		return IRExpr_Binop(Iop_CmpEQ64,
				    random_irexpr3(depth - 1),
				    random_irexpr3(depth - 1));
	case 2:
		return IRExpr_Binop(Iop_CmpLT64U,
				    random_irexpr3(depth - 1),
				    random_irexpr3(depth - 1));
	case 3:
		return IRExpr_Binop(Iop_CmpLT64S,
				    random_irexpr3(depth - 1),
				    random_irexpr3(depth - 1));
	case 4:
		return IRExpr_Binop(Iop_CC_OverflowSub,
				    random_irexpr3(depth - 1),
				    random_irexpr3(depth - 1));
	case 5: {
		unsigned op;
		switch (random() % 4) {
		case 0:
			op = AMD64G_CC_OP_COPY;
			break;
		case 1:
			op = AMD64G_CC_OP_ADDQ;
			break;
		case 2:
			op = AMD64G_CC_OP_SUBQ;
			break;
		case 3:
			op = AMD64G_CC_OP_LOGICQ;
			break;
		default:
			abort();
		}
		
		return mkIRExprCCall(
			Ity_I64,
			0,
			"amd64g_calculate_condition",
			(void *)amd64g_calculate_condition,
			mkIRExprVec_5(IRExpr_Const(IRConst_U64(random() % 16)),
				      IRExpr_Const(IRConst_U64(op)),
				      random_irexpr3(depth - 1),
				      random_irexpr3(depth - 1),
				      random_irexpr3(depth - 1)));
	}
	}
	abort();
}

/* Build boolean layer */
static IRExpr *
random_irexpr1(unsigned depth)
{
	if (!depth)
		return IRExpr_Const(IRConst_U1(random() % 2));
	switch (random() % 5) {
	case 0:
		return IRExpr_Binop(Iop_And1,
				    random_irexpr1(depth - 1),
				    random_irexpr1(depth - 1));
	case 1:
		return IRExpr_Binop(Iop_Xor1,
				    random_irexpr1(depth - 1),
				    random_irexpr1(depth - 1));
	case 2:
		return IRExpr_Binop(Iop_Or1,
				    random_irexpr1(depth - 1),
				    random_irexpr1(depth - 1));
	case 3:
		return IRExpr_Unop(Iop_Not1,
				   random_irexpr1(depth - 1));
	case 4:
		return random_irexpr2(depth);
	}
	abort();
}

/* Check that sortIRExprs() produces vaguely sane results. */
void
sanity_check_irexpr_sorter(void)
{
	srandom(time(NULL));
#define NR_EXPRS 10000
	IRExpr *exprs[NR_EXPRS];
	int x;
	int y;

	printf("Generating %d random expressions\n", NR_EXPRS);
	for (x = 0; x < NR_EXPRS; x++)
		exprs[x] = random_irexpr1(3);

	printf("Ordering should be anti-reflexive.\n");
	for (x = 0; x < NR_EXPRS; x++)
		assert(!sortIRExprs(exprs[x], exprs[x]));

	printf("Ordering should be anti-symmetric.\n");
	for (x = 0; x < NR_EXPRS; x++) {
		for (y = x + 1; y < NR_EXPRS; y++) {
			if (sortIRExprs(exprs[x], exprs[y]))
				assert(!sortIRExprs(exprs[y], exprs[x]));
		}
	}

	/* Ordering must be transitive and total.  We check this by
	 * performing a naive topological sort on the expressions and
	 * then checking that whenever x < y exprs[x] < exprs[y]. */
	IRExpr *exprs2[NR_EXPRS];

	int nr_exprs2 = 0;
	int candidate;
	int probe;
	bool progress = true;
	printf("Toposorting...\n");
	while (nr_exprs2 < NR_EXPRS) {
		/* Try to find an ordering-minimal entry in the
		 * array.  */
		assert(progress);
		progress = false;
		for (candidate = 0; candidate < NR_EXPRS; candidate++) {
			if (!exprs[candidate])
				continue;
			for (probe = 0; probe < NR_EXPRS; probe++) {
				if (!exprs[probe])
					continue;
				if (sortIRExprs(exprs[probe], exprs[candidate])) {
					/* probe is less than
					   candidate, so candidate
					   fails. */
					break;
				}
			}
			if (probe == NR_EXPRS) {
				/* This candidate passes.  Add it to
				   the list. */
				exprs2[nr_exprs2] = exprs[candidate];
				exprs[candidate] = NULL;
				nr_exprs2++;
				progress = true;
			}
		}
	}

	/* Okay, have a topo sort.  The ordering is supposed to be
	   total, so that should have just been an O(n^3) selection
	   sort, and the array should now be totally sorted.  check
	   it. */
	printf("Check toposort is total...\n");
	for (x = 0; x < NR_EXPRS; x++)
		for (y = x + 1; y < NR_EXPRS; y++)
			assert(!sortIRExprs(exprs2[y], exprs2[x]));
#undef NR_EXPRS
}

class RandomExpressionEvalCtxt {
public:
	std::map<std::pair<IRTemp, unsigned>, unsigned long> temporaries;
	std::map<std::pair<unsigned, unsigned>, unsigned long> registers;
	std::map<unsigned long, int> badAddress;
};

static unsigned long
randomEvalExpression(RandomExpressionEvalCtxt &ctxt, IRExpr *expr)
{
	switch (expr->tag) {
	case Iex_Const:
		return expr->Iex.Const.con->Ico.U64;
	case Iex_RdTmp: {
		std::pair<IRTemp, unsigned> k(expr->Iex.RdTmp.tmp, expr->Iex.RdTmp.tid);
		if (!ctxt.temporaries.count(k))
			ctxt.temporaries[k] = random();
		return ctxt.temporaries[k];
	}
	case Iex_Get: {
		std::pair<unsigned, unsigned> k(expr->Iex.Get.offset, expr->Iex.Get.tid);
		if (!ctxt.registers.count(k))
			ctxt.registers[k] = random();
		return ctxt.registers[k];
		
	}
	case Iex_Mux0X:
		if (randomEvalExpression(ctxt, expr->Iex.Mux0X.cond))
			return randomEvalExpression(ctxt, expr->Iex.Mux0X.exprX);
		else
			return randomEvalExpression(ctxt, expr->Iex.Mux0X.expr0);
	case Iex_Binop: {
		unsigned long l = randomEvalExpression(ctxt, expr->Iex.Binop.arg1);
		unsigned long r = randomEvalExpression(ctxt, expr->Iex.Binop.arg2);
		switch (expr->Iex.Binop.op) {
		case Iop_And1:
		case Iop_And64:
			return l & r;
		case Iop_Xor1:
		case Iop_Xor64:
			return l ^ r;
		case Iop_Or1:
		case Iop_Or64:
			return l | r;
		case Iop_Sar64:
			return l >> r;
		case Iop_CmpEQ64:
			return l == r;
		case Iop_CmpLT64U:
			return l < r;
		case Iop_CmpLT64S:
			return (long)l < (long)r;
		case Iop_CC_OverflowSub:
			return ((l ^ r) & (l ^ (l - r))) >> 63;
		default:
			abort();
			return 0;
		}
	}
	case Iex_Associative: {
		std::vector<unsigned long> args;
		args.resize(expr->Iex.Associative.nr_arguments);
		for (int i = 0; i < expr->Iex.Associative.nr_arguments; i++)
			args[i] = randomEvalExpression(ctxt, expr->Iex.Associative.contents[i]);
		unsigned long acc;
		switch (expr->Iex.Associative.op) {
		case Iop_And1:
			acc = 1;
			for (unsigned i = 0; i < args.size(); i++)
				acc &= args[i];
			return acc;
		case Iop_And64:
			acc = ~0ul;
			for (unsigned i = 0; i < args.size(); i++)
				acc &= args[i];
			return acc;
		case Iop_Xor1:
		case Iop_Xor64:
			acc = 0;
			for (unsigned i = 0; i < args.size(); i++)
				acc ^= args[i];
			return acc;
		case Iop_Or1:
		case Iop_Or64:
			acc = 0;
			for (unsigned i = 0; i < args.size(); i++)
				acc |= args[i];
			return acc;
		case Iop_Add64:
			acc = 0;
			for (unsigned i = 0; i < args.size(); i++)
				acc += args[i];
			return acc;
		default:
			abort();
		}
	}
	case Iex_Unop: {
		unsigned long a = randomEvalExpression(ctxt, expr->Iex.Unop.arg);
		switch (expr->Iex.Unop.op) {
		case Iop_Not1:
			return !a;
		case Iop_Neg64:
			return -a;
		case Iop_Not64:
			return ~a;
		case Iop_BadPtr:
			if (a < 4096)
				return 1;
			if (!ctxt.badAddress.count(a / 4096))
				ctxt.badAddress[a/4096] = random() % 2;
			return ctxt.badAddress[a/4096];
		default:
			abort();
		}
	}
	case Iex_CCall:
		assert(!strcmp(expr->Iex.CCall.cee->name, "amd64g_calculate_condition"));
		return amd64g_calculate_condition(
			randomEvalExpression(ctxt, expr->Iex.CCall.args[0]),
			randomEvalExpression(ctxt, expr->Iex.CCall.args[1]),
			randomEvalExpression(ctxt, expr->Iex.CCall.args[2]),
			randomEvalExpression(ctxt, expr->Iex.CCall.args[3]),
			randomEvalExpression(ctxt, expr->Iex.CCall.args[4]));
	default:
		abort();
	}
	abort();
	return 0;
}

void
sanity_check_optimiser(void)
{
	/* x + -x -> 0 */
	IRExpr *start =
		IRExpr_Associative(
			Iop_Add64,
			IRExpr_Get(0, Ity_I64, 0),
			IRExpr_Unop(
				Iop_Neg64,
				IRExpr_Get(0, Ity_I64, 0)),
			NULL);
	IRExpr *end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	assert(physicallyEqual(end, IRExpr_Const(IRConst_U64(0))));
	/* x & ~x -> 0 */
	start = IRExpr_Associative(
		Iop_And1,
		IRExpr_Unop(
			Iop_Not1,
			IRExpr_Get(0, Ity_I64, 0)),
		IRExpr_Get(0, Ity_I64, 0),
		NULL);
	end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	assert(physicallyEqual(end, IRExpr_Const(IRConst_U64(0))));

	for (unsigned cntr1 = 0; cntr1 < 10000; cntr1++) {
		IRExpr *orig;
		IRExpr *optimised;
		do {
			orig = random_irexpr1(4);
			optimised = simplifyIRExpr(orig, AllowableOptimisations::defaultOptimisations);
		} while (physicallyEqual(orig, optimised));

		for (unsigned cntr2 = 0; cntr2 < 100; cntr2++) {
			RandomExpressionEvalCtxt ctxt;
			assert(ctxt.temporaries.size() == 0);
			assert(randomEvalExpression(ctxt, orig) == randomEvalExpression(ctxt, optimised));
		}
	}
}
