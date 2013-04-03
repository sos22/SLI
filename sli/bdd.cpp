#include "sli.h"
#include "bdd.hpp"
#include "simplify_irexpr.hpp"
#include "stacked_cdf.hpp"

#include "bdd_tmpl.cpp"

bool bdd_use_dereferences;

/* Convert @what so that it uses muxes wherever possible (i.e. no
   And1, Or1, or Not1 operators) and so that all muxes are at top
   level. */
static IRExpr *muxify(IRExpr *what, std::map<IRExpr *, IRExpr *> &memo);
static IRExpr *
_muxify(IRExpr *what, std::map<IRExpr *, IRExpr *> &memo)
{
	if (TIMEOUT)
		return what;
	switch (what->tag) {
	case Iex_Get:
		return what;
	case Iex_GetI:
		abort();
	case Iex_Qop: {
		IRExprQop *w = (IRExprQop *)what;
		IRExpr *a = muxify(w->arg1, memo);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Qop(
					       w->op,
					       ((IRExprMux0X *)a)->expr0,
					       w->arg2,
					       w->arg3,
					       w->arg4),
				       memo),
				muxify(IRExpr_Qop(
					       w->op,
					       ((IRExprMux0X *)a)->exprX,
					       w->arg2,
					       w->arg3,
					       w->arg4),
				       memo));
		IRExpr *b = muxify(w->arg2, memo);
		if (b->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)b)->cond,
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->expr0,
					       w->arg3,
					       w->arg4),
				       memo),
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->exprX,
					       w->arg3,
					       w->arg4),
				       memo));
		IRExpr *c = muxify(w->arg3, memo);
		if (c->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)c)->cond,
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       b,
					       ((IRExprMux0X *)c)->expr0,
					       w->arg4),
				       memo),
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       b,
					       ((IRExprMux0X *)c)->exprX,
					       w->arg4),
				       memo));
		IRExpr *d = muxify(w->arg4, memo);
		if (d->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)c)->cond,
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       b,
					       c,
					       ((IRExprMux0X *)d)->expr0),
				       memo),
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       b,
					       c,
					       ((IRExprMux0X *)d)->exprX),
				       memo));
		assert(a == w->arg1 && b == w->arg2 && c == w->arg3 && d == w->arg4);
		return what;
	}
	case Iex_Triop: {
		IRExprTriop *w = (IRExprTriop *)what;
		IRExpr *a = muxify(w->arg1, memo);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Triop(
					       w->op,
					       ((IRExprMux0X *)a)->expr0,
					       w->arg2,
					       w->arg3),
				       memo),
				muxify(IRExpr_Triop(
					       w->op,
					       ((IRExprMux0X *)a)->exprX,
					       w->arg2,
					       w->arg3),
				       memo));
		IRExpr *b = muxify(w->arg2, memo);
		if (b->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)b)->cond,
				muxify(IRExpr_Triop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->expr0,
					       w->arg3),
				       memo),
				muxify(IRExpr_Triop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->exprX,
					       w->arg3),
				       memo));
		IRExpr *c = muxify(w->arg3, memo);
		if (c->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)c)->cond,
				muxify(IRExpr_Triop(
					       w->op,
					       a,
					       b,
					       ((IRExprMux0X *)c)->expr0),
				       memo),
				muxify(IRExpr_Triop(
					       w->op,
					       a,
					       b,
					       ((IRExprMux0X *)c)->exprX),
				       memo));
		if (a == w->arg1 && b == w->arg2 && c == w->arg3)
			return what;
		else
			return IRExpr_Triop(w->op, a, b, c);
	}
	case Iex_Binop: {
		IRExprBinop *w = (IRExprBinop *)what;
		IRExpr *a = muxify(w->arg1, memo);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Binop(
					       w->op,
					       ((IRExprMux0X *)a)->expr0,
					       w->arg2),
				       memo),
				muxify(IRExpr_Binop(
					       w->op,
					       ((IRExprMux0X *)a)->exprX,
					       w->arg2),
				       memo));
		IRExpr *b = muxify(w->arg2, memo);
		if (b->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)b)->cond,
				muxify(IRExpr_Binop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->expr0),
				       memo),
				muxify(IRExpr_Binop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->exprX),
				       memo));
		assert(a == w->arg1 && b == w->arg2);
		return what;
	}
	case Iex_Unop: {
		IRExprUnop *w = (IRExprUnop *)what;
		IRExpr *a = muxify(w->arg, memo);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Unop(
					       w->op,
					       ((IRExprMux0X *)a)->expr0),
				       memo),
				muxify(IRExpr_Unop(
					       w->op,
					       ((IRExprMux0X *)a)->exprX),
				       memo));
		if (w->op == Iop_Not1)
			return IRExpr_Mux0X(
				a,
				IRExpr_Const_U1(true),
				IRExpr_Const_U1(false));
		assert(a == w->arg);
		return w;
	}
	case Iex_Const:
		return what;
	case Iex_Mux0X: {
		IRExprMux0X *m = (IRExprMux0X *)what;
		IRExpr *cond = muxify(m->cond, memo);
		IRExpr *expr0 = muxify(m->expr0, memo);
		IRExpr *exprX = muxify(m->exprX, memo);
		if (cond == m->cond && expr0 == m->expr0 && exprX == m->exprX)
			return what;
		else
			return IRExpr_Mux0X(cond, expr0, exprX);
	}
	case Iex_CCall: {
		IRExprCCall *cee = (IRExprCCall *)what;
		IRExpr *a;
		int i;

		/* Shut compiler up */
		a = (IRExpr *)0xf001;

		for (i = 0; cee->args[i]; i++) {
			a = muxify(cee->args[i], memo);
			if (a->tag == Iex_Mux0X)
				break;
			assert(a == cee->args[i]);
		}
		if (!cee->args[i])
			return what;
		int nr_args;
		for (nr_args = i; cee->args[nr_args]; nr_args++)
			;
		IRExpr **newArgs0 = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_args + 1);
		memcpy(newArgs0, cee->args, sizeof(cee->args[0]) * (nr_args + 1));
		newArgs0[i] = ((IRExprMux0X *)a)->expr0;
		IRExpr **newArgsX = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_args + 1);
		memcpy(newArgsX, cee->args, sizeof(cee->args[0]) * (nr_args + 1));
		newArgsX[i] = ((IRExprMux0X *)a)->exprX;
		return muxify(
			IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				IRExpr_CCall(cee->cee, cee->retty, newArgs0),
				IRExpr_CCall(cee->cee, cee->retty, newArgsX)),
			memo);
	}
	case Iex_Associative: {
		IRExprAssociative *iea = (IRExprAssociative *)what;
		if (iea->op == Iop_And1) {
			IRExpr *acc = IRExpr_Const_U1(true);
			IRExpr *fls = IRExpr_Const_U1(false);
			for (int i = 0; i < iea->nr_arguments; i++)
				acc = IRExpr_Mux0X(
					muxify(iea->contents[i], memo),
					fls,
					acc);
			return acc;
		} else if (iea->op == Iop_Or1) {
			IRExpr *acc = IRExpr_Const_U1(false);
			IRExpr *tru = IRExpr_Const_U1(true);
			for (int i = 0; i < iea->nr_arguments; i++)
				acc = IRExpr_Mux0X(
					muxify(iea->contents[i], memo),
					acc,
					tru);
			return acc;
		}

		assert(iea->nr_arguments > 0);
		IRExpr *a = (IRExpr *)0xdead;
		int i;
		for (i = 0; i < iea->nr_arguments; i++) {
			a = muxify(iea->contents[i], memo);
			if (a->tag == Iex_Mux0X)
				break;
			assert(a == iea->contents[i]);
		}
		if (i == iea->nr_arguments)
			return what;
		IRExpr **newArgs0 = alloc_irexpr_array(iea->nr_arguments);
		memcpy(newArgs0, iea->contents, sizeof(iea->contents[0]) * iea->nr_arguments);
		newArgs0[i] = ((IRExprMux0X *)a)->expr0;
		IRExpr **newArgsX = alloc_irexpr_array(iea->nr_arguments);
		memcpy(newArgsX, iea->contents, sizeof(iea->contents[0]) * iea->nr_arguments);
		newArgsX[i] = ((IRExprMux0X *)a)->exprX;
		IRExprAssociative *exp0 = IRExpr_Associative_Claim(iea->op, iea->nr_arguments, newArgs0);
		IRExprAssociative *expX = IRExpr_Associative_Claim(iea->op, iea->nr_arguments, newArgsX);
		return muxify(
			IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				exp0,
				expX),
			memo);
	}
		
	case Iex_Load: {
		IRExprLoad *l = (IRExprLoad *)what;
		IRExpr *a = muxify(l->addr, memo);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Load(
					       l->ty,
					       ((IRExprMux0X *)a)->expr0),
				       memo),
				muxify(IRExpr_Load(
					       l->ty,
					       ((IRExprMux0X *)a)->exprX),
				       memo));
		assert(a == l->addr);
		return what;
	}
	case Iex_HappensBefore:
		return what;
	case Iex_FreeVariable:
		return what;
	case Iex_EntryPoint:
		return what;
	case Iex_ControlFlow:
		return what;
	}
	abort();
}

static IRExpr *
muxify(IRExpr *what, std::map<IRExpr *, IRExpr *> &memo)
{
	auto it_did_insert = memo.insert(std::pair<IRExpr *, IRExpr *>(what, (IRExpr *)0xf001));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = _muxify(what, memo);
	return it->second;
}

static bool
isZero(IRExprConst *iec)
{
	switch (iec->Ico.ty) {
	case Ity_I1:
		return iec->Ico.content.U1 == 0;
	case Ity_I8:
		return iec->Ico.content.U8 == 0;
	case Ity_I16:
		return iec->Ico.content.U16 == 0;
	case Ity_I32:
		return iec->Ico.content.U32 == 0;
	case Ity_I64:
		return iec->Ico.content.U64 == 0;
	case Ity_I128:
		return iec->Ico.content.U128.lo == 0 &&
			iec->Ico.content.U128.hi == 0;
	case Ity_INVALID:
		abort();
	}
	abort();
}

/* Check if something is ``small''.  BadPtr(k + x) == BadPtr(x)
   whenever k is small. */
static bool
isSmall64(IRExpr *what)
{
	if (what->tag == Iex_Const) {
		IRExprConst *ico = (IRExprConst *)what;
		assert(ico->Ico.ty == Ity_I64);
		return ico->Ico.content.U64 < (1ul << 22);
	}
	if (what->tag == Iex_Unop) {
		IRExprUnop *u = (IRExprUnop *)what;
		return u->op == Iop_8Uto64 ||
			u->op == Iop_16Uto64;
	}
	return false;
}
/* Check if something is a small mask.  BadPtr(k & x) == BadPtr(x)
   whenever k is a small mask. */
static bool
isSmallMask64(IRExpr *what)
{
	if (what->tag == Iex_Const) {
		IRExprConst *ico = (IRExprConst *)what;
		assert(ico->Ico.ty == Ity_I64);
		return ~ico->Ico.content.U64 < (1ul << 22);
	}
	if (what->tag == Iex_Unop) {
		IRExprUnop *u = (IRExprUnop *)what;
		return u->op == Iop_Not64 && isSmall64(u->arg);
	}
	return false;
}

/* Some very quick simplifications which are always applied to the
 * condition of BDD internal nodes.  This isn't much more than just
 * constant folding. */
static IRExpr *
_quickSimplify(IRExpr *a, std::map<IRExpr *, IRExpr *> &memo)
{
	switch (a->tag) {
	case Iex_Unop: {
		IRExprUnop *au = (IRExprUnop *)a;
		auto arg = quickSimplify(au->arg, memo);
		top_unop:
		if (arg->tag == Iex_Associative) {
			IRExprAssociative *argA = (IRExprAssociative *)arg;
			if (au->op >= Iop_Neg8 &&
			    au->op <= Iop_Neg64 &&
			    argA->op >= Iop_Add8 &&
			    argA->op <= Iop_Add64) {
				/* Turn -(x + y) into -x + -y */
				IRExpr *args[argA->nr_arguments];
				for (int i = 0; i < argA->nr_arguments; i++) {
					args[i] = quickSimplify(IRExpr_Unop(au->op, argA->contents[i]), memo);
				}
				return quickSimplify(
					IRExpr_Associative_Copy(
						argA->op,
						argA->nr_arguments,
						args),
					memo);
			}
			if (au->op == Iop_BadPtr &&
			    (argA->op == Iop_Add64 || argA->op == Iop_Or64)) {
				if (isSmall64(argA->contents[0])) {
					if (argA->nr_arguments == 2) {
						arg = argA->contents[1];
					} else {
						arg = quickSimplify(
							IRExpr_Associative_Copy(
								argA->op,
								argA->nr_arguments - 1,
								argA->contents + 1),
							memo);
					}
					goto top_unop;
				} else if (argA->contents[0]->tag == Iex_Const) {
					IRExprConst *cnst = (IRExprConst *)argA->contents[0];
					unsigned long c = cnst->Ico.content.U64;
					unsigned long newC = c & ~((1ul << 22) - 1);
					if (c != newC) {
						assert(newC != 0);
						IRExpr *newCnst = IRExpr_Const_U64(newC);
						IRExpr *newArgs[argA->nr_arguments];
						memcpy(newArgs, argA->contents, sizeof(newArgs[0]) * argA->nr_arguments);
						newArgs[0] = newCnst;
						arg = quickSimplify(
							IRExpr_Associative_Copy(
								argA->op,
								argA->nr_arguments,
								newArgs),
							memo);
						goto top_unop;
					}
				}
			}

			if (au->op == Iop_BadPtr &&
			    argA->op == Iop_And64 &&
			    isSmallMask64(argA->contents[0])) {
				if (argA->nr_arguments == 2) {
					arg = argA->contents[1];
				} else {
					arg = quickSimplify(
						IRExpr_Associative_Copy(
							argA->op,
							argA->nr_arguments - 1,
							argA->contents + 1),
						memo);
				}
				goto top_unop;
			}

			/* Narrowing operations should usually be
			   pushed through associative ones. */
			bool simple_narrowing =
				(au->op == Iop_64to8 ||
				 au->op == Iop_64to16 ||
				 au->op == Iop_64to32 ||
				 au->op == Iop_32to8 ||
				 au->op == Iop_32to16 ||
				 au->op == Iop_16to8);
			bool lane_narrowing =
				(au->op == Iop_16HIto8 ||
				 au->op == Iop_32HIto16 ||
				 au->op == Iop_64HIto32 ||
				 au->op == Iop_128HIto64);
			bool mul = argA->op >= Iop_Mul8 && argA->op <= Iop_Mul64;
			bool otherSafe = (argA->op >= Iop_Add8 && argA->op <= Iop_Add64) ||
				(argA->op >= Iop_And8 && argA->op <= Iop_And64) ||
				(argA->op >= Iop_Or8 && argA->op <= Iop_Or64);
			if ((simple_narrowing && mul) ||
			    ((simple_narrowing || lane_narrowing) &&
			     (mul || otherSafe))) {
				IRExpr *args[argA->nr_arguments];
				for (int i = 0; i < argA->nr_arguments; i++) {
					args[i] = quickSimplify(IRExpr_Unop(au->op, argA->contents[i]),
								memo);
				}
				int op = (int)argA->op;
				switch (argA->type()) {
				case Ity_I8:
					break;
				case Ity_I16:
					op--;
					break;
				case Ity_I32:
					op -= 2;
					break;
				case Ity_I64:
					op -= 3;
					break;
				case Ity_INVALID:
				case Ity_I1:
				case Ity_I128:
					abort();
				}
				switch (au->type()) {
				case Ity_I8:
					break;
				case Ity_I16:
					op++;
					break;
				case Ity_I32:
					op+=2;
					break;
				case Ity_I64:
					op+=3;
					break;
				case Ity_INVALID:
				case Ity_I1:
				case Ity_I128:
					abort();
				}
				return quickSimplify(IRExpr_Associative_Copy(
							     (IROp)op,
							     argA->nr_arguments,
							     args),
						     memo);
			}
		}

		IROp op = au->op;
		if (arg->tag == Iex_Unop) {
			IRExprUnop *argU = (IRExprUnop *)arg;
			if (inverseUnops(au->op, argU->op)) {
				return argU->arg;
			}
			IROp c;
			if (shortCircuitableUnops(au->op, argU->op, &c)) {
				arg = argU->arg;
				op = c;
			}
		}

		if (au->op == Iop_64to32 && arg->tag == Iex_Binop) {
			IRExprBinop *ieb = (IRExprBinop *)arg;
			if (ieb->op == Iop_DivModS64to32) {
				arg = quickSimplify(IRExpr_Binop(
							    Iop_DivS64,
							    ieb->arg1,
							    ieb->arg2),
						    memo);
			} else if (ieb->op == Iop_DivModU64to32) {
				arg = quickSimplify(IRExpr_Binop(
							    Iop_DivU64,
							    ieb->arg1,
							    ieb->arg2),
						    memo);
			}
		}

		if (arg->tag == Iex_Const) {
			IRExprConst *argc = (IRExprConst *)arg;
			switch (op) {
#define do_uconv(_from, _to)						\
				case Iop_ ## _from ## Uto ## _to:	\
					return IRExpr_Const_U ## _to (argc->Ico.content.U ## _from)
				do_uconv(1, 8);
				//do_uconv(1, 16); /*1Uto16 doesn't exist, for some reason */
				do_uconv(1, 32);
				do_uconv(1, 64);
				do_uconv(8, 16);
				do_uconv(8, 32);
				do_uconv(8, 64);
				do_uconv(16, 32);
				do_uconv(16, 64);
				do_uconv(32, 64);
#undef do_uconv
#define do_sconv(_from, _fromt, _to, _tot)				\
				case Iop_ ## _from ## Sto ## _to:	\
					return IRExpr_Const_U ## _to (	\
						(_tot)(_fromt)argc->Ico.content.U ## _from )
				do_sconv(8, char, 16, short);
				do_sconv(8, char, 32, int);
				do_sconv(8, char, 64, long);
				do_sconv(16, short, 32, int);
				do_sconv(16, short, 64, long);
				do_sconv(32, int, 64, long);
#undef do_sconv
#define do_downconv(_from, _to)						\
				case Iop_ ## _from ## to ## _to:	\
					return IRExpr_Const_U ## _to (argc->Ico.content.U ## _from)
				do_downconv(64, 1);
				do_downconv(64, 8);
				do_downconv(64, 16);
				do_downconv(64, 32);
				do_downconv(32, 1);
				do_downconv(32, 8);
				do_downconv(32, 16);
				do_downconv(16, 1);
				do_downconv(16, 8);
				do_downconv(8, 1);
#undef do_downconv
			case Iop_128to64:
				return IRExpr_Const_U64(argc->Ico.content.U128.lo);
			case Iop_128HIto64:
				return IRExpr_Const_U64(argc->Ico.content.U128.hi);
			case Iop_64HIto32:
				return IRExpr_Const_U32(argc->Ico.content.U64 >> 32);
			case Iop_64UtoV128:
				return IRExpr_Const_U128(0, argc->Ico.content.U64);
			case Iop_BadPtr:
				/* Can't constant fold these without an
				 * IRExprOptimisations struct. */
				if (argc->Ico.content.U64 < 4096)
					return IRExpr_Const_U1(true);
				if (arg == au->arg)
					return au;
				else
					return IRExprUnop::mk(au->op, arg);
				break;
			case Iop_Neg8:
				return IRExpr_Const_U8(-argc->Ico.content.U8);
			case Iop_Neg16:
				return IRExpr_Const_U16(-argc->Ico.content.U16);
			case Iop_Neg32:
				return IRExpr_Const_U32(-argc->Ico.content.U32);
			case Iop_Neg64:
				return IRExpr_Const_U64(-argc->Ico.content.U64);
			case Iop_Not1:
				return IRExpr_Const_U1(!argc->Ico.content.U1);
			case Iop_Not8:
				return IRExpr_Const_U8(~argc->Ico.content.U8);
			case Iop_Not16:
				return IRExpr_Const_U16(~argc->Ico.content.U16);
			case Iop_Not32:
				return IRExpr_Const_U32(~argc->Ico.content.U32);
			case Iop_Not64:
				return IRExpr_Const_U64(~argc->Ico.content.U64);
			default:
				abort();
			}
		}
		if (arg == au->arg && au->op == op)
			return au;
		else
			return IRExprUnop::mk(op, arg);
	}
	case Iex_Binop: {
		IRExprBinop *_ieb = (IRExprBinop *)a;
		auto arg1 = quickSimplify(_ieb->arg1, memo);
		auto arg2 = quickSimplify(_ieb->arg2, memo);

		IRExprConst *arg1C = (arg1->tag == Iex_Const) ? (IRExprConst *)arg1 : NULL;
		IRExprConst *arg2C = (arg2->tag == Iex_Const) ? (IRExprConst *)arg2 : NULL;
		IRExprAssociative *arg1A = (arg1->tag == Iex_Associative) ? (IRExprAssociative *)arg1 : NULL;
		IRExprAssociative *arg2A = (arg2->tag == Iex_Associative) ? (IRExprAssociative *)arg2 : NULL;
		IRExprUnop *arg2U = (arg2->tag == Iex_Unop) ? (IRExprUnop *)arg2 : NULL;
		bool is_eq = _ieb->op >= Iop_CmpEQ8 && _ieb->op <= Iop_CmpEQ64;

		/* x < 0 is always false, for unsigned comparisons. */
		if (_ieb->op >= Iop_CmpLT8U &&
		    _ieb->op <= Iop_CmpLT64U &&
		    arg2C &&
		    isZero(arg2C)) {
			return IRExpr_Const_U1(0);
		}
		/* We can sometimes simplify a bit if we have k1 == (k2 & x)
		   or k1 == (k2 | x) */
		if (is_eq && arg1C && arg2A && arg2A->contents[0]->tag == Iex_Const) {
			IRExprConst *cnst2 = (IRExprConst *)arg2A->contents[0];
			bool doit = false;
			switch (arg2A->op) {
			case Iop_Or8:
				doit = !!(cnst2->Ico.content.U8 & ~arg1C->Ico.content.U8);
				break;
			case Iop_Or16:
				doit = !!(cnst2->Ico.content.U16 & ~arg1C->Ico.content.U16);
				break;
			case Iop_Or32:
				doit = !!(cnst2->Ico.content.U32 & ~arg1C->Ico.content.U32);
				break;
			case Iop_Or64:
				doit = !!(cnst2->Ico.content.U64 & ~arg1C->Ico.content.U64);
				break;
			case Iop_And8:
				doit = !!(arg1C->Ico.content.U8 & ~cnst2->Ico.content.U8);
				break;
			case Iop_And16:
				doit = !!(arg1C->Ico.content.U16 & ~cnst2->Ico.content.U16);
				break;
			case Iop_And32:
				doit = !!(arg1C->Ico.content.U32 & ~cnst2->Ico.content.U32);
				break;
			case Iop_And64:
				doit = !!(arg1C->Ico.content.U64 & ~cnst2->Ico.content.U64);
				break;
			default:
				doit = false;
				break;
			}
			if (doit) {
				return IRExpr_Const_U1(false);
			}
		}
		/* k1 == k2 + x -> k1 - k2 == x */
		if (is_eq && arg1C && arg2A && arg2A->op >= Iop_Add8 && arg2A->op <= Iop_Add64 &&
		    arg2A->contents[0]->tag == Iex_Const) {
			IRExprConst *k2 = (IRExprConst *)arg2A->contents[0];
			IRExpr *newR;
			if (arg2A->nr_arguments == 2) {
				newR = arg2A->contents[1];
			} else {
				newR = IRExpr_Associative_Copy(
					arg2A->op,
					arg2A->nr_arguments - 1,
					arg2A->contents + 1);
			}
			IRExpr *newL;
			switch (_ieb->op) {
			case Iop_CmpEQ8:
				newL = IRExpr_Const_U8(arg1C->Ico.content.U8 - k2->Ico.content.U8);
				break;
			case Iop_CmpEQ16:
				newL = IRExpr_Const_U16(arg1C->Ico.content.U16 - k2->Ico.content.U16);
				break;
			case Iop_CmpEQ32:
				newL = IRExpr_Const_U32(arg1C->Ico.content.U32 - k2->Ico.content.U32);
				break;
			case Iop_CmpEQ64:
				newL = IRExpr_Const_U64(arg1C->Ico.content.U64 - k2->Ico.content.U64);
				break;
			default:
				abort();
			}
			return quickSimplify(IRExpr_Binop(_ieb->op, newL, newR), memo);						
		}
		/* Turn 0 == x - y into x == y */
		if (is_eq && arg1C && isZero(arg1C) &&
		    arg2A && arg2A->op >= Iop_Add8 && arg2A->op <= Iop_Add64 &&
		    arg2A->contents[1]->tag == Iex_Unop) {
			IRExprUnop *uu = (IRExprUnop *)arg2A->contents[1];
			if (uu->op >= Iop_Neg8 && uu->op <= Iop_Neg64) {
				return quickSimplify(
					IRExpr_Binop(_ieb->op, arg2A->contents[0], uu->arg),
					memo);
			}
		}
		/* Turn k == -(x) into just -k == x */
		if (is_eq && arg1C && arg2U && arg2U->op >= Iop_Neg8 && arg2U->op <= Iop_Neg64) {
			IRExpr *newR = arg2U->arg;
			IRExpr *newL;
			switch (_ieb->op) {
			case Iop_CmpEQ8:
				newL = IRExpr_Const_U8(-arg1C->Ico.content.U8);
				break;
			case Iop_CmpEQ16:
				newL = IRExpr_Const_U16(-arg1C->Ico.content.U16);
				break;
			case Iop_CmpEQ32:
				newL = IRExpr_Const_U32(-arg1C->Ico.content.U32);
				break;
			case Iop_CmpEQ64:
				newL = IRExpr_Const_U64(-arg1C->Ico.content.U64);
				break;
			default:
				abort();
			}
			return quickSimplify(IRExpr_Binop(_ieb->op, newL, newR), memo);
		}
		/* k == widen(X) can be dealt with early */
		if (is_eq && arg1C && arg2U && arg2U->op >= Iop_8Uto16 && arg2U->op <= Iop_32Sto64) {
			switch (arg2U->op) {
			case Iop_8Uto16:
				if (arg1C->Ico.content.U16 & 0xff00) {
					return IRExpr_Const_U1(false);
				} else {
					return quickSimplify(
						IRExpr_Binop(Iop_CmpEQ8,
							     IRExpr_Const_U8(arg1C->Ico.content.U16 & 0xff),
							     arg2U->arg),
						memo);
				}
			case Iop_8Uto32:
				if (arg1C->Ico.content.U32 & 0xffffff00) {
					return IRExpr_Const_U1(false);
				} else {
					return quickSimplify(
						IRExpr_Binop(Iop_CmpEQ8,
							     IRExpr_Const_U8(arg1C->Ico.content.U32 & 0xff),
							     arg2U->arg),
						memo);
				}
			case Iop_8Uto64:
				if (arg1C->Ico.content.U64 & ~0xfful) {
					return IRExpr_Const_U1(false);
				} else {
					return quickSimplify(
						IRExpr_Binop(Iop_CmpEQ8,
							     IRExpr_Const_U8(arg1C->Ico.content.U64 & 0xff),
							     arg2U->arg),
						memo);
				}
			case Iop_16Uto32:
				if (arg1C->Ico.content.U32 & 0xffff0000) {
					return IRExpr_Const_U1(false);
				} else {
					return quickSimplify(
						IRExpr_Binop(Iop_CmpEQ16,
							     IRExpr_Const_U16(arg1C->Ico.content.U32 & 0xffff),
							     arg2U->arg),
						memo);
				}
			case Iop_16Uto64:
				if (arg1C->Ico.content.U64 & ~0xfffful) {
					return IRExpr_Const_U1(false);
				} else {
					return quickSimplify(
						IRExpr_Binop(Iop_CmpEQ16,
							     IRExpr_Const_U16(arg1C->Ico.content.U64 & 0xffff),
							     arg2U->arg),
						memo);
				}
			case Iop_32Uto64:
				if (arg1C->Ico.content.U64 & ~0xfffffffful) {
					return IRExpr_Const_U1(false);
				} else {
					return quickSimplify(
						IRExpr_Binop(Iop_CmpEQ32,
							     IRExpr_Const_U32(arg1C->Ico.content.U64 & 0xffffffff),
							     arg2U->arg),
						memo);
				}
			case Iop_8Sto16:
				if ((char)arg1C->Ico.content.U16 != arg1C->Ico.content.U16) {
					return IRExpr_Const_U1(false);
				} else {
					return quickSimplify(
						IRExpr_Binop(Iop_CmpEQ8,
							     IRExpr_Const_U8(arg1C->Ico.content.U16 & 0xff),
							     arg2U->arg),
						memo);
				}
			case Iop_8Sto32:
				if ((unsigned)(int)(char)arg1C->Ico.content.U32 != arg1C->Ico.content.U32) {
					return IRExpr_Const_U1(false);
				} else {
					return quickSimplify(
						IRExpr_Binop(Iop_CmpEQ8,
							     IRExpr_Const_U8(arg1C->Ico.content.U32 & 0xff),
							     arg2U->arg),
						memo);
				}
			case Iop_8Sto64:
				if ((unsigned long)(long)(char)arg1C->Ico.content.U64 != arg1C->Ico.content.U64) {
					return IRExpr_Const_U1(false);
				} else {
					return quickSimplify(
						IRExpr_Binop(Iop_CmpEQ8,
							     IRExpr_Const_U8(arg1C->Ico.content.U64 & 0xff),
							     arg2U->arg),
						memo);
				}
			case Iop_16Sto32:
				if ((unsigned)(int)(short)arg1C->Ico.content.U32 != arg1C->Ico.content.U32) {
					return IRExpr_Const_U1(false);
				} else {
					return quickSimplify(
						IRExpr_Binop(Iop_CmpEQ16,
							     IRExpr_Const_U16(arg1C->Ico.content.U32 & 0xffff),
							     arg2U->arg),
						memo);
				}
			case Iop_16Sto64:
				if ((unsigned long)(long)(short)arg1C->Ico.content.U64 != arg1C->Ico.content.U64) {
					return IRExpr_Const_U1(false);
				} else {
					return quickSimplify(
						IRExpr_Binop(Iop_CmpEQ16,
							     IRExpr_Const_U16(arg1C->Ico.content.U64 & 0xffff),
							     arg2U->arg),
						memo);
				}
			case Iop_32Sto64:
				if ((unsigned long)(long)(int)arg1C->Ico.content.U64 != arg1C->Ico.content.U64) {
					return IRExpr_Const_U1(false);
				} else {
					return quickSimplify(
						IRExpr_Binop(Iop_CmpEQ32,
							     IRExpr_Const_U32(arg1C->Ico.content.U64 & 0xffffffff),
							     arg2U->arg),
						memo);
				}
			default:
				abort();
			}
		}

		/* k | (m & x) == m & x' where k & m == 0, k != 0 -> false */
		if (is_eq &&
		    arg1A &&
		    arg1A->op >= Iop_Or8 && arg1A->op <= Iop_Or64 &&
		    arg2A &&
		    arg2A->op >= Iop_And8 && arg2A->op <= Iop_And64 &&
		    arg1A->contents[0]->tag == Iex_Const &&
		    arg1A->contents[1]->tag == Iex_Associative &&
		    ((IRExprAssociative *)arg1A->contents[1])->op == arg2A->op &&
		    arg2A->contents[0] == ((IRExprAssociative *)arg1A->contents[1])->contents[0]) {
			auto k = (IRExprConst *)arg1A->contents[0];
			auto m = (IRExprConst *)arg2A->contents[0];
			assert(k->Ico.content.U64);
			assert(!(k->Ico.content.U64 & m->Ico.content.U64));
			return IRExpr_Const_U1(false);
		}

		/* Unique free variables can never be equal to
		   constants, LDs, or the initial value of a
		   register. */
		if (is_eq &&
		    arg2->tag == Iex_FreeVariable &&
		    ((IRExprFreeVariable *)arg2)->isUnique &&
		    (arg1->tag == Iex_Const ||
		     arg1->tag == Iex_Load ||
		     (arg1->tag == Iex_Get &&
		      ((IRExprGet *)arg1)->reg.gen() == (unsigned)-1))) {
			return IRExpr_Const_U1(false);
		}

		if (_ieb->op >= Iop_CmpLT8U && _ieb->op <= Iop_CmpLT64U) {
			if (arg1A && arg1A->nr_arguments == 2 &&
			    arg1A->op >= Iop_Add8 && arg1A->op <= Iop_Add64 &&
			    arg1A->contents[1] == arg2) {
				/* k + X < X => intmax - k - 1 < x */
				IRExpr *k = arg1A->contents[0];
				IRExprConst *kc = k->tag == Iex_Const ? (IRExprConst *)k : NULL;
				switch (arg1A->op) {
#define mk_size(sz, max)						\
					case Iop_Add ## sz :		\
						if (kc) {		\
							arg1 = IRExpr_Const_U ## sz (max - kc->Ico.content.U ## sz); \
						} else {		\
							arg1 = IRExpr_Associative_V( \
								Iop_Add ## sz, \
								IRExpr_Const_U ## sz (max), \
								quickSimplify( \
									IRExpr_Unop( \
										Iop_Neg ## sz, \
										k), \
									memo), \
								NULL);	\
							arg1 = quickSimplify(arg1, memo); \
						}			\
						break
					mk_size(8, 255);
					mk_size(16, 65535);
					mk_size(32, ~0u);
					mk_size(64, ~0ul);
#undef mk_size
				default:
					abort();
				}
			}
			arg1C = (arg1->tag == Iex_Const) ? (IRExprConst *)arg1 : NULL;
			arg1A = (arg1->tag == Iex_Associative) ? (IRExprAssociative *)arg1 : NULL;

			if (arg1C) {
#define mk_size(sz, max)						\
				if (_ieb->op == Iop_CmpLT ## sz ## U && \
				    arg1C->Ico.content.U ## sz == max) { \
					return IRExpr_Const_U1(false);	\
				}					\
				if (_ieb->op == Iop_CmpLT ## sz ## U && \
				    arg1C->Ico.content.U ## sz  == max - 1) { \
					return quickSimplify(		\
						IRExpr_Binop(		\
							Iop_CmpEQ ## sz, \
							IRExpr_Const_U ## sz(max), \
							arg2),		\
						memo);			\
				}
				mk_size(8, 255);
				mk_size(16, 65535);
				mk_size(32, ~0u);
				mk_size(64, ~0ul);
#undef mk_size
			}
		}

		if (arg1C && arg2C) {
			switch (_ieb->op) {
#define do_type(sz)							\
			case Iop_CmpEQ ## sz:				\
				return IRExpr_Const_U1(arg1C->Ico.content.U ## sz == arg2C->Ico.content.U ## sz); \
			case Iop_CmpLT ## sz ## U:			\
				return IRExpr_Const_U1(arg1C->Ico.content.U ## sz < arg2C->Ico.content.U ## sz)
				do_type(8);
				do_type(16);
				do_type(32);
				do_type(64);
#undef do_type
			case Iop_CmpLT8S:
				return IRExpr_Const_U1((char)arg1C->Ico.content.U8 < (char)arg2C->Ico.content.U8);
			case Iop_CmpLT16S:
				return IRExpr_Const_U1((short)arg1C->Ico.content.U16 < (short)arg2C->Ico.content.U16);
			case Iop_CmpLT32S:
				return IRExpr_Const_U1((int)arg1C->Ico.content.U32 < (int)arg2C->Ico.content.U32);
			case Iop_CmpLT64S:
				return IRExpr_Const_U1((long)arg1C->Ico.content.U64 < (long)arg2C->Ico.content.U64);
			case Iop_CmpLE64U:
				return IRExpr_Const_U1(arg1C->Ico.content.U64 <= arg2C->Ico.content.U64);
			case Iop_Shl64:
				return IRExpr_Const_U64(arg1C->Ico.content.U64 << arg2C->Ico.content.U8);
			case Iop_Shr64:
				return IRExpr_Const_U64(arg1C->Ico.content.U64 >> arg2C->Ico.content.U8);
			case Iop_Sar64:
				return IRExpr_Const_U64((long)arg1C->Ico.content.U64 >> arg2C->Ico.content.U8);
			case Iop_32HLto64:
				return IRExpr_Const_U64(arg1C->Ico.content.U32 | ((unsigned long)arg2C->Ico.content.U32 << 32));
			case Iop_DivModU64to32: {
				unsigned long num = arg1C->Ico.content.U64;
				unsigned long denom = arg2C->Ico.content.U32;
				if (denom == 0) {
					warning("Constant division by zero (%ld/%ld)?\n",
						num, denom);
					break;
				}
				unsigned long div = num / denom;
				unsigned long mod = num % denom;
				return IRExpr_Const_U64((div << 32) | (mod & 0xffffffff));
			}
			case Iop_DivU64: {
				unsigned long num = arg1C->Ico.content.U64;
				unsigned long denom = arg2C->Ico.content.U32;
				if (denom == 0) {
					warning("Constant division by zero (%ld/%ld)?\n",
						num, denom);
					break;
				}
				unsigned long div = num / denom;
				return IRExpr_Const_U64(div);
			}
			case Iop_Mul64:
				return IRExpr_Const_U64(arg1C->Ico.content.U64 * arg2C->Ico.content.U64);
			case Iop_MullS64: {
				__int128_t a = arg1C->Ico.content.U64;
				__int128_t b = arg2C->Ico.content.U64;
				__int128_t res = a * b;
				return IRExpr_Const_U128(res >> 64, res);
			}
			case Iop_MullU64: {
				__uint128_t a = arg1C->Ico.content.U64;
				__uint128_t b = arg2C->Ico.content.U64;
				__uint128_t res = a * b;
				return IRExpr_Const_U128(res >> 64, res);
			}
			case Iop_MullU32: {
				unsigned long a = arg1C->Ico.content.U32;
				unsigned long b = arg2C->Ico.content.U32;
				unsigned long res = a * b;
				return IRExpr_Const_U64(res);
			}
			case Iop_MullS32: {
				long a = arg1C->Ico.content.U32;
				long b = arg2C->Ico.content.U32;
				long res = a * b;
				return IRExpr_Const_U64(res);
			}
			case Iop_64HLto128:
				return IRExpr_Const_U128(arg1C->Ico.content.U64, arg2C->Ico.content.U64);
			case Iop_DivModU128to64: {
				__uint128_t num;
				unsigned long denom = arg2C->Ico.content.U64;
				num = arg1C->Ico.content.U128.hi;
				num <<= 64;
				num |= arg1C->Ico.content.U128.lo;
				if (denom == 0) {
					warning("Constant division by zero (%ld:%ld/%ld)?\n",
						(unsigned long)(num >> 64),
						(unsigned long)num,
						denom);
					break;
				}
				unsigned long div = num / denom;
				unsigned long mod = num % denom;
				return IRExpr_Const_U128(mod, div);
			}
			case Iop_DivModS128to64: {
				__int128_t num;
				unsigned long denom = arg2C->Ico.content.U64;
				num = arg1C->Ico.content.U128.hi;
				num <<= 64;
				num |= arg1C->Ico.content.U128.lo;
				if (denom == 0) {
					warning("Constant division by zero (%ld:%ld/%ld)?\n",
						(unsigned long)(num >> 64),
						(unsigned long)num,
						denom);
					break;
				}
				unsigned long div = num / denom;
				unsigned long mod = num % denom;
				return IRExpr_Const_U128(mod, div);
			}
			case Iop_CmpF64:
			case Iop_Sub64F0x2:
			case Iop_F64toI64: {
				/* It's not worth trying to constant
				 * fold these ones. */
				return a;
			}
			default:
				abort();
			}
		}
		if (arg2C && _ieb->op >= Iop_Shl8 && _ieb->op <= Iop_Shl64) {
			unsigned shift = arg2C->Ico.content.U8;
			/* Replace shift left by constant with an
			 * unsigned multiply.  Be careful not to
			 * overflow the shift types!*/
			switch (_ieb->op) {
			case Iop_Shl64:
				if (shift >= 64) {
					return IRExpr_Const_U64(0);
				} else {
					return IRExpr_Binop(
						Iop_Mul64,
						arg1,
						IRExpr_Const_U64(1ul << shift));
				}
			case Iop_Shl32:
				if (shift >= 32) {
					return IRExpr_Const_U32(0);
				} else {
					return IRExpr_Binop(
						Iop_Mul32,
						arg1,
						IRExpr_Const_U32(1ul << shift));
				}
			case Iop_Shl16:
				if (shift >= 16) {
					return IRExpr_Const_U16(0);
				} else {
					return IRExpr_Binop(
						Iop_Mul16,
						arg1,
						IRExpr_Const_U16(1ul << shift));
				}
			case Iop_Shl8:
				if (shift >= 8) {
					return IRExpr_Const_U8(0);
				} else {
					return IRExpr_Binop(
						Iop_Mul8,
						arg1,
						IRExpr_Const_U8(1ul << shift));
				}
			default:
				abort();
			}
		}

		if (_ieb->op >= Iop_CmpEQ8 &&
		    _ieb->op <= Iop_CmpEQ64 &&
		    arg1C &&
		    arg2A &&
		    arg2A->op >= Iop_Add8 &&
		    arg2A->op <= Iop_Add64 &&
		    arg2A->nr_arguments >= 2 &&
		    arg2A->contents[0]->tag == Iex_Const) {
			IRExprConst *arg2C = (IRExprConst *)arg2A->contents[0];
			IRExprConst *newArg1;
			switch (_ieb->op) {
			case Iop_CmpEQ8:
				newArg1 = IRExpr_Const_U8(arg1C->Ico.content.U8 - arg2C->Ico.content.U8);
				break;
			case Iop_CmpEQ16:
				newArg1 = IRExpr_Const_U16(arg1C->Ico.content.U16 - arg2C->Ico.content.U16);
				break;
			case Iop_CmpEQ32:
				newArg1 = IRExpr_Const_U32(arg1C->Ico.content.U32 - arg2C->Ico.content.U32);
				break;
			case Iop_CmpEQ64:
				newArg1 = IRExpr_Const_U64(arg1C->Ico.content.U64 - arg2C->Ico.content.U64);
				break;
			default:
				abort();
			}
			IRExpr *newArg2;
			if (arg2A->nr_arguments == 2) {
				newArg2 = arg2A->contents[1];
			} else {
				newArg2 = IRExpr_Associative_Copy(arg2A->op, arg2A->nr_arguments - 1, arg2A->contents + 1);
			}
			return IRExpr_Binop(_ieb->op, newArg1, newArg2);
		}
		if (_ieb->op >= Iop_CmpEQ8 &&
		    _ieb->op <= Iop_CmpEQ64 &&
		    arg1 == arg2) {
			return IRExpr_Const_U1(true);
		}
		if (arg1 == arg2 &&
		    ((_ieb->op >= Iop_CmpLT8U && _ieb->op <= Iop_CmpLT64U) ||
		     (_ieb->op >= Iop_CmpLT8S && _ieb->op <= Iop_CmpLT64S))) {
			return IRExpr_Const_U1(false);
		}
		if (arg1 != _ieb->arg1 || arg2 != _ieb->arg2)
			a = IRExprBinop::mk(_ieb->op, arg1, arg2);
		break;
	}
	case Iex_Associative: {
		IRExprAssociative *_iea = (IRExprAssociative *)a;
		int const nr_arguments = _iea->nr_arguments;
		IROp const op = _iea->op;
		unsigned long mask;
		unsigned long acc;
		unsigned long defaultValue;
		int new_nr_args = 0;
		IRExpr *simpleArgs[nr_arguments];
		bool realloc = false;

		assert(nr_arguments != 0);

		switch (op) {
		case Iop_And1:                                 mask = 1;      defaultValue = mask; break;
		case Iop_And8:                                 mask = 0xff;   defaultValue = mask; break;
		case Iop_And16:                                mask = 0xffff; defaultValue = mask; break;
		case Iop_And32:                                mask = ~0u;    defaultValue = mask; break;
		case Iop_And64:                                mask = ~0ul;   defaultValue = mask; break;
		                case Iop_Or1:                  mask = 1;      defaultValue = 0; break;
		case Iop_Xor8:  case Iop_Or8:  case Iop_Add8:  mask = 0xff;   defaultValue = 0; break;
		case Iop_Xor16: case Iop_Or16: case Iop_Add16: mask = 0xffff; defaultValue = 0; break;
		case Iop_Xor32: case Iop_Or32: case Iop_Add32: mask = ~0u;    defaultValue = 0; break;
		case Iop_Xor64: case Iop_Or64: case Iop_Add64: mask = ~0ul;   defaultValue = 0; break;
		case Iop_Mul8:                                 mask = 0xff;   defaultValue = 1; break;
		case Iop_Mul16:                                mask = 0xffff; defaultValue = 1; break;
		case Iop_Mul32:                                mask = ~0u;    defaultValue = 1; break;
		case Iop_Mul64:                                mask = ~0ul;   defaultValue = 1; break;
			break;
		default:
			abort();
		}
		acc = defaultValue;
		for (int i = 0; i < nr_arguments; i++) {
			simpleArgs[i] = quickSimplify(_iea->contents[i], memo);
			if (simpleArgs[i] != _iea->contents[i])
				realloc = true;
			if (op >= Iop_And8 &&
			    op <= Iop_And64 &&
			    simpleArgs[i]->tag == Iex_Unop &&
			    ((IRExprUnop *)simpleArgs[i])->op >= Iop_8Uto16 &&
			    ((IRExprUnop *)simpleArgs[i])->op <= Iop_32Uto64) {
				/* We know that unsigned upcasts never set the high bits */
				switch (((IRExprUnop *)simpleArgs[i])->arg->type()) {
				case Ity_I8:
					acc &= 0xff;
					break;
				case Ity_I16:
					acc &= 0xffff;
					break;
				case Ity_I32:
					acc &= 0xffffffff;
					break;
				default:
					abort();
				}
			}

			if (simpleArgs[i]->tag == Iex_Const) {
				switch (op) {
				case Iop_And1: case Iop_And8: case Iop_And16:
				case Iop_And32: case Iop_And64:
					acc &= ((IRExprConst *)simpleArgs[i])->Ico.content.U64;
					break;
				case Iop_Or1: case Iop_Or8: case Iop_Or16:
				case Iop_Or32: case Iop_Or64:
					acc |= ((IRExprConst *)simpleArgs[i])->Ico.content.U64;
					break;
				case Iop_Xor8: case Iop_Xor16:
				case Iop_Xor32: case Iop_Xor64:
					acc ^= ((IRExprConst *)simpleArgs[i])->Ico.content.U64;
					break;
				case Iop_Add8: case Iop_Add16:
				case Iop_Add32: case Iop_Add64:
					acc += ((IRExprConst *)simpleArgs[i])->Ico.content.U64;
					break;
				case Iop_Mul8: case Iop_Mul16:
				case Iop_Mul32: case Iop_Mul64:
					acc *= ((IRExprConst *)simpleArgs[i])->Ico.content.U64;
					break;
				default:
					abort();
				}
			} else if (simpleArgs[i]->tag == Iex_Associative &&
				   ((IRExprAssociative *)simpleArgs[i])->op == op) {
				realloc = true;
				IRExprAssociative *arg = (IRExprAssociative *)simpleArgs[i];
				for (int j = 0; j < arg->nr_arguments; j++) {
					if (arg->contents[j]->tag == Iex_Const) {
						switch (op) {
						case Iop_And1: case Iop_And8: case Iop_And16:
						case Iop_And32: case Iop_And64:
							acc &= ((IRExprConst *)arg->contents[j])->Ico.content.U64;
							break;
						case Iop_Or1: case Iop_Or8: case Iop_Or16:
						case Iop_Or32: case Iop_Or64:
							acc |= ((IRExprConst *)arg->contents[j])->Ico.content.U64;
							break;
						case Iop_Xor8: case Iop_Xor16:
						case Iop_Xor32: case Iop_Xor64:
							acc ^= ((IRExprConst *)arg->contents[j])->Ico.content.U64;
							break;
						case Iop_Add8: case Iop_Add16:
						case Iop_Add32: case Iop_Add64:
							acc += ((IRExprConst *)arg->contents[j])->Ico.content.U64;
							break;
						case Iop_Mul8: case Iop_Mul16:
						case Iop_Mul32: case Iop_Mul64:
							acc *= ((IRExprConst *)arg->contents[j])->Ico.content.U64;
							break;
						default:
							abort();
						}
					} else {
						new_nr_args++;
					}
				}
			} else {
				new_nr_args++;
			}
		}
		acc &= mask;
		if (op == Iop_And1 && acc == 0)
			return IRExpr_Const_U1(false);
		if (op == Iop_Or1 && acc == 1)
			return IRExpr_Const_U1(true);
		if (acc == 0 &&
		    ((op >= Iop_Mul8 && op <= Iop_Mul64) ||
		     (op >= Iop_And8 && op <= Iop_And64))) {
			switch (op) {
			case Iop_Mul8: case Iop_And8: return IRExpr_Const_U8(0);
			case Iop_Mul16: case Iop_And16: return IRExpr_Const_U16(0);
			case Iop_Mul32: case Iop_And32: return IRExpr_Const_U32(0);
			case Iop_Mul64: case Iop_And64: return IRExpr_Const_U64(0);
			default: abort();
			}
		}

		if (new_nr_args == 0) {
		result_is_zero:
			switch (_iea->type()) {
#define do_ty(n)							\
			case Ity_I ## n :				\
				return IRExpr_Const_U ## n(acc);
				do_ty(1);
				do_ty(8);
				do_ty(16);
				do_ty(32);
				do_ty(64);
#undef do_ty
			default:
				abort();
			}
		}
		if (acc != defaultValue)
			new_nr_args++;
		if (new_nr_args == 1 && !realloc) {
			for (int i = 0; i < nr_arguments; i++)
				if (simpleArgs[i]->tag != Iex_Const)
					return simpleArgs[i];
			abort();
		}
		if (!realloc && new_nr_args == nr_arguments)
			return _iea;
		IRExpr **newArgs = alloc_irexpr_array(new_nr_args);
		int outIdx = 0;
		if (acc != defaultValue) {
			switch (_iea->type()) {
#define do_ty(n)							\
				case Ity_I ## n :			\
					newArgs[0] = IRExpr_Const_U ## n(acc); \
					break;
				do_ty(1);
				do_ty(8);
				do_ty(16);
				do_ty(32);
				do_ty(64);
#undef do_ty
			default:
				abort();
			}
			outIdx++;
		}

		for (int i = 0; i < nr_arguments; i++) {
			if (simpleArgs[i]->tag == Iex_Const) {
				/* Already handled */
			} else if (simpleArgs[i]->tag == Iex_Associative &&
				   ((IRExprAssociative *)simpleArgs[i])->op == op) {
				IRExprAssociative *arg = (IRExprAssociative *)simpleArgs[i];
				for (int j = 0; j < arg->nr_arguments; j++) {
					if (arg->contents[j]->tag == Iex_Const) {
						/* Already handled */
					} else {
						newArgs[outIdx] = arg->contents[j];
						outIdx++;
					}
				}
			} else {
				newArgs[outIdx] = simpleArgs[i];
				outIdx++;
			}
		}
		assert(outIdx == new_nr_args);
		if (op >= Iop_Add8 &&
		    op <= Iop_Add64) {
			/* Find anything which goes x - x and remove it. */
			for (int i = 0; i < outIdx; i++) {
				if (newArgs[i]->tag != Iex_Unop) {
					continue;
				}
				IRExprUnop *ieu = (IRExprUnop *)newArgs[i];
				if (ieu->op < Iop_Neg8 || ieu->op > Iop_Neg64) {
					continue;
				}
				IRExpr *k = ieu->arg;
				for (int j = 0; j < outIdx; j++) {
					if (newArgs[j] == k) {
						assert(j != i);
						/* Need to remove both i and j from the list */
						if (i < j) {
							memmove(newArgs + i,
								newArgs + i + 1,
								sizeof(IRExpr *) * (j - i) - 1);
							memmove(newArgs + j - 1,
								newArgs + j + 1,
								sizeof(IRExpr *) * (outIdx - j - 1));
						} else {
							memmove(newArgs + j,
								newArgs + j + 1,
								sizeof(IRExpr *) * (i - j) - 1);
							memmove(newArgs + i - 1,
								newArgs + i + 1,
								sizeof(IRExpr *) * (outIdx - i - 1));
							i--;
						}
						outIdx -= 2;
						break;
					}
				}
			}
		}

		if (outIdx == 0) {
			goto result_is_zero;
		}
		/* k | (k2 & x) -> k | ((k2 & ~k) & x) */
		if (outIdx > 1 &&
		    op >= Iop_Or8 && op <= Iop_Or16 && outIdx > 1 &&
		    newArgs[0]->tag == Iex_Const &&
		    newArgs[1]->tag == Iex_Associative &&
		    ((IRExprAssociative *)newArgs[1])->op >= Iop_And8 &&
		    ((IRExprAssociative *)newArgs[1])->op <= Iop_And64 &&
		    ((IRExprAssociative *)newArgs[1])->contents[0]->tag == Iex_Const) {
			IRExprConst *k = (IRExprConst *)newArgs[0];
			IRExprAssociative *kOwner = (IRExprAssociative *)newArgs[1];
			IRExprConst *k2 = (IRExprConst *)kOwner->contents[0];
			IRExpr *newC;
			switch (op) {
#define do_size(sz)							\
				case Iop_Or ## sz:			\
					if ( (k2->Ico.content.U ## sz & ~k->Ico.content.U ## sz) == k2->Ico.content.U ## sz) { \
						newC = k2;		\
					} else {			\
						newC = IRExpr_Const_U8(k2->Ico.content.U ## sz & ~k->Ico.content.U ## sz); \
					}				\
					break
				do_size(8);
				do_size(16);
				do_size(32);
				do_size(64);
#undef do_size
			default:
				abort();
			}
			if (newC != k2) {
				IRExpr *cc[kOwner->nr_arguments];
				memcpy(cc, kOwner->contents, sizeof(IRExpr *) * kOwner->nr_arguments);
				cc[0] = newC;
				newArgs[1] = quickSimplify(IRExpr_Associative_Copy(kOwner->op, kOwner->nr_arguments, cc),
							   memo);
			}
		}
		if (outIdx == 1) {
			a = newArgs[0];
		} else {
			a = IRExpr_Associative_Claim(op, outIdx, newArgs);
		}
		break;
	}
	case Iex_Mux0X: {
		IRExprMux0X *m = (IRExprMux0X *)a;
		auto cond = quickSimplify(m->cond, memo);
		auto expr0 = quickSimplify(m->expr0, memo);
		auto exprX = quickSimplify(m->exprX, memo);
		if (cond != m->cond || expr0 != m->expr0 ||
		    exprX != m->exprX)
			a = IRExprMux0X::mk(cond, expr0, exprX);
		break;
	}
	case Iex_Load: {
		IRExprLoad *l = (IRExprLoad *)a;
		auto addr = quickSimplify(l->addr, memo);
		if (addr != l->addr)
			a = IRExprLoad::mk(l->ty, addr);
		break;
	}
	case Iex_Get:
	case Iex_GetI:
	case Iex_Const:
	case Iex_HappensBefore:
	case Iex_FreeVariable:
	case Iex_EntryPoint:
	case Iex_ControlFlow:
		break;
	case Iex_Qop: {
		IRExprQop *q = (IRExprQop *)a;
		auto a1 = quickSimplify(q->arg1, memo);
		auto a2 = quickSimplify(q->arg2, memo);
		auto a3 = quickSimplify(q->arg3, memo);
		auto a4 = quickSimplify(q->arg4, memo);
		if (a1 != q->arg1 || a2 != q->arg2 || a3 != q->arg3 || a4 != q->arg4)
			a = IRExprQop::mk(q->op, a1, a2, a3, a4);
		break;
	}
	case Iex_Triop: {
		IRExprTriop *q = (IRExprTriop *)a;
		auto a1 = quickSimplify(q->arg1, memo);
		auto a2 = quickSimplify(q->arg2, memo);
		auto a3 = quickSimplify(q->arg3, memo);
		if (a1 != q->arg1 || a2 != q->arg2 || a3 != q->arg3)
			a = IRExprTriop::mk(q->op, a1, a2, a3);
		break;
	}
	case Iex_CCall: {
		auto c = (IRExprCCall *)a;
		int nr_args;
		for (nr_args = 0; c->args[nr_args]; nr_args++)
			;
		IRExpr *newArgs[nr_args + 1];
		newArgs[nr_args] = NULL;
		bool realloc = false;
		for (int i = 0; i < nr_args; i++) {
			newArgs[i] = quickSimplify(c->args[i], memo);
			if (newArgs[i] != c->args[i])
				realloc = true;
		}
		if (nr_args == 5 &&
		    newArgs[0]->tag == Iex_Const &&
		    newArgs[1]->tag == Iex_Const &&
		    !strcmp(c->cee->name, "amd64g_calculate_condition")) {
			auto r = optimise_condition_calculation(
				newArgs[0],
				newArgs[1],
				newArgs[2],
				newArgs[3]);
			if (r) {
				return _quickSimplify(r, memo);
			}
		}
		if (realloc) {
			IRExpr **n = alloc_irexpr_array(nr_args+1);
			memcpy(n, newArgs, (nr_args+1) * sizeof(IRExpr *));
			a = IRExpr_CCall(c->cee, c->retty, n);
		}
		break;
	}
	}
	return a;
}

IRExpr *
quickSimplify(IRExpr *a, std::map<IRExpr *, IRExpr *> &memo)
{
	auto it_did_insert = memo.insert(std::pair<IRExpr *, IRExpr *>(a, (IRExpr *)0xf001));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = _quickSimplify(a, memo);
	return it->second;
}

bbdd *
bbdd::_var(scope *scope, IRExpr *a, std::map<IRExpr *, bbdd *> &memo)
{
	if (TIMEOUT)
		return scope->cnst(true);
	auto it_did_insert = memo.insert(std::pair<IRExpr *, bbdd *>(a, (bbdd *)0xf00));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;
	if (a->tag == Iex_Mux0X) {
		it->second = ifelse(
			scope,
			_var(scope, ((IRExprMux0X *)a)->cond, memo),
			_var(scope, ((IRExprMux0X *)a)->exprX, memo),
			_var(scope, ((IRExprMux0X *)a)->expr0, memo));
	} else {
		it->second = scope->node(
			a,
			scope->ordering->rankVariable(a),
			scope->cnst(true),
			scope->cnst(false));
	}
	return it->second;
}
bbdd *
bbdd::var(scope *scope, IRExpr *a)
{
	std::map<IRExpr *, IRExpr *> qsMemo;
	std::map<IRExpr *, IRExpr *> muxMemo;
	std::map<IRExpr *, bbdd *> vMemo;
	return _var(
		scope,
		quickSimplify(
			muxify(
				quickSimplify(a, qsMemo),
				muxMemo),
			qsMemo),
		vMemo);
}

class binary_zip_internal {
public:
	bool isAnd;
	bbdd *first;
	bbdd *second;
	void move(binary_zip_internal &o) const {
		o = *this;
	}
	const bdd_rank &bestCond(IRExpr **cond) const {
		assert(!(first->isLeaf() && second->isLeaf()));
		if (first->isLeaf()) {
			*cond = second->internal().condition;
			return second->internal().rank;
		} else if (second->isLeaf()) {
			*cond = first->internal().condition;
			return first->internal().rank;
		} else if (first->internal().rank < second->internal().rank) {
			*cond = first->internal().condition;
			return first->internal().rank;
		} else {
			*cond = second->internal().condition;
			return second->internal().rank;
		}
	}
	binary_zip_internal trueSucc(const bdd_rank &cond) const {
		return binary_zip_internal(
			isAnd,
			first->trueBranch(cond),
			second->trueBranch(cond));
	}
	binary_zip_internal falseSucc(const bdd_rank &cond) const {
		return binary_zip_internal(
			isAnd,
			first->falseBranch(cond),
			second->falseBranch(cond));
	}
	binary_zip_internal(bool _isAnd, bbdd *_first, bbdd *_second)
		: isAnd(_isAnd), first(_first), second(_second)
	{}
	bool isLeaf() const {
		if (first == second)
			return true;
		return first->isLeaf() || second->isLeaf();
	}
	bbdd *leafzip() const {
		assert(isLeaf());
		if (first == second)
			return first;
		if (first->isLeaf()) {
			if (first->leaf()) {
				if (isAnd)
					return second;
				else
					return first;
			} else {
				if (isAnd)
					return first;
				else
					return second;
			}
		} else if (second->isLeaf()) {
			if (second->leaf()) {
				if (isAnd)
					return first;
				else
					return second;
			} else {
				if (isAnd)
					return second;
				else
					return first;
			}
		} else {
			abort();
		}

	}
	static bbdd *fixup(bbdd *what) {
		return what;
	}
	static bool badPtr(bbdd *) {
		return false;
	}
	bool operator<(const binary_zip_internal &o) const {
		if (first < o.first)
			return true;
		if (first > o.first)
			return false;
		return second < o.second;
	}
};
bbdd *
bbdd::And(scope *scope, bbdd *a, bbdd *b)
{
	if (!TIMEOUT) {
		binary_zip_internal f(true, a, b);
		auto r = zip(scope, f);
		if (!TIMEOUT) {
			return r;
		}
	}
	return scope->cnst(true);
}
bbdd *
bbdd::Or(scope *scope, bbdd *a, bbdd *b)
{
	if (!TIMEOUT) {
		binary_zip_internal f(false, a, b);
		auto r = zip(scope, f);
		if (!TIMEOUT) {
			return r;
		}
	}
	return scope->cnst(false);
}

bbdd *
bbdd::invert(scope *scope, bbdd *a, std::map<bbdd *, bbdd *> &memo)
{
	if (TIMEOUT)
		return a;
	if (a->isLeaf())
		return scope->cnst(!a->leaf());

	auto it_did_insert = memo.insert(std::pair<bbdd *, bbdd *>(a, (bbdd *)0xf00));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;
	bbdd *t = bbdd::invert(scope, a->internal().trueBranch, memo);
	bbdd *f = bbdd::invert(scope, a->internal().falseBranch, memo);
	it->second = scope->node(a->internal().condition, a->internal().rank, t, f);
	return it->second;
}

bdd_rank
bdd_ordering::rankVariable(const IRExpr *a)
{
	bdd_rank::clsT cls;
	if (a->tag == Iex_EntryPoint || a->tag == Iex_ControlFlow) {
		cls.tag = bdd_rank::clsT::cls_entry;
	} else if (a->tag == Iex_HappensBefore) {
		cls.tag = bdd_rank::clsT::cls_hb;
		cls.hb1 = -((IRExprHappensBefore *)a)->before.id;
		cls.hb2 = ((IRExprHappensBefore *)a)->after.id;
	} else {
		cls.tag = bdd_rank::clsT::cls_norm;
	}
	long &rankNr(nextRanking[cls]);
	bdd_rank rank;
	rank.cls = cls;
	rank.val = rankNr;
	auto it_did_insert = variableRankings.insert(std::pair<const IRExpr *, bdd_rank>(a, rank));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		rankNr--;
	}
	return it->second;
}

void
bdd_ordering::runGc(HeapVisitor &hv)
{
	std::map<const IRExpr *, bdd_rank> newRankings;
	for (auto it = variableRankings.begin();
	     it != variableRankings.end();
	     it++) {
		const IRExpr *a = hv.visited(it->first);
		if (a)
			newRankings[a] = it->second;
	}
	variableRankings = newRankings;
}

void
bdd_rank::prettyPrint(FILE *f) const
{
	switch (cls.tag) {
	case clsT::cls_entry:
		fprintf(f, "e%ld", val);
		return;
	case clsT::cls_hb:
		fprintf(f, "hb%d:%d:%ld",
			cls.hb1, cls.hb2,
			val);
		return;
	case clsT::cls_norm:
		fprintf(f, "r%ld", val);
		return;
	}
	abort();
}

bool
bdd_rank::parse(const char *buf, const char **end)
{
	if (parseThisChar('e', buf, &buf) &&
	    parseDecimalLong(&val, buf, end)) {
		cls.tag = clsT::cls_entry;
		return true;
	} else if (parseThisString("hb", buf, &buf) &&
		   parseDecimalInt(&cls.hb1, buf, &buf) &&
		   parseThisChar(':', buf, &buf) &&
		   parseDecimalInt(&cls.hb2, buf, &buf) &&
		   parseThisChar(':', buf, &buf) &&
		   parseDecimalLong(&val, buf, end)) {
		cls.tag = clsT::cls_hb;
		return true;
	} else if (parseThisChar('r', buf, &buf) &&
		   parseDecimalLong(&val, buf, end)) {
		cls.tag = clsT::cls_norm;
		return true;
	} else {
		return false;
	}
}

void
bdd_ordering::prettyPrint(FILE *f, const std::set<bdd_rank> *neededRanks) const
{
	std::set<bdd_rank> printed;
	fprintf(f, "Variable rankings:\n");
	for (auto it = variableRankings.begin();
	     it != variableRankings.end();
	     it++) {
		if ((neededRanks && !neededRanks->count(it->second)) ||
		    !printed.insert(it->second).second)
			continue;
		fprintf(f, "\t");
		ppIRExpr(it->first, f);
		fprintf(f, "\t -> \t");
		it->second.prettyPrint(f);
		fprintf(f, "\n");
	}
}

bool
bdd_ordering::parse(const char *buf, const char **end)
{
	if (!parseThisString("Variable rankings:\n", buf, &buf))
		return false;
	variableRankings.clear();
	while (1) {
		IRExpr *key;
		bdd_rank rank;
		if (!parseIRExpr(&key, buf, &buf) ||
		    !parseThisString("\t->\t", buf, &buf) ||
		    !rank.parse(buf, &buf) ||
		    !parseThisChar('\n', buf, &buf))
			break;
		variableRankings[key] = rank;
		if (nextRanking[rank.cls] >= rank.val) {
			nextRanking[rank.cls] = rank.val - 1;
		}
	}
	*end = buf;
	return true;
}

void
exprbdd::sanity_check(bdd_ordering *ordering) const
{
	std::set<const IRExpr *> terminals;
	std::set<const exprbdd *> visited;
	std::vector<const exprbdd *> q;
	q.push_back(this);
	IRType ty = Ity_INVALID;
	while (!q.empty()) {
		const exprbdd *e = q.back();
		q.pop_back();
		if (!visited.insert(e).second)
			continue;
		if (e->isLeaf()) {
			assert(e->leaf()->tag != Iex_Mux0X);
			if (ty == Ity_INVALID)
				ty = e->leaf()->type();
			else
				assert(ty == e->leaf()->type());
			assert(ty != Ity_I1 || e->leaf()->tag == Iex_Const);
		} else {
			assert(e->internal().condition->tag != Iex_Mux0X);
			q.push_back(e->internal().trueBranch);
			q.push_back(e->internal().falseBranch);
		}
	}
	parentT::sanity_check(ordering);
}

exprbdd *
exprbdd::_var(exprbdd::scope *scope, bbdd::scope *bscope, IRExpr *what, std::map<IRExpr *, exprbdd *> &memo)
{
	if (TIMEOUT)
		return NULL;

	auto it_did_insert = memo.insert(std::pair<IRExpr *, exprbdd *>(what, (exprbdd *)0xf001));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;

	if (what->tag == Iex_Mux0X)
		it->second = ifelse(
			scope,
			bbdd::var(bscope, ((IRExprMux0X *)what)->cond),
			_var(scope, bscope, ((IRExprMux0X *)what)->exprX, memo),
			_var(scope, bscope, ((IRExprMux0X *)what)->expr0, memo));
	else if (what->type() == Ity_I1)
		it->second = ifelse(
			scope,
			bbdd::var(bscope, what),
			scope->cnst(IRExpr_Const_U1(true)),
			scope->cnst(IRExpr_Const_U1(false)));
	else
		it->second = scope->cnst(what);
	return it->second;
}

exprbdd *
exprbdd::var(exprbdd::scope *scope, bbdd::scope *bscope, IRExpr *what)
{
	std::map<IRExpr *, IRExpr *> qsMemo;
	std::map<IRExpr *, IRExpr *> muxMemo;
	std::map<IRExpr *, exprbdd *> vMemo;
	return _var(scope, bscope, quickSimplify(muxify(quickSimplify(what, qsMemo), muxMemo), qsMemo), vMemo);
}

IRExpr *
exprbdd::to_irexpr(exprbdd *what, std::map<exprbdd *, IRExpr *> &memo)
{
	if (what->isLeaf())
		return what->leaf();
	auto it_did_insert = memo.insert(std::pair<exprbdd *, IRExpr *>(what, (IRExpr *)0xf001));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = IRExpr_Mux0X(
			what->internal().condition,
			to_irexpr(what->internal().falseBranch, memo),
			to_irexpr(what->internal().trueBranch, memo));
	return it->second;
}

IRExpr *
exprbdd::to_irexpr(exprbdd *what)
{
	if (!what)
		return NULL;
	std::map<exprbdd *, IRExpr *> memo;
	stackedCdf::startBDD();
	auto res = to_irexpr(what, memo);
	stackedCdf::stopBDD();
	return res;
}

exprbdd *
exprbdd::parseLeaf(scope *scope, const char *str, const char **suffix)
{
	IRExpr *a;
	if (parseThisChar('<', str, &str) &&
	    parseIRExpr(&a, str, &str) &&
	    parseThisChar('>', str, suffix))
		return scope->cnst(a);
	else
		return NULL;
}

exprbdd *
exprbdd_scope::cnst(IRExpr *what)
{
	auto it_did_insert = leaves.insert(std::pair<IRExpr *, exprbdd *>(what, (exprbdd *)0xf001));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		it->second = new exprbdd(what);
		nr_ever++;
	}
	return it->second;
}

void
exprbdd_scope::runGc(HeapVisitor &hv)
{
	std::map<IRExpr *, exprbdd *> newLeaves;
	for (auto it = leaves.begin(); it != leaves.end(); it++) {
		IRExpr *k = it->first;
		k = hv.visited(k);
		if (!k)
			continue;
		exprbdd *old = it->second;
		exprbdd *nw = hv.visited(old);
		if (nw) {
			newLeaves[k] = nw;
			assert(nw->type() == k->type());
		}
	}
	leaves = newLeaves;
	bdd_scope<exprbdd>::runGc(hv);
}

class unop_zipper {
	IROp op;
	exprbdd *what;
public:
	unop_zipper(IROp _op, exprbdd *_what)
		: op(_op), what(_what)
	{}
	bool isLeaf() const { return what->isLeaf(); }
	exprbdd *leaf(exprbdd::scope *scope,
		      bbdd::scope *bscope) const {
		return exprbdd::var(
			scope,
			bscope,
			IRExpr_Unop(op, what->leaf()));
	}
	IRExpr *condition() const {
		return what->internal().condition;
	}
	const bdd_rank &rank() const {
		return what->internal().rank;
	}
	unop_zipper trueBranch() const {
		return unop_zipper(op, what->internal().trueBranch);
	}
	unop_zipper falseBranch() const {
		return unop_zipper(op, what->internal().falseBranch);
	}
	bool operator<(const unop_zipper &o) const {
		if (what < o.what)
			return true;
		if (what > o.what)
			return false;
		return op < o.op;
	}
};
exprbdd *
exprbdd::unop(scope *scope, bbdd::scope *bscope, IROp op, exprbdd *what)
{
	if (!TIMEOUT) {
		auto r = exprbdd::restructure_zip(scope, bscope, unop_zipper(op, what));
		if (!TIMEOUT) {
			return r;
		}
	}
	return what;
}

class binop_zip {
	IROp op;
	exprbdd *a;
	exprbdd *b;
public:
	binop_zip(IROp _op, exprbdd *_a, exprbdd *_b)
		: op(_op), a(_a), b(_b)
	{}
	bool isLeaf() const {
		return a->isLeaf() && b->isLeaf();
	}
	exprbdd *leaf(exprbdd::scope *scope, bbdd::scope *bscope) const {
		return exprbdd::var(scope, bscope, IRExpr_Binop(op, a->leaf(), b->leaf()));
	}
	IRExpr *condition() const {
		if (a->isLeaf()) {
			assert(!b->isLeaf());
			return b->internal().condition;
		} else if (b->isLeaf()) {
			return a->internal().condition;
		} else if (a->internal().rank <= b->internal().rank) {
			return a->internal().condition;
		} else {
			return b->internal().condition;
		}
	}
	const bdd_rank &rank() const {
		if (a->isLeaf()) {
			assert(!b->isLeaf());
			return b->internal().rank;
		} else if (b->isLeaf()) {
			return a->internal().rank;
		} else if (a->internal().rank <= b->internal().rank) {
			return a->internal().rank;
		} else {
			return b->internal().rank;
		}
	}
	binop_zip trueBranch() const {
		if (a->isLeaf()) {
			assert(!b->isLeaf());
			return binop_zip(op, a, b->internal().trueBranch);
		} else if (b->isLeaf()) {
			return binop_zip(op, a->internal().trueBranch, b);
		} else if (a->internal().rank < b->internal().rank) {
			return binop_zip(op, a->internal().trueBranch, b);
		} else if (a->internal().rank == b->internal().rank) {
			return binop_zip(op, a->internal().trueBranch, b->internal().trueBranch);
		} else {
			return binop_zip(op, a, b->internal().trueBranch);
		}
	}
	binop_zip falseBranch() const {
		if (a->isLeaf()) {
			assert(!b->isLeaf());
			return binop_zip(op, a, b->internal().falseBranch);
		} else if (b->isLeaf()) {
			return binop_zip(op, a->internal().falseBranch, b);
		} else if (a->internal().rank < b->internal().rank) {
			return binop_zip(op, a->internal().falseBranch, b);
		} else if (a->internal().rank == b->internal().rank) {
			return binop_zip(op, a->internal().falseBranch, b->internal().falseBranch);
		} else {
			return binop_zip(op, a, b->internal().falseBranch);
		}
	}
	bool operator<(const binop_zip &o) const {
		if (a < o.a)
			return true;
		if (a > o.a)
			return false;
		if (b < o.b)
			return true;
		if (b > o.b)
			return false;
		return op < o.op;
	}
};
exprbdd *
exprbdd::binop(scope *scope, bbdd::scope *bscope, IROp op, exprbdd *a, exprbdd *b)
{
	return restructure_zip(scope, bscope, binop_zip(op, a, b));
}

class load_zipper {
	IRType ty;
	exprbdd *what;
public:
	load_zipper(IRType _ty, exprbdd *_what)
		: ty(_ty), what(_what)
	{}
	bool isLeaf() const { return what->isLeaf(); }
	exprbdd *leaf(exprbdd::scope *scope,
		      bbdd::scope *bscope) const {
		return exprbdd::var(
			scope,
			bscope,
			IRExpr_Load(ty, what->leaf()));
	}
	IRExpr *condition() const {
		return what->internal().condition;
	}
	const bdd_rank &rank() const {
		return what->internal().rank;
	}
	load_zipper trueBranch() const {
		return load_zipper(ty, what->internal().trueBranch);
	}
	load_zipper falseBranch() const {
		return load_zipper(ty, what->internal().falseBranch);
	}
	bool operator<(const load_zipper &o) const {
		if (what < o.what)
			return true;
		if (what > o.what)
			return false;
		return ty < o.ty;
	}
};
exprbdd *
exprbdd::load(scope *scope, bbdd::scope *bscope, IRType ty, exprbdd *what)
{
	return restructure_zip(scope, bscope, load_zipper(ty, what));
}

exprbdd *
exprbdd::coerceTypes(scope *scope, bbdd::scope *bscope, IRType to, exprbdd *what)
{
	return unop(scope, bscope, coerceTypesOp(what->type(), to), what);
}

bbdd *
exprbdd::to_bbdd(bbdd::scope *scope, exprbdd *expr, std::map<exprbdd *, bbdd *> &memo)
{
	auto it_did_insert = memo.insert(std::pair<exprbdd *, bbdd *>(expr, (bbdd *)0xf001));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (expr->isLeaf()) {
			IRExpr *l = expr->leaf();
			if (l->tag == Iex_Const) {
				it->second = scope->cnst( ((IRExprConst *)l)->Ico.content.U1);
			} else {
				it->second =
					scope->node(
						l,
						scope->ordering->rankVariable(l),
						scope->cnst(true),
						scope->cnst(false));
			}
		} else {
			it->second = scope->node(
				expr->internal().condition,
				expr->internal().rank,
				to_bbdd(scope, expr->internal().trueBranch, memo),
				to_bbdd(scope, expr->internal().falseBranch, memo));
		}
	}
	return it->second;				
}

bbdd *
exprbdd::to_bbdd(bbdd::scope *scope, exprbdd *expr)
{
	if (TIMEOUT) {
		return scope->cnst(true);
	}
	assert(expr->type() == Ity_I1);
	std::map<exprbdd *, bbdd *> memo;
	stackedCdf::startBDD();
	auto res = to_bbdd(scope, expr, memo);
	stackedCdf::stopBDD();
	return res;
}

class ignore_unreached_internal {
	smrbdd *what;
public:
	ignore_unreached_internal(smrbdd *_what)
		: what(_what)
	{}
	void move(ignore_unreached_internal &o) const {
		o = *this;
	}
	const bdd_rank &bestCond(IRExpr **cond) const {
		assert(!what->isLeaf());
		*cond = what->internal().condition;
		return what->internal().rank;
	}
	ignore_unreached_internal trueSucc(const bdd_rank &) const {
		assert(!what->isLeaf());
		return ignore_unreached_internal(what->internal().trueBranch);
	}
	ignore_unreached_internal falseSucc(const bdd_rank &) const {
		assert(!what->isLeaf());
		return ignore_unreached_internal(what->internal().falseBranch);
	}
	bool isLeaf() const {
		return what->isLeaf();
	}
	smrbdd *leafzip() const {
		assert(what->isLeaf());
		if (what->leaf() == smr_unreached) {
			return NULL;
		} else {
			return what;
		}
	}
	static smrbdd *fixup(smrbdd *what) {
		if (what->isLeaf()) {
			return what;
		}
		if (!what->internal().trueBranch) {
			return what->internal().falseBranch;
		}
		if (!what->internal().falseBranch) {
			return what->internal().trueBranch;
		}
		return what;
	}
	static bool badPtr(smrbdd *what) {
		return what == NULL;
	}
	bool operator<(const ignore_unreached_internal &o) const {
		return what < o.what;
	}
};

smrbdd *
smrbdd::ignore_unreached(scope *scp, smrbdd *what)
{
	ignore_unreached_internal f(what);
	return zip(scp, f);
}

template void _bdd<bool, bbdd>::prettyPrint(FILE *);
template bbdd *_bdd<bool, bbdd>::assume(const_bdd_scope<bbdd> *, bbdd *, bbdd*);
template IRExpr *const_bdd<bool, bbdd>::to_irexpr<bbdd::mkConst>(bbdd *);
template bbdd *_bdd<bool, bbdd>::ifelse(const_bdd_scope<bbdd> *, bbdd *, bbdd *, bbdd *);
template void const_bdd_scope<bbdd>::runGc(HeapVisitor &hv);

template void _bdd<int, intbdd>::prettyPrint(FILE *);
template bool _bdd<bool, bbdd>::_parse<const_bdd_scope<bbdd>, bbdd::parseBool>(const_bdd_scope<bbdd>*, bbdd **, const char *, const char **);
template intbdd *_bdd<int, intbdd>::assume(const_bdd_scope<intbdd> *, intbdd *, bbdd*);
template intbdd *_bdd<int, intbdd>::from_enabling(const_bdd_scope<intbdd> *, const enablingTableT &, intbdd *);

template void _bdd<StateMachineRes, smrbdd>::prettyPrint(FILE *);
template bool _bdd<StateMachineRes, smrbdd>::_parse<const_bdd_scope<smrbdd>, smrbdd::parseLeaf>(const_bdd_scope<smrbdd>*, smrbdd **, const char *, const char **);
template smrbdd *_bdd<StateMachineRes, smrbdd>::assume(const_bdd_scope<smrbdd> *, smrbdd *, bbdd*);
template smrbdd *_bdd<StateMachineRes, smrbdd>::ifelse(const_bdd_scope<smrbdd> *, bbdd *, smrbdd *, smrbdd *);
template std::map<StateMachineRes, bbdd *> _bdd<StateMachineRes, smrbdd>::to_selectors(const_bdd_scope<bbdd> *, smrbdd *);
template smrbdd *_bdd<StateMachineRes, smrbdd>::from_enabling(const_bdd_scope<smrbdd> *, const enablingTableT &, smrbdd *);
template smrbdd *const_bdd<StateMachineRes, smrbdd>::replaceTerminal(const_bdd_scope<smrbdd> *, StateMachineRes, StateMachineRes, smrbdd *);
template void const_bdd_scope<smrbdd>::runGc(HeapVisitor &hv);

template void _bdd<IRExpr *, exprbdd>::prettyPrint(FILE *);
template bool _bdd<IRExpr *, exprbdd>::_parse<exprbdd_scope, exprbdd::parseLeaf>(exprbdd_scope *, exprbdd **, const char *, const char **);
template exprbdd *_bdd<IRExpr *, exprbdd>::assume(exprbdd_scope *, exprbdd *, bbdd*);
template std::map<IRExpr *, bbdd *> _bdd<IRExpr *, exprbdd>::to_selectors(const_bdd_scope<bbdd> *, exprbdd *);
template exprbdd *_bdd<IRExpr *, exprbdd>::from_enabling(exprbdd_scope *, const enablingTableT &, exprbdd *);

template void _bdd<IRExpr *, exprbdd>::dotPrint(FILE *f) const;
template void _bdd<bool, bbdd>::dotPrint(FILE *f) const;
template void _bdd<StateMachineRes, smrbdd>::dotPrint(FILE *f) const;
