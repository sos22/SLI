#include "sli.h"
#include "bdd.hpp"
#include "simplify_irexpr.hpp"

#include "bdd_tmpl.cpp"

/* Convert @what so that it uses muxes wherever possible (i.e. no
   And1, Or1, or Not1 operators) and so that all muxes are at top
   level. */
static IRExpr *
muxify(IRExpr *what)
{
	switch (what->tag) {
	case Iex_Get:
		return what;
	case Iex_GetI:
		abort();
	case Iex_Qop: {
		IRExprQop *w = (IRExprQop *)what;
		IRExpr *a = muxify(w->arg1);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Qop(
					       w->op,
					       ((IRExprMux0X *)a)->expr0,
					       w->arg2,
					       w->arg3,
					       w->arg4)),
				muxify(IRExpr_Qop(
					       w->op,
					       ((IRExprMux0X *)a)->exprX,
					       w->arg2,
					       w->arg3,
					       w->arg4)));
		IRExpr *b = muxify(w->arg2);
		if (b->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)b)->cond,
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->expr0,
					       w->arg3,
					       w->arg4)),
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->exprX,
					       w->arg3,
					       w->arg4)));
		IRExpr *c = muxify(w->arg3);
		if (c->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)c)->cond,
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       b,
					       ((IRExprMux0X *)c)->expr0,
					       w->arg4)),
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       b,
					       ((IRExprMux0X *)c)->exprX,
					       w->arg4)));
		IRExpr *d = muxify(w->arg4);
		if (d->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)c)->cond,
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       b,
					       c,
					       ((IRExprMux0X *)d)->expr0)),
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       b,
					       c,
					       ((IRExprMux0X *)d)->exprX)));
		assert(a == w->arg1 && b == w->arg2 && c == w->arg3 && d == w->arg4);
		return what;
	}
	case Iex_Triop: {
		IRExprTriop *w = (IRExprTriop *)what;
		IRExpr *a = muxify(w->arg1);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Triop(
					       w->op,
					       ((IRExprMux0X *)a)->expr0,
					       w->arg2,
					       w->arg3)),
				muxify(IRExpr_Triop(
					       w->op,
					       ((IRExprMux0X *)a)->exprX,
					       w->arg2,
					       w->arg3)));
		IRExpr *b = muxify(w->arg2);
		if (b->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)b)->cond,
				muxify(IRExpr_Triop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->expr0,
					       w->arg3)),
				muxify(IRExpr_Triop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->exprX,
					       w->arg3)));
		IRExpr *c = muxify(w->arg3);
		if (c->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)c)->cond,
				muxify(IRExpr_Triop(
					       w->op,
					       a,
					       b,
					       ((IRExprMux0X *)c)->expr0)),
				muxify(IRExpr_Triop(
					       w->op,
					       a,
					       b,
					       ((IRExprMux0X *)c)->exprX)));
		if (a == w->arg1 && b == w->arg2 && c == w->arg3)
			return what;
		else
			return IRExpr_Triop(w->op, a, b, c);
	}
	case Iex_Binop: {
		IRExprBinop *w = (IRExprBinop *)what;
		IRExpr *a = muxify(w->arg1);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Binop(
					       w->op,
					       ((IRExprMux0X *)a)->expr0,
					       w->arg2)),
				muxify(IRExpr_Binop(
					       w->op,
					       ((IRExprMux0X *)a)->exprX,
					       w->arg2)));
		IRExpr *b = muxify(w->arg2);
		if (b->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)b)->cond,
				muxify(IRExpr_Binop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->expr0)),
				muxify(IRExpr_Binop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->exprX)));
		assert(a == w->arg1 && b == w->arg2);
		return what;
	}
	case Iex_Unop: {
		IRExprUnop *w = (IRExprUnop *)what;
		IRExpr *a = muxify(w->arg);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Unop(
					       w->op,
					       ((IRExprMux0X *)a)->expr0)),
				muxify(IRExpr_Unop(
					       w->op,
					       ((IRExprMux0X *)a)->exprX)));
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
		IRExpr *cond = muxify(m->cond);
		IRExpr *expr0 = muxify(m->expr0);
		IRExpr *exprX = muxify(m->exprX);
		if (cond == m->cond && expr0 == m->expr0 && exprX == m->exprX)
			return what;
		else
			return IRExpr_Mux0X(cond, expr0, exprX);
	}
	case Iex_CCall: {
		IRExprCCall *cee = (IRExprCCall *)what;
		IRExpr *a;
		int i;
		for (i = 0; cee->args[i]; i++) {
			a = muxify(cee->args[i]);
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
				IRExpr_CCall(cee->cee, cee->retty, newArgsX)));
	}
	case Iex_Associative: {
		IRExprAssociative *iea = (IRExprAssociative *)what;
		if (iea->op == Iop_And1) {
			IRExpr *acc = IRExpr_Const_U1(true);
			IRExpr *fls = IRExpr_Const_U1(false);
			for (int i = 0; i < iea->nr_arguments; i++)
				acc = IRExpr_Mux0X(
					muxify(iea->contents[i]),
					fls,
					acc);
			return acc;
		} else if (iea->op == Iop_Or1) {
			IRExpr *acc = IRExpr_Const_U1(false);
			IRExpr *tru = IRExpr_Const_U1(true);
			for (int i = 0; i < iea->nr_arguments; i++)
				acc = IRExpr_Mux0X(
					muxify(iea->contents[i]),
					acc,
					tru);
			return acc;
		}

		assert(iea->nr_arguments > 0);
		IRExpr *a = (IRExpr *)0xdead;
		int i;
		for (i = 0; i < iea->nr_arguments; i++) {
			a = muxify(iea->contents[i]);
			if (a->tag == Iex_Mux0X)
				break;
			assert(a == iea->contents[i]);
		}
		if (i == iea->nr_arguments)
			return what;
		IRExpr **newArgs0 = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, iea->nr_arguments);
		memcpy(newArgs0, iea->contents, sizeof(iea->contents[0]) * iea->nr_arguments);
		newArgs0[i] = ((IRExprMux0X *)a)->expr0;
		IRExpr **newArgsX = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, iea->nr_arguments);
		memcpy(newArgsX, iea->contents, sizeof(iea->contents[0]) * iea->nr_arguments);
		newArgsX[i] = ((IRExprMux0X *)a)->exprX;
		IRExprAssociative *exp0 = new IRExprAssociative();
		exp0->op = iea->op;
		exp0->nr_arguments = iea->nr_arguments;
		exp0->nr_arguments_allocated = iea->nr_arguments;
		exp0->contents = newArgs0;
		IRExprAssociative *expX = new IRExprAssociative();
		expX->op = iea->op;
		expX->nr_arguments = iea->nr_arguments;
		expX->nr_arguments_allocated = iea->nr_arguments;
		expX->contents = newArgsX;
		return muxify(
			IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				exp0,
				expX));
	}
		
	case Iex_Load: {
		IRExprLoad *l = (IRExprLoad *)what;
		IRExpr *a = muxify(l->addr);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Load(
					       l->ty,
					       ((IRExprMux0X *)a)->expr0)),
				muxify(IRExpr_Load(
					       l->ty,
					       ((IRExprMux0X *)a)->exprX)));
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

/* Some very quick simplifications which are always applied to the
 * condition of BDD internal nodes.  This isn't much more than just
 * constant folding. */
static IRExpr *
quickSimplify(IRExpr *a)
{
	if (a->optimisationsApplied)
		return a;
	if (a->tag == Iex_Unop) {
		IRExprUnop *au = (IRExprUnop *)a;
		au->arg = quickSimplify(au->arg);
		if (au->arg->tag != Iex_Const)
			return au;
		IRExprConst *arg = (IRExprConst *)au->arg;
		switch (au->op) {
#define do_uconv(_from, _to)						\
			case Iop_ ## _from ## Uto ## _to:		\
				return IRExpr_Const_U ## _to (arg->Ico.U ## _from)
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
			case Iop_ ## _from ## Sto ## _to:		\
				return IRExpr_Const_U ## _to (		\
					(_tot)(_fromt)arg->Ico.U ## _from )
			do_sconv(8, char, 16, short);
			do_sconv(8, char, 32, int);
			do_sconv(8, char, 64, long);
			do_sconv(16, short, 32, int);
			do_sconv(16, short, 64, long);
			do_sconv(32, int, 64, long);
#undef do_sconv
#define do_downconv(_from, _to)						\
			case Iop_ ## _from ## to ## _to:		\
				return IRExpr_Const_U ## _to (arg->Ico.U ## _from)
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
		case Iop_Not1:
			return IRExpr_Const_U1(!arg->Ico.U1);
		case Iop_BadPtr:
			/* Can't constant fold these without an
			 * IRExprOptimisations struct. */
			if (arg->Ico.U64 < 4096)
				return IRExpr_Const_U1(true);
			break;
		case Iop_Neg8:
			return IRExpr_Const_U8(-arg->Ico.U8);
		case Iop_Neg16:
			return IRExpr_Const_U16(-arg->Ico.U16);
		case Iop_Neg32:
			return IRExpr_Const_U32(-arg->Ico.U32);
		case Iop_Neg64:
			return IRExpr_Const_U64(-arg->Ico.U64);
		default:
			abort();
		}
	} else if (a->tag == Iex_Binop) {
		IRExprBinop *ieb = (IRExprBinop *)a;
		ieb->arg1 = quickSimplify(ieb->arg1);
		ieb->arg2 = quickSimplify(ieb->arg2);
		if (ieb->arg1->tag == Iex_Const &&
		    ieb->arg2->tag == Iex_Const) {
			IRExprConst *arg1c = (IRExprConst *)ieb->arg1;
			IRExprConst *arg2c = (IRExprConst *)ieb->arg2;
			switch (ieb->op) {
			case Iop_CmpEQ8:
				return IRExpr_Const_U1(arg1c->Ico.U8 == arg2c->Ico.U8);
			case Iop_CmpEQ32:
				return IRExpr_Const_U1(arg1c->Ico.U32 == arg2c->Ico.U32);
			case Iop_CmpEQ64:
				return IRExpr_Const_U1(arg1c->Ico.U64 == arg2c->Ico.U64);
			case Iop_CmpLT64U:
				return IRExpr_Const_U1(arg1c->Ico.U64 < arg2c->Ico.U64);
			case Iop_Shl64:
				return IRExpr_Const_U64(arg1c->Ico.U64 << arg2c->Ico.U8);
			default:
				abort();
			}
		}
		if (ieb->op == Iop_CmpEQ32 &&
		    ieb->arg1->tag == Iex_Const &&
		    ieb->arg2->tag == Iex_Associative &&
		    ((IRExprAssociative *)ieb->arg2)->op == Iop_Add32 &&
		    ((IRExprAssociative *)ieb->arg2)->nr_arguments >= 2 &&
		    ((IRExprAssociative *)ieb->arg2)->contents[0]->tag == Iex_Const) {
			IRExprConst *arg1 = (IRExprConst *)ieb->arg1;
			IRExprAssociative *arg2 = (IRExprAssociative *)ieb->arg2;
			IRExprConst *arg2a = (IRExprConst *)arg2->contents[0];
			IRExprConst *newArg1 = IRExpr_Const_U32(arg1->Ico.U32 - arg2a->Ico.U32);
			IRExpr *newArg2;
			if (arg2->nr_arguments == 2) {
				newArg2 = arg2->contents[1];
			} else {
				IRExprAssociative *newArg2a = IRExpr_Associative(arg2->nr_arguments - 1, Iop_Add32);
				memcpy(newArg2a->contents, arg2->contents + 1, sizeof(IRExpr *) * (arg2->nr_arguments - 1));
				newArg2 = newArg2a;
			}
			return IRExpr_Binop(ieb->op, newArg1, newArg2);
		}
	} else if (a->tag == Iex_Associative) {
		IRExprAssociative *iea = (IRExprAssociative *)a;
		bool haveConsts = false;
		unsigned long mask;
		unsigned long acc;
		unsigned long defaultValue;
		bool haveNested = false;

		switch (iea->op) {
		case Iop_And1:                                 mask = 1;      defaultValue = mask; break;
		case Iop_And8:                                 mask = 0xff;   defaultValue = mask; break;
		case Iop_And16:                                mask = 0xffff; defaultValue = mask; break;
		case Iop_And32:                                mask = ~0u;    defaultValue = mask; break;
		case Iop_And64:                                mask = ~0ul;   defaultValue = mask; break;
		case Iop_Xor1:  case Iop_Or1:                  mask = 1;      defaultValue = 0; break;
		case Iop_Xor8:  case Iop_Or8:  case Iop_Add8:  mask = 0xff;   defaultValue = 0; break;
		case Iop_Xor16: case Iop_Or16: case Iop_Add16: mask = 0xffff; defaultValue = 0; break;
		case Iop_Xor32: case Iop_Or32: case Iop_Add32: mask = ~0u;    defaultValue = 0; break;
		case Iop_Xor64: case Iop_Or64: case Iop_Add64: mask = ~0ul;   defaultValue = 0; break;
			break;
		default:
			abort();
		}
		acc = defaultValue;
		int new_nr_args = 0;
		for (int i = 0; i < iea->nr_arguments; i++) {
			iea->contents[i] = quickSimplify(iea->contents[i]);
			if (iea->contents[i]->tag == Iex_Const) {
				if (!haveConsts)
					new_nr_args++;
				haveConsts = true;
				switch (iea->op) {
				case Iop_And1: case Iop_And8: case Iop_And16:
				case Iop_And32: case Iop_And64:
					acc &= ((IRExprConst *)iea->contents[i])->Ico.U64;
					break;
				case Iop_Or1: case Iop_Or8: case Iop_Or16:
				case Iop_Or32: case Iop_Or64:
					acc |= ((IRExprConst *)iea->contents[i])->Ico.U64;
					break;
				case Iop_Xor1: case Iop_Xor8: case Iop_Xor16:
				case Iop_Xor32: case Iop_Xor64:
					acc ^= ((IRExprConst *)iea->contents[i])->Ico.U64;
					break;
				case Iop_Add8: case Iop_Add16:
				case Iop_Add32: case Iop_Add64:
					acc += ((IRExprConst *)iea->contents[i])->Ico.U64;
					break;
				default:
					abort();
				}
			} else if (iea->contents[i]->tag == Iex_Associative &&
			    ((IRExprAssociative *)iea->contents[i])->op == iea->op) {
				haveNested = true;
				IRExprAssociative *arg = (IRExprAssociative *)iea->contents[i];
				for (int j = 0; j < arg->nr_arguments; j++) {
					if (arg->contents[j]->tag == Iex_Const) {
						if (!haveConsts)
							new_nr_args++;
						haveConsts = true;
						switch (iea->op) {
						case Iop_And1: case Iop_And8: case Iop_And16:
						case Iop_And32: case Iop_And64:
							acc &= ((IRExprConst *)arg->contents[j])->Ico.U64;
							break;
						case Iop_Or1: case Iop_Or8: case Iop_Or16:
						case Iop_Or32: case Iop_Or64:
							acc |= ((IRExprConst *)arg->contents[j])->Ico.U64;
							break;
						case Iop_Xor1: case Iop_Xor8: case Iop_Xor16:
						case Iop_Xor32: case Iop_Xor64:
							acc ^= ((IRExprConst *)arg->contents[j])->Ico.U64;
							break;
						case Iop_Add8: case Iop_Add16:
						case Iop_Add32: case Iop_Add64:
							acc += ((IRExprConst *)arg->contents[j])->Ico.U64;
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
		if ((iea->op == Iop_And1 || iea->op == Iop_Or1) &&
		    haveConsts) {
			if (iea->op == Iop_And1) {
				if (acc) {
					haveConsts = false;
					new_nr_args--;
				} else {
					return IRExpr_Const_U1(false);
				}
			} else {
				if (!acc) {
					haveConsts = false;
					new_nr_args--;
				} else {
					return IRExpr_Const_U1(true);
				}
			}
		}
		if (haveConsts && acc == defaultValue) {
			haveConsts = false;
			new_nr_args--;
		}
		if (new_nr_args == 0) {
			acc = defaultValue;
			haveConsts = true;
			new_nr_args = 1;
		}
		if (new_nr_args == 1 && haveConsts) {
			switch (iea->type()) {
#define do_ty(n)							\
				case Ity_I ## n :			\
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
		if (new_nr_args == 1) {
			for (int i = 0; i < iea->nr_arguments; i++)
				if (iea->contents[i]->tag != Iex_Const)
					return iea->contents[i];
			abort();
		}
		if (!haveNested && new_nr_args == iea->nr_arguments)
			return iea;
		static libvex_allocation_site __las = {0, __FILE__, __LINE__};
		IRExpr **newArgs = (IRExpr **)
			__LibVEX_Alloc_Bytes(&ir_heap,
					     sizeof(IRExpr *) * new_nr_args,
					     &__las);
		int outIdx = 0;
		if (haveConsts) {
			switch (iea->type()) {
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

		for (int i = 0; i < iea->nr_arguments; i++) {
			if (iea->contents[i]->tag == Iex_Const) {
				/* Already handled */
			} else if (iea->contents[i]->tag == Iex_Associative &&
				   ((IRExprAssociative *)iea->contents[i])->op == iea->op) {
				IRExprAssociative *arg = (IRExprAssociative *)iea->contents[i];
				for (int j = 0; j < arg->nr_arguments; j++) {
					if (arg->contents[j]->tag == Iex_Const) {
						/* Already handled */
					} else {
						newArgs[outIdx] = arg->contents[j];
						outIdx++;
					}
				}
			} else {
				newArgs[outIdx] = iea->contents[i];
				outIdx++;
			}
		}
		assert(outIdx == new_nr_args);
		iea->nr_arguments = new_nr_args;
		iea->nr_arguments_allocated = new_nr_args;
		iea->contents = newArgs;
	} else if (a->tag == Iex_Mux0X) {
		IRExprMux0X *m = (IRExprMux0X *)a;
		m->cond = quickSimplify(m->cond);
		m->expr0 = quickSimplify(m->expr0);
		m->exprX = quickSimplify(m->exprX);
	}
	return a;
}

bbdd *
bbdd::_var(scope *scope, IRExpr *a)
{
	if (a->tag == Iex_Mux0X)
		return ifelse(
			scope,
			_var(scope, ((IRExprMux0X *)a)->cond),
			_var(scope, ((IRExprMux0X *)a)->exprX),
			_var(scope, ((IRExprMux0X *)a)->expr0));
	else
		return scope->makeInternal(a,
					   scope->cnst(true),
					   scope->cnst(false));
}
bbdd *
bbdd::var(scope *scope, IRExpr *a)
{
	return _var(scope, quickSimplify(muxify(quickSimplify(a))));
}

class binary_zip_internal {
public:
	bool isAnd;
	bbdd *first;
	bbdd *second;
	const bdd_rank &bestCond(IRExpr **cond) const {
		assert(!(first->isLeaf && second->isLeaf));
		if (first->isLeaf) {
			*cond = second->internal().condition;
			return second->internal().rank;
		} else if (second->isLeaf) {
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
	binary_zip_internal trueSucc(bdd_ordering *ordering, const bdd_rank &cond) const {
		return binary_zip_internal(
			isAnd,
			ordering->trueBranch(first, cond),
			ordering->trueBranch(second, cond));
	}
	binary_zip_internal falseSucc(bdd_ordering *ordering, const bdd_rank &cond) const {
		return binary_zip_internal(
			isAnd,
			ordering->falseBranch(first, cond),
			ordering->falseBranch(second, cond));
	}
	binary_zip_internal(bool _isAnd, bbdd *_first, bbdd *_second)
		: isAnd(_isAnd), first(_first), second(_second)
	{}
	bool isLeaf() const {
		if (first == second)
			return true;
		return first->isLeaf || second->isLeaf;
	}
	bbdd *leafzip() const {
		assert(isLeaf());
		if (first == second)
			return first;
		if (first->isLeaf) {
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
		} else if (second->isLeaf) {
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
	bbdd *mkNode(bbdd::scope *scope,
		     IRExpr *a,
		     bbdd *t,
		     bbdd *f) const
	{
		return scope->makeInternal(a, t, f);
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
	return zip(scope, binary_zip_internal(true, a, b));
}
bbdd *
bbdd::Or(scope *scope, bbdd *a, bbdd *b)
{
	return zip(scope, binary_zip_internal(false, a, b));
}

bbdd *
bbdd::invert(scope *scope, bbdd *a)
{
	if (a->isLeaf)
		return scope->cnst(!a->leaf());
	else
		return scope->makeInternal(
			a->internal().condition,
			bbdd::invert(scope, a->internal().trueBranch),
			bbdd::invert(scope, a->internal().falseBranch));
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
		bool dupe = false;
		for (auto it2 = variableRankings.begin();
		     !dupe && it2 != variableRankings.end();
		     it2++) {
			if (a != it2->first && physicallyEqual(a, it2->first)) {
				it->second = it2->second;
				dupe = true;
			}
		}
		if (!dupe)
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
	fprintf(f, "r%ld", val);
}

bool
bdd_rank::parse(const char *buf, const char **end)
{
	return parseThisChar('r', buf, &buf) &&
		parseDecimalLong(&val, buf, end);
}

void
bdd_ordering::prettyPrint(FILE *f) const
{
	fprintf(f, "Variable rankings:\n");
	for (auto it = variableRankings.begin();
	     it != variableRankings.end();
	     it++) {
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
		if (e->isLeaf) {
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
exprbdd::_var(exprbdd::scope *scope, bbdd::scope *bscope, IRExpr *what)
{
	if (what->tag == Iex_Mux0X)
		return ifelse(
			scope,
			bbdd::var(bscope, ((IRExprMux0X *)what)->cond),
			_var(scope, bscope, ((IRExprMux0X *)what)->exprX),
			_var(scope, bscope, ((IRExprMux0X *)what)->expr0));
	else if (what->type() == Ity_I1)
		return ifelse(
			scope,
			bbdd::var(bscope, what),
			scope->cnst(IRExpr_Const_U1(true)),
			scope->cnst(IRExpr_Const_U1(false)));
	else
		return scope->cnst(what);
}

exprbdd *
exprbdd::var(exprbdd::scope *scope, bbdd::scope *bscope, IRExpr *what)
{
	return _var(scope, bscope, quickSimplify(muxify(quickSimplify(what))));
}

IRExpr *
exprbdd::to_irexpr(exprbdd *what, std::map<exprbdd *, IRExpr *> &memo)
{
	if (what->isLeaf)
		return what->leaf();
	auto it_did_insert = memo.insert(std::pair<exprbdd *, IRExpr *>(what, (IRExpr *)NULL));
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
	std::map<exprbdd *, IRExpr *> memo;
	return to_irexpr(what, memo);
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
	what = internIRExpr(what, tab);
	auto it_did_insert = leaves.insert(std::pair<IRExpr *, exprbdd *>(what, (exprbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = new exprbdd(what);
	return it->second;
}

void
exprbdd_scope::runGc(HeapVisitor &hv)
{
	std::map<IRExpr *, exprbdd *> newLeaves;
	for (auto it = leaves.begin(); it != leaves.end(); it++) {
		exprbdd *b = hv.visited(it->second);
		newLeaves[it->first] = b;
	}
	leaves = newLeaves;
}

exprbdd *
exprbdd::unop(scope *scope, bbdd::scope *bscope, IROp op, exprbdd *what)
{
	if (what->isLeaf)
		return var(
			scope,
			bscope,
			IRExpr_Unop(op, what->leaf()));
	else
		return ifelse(
			scope,
			bbdd::var(bscope, what->internal().condition),
			unop(scope, bscope, op, what->internal().trueBranch),
			unop(scope, bscope, op, what->internal().falseBranch));
}

exprbdd *
exprbdd::binop(scope *scope, bbdd::scope *bscope, IROp op, IRExpr *a, exprbdd *b)
{
	if (b->isLeaf)
		return var(
			scope,
			bscope,
			IRExpr_Binop(op, a, b->leaf()));
	else
		return ifelse(
			scope,
			bbdd::var(bscope, b->internal().condition),
			exprbdd::binop(scope, bscope, op, a, b->internal().trueBranch),
			exprbdd::binop(scope, bscope, op, a, b->internal().falseBranch));
}

exprbdd *
exprbdd::binop(scope *scope, bbdd::scope *bscope, IROp op, exprbdd *a, IRExpr *b)
{
	if (a->isLeaf)
		return var(
			scope,
			bscope,
			IRExpr_Binop(op, a->leaf(), b));
	else
		return ifelse(
			scope,
			bbdd::var(bscope, a->internal().condition),
			exprbdd::binop(scope, bscope, op, a->internal().trueBranch,  b),
			exprbdd::binop(scope, bscope, op, a->internal().falseBranch, b));
}

exprbdd *
exprbdd::binop(scope *scope, bbdd::scope *bscope, IROp op, exprbdd *a, exprbdd *b)
{
	if (a->isLeaf && b->isLeaf)
		return var(
			scope,
			bscope,
			IRExpr_Binop(op, a->leaf(), b->leaf()));
	else if (a->isLeaf)
		return binop(scope, bscope, op, a->leaf(), b);
	else if (b->isLeaf)
		return binop(scope, bscope, op, a, b->leaf());
	else if (a->internal().rank < b->internal().rank)
		return ifelse(
			scope,
			bbdd::var(bscope, a->internal().condition),
			binop(scope, bscope, op, a->internal().trueBranch, b),
			binop(scope, bscope, op, a->internal().falseBranch, b));
	else if (a->internal().rank == b->internal().rank)
		return ifelse(
			scope,
			bbdd::var(bscope, a->internal().condition),
			binop(scope, bscope, op, a->internal().trueBranch, b->internal().trueBranch),
			binop(scope, bscope, op, a->internal().falseBranch, b->internal().falseBranch));
	else
		return ifelse(
			scope,
			bbdd::var(bscope, b->internal().condition),
			binop(scope, bscope, op, a, b->internal().trueBranch),
			binop(scope, bscope, op, a, b->internal().falseBranch));
}

exprbdd *
exprbdd::load(scope *scope, bbdd::scope *bscope, IRType ty, exprbdd *what)
{
	if (what->isLeaf)
		return var(
			scope,
			bscope,
			IRExpr_Load(ty, what->leaf()));
	else
		return ifelse(
			scope,
			bbdd::var(bscope, what->internal().condition),
			load(scope, bscope, ty, what->internal().trueBranch),
			load(scope, bscope, ty, what->internal().falseBranch));	
}

exprbdd *
exprbdd::coerceTypes(scope *scope, bbdd::scope *bscope, IRType to, exprbdd *what)
{
	return unop(scope, bscope, coerceTypesOp(what->type(), to), what);
}

bbdd *
exprbdd::to_bbdd(bbdd::scope *scope, exprbdd *expr, std::map<exprbdd *, bbdd *> &memo)
{
	auto it_did_insert = memo.insert(std::pair<exprbdd *, bbdd *>(expr, (bbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (expr->isLeaf) {
			IRExpr *l = expr->leaf();
			if (l->tag == Iex_Const) {
				it->second = scope->cnst( ((IRExprConst *)l)->Ico.U1);
			} else {
				it->second =
					scope->makeInternal(
						l,
						scope->cnst(true),
						scope->cnst(false));
			}
		} else {
			it->second = scope->makeInternal(
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
	assert(expr->type() == Ity_I1);
	std::map<exprbdd *, bbdd *> memo;
	return to_bbdd(scope, expr, memo);
}

template void _bdd<bool, bbdd>::prettyPrint(FILE *);
template bbdd *_bdd<bool, bbdd>::assume(const_bdd_scope<bbdd> *, bbdd *, bbdd*);
template IRExpr *const_bdd<bool, bbdd>::to_irexpr<bbdd::mkConst>(bbdd *);
template bbdd *_bdd<bool, bbdd>::ifelse(const_bdd_scope<bbdd> *, bbdd *, bbdd *, bbdd *);

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

template void _bdd<IRExpr *, exprbdd>::prettyPrint(FILE *);
template bool _bdd<IRExpr *, exprbdd>::_parse<exprbdd_scope, exprbdd::parseLeaf>(exprbdd_scope *, exprbdd **, const char *, const char **);
template exprbdd *_bdd<IRExpr *, exprbdd>::assume(exprbdd_scope *, exprbdd *, bbdd*);
template std::map<IRExpr *, bbdd *> _bdd<IRExpr *, exprbdd>::to_selectors(const_bdd_scope<bbdd> *, exprbdd *);
template exprbdd *_bdd<IRExpr *, exprbdd>::from_enabling(exprbdd_scope *, const enablingTableT &, exprbdd *);
