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
	if (TIMEOUT)
		return what;
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

		/* Shut compiler up */
		a = (IRExpr *)0xf001;

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
	if (a->optimisationsApplied || TIMEOUT)
		return a;
	switch (a->tag) {
	case Iex_Unop: {
		IRExprUnop *au = (IRExprUnop *)a;
		auto arg = quickSimplify(au->arg);
		if (arg->tag != Iex_Const) {
			if (arg == au->arg)
				return au;
			else
				return IRExprUnop::mk(au->op, arg);
		}
		IRExprConst *argc = (IRExprConst *)arg;
		switch (au->op) {
#define do_uconv(_from, _to)						\
			case Iop_ ## _from ## Uto ## _to:		\
				return IRExpr_Const_U ## _to (argc->Ico.U ## _from)
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
					(_tot)(_fromt)argc->Ico.U ## _from )
			do_sconv(8, char, 16, short);
			do_sconv(8, char, 32, int);
			do_sconv(8, char, 64, long);
			do_sconv(16, short, 32, int);
			do_sconv(16, short, 64, long);
			do_sconv(32, int, 64, long);
#undef do_sconv
#define do_downconv(_from, _to)						\
			case Iop_ ## _from ## to ## _to:		\
				return IRExpr_Const_U ## _to (argc->Ico.U ## _from)
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
			return IRExpr_Const_U64(argc->Ico.U128.lo);
		case Iop_64UtoV128:
			return IRExpr_Const_U128(0, argc->Ico.U64);
		case Iop_BadPtr:
			/* Can't constant fold these without an
			 * IRExprOptimisations struct. */
			if (argc->Ico.U64 < 4096)
				return IRExpr_Const_U1(true);
			if (arg == au->arg)
				return au;
			else
				return IRExprUnop::mk(au->op, arg);
			break;
		case Iop_Neg8:
			return IRExpr_Const_U8(-argc->Ico.U8);
		case Iop_Neg16:
			return IRExpr_Const_U16(-argc->Ico.U16);
		case Iop_Neg32:
			return IRExpr_Const_U32(-argc->Ico.U32);
		case Iop_Neg64:
			return IRExpr_Const_U64(-argc->Ico.U64);
		case Iop_Not1:
			return IRExpr_Const_U1(!argc->Ico.U1);
		case Iop_Not8:
			return IRExpr_Const_U8(~argc->Ico.U8);
		case Iop_Not16:
			return IRExpr_Const_U16(~argc->Ico.U16);
		case Iop_Not32:
			return IRExpr_Const_U32(~argc->Ico.U32);
		case Iop_Not64:
			return IRExpr_Const_U64(~argc->Ico.U64);
		default:
			abort();
		}
		break;
	}
	case Iex_Binop: {
		IRExprBinop *_ieb = (IRExprBinop *)a;
		auto arg1 = quickSimplify(_ieb->arg1);
		auto arg2 = quickSimplify(_ieb->arg2);
		if (arg1->tag == Iex_Const &&
		    arg2->tag == Iex_Const) {
			IRExprConst *arg1c = (IRExprConst *)arg1;
			IRExprConst *arg2c = (IRExprConst *)arg2;
			switch (_ieb->op) {
#define do_type(sz)							\
				case Iop_CmpEQ ## sz:			\
					return IRExpr_Const_U1(arg1c->Ico.U ## sz == arg2c->Ico.U ## sz); \
			case Iop_CmpLT ## sz ## U:			\
				return IRExpr_Const_U1(arg1c->Ico.U ## sz < arg2c->Ico.U ## sz)
				do_type(8);
				do_type(16);
				do_type(32);
				do_type(64);
#undef do_type
			case Iop_CmpLT8S:
				return IRExpr_Const_U1((char)arg1c->Ico.U8 < (char)arg2c->Ico.U8);
			case Iop_CmpLT16S:
				return IRExpr_Const_U1((short)arg1c->Ico.U16 < (short)arg2c->Ico.U16);
			case Iop_CmpLT32S:
				return IRExpr_Const_U1((int)arg1c->Ico.U32 < (int)arg2c->Ico.U32);
			case Iop_CmpLT64S:
				return IRExpr_Const_U1((long)arg1c->Ico.U64 < (long)arg2c->Ico.U64);
			case Iop_Shl64:
				return IRExpr_Const_U64(arg1c->Ico.U64 << arg2c->Ico.U8);
			case Iop_Shr64:
				return IRExpr_Const_U64(arg1c->Ico.U64 >> arg2c->Ico.U8);
			case Iop_Sar64:
			  return IRExpr_Const_U64((long)arg1c->Ico.U64 >> arg2c->Ico.U8);
			case Iop_32HLto64:
				return IRExpr_Const_U64(arg1c->Ico.U32 | ((unsigned long)arg2c->Ico.U32 << 32));
			case Iop_DivModU64to32: {
				unsigned long num = arg1c->Ico.U64;
				unsigned long denom = arg2c->Ico.U32;
				if (denom == 0) {
					warning("Constant division by zero (%ld/%ld)?\n",
						num, denom);
					break;
				}
				unsigned long div = num / denom;
				unsigned long mod = num % denom;
				return IRExpr_Const_U64((div << 32) | (mod & 0xffffffff));
			}
			case Iop_Mul64:
				return IRExpr_Const_U64(arg1c->Ico.U64 * arg2c->Ico.U64);
			case Iop_64HLto128:
				return IRExpr_Const_U128(arg1c->Ico.U64, arg2c->Ico.U64);
			case Iop_DivModU128to64: {
				__uint128_t num;
				unsigned long denom = arg2c->Ico.U64;
				num = arg1c->Ico.U128.hi;
				num <<= 64;
				num |= arg1c->Ico.U128.lo;
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
			default:
				abort();
			}
		}
		if (_ieb->op == Iop_CmpEQ32 &&
		    arg1->tag == Iex_Const &&
		    arg2->tag == Iex_Associative &&
		    ((IRExprAssociative *)arg2)->op == Iop_Add32 &&
		    ((IRExprAssociative *)arg2)->nr_arguments >= 2 &&
		    ((IRExprAssociative *)arg2)->contents[0]->tag == Iex_Const) {
			IRExprConst *arg1c = (IRExprConst *)arg1;
			IRExprAssociative *arg2a = (IRExprAssociative *)arg2;
			IRExprConst *arg2c = (IRExprConst *)arg2a->contents[0];
			IRExprConst *newArg1 = IRExpr_Const_U32(arg1c->Ico.U32 - arg2c->Ico.U32);
			IRExpr *newArg2;
			if (arg2a->nr_arguments == 2) {
				newArg2 = arg2a->contents[1];
			} else {
				newArg2 = IRExpr_Associative_Copy(Iop_Add32, arg2a->nr_arguments - 1, arg2a->contents + 1);
			}
			return IRExpr_Binop(_ieb->op, newArg1, newArg2);
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
			break;
		default:
			abort();
		}
		acc = defaultValue;
		for (int i = 0; i < nr_arguments; i++) {
			simpleArgs[i] = quickSimplify(_iea->contents[i]);
			if (simpleArgs[i] != _iea->contents[i])
				realloc = true;
			if (simpleArgs[i]->tag == Iex_Const) {
				switch (op) {
				case Iop_And1: case Iop_And8: case Iop_And16:
				case Iop_And32: case Iop_And64:
					acc &= ((IRExprConst *)simpleArgs[i])->Ico.U64;
					break;
				case Iop_Or1: case Iop_Or8: case Iop_Or16:
				case Iop_Or32: case Iop_Or64:
					acc |= ((IRExprConst *)simpleArgs[i])->Ico.U64;
					break;
				case Iop_Xor8: case Iop_Xor16:
				case Iop_Xor32: case Iop_Xor64:
					acc ^= ((IRExprConst *)simpleArgs[i])->Ico.U64;
					break;
				case Iop_Add8: case Iop_Add16:
				case Iop_Add32: case Iop_Add64:
					acc += ((IRExprConst *)simpleArgs[i])->Ico.U64;
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
							acc &= ((IRExprConst *)arg->contents[j])->Ico.U64;
							break;
						case Iop_Or1: case Iop_Or8: case Iop_Or16:
						case Iop_Or32: case Iop_Or64:
							acc |= ((IRExprConst *)arg->contents[j])->Ico.U64;
							break;
						case Iop_Xor8: case Iop_Xor16:
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
		if (op == Iop_And1 && acc == 0)
			return IRExpr_Const_U1(false);
		if (op == Iop_Or1 && acc == 1)
			return IRExpr_Const_U1(true);
		if (new_nr_args == 0) {
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
		if (new_nr_args == 1) {
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
		a = IRExpr_Associative_Claim(op, new_nr_args, newArgs);
		break;
	}
	case Iex_Mux0X: {
		IRExprMux0X *m = (IRExprMux0X *)a;
		auto cond = quickSimplify(m->cond);
		auto expr0 = quickSimplify(m->expr0);
		auto exprX = quickSimplify(m->exprX);
		if (cond != m->cond || expr0 != m->expr0 ||
		    exprX != m->exprX)
			a = IRExprMux0X::mk(cond, expr0, exprX);
		break;
	}
	case Iex_Load: {
		IRExprLoad *l = (IRExprLoad *)a;
		auto addr = quickSimplify(l->addr);
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
		auto a1 = quickSimplify(q->arg1);
		auto a2 = quickSimplify(q->arg2);
		auto a3 = quickSimplify(q->arg3);
		auto a4 = quickSimplify(q->arg4);
		if (a1 != q->arg1 || a2 != q->arg2 || a3 != q->arg3 || a4 != q->arg4)
			a = IRExprQop::mk(q->op, a1, a2, a3, a4);
		break;
	}
	case Iex_Triop: {
		IRExprTriop *q = (IRExprTriop *)a;
		auto a1 = quickSimplify(q->arg1);
		auto a2 = quickSimplify(q->arg2);
		auto a3 = quickSimplify(q->arg3);
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
			newArgs[i] = quickSimplify(c->args[i]);
			if (newArgs[i] != c->args[i])
				realloc = true;
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
	binary_zip_internal f(true, a, b);
	return zip(scope, f);
}
bbdd *
bbdd::Or(scope *scope, bbdd *a, bbdd *b)
{
	binary_zip_internal f(false, a, b);
	return zip(scope, f);
}

bbdd *
bbdd::invert(scope *scope, bbdd *a, std::map<bbdd *, bbdd *> &memo)
{
	if (TIMEOUT)
		return NULL;
	if (a->isLeaf())
		return scope->cnst(!a->leaf());

	auto it_did_insert = memo.insert(std::pair<bbdd *, bbdd *>(a, (bbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;
	bbdd *t = bbdd::invert(scope, a->internal().trueBranch, memo);
	bbdd *f = bbdd::invert(scope, a->internal().falseBranch, memo);
	if (!t || !f)
		return NULL;
	it->second = scope->makeInternal(a->internal().condition, t, f);
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
bdd_ordering::prettyPrint(FILE *f) const
{
	std::set<bdd_rank> printed;
	fprintf(f, "Variable rankings:\n");
	for (auto it = variableRankings.begin();
	     it != variableRankings.end();
	     it++) {
		if (!printed.insert(it->second).second)
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
exprbdd::_var(exprbdd::scope *scope, bbdd::scope *bscope, IRExpr *what)
{
	if (TIMEOUT)
		return NULL;

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
	if (what->isLeaf())
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
	if (!what)
		return NULL;
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
	return exprbdd::restructure_zip(scope, bscope, unop_zipper(op, what));
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
	auto it_did_insert = memo.insert(std::pair<exprbdd *, bbdd *>(expr, (bbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (expr->isLeaf()) {
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
	if (TIMEOUT)
		return NULL;
	assert(expr->type() == Ity_I1);
	std::map<exprbdd *, bbdd *> memo;
	return to_bbdd(scope, expr, memo);
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
