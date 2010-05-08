#include <math.h>
#include <string.h>

#include "libvex.h"
#include "libvex_ir.h"
#include "libvex_emwarn.h"
#include "libvex_guest_amd64.h"
#include "guest_generic_bb_to_IR.h"
#include "guest_amd64_defs.h"
#include "main_util.h"

#define FOOTSTEP_REGS_ONLY
#include "ppres.h"

#include "sli.h"

static Bool chase_into_ok(void *ignore1, Addr64 ignore2)
{
	return False;
}

#define REG_LAST 128

static unsigned long *
get_reg(Thread *state, unsigned offset)
{
	assert(!(offset % 8));
	assert(offset < sizeof(state->regs.regs));
	return &((unsigned long *)&state->regs.regs)[offset/8];
}

static const struct expression *
read_reg(Thread *state, unsigned offset, unsigned long *v)
{
	*v = *get_reg(state, offset);
	return NULL;
}

ThreadEvent *
Thread::do_dirty_call(IRDirty *details)
{
	struct expression_result args[6];
	unsigned x;

	if (details->guard) {
		expression_result guard = eval_expression(details->guard);
		if (!guard.lo.v)
			return NULL;
	}
	for (x = 0; details->args[x]; x++) {
		assert(x < 6);
		args[x] = eval_expression(details->args[x]);
	}
	assert(!details->cee->regparms);

	if (!strcmp(details->cee->name, "amd64g_dirtyhelper_RDTSC")) {
		return new RdtscEvent(details->tmp);
	} else if (!strcmp(details->cee->name, "helper_load_8")) {
		return new LoadEvent(details->tmp, args[0].lo.v, 1);
	} else if (!strcmp(details->cee->name, "helper_load_16")) {
		return new LoadEvent(details->tmp, args[0].lo.v, 2);
	} else if (!strcmp(details->cee->name, "helper_load_32")) {
		return new LoadEvent(details->tmp, args[0].lo.v, 4);
	} else if (!strcmp(details->cee->name, "helper_load_64")) {
		return new LoadEvent(details->tmp, args[0].lo.v, 8);
	} else if (!strcmp(details->cee->name, "helper_load_128")) {
		return new LoadEvent(details->tmp, args[0].lo.v, 16);
	} else if (!strcmp(details->cee->name, "amd64g_dirtyhelper_CPUID_sse3_and_cx16")) {
		unsigned long res;
		if (details->needsBBP) {
			res = ((unsigned long (*)(VexGuestAMD64State *,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long))(details->cee->addr))
				(&regs.regs, args[0].lo.v, args[1].lo.v, args[2].lo.v, args[3].lo.v,
				 args[4].lo.v, args[5].lo.v);
		} else {
			res = ((unsigned long (*)(unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long))(details->cee->addr))
				(args[0].lo.v, args[1].lo.v, args[2].lo.v, args[3].lo.v,
				 args[4].lo.v, args[5].lo.v);
		}
		if (details->tmp != IRTemp_INVALID) {
			temporaries[details->tmp].lo.v = res;
			temporaries[details->tmp].hi.v = 0;
		}
		return NULL;
	} else {
		throw NotImplementedException("Unknown dirty call %s\n", details->cee->name);
	}
}

static void
calculate_condition_flags_XXX(unsigned long op,
			      unsigned long dep1,
			      unsigned long dep2,
			      unsigned long ndep,
			      unsigned &cf,
			      unsigned &zf,
			      unsigned &sf,
			      unsigned &of)
{
	cf = zf = sf = of = 0;

	switch (op) {
	case AMD64G_CC_OP_COPY:
		cf = dep1;
		zf = dep1 >> 6;
		sf = dep1 >> 7;
		of = dep1 >> 11;
		break;

#define DO_ACT(name, type_tag, type, bits)				\
		case AMD64G_CC_OP_ ## name ## type_tag:			\
			ACTIONS_ ## name (type, bits);		        \
		        break
#define ACTION(name)							\
		DO_ACT(name, B, unsigned char, 7);			\
		DO_ACT(name, W, unsigned short, 15);			\
		DO_ACT(name, L, unsigned, 31);		                \
		DO_ACT(name, Q, unsigned long, 63)
#define ACTIONS_ADD(type, bits)                                         \
		do {							\
			type res;					\
			res = dep1 + dep2;				\
			cf = res < (type)dep1;				\
			zf = (res == 0);				\
			sf = (res >> bits);				\
			of = (~(dep1 ^ dep2) &				\
			      (dep1 ^ res)) >> bits;			\
		} while (0)
#define ACTIONS_SUB(type, bits)						\
		do {							\
			type res;					\
			res = dep1 - dep2;				\
			cf = (type)dep1 < (type)dep2;			\
			zf = (res == 0);				\
			sf = res >> bits;				\
			of = ( (dep1 ^ dep2) &				\
			       (dep1 ^ res) ) >> bits;			\
		} while (0)
#define ACTIONS_LOGIC(type, bits)		                        \
		do {							\
			cf = 0;						\
			zf = (type)dep1 == 0;				\
			sf = (type)dep1 >> bits;			\
			of = 0;						\
		} while (0)
#define ACTIONS_INC(type, bits)			                        \
		do {				                        \
			type res = dep1;				\
			cf = ndep & 1;					\
			zf = (res == 0);				\
			sf = res >> bits;				\
			of = res == (1ull << bits);			\
		} while (0)
#define ACTIONS_DEC(type, bits)			                        \
		do {				                        \
			type res = dep1;				\
			cf = ndep & 1;					\
			zf = (res == 0);				\
			sf = res >> bits;				\
			of = (type)(res + 1) == (1ull << bits);		\
		} while (0)
#define ACTIONS_SHR(type, bits)			                        \
		do {				                        \
			cf = dep2 & 1;					\
			zf = (dep1 == 0);				\
			sf = dep1 >> bits;				\
			of = (dep1 ^ dep2) >> bits;			\
		} while (0)
	ACTION(ADD);
	ACTION(SUB);
	ACTION(LOGIC);
	ACTION(INC);
	ACTION(DEC);
	ACTION(SHR);
#undef DO_ACT
#undef ACTION
#undef ACTIONS_ADD
#undef ACTIONS_SUB
#undef ACTIONS_LOGIC
#undef ACTIONS_INC
#undef ACTIONS_DEC
#undef ACTIONS_SHR
	default:
		throw NotImplementedException("Strange operation code %ld\n", op);
	}

	of &= 1;
	sf &= 1;
	zf &= 1;
	cf &= 1;
}

expression_result
Thread::do_ccall_calculate_condition(struct expression_result *args)
{
	struct expression_result condcode = args[0];
	struct expression_result op = args[1];
	struct expression_result dep1 =	args[2];
	struct expression_result dep2 =	args[3];
	struct expression_result ndep =	args[4];
	struct expression_result res;
	int inv;
	unsigned cf, zf, sf, of;

	calculate_condition_flags_XXX(op.lo.v,
				      dep1.lo.v,
				      dep2.lo.v,
				      ndep.lo.v,
				      cf,
				      zf,
				      sf,
				      of);

	inv = condcode.lo.v & 1;
	switch (condcode.lo.v & ~1) {
	case AMD64CondZ:
		res.lo.v = zf;
		break;
	case AMD64CondL:
		res.lo.v = sf ^ of;
		break;
	case AMD64CondLE:
		res.lo.v = (sf ^ of) | zf;
		break;
	case AMD64CondB:
		res.lo.v = cf;
		break;
	case AMD64CondBE:
		res.lo.v = cf | zf;
		break;
	case AMD64CondS:
		res.lo.v = sf;
		break;

	default:
		throw NotImplementedException("Strange cond code %ld (op %ld)\n", condcode.lo.v, op.lo.v);
	}

	if (inv)
		res.lo.v ^= 1;

	return res;
}

expression_result
Thread::do_ccall_calculate_rflags_c(expression_result *args)
{
	struct expression_result op = args[0];
	struct expression_result dep1 =	args[1];
	struct expression_result dep2 =	args[2];
	struct expression_result ndep =	args[3];
	struct expression_result res;
	unsigned cf, zf, sf, of;

	calculate_condition_flags_XXX(op.lo.v,
				      dep1.lo.v,
				      dep2.lo.v,
				      ndep.lo.v,
				      cf,
				      zf,
				      sf,
				      of);

	res.lo.v = cf;
	return res;
}

expression_result
Thread::do_ccall_generic(IRCallee *cee,
			 struct expression_result *rargs)
{
	struct expression_result res;

	res.lo.v = ((unsigned long (*)(unsigned long, unsigned long, unsigned long,
				       unsigned long, unsigned long, unsigned long))cee->addr)
		(rargs[0].lo.v, rargs[1].lo.v, rargs[2].lo.v, rargs[3].lo.v, rargs[4].lo.v,
		 rargs[5].lo.v);
	res.hi.v = 0;
	return res;
}

expression_result
Thread::do_ccall(IRCallee *cee,
		 IRExpr **args)
{
	struct expression_result rargs[6];
	unsigned x;

	assert(cee->regparms == 0);
	for (x = 0; args[x]; x++) {
		assert(x < 6);
		rargs[x] = eval_expression(args[x]);
	}
	if (!strcmp(cee->name, "amd64g_calculate_condition")) {
		return do_ccall_calculate_condition(rargs);
	} else if (!strcmp(cee->name, "amd64g_calculate_rflags_c")) {
		return do_ccall_calculate_rflags_c(rargs);
	} else {
		printf("Unknown clean call %s\n", cee->name);
		return do_ccall_generic(cee, rargs);
	}
}

/* Borrowed from gnucash */
static void
mulls64(struct expression_result *dest, const struct expression_result &src1,
	const struct expression_result &src2)
{
	bool isneg = false;
	long a = src1.lo.v;
	long b = src2.lo.v;
	unsigned long a0, a1;
	unsigned long b0, b1;
	unsigned long d, d0, d1;
	unsigned long e, e0, e1;
	unsigned long f, f0, f1;
	unsigned long g, g0, g1;
	unsigned long sum, carry, roll, pmax;
 
	if (0 > a)
	{
		isneg = !isneg;
		a = -a;
	}
 
	if (0 > b)
	{
		isneg = !isneg;
		b = -b;
	}
 
	a1 = a >> 32;
	a0 = a - (a1 << 32);
 
	b1 = b >> 32;
	b0 = b - (b1 << 32);
 
	d = a0 * b0;
	d1 = d >> 32;
	d0 = d - (d1 << 32);
 
	e = a0 * b1;
	e1 = e >> 32;
	e0 = e - (e1 << 32);
 
	f = a1 * b0;
	f1 = f >> 32;
	f0 = f - (f1 << 32);
 
	g = a1 * b1;
	g1 = g >> 32;
	g0 = g - (g1 << 32);
 
	sum = d1 + e0 + f0;
	carry = 0;
	/* Can't say 1<<32 cause cpp will goof it up; 1ULL<<32 might work */
	roll = 1 << 30;
	roll <<= 2;
 
	pmax = roll - 1;
	while (pmax < sum)
	{
		sum -= roll;
		carry ++;
	}
 
	dest->lo.v = d0 + (sum << 32);
	dest->hi.v = carry + e1 + f1 + g0 + (g1 << 32);
	if (isneg) {
		dest->lo.v = ~dest->lo.v;
		dest->hi.v = ~dest->hi.v;
		dest->lo.v++;
		if (dest->lo.v == 0)
			dest->hi.v++;
	}
}

expression_result
Thread::eval_expression(IRExpr *expr)
{
	struct expression_result res;
	struct expression_result *dest = &res;
	dest->lo.v = 0xdeadbeeff001f001;
	dest->hi.v = 0xaaaaaaaaaaaaaaaa;

	switch (expr->tag) {
	case Iex_Get: {
		unsigned long v1;
		const struct expression *src1;
		unsigned sub_word_offset = expr->Iex.Get.offset & 7;
		src1 = read_reg(this,
				expr->Iex.Get.offset - sub_word_offset,
				&v1);
		switch (expr->Iex.Get.ty) {
		case Ity_I64:
		case Ity_F64:
			assert(!sub_word_offset);
			dest->lo.v = v1;
			break;
		case Ity_V128:
			assert(!sub_word_offset);
			dest->lo.v = v1;
			read_reg(this,
				 expr->Iex.Get.offset - sub_word_offset + 8,
				 &dest->hi.v);
			break;
		case Ity_I32:
		case Ity_F32:
			assert(!(sub_word_offset % 4));
			dest->lo.v = (v1 >> (sub_word_offset * 8)) & 0xffffffff;
			break;
		case Ity_I16:
			assert(!(sub_word_offset % 2));
			dest->lo.v = (v1 >> (sub_word_offset * 8)) & 0xffff;
			break;
		case Ity_I8:
			dest->lo.v = (v1 >> (sub_word_offset * 8)) & 0xff;
			break;
		default:
			ppIRExpr(expr);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_RdTmp:
		*dest = temporaries[expr->Iex.RdTmp.tmp];
		break;

	case Iex_Load:
		throw SliException("transform_expr failed to remove all load expressions\n");

	case Iex_Const: {
		IRConst *cnst = expr->Iex.Const.con;
		switch (cnst->tag) {
		case Ico_U1:
			dest->lo.v = cnst->Ico.U1;
			break;
		case Ico_U8:
			dest->lo.v = cnst->Ico.U8;
			break;
		case Ico_U16:
			dest->lo.v = cnst->Ico.U16;
			break;
		case Ico_U32:
			dest->lo.v = cnst->Ico.U32;
			break;
		case Ico_U64:
		case Ico_F64:
		case Ico_F64i:
			dest->lo.v = cnst->Ico.U64;
			break;
		case Ico_V128:
			dest->lo.v = cnst->Ico.V128;
			dest->lo.v = dest->lo.v | (dest->lo.v << 16) | (dest->lo.v << 32) | (dest->lo.v << 48);
			dest->hi.v = dest->lo.v;
			break;
		default:
			ppIRExpr(expr);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_Binop: {
		struct expression_result arg1 = eval_expression(expr->Iex.Binop.arg1);
		struct expression_result arg2 = eval_expression(expr->Iex.Binop.arg2);
		switch (expr->Iex.Binop.op) {
		case Iop_Sub8:
		case Iop_Sub16:
		case Iop_Sub32:
		case Iop_Sub64:
			dest->lo.v = arg1.lo.v - arg2.lo.v;
			break;
		case Iop_Add8:
		case Iop_Add16:
		case Iop_Add32:
		case Iop_Add64:
			dest->lo.v = arg1.lo.v + arg2.lo.v;
			break;
		case Iop_Add64x2:
			dest->lo.v = arg1.lo.v + arg2.lo.v;
			dest->hi.v = arg1.hi.v + arg2.hi.v;
			break;
		case Iop_And64:
		case Iop_And32:
		case Iop_And16:
		case Iop_And8:
			dest->lo.v = arg1.lo.v & arg2.lo.v;
			break;
		case Iop_Or8:
		case Iop_Or16:
		case Iop_Or32:
		case Iop_Or64:
			dest->lo.v = arg1.lo.v | arg2.lo.v;
			break;
		case Iop_Shl32:
		case Iop_Shl64:
			dest->lo.v = arg1.lo.v << arg2.lo.v;
			break;
		case Iop_Sar64:
			dest->lo.v = (long)arg1.lo.v >> arg2.lo.v;
			break;
		case Iop_Shr32:
		case Iop_Shr64:
			dest->lo.v = arg1.lo.v >> arg2.lo.v;
			break;
		case Iop_XorV128:
		case Iop_Xor64:
		case Iop_Xor32:
		case Iop_Xor16:
		case Iop_Xor8:
			dest->lo.v = arg1.lo.v ^ arg2.lo.v;
			dest->hi.v = arg1.hi.v ^ arg2.hi.v;
			break;
		case Iop_CmpNE8:
			dest->lo.v = arg1.lo.v != arg2.lo.v;
			break;
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			dest->lo.v = arg1.lo.v == arg2.lo.v;
			break;
		case Iop_CmpNE32:
		case Iop_CasCmpNE32:
		case Iop_CmpNE64:
			dest->lo.v = arg1.lo.v != arg2.lo.v;
			break;
		case Iop_CmpLE64U:
			dest->lo.v = arg1.lo.v <= arg2.lo.v;
			break;
		case Iop_CmpLE64S:
			dest->lo.v = (long)arg1.lo.v <= (long)arg2.lo.v;
			break;
		case Iop_CmpLT64S:
			dest->lo.v = (long)arg1.lo.v < (long)arg2.lo.v;
			break;
		case Iop_CmpLT64U:
			dest->lo.v = arg1.lo.v < arg2.lo.v;
			break;
		case Iop_Mul64:
		case Iop_Mul32:
			dest->lo.v = arg1.lo.v * arg2.lo.v;
			break;

		case Iop_MullU32: {
			dest->lo.v = arg1.lo.v * arg2.lo.v;
			break;
		}
		case Iop_MullS32: {
			dest->lo.v = (long)(int)arg1.lo.v * (long)(int)arg2.lo.v;
			break;
		}

		case Iop_MullS64:
			mulls64(dest, arg1, arg2);
			break;

		case Iop_MullU64: {
			unsigned long a1, a2, b1, b2;
			dest->lo.v = arg1.lo.v * arg2.lo.v;
			a1 = arg1.lo.v & 0xffffffff;
			a2 = arg1.lo.v >> 32;
			b1 = arg2.lo.v & 0xffffffff;
			b2 = arg2.lo.v >> 32;
			dest->hi.v = a2 * b2 +
				( (a1 * b2 + a2 * b1 +
				   ((a1 * b1) >> 32)) >> 32);
			break;
		}
		case Iop_32HLto64:
			dest->lo.v = (arg1.lo.v << 32) | arg2.lo.v;
			break;

		case Iop_64HLtoV128:
		case Iop_64HLto128:
			dest->lo.v = arg2.lo.v;
			dest->hi.v = arg1.lo.v;
			break;

		case Iop_DivModU64to32:
			dest->lo.v = (arg1.lo.v / arg2.lo.v) |
				((arg1.lo.v % arg2.lo.v) << 32);
			break;

		case Iop_DivModS64to32: {
			long a1 = arg1.lo.v;
			long a2 = arg2.lo.v;
			dest->lo.v = ((a1 / a2) & 0xffffffff) |
				((a1 % a2) << 32);
			break;
		}

		case Iop_DivModU128to64:
			/* arg1 is a I128, arg2 is an I64, result is
			   128 bits and has the dividend in its low 64
			   bits and the modulus in its high 64
			   bits. */
			asm ("div %4\n"
			     : "=a" (dest->lo.v), "=d" (dest->hi.v)
			     : "0" (arg1.lo.v), "1" (arg1.hi.v), "r" (arg2.lo.v));
			break;

		case Iop_DivModS128to64:
			asm ("idiv %4\n"
			     : "=a" (dest->lo.v), "=d" (dest->hi.v)
			     : "0" (arg1.lo.v), "1" (arg1.hi.v), "r" (arg2.lo.v));
			break;

		case Iop_Add32x4:
			dest->lo.v = ((arg1.lo.v + arg2.lo.v) & 0xffffffff) +
				((arg1.lo.v & ~0xfffffffful) + (arg2.lo.v & ~0xfffffffful));
			dest->hi.v = ((arg1.hi.v + arg2.hi.v) & 0xffffffff) +
				((arg1.hi.v & ~0xfffffffful) + (arg2.hi.v & ~0xfffffffful));
			break;

		case Iop_InterleaveLO64x2:
			dest->lo.v = arg2.lo.v;
			dest->hi.v = arg1.lo.v;
			break;

		case Iop_InterleaveHI64x2:
			dest->lo.v = arg2.hi.v;
			dest->hi.v = arg1.hi.v;
			break;

		case Iop_InterleaveLO32x4:
			dest->lo.v = (arg2.lo.v & 0xffffffff) | (arg1.lo.v << 32);
			dest->hi.v = (arg2.lo.v >> 32) | (arg1.lo.v & 0xffffffff00000000ul);
			break;

		case Iop_InterleaveHI32x4:
			dest->lo.v = (arg2.hi.v & 0xffffffff) | (arg1.hi.v << 32);
			dest->hi.v = (arg2.hi.v >> 32) | (arg1.hi.v & 0xffffffff00000000ul);
			break;

		case Iop_ShrN64x2:
			dest->lo.v = arg1.lo.v >> arg2.lo.v;
			dest->hi.v = arg1.hi.v >> arg2.lo.v;
			break;

		case Iop_ShlN64x2:
			dest->lo.v = arg1.lo.v << arg2.lo.v;
			dest->hi.v = arg1.hi.v << arg2.lo.v;
			break;

		case Iop_CmpGT32Sx4:
			dest->lo.v = 0;
			dest->hi.v = 0;
			if ( (int)arg1.lo.v > (int)arg2.lo.v )
				dest->lo.v |= 0xffffffff;
			if ( (int)(arg1.lo.v >> 32) > (int)(arg2.lo.v >> 32) )
				dest->lo.v |= 0xffffffff00000000;
			if ( (int)arg1.hi.v > (int)arg2.hi.v )
				dest->hi.v |= 0xffffffff;
			if ( (int)(arg1.hi.v >> 32) > (int)(arg2.hi.v >> 32) )
				dest->hi.v |= 0xffffffff00000000;
			break;
			
		case Iop_I64toF64: {
			switch (arg1.lo.v) {
			case 0:
				/* Round to nearest even mode. */
				*(double *)&dest->lo.v = arg2.lo.v;
				break;
			default:
				throw NotImplementedException("unknown rounding mode %ld\n",
							      arg1.lo.v);
			}
			break;
		}

		case Iop_F64toI32: {
			switch (arg1.lo.v) {
			case 3:
				dest->lo.v = (unsigned)*(double *)&arg2.lo.v;
				break;
			default:
				throw NotImplementedException("unknown rounding mode %ld\n",
							      arg1.lo.v);
			}
			break;
		}

		case Iop_CmpF64: {
			double a1 = *(double *)&arg1.lo.v;
			double a2 = *(double *)&arg2.lo.v;
			if (a1 < a2)
				dest->lo.v = 1;
			else if (a1 == a2)
				dest->lo.v = 0x40;
			else if (a1 > a2)
				dest->lo.v = 0;
			else
				dest->lo.v = 0x45;
			break;
		}

		default:
			ppIRExpr(expr);
			throw NotImplementedException();
		}

		IRType t, ign1, ign2, ign3, ign4;
		typeOfPrimop(expr->Iex.Binop.op, &t, &ign1, &ign2, &ign3, &ign4);
		switch (t) {
		case Ity_I1:
			dest->lo.v &= 1;
			dest->hi.v = 0;
			break;
		case Ity_I8:
			dest->lo.v &= 0xff;
			dest->hi.v = 0;
			break;
		case Ity_I16:
			dest->lo.v &= 0xffff;
			dest->hi.v = 0;
			break;
		case Ity_I32:
			dest->lo.v &= 0xffffffff;
			dest->hi.v = 0;
			break;
		case Ity_I64:
			dest->hi.v = 0;
			break;

			/* Floating types follow the same rule as the
			   integer ones (unused bits must be zero),
			   but it's not safe to enforce it with a
			   simple mask, so assert that it's already
			   true. */
		case Ity_F32:
			assert(!(dest->lo.v & ~0xfffffffful));
		case Ity_F64:
			assert(dest->hi.v == 0);
			break;

		case Ity_I128:
		case Ity_V128:
			break;
		default:
			ppIRType(t);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_Unop: {
		struct expression_result arg = eval_expression(expr->Iex.Unop.arg);
		switch (expr->Iex.Unop.op) {
		case Iop_64HIto32:
			dest->lo.v = arg.lo.v >> 32;
			break;
		case Iop_64to32:
			dest->lo.v = arg.lo.v & 0xffffffff;
			break;
		case Iop_64to16:
			dest->lo.v = arg.lo.v & 0xffff;
			break;
		case Iop_64to8:
			dest->lo.v = arg.lo.v & 0xff;
			break;
		case Iop_128to64:
		case Iop_V128to64:
			dest->lo.v = arg.lo.v;
			break;
		case Iop_64UtoV128:
			dest->lo.v = arg.lo.v;
			dest->hi.v = 0;
			break;
		case Iop_64to1:
			dest->lo.v = arg.lo.v & 1;
			break;
		case Iop_32Uto64:
		case Iop_16Uto64:
		case Iop_16Uto32:
		case Iop_1Uto64:
		case Iop_1Uto8:
		case Iop_8Uto32:
		case Iop_8Uto64:
			*dest = arg;
			break;
		case Iop_32Sto64:
			dest->lo.v = (long)(int)arg.lo.v;
			break;
		case Iop_8Sto64:
			dest->lo.v = (long)(signed char)arg.lo.v;
			break;
		case Iop_16Sto32:
			dest->lo.v = (unsigned)(signed short)arg.lo.v;
			break;
		case Iop_8Sto32:
			dest->lo.v = (unsigned)(signed char)arg.lo.v;
			break;
		case Iop_16Sto64:
			dest->lo.v = (long)(short)arg.lo.v;
			break;
		case Iop_128HIto64:
		case Iop_V128HIto64:
			dest->lo.v = arg.hi.v;
			break;

		case Iop_Not1:
			dest->lo.v = !arg.lo.v;
			break;

		case Iop_Not32:
			dest->lo.v = ~arg.lo.v & 0xffffffff;
			break;

		case Iop_Not64:
			dest->lo.v = ~arg.lo.v;
			break;
			
		case Iop_Clz64:
			dest->lo.v = 0;
			while (!(arg.lo.v & (1ul << (63 - dest->lo.v))) &&
			       dest->lo.v < 63)
				dest->lo.v++;
			break;

		case Iop_Ctz64:
			dest->lo.v = 0;
			while (!(arg.lo.v & (1ul << dest->lo.v)) &&
			       dest->lo.v < 63)
				dest->lo.v++;
			break;

		default:
			ppIRExpr(expr);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_Mux0X: {
		struct expression_result cond = eval_expression(expr->Iex.Mux0X.cond);
		struct expression_result res0 = eval_expression(expr->Iex.Mux0X.expr0);
		struct expression_result resX = eval_expression(expr->Iex.Mux0X.exprX);
		struct expression_result *choice;
		if (cond.lo.v == 0) {
			choice = &res0;
		} else {
			choice = &resX;
		}
		*dest = *choice;
		break;
	}

	case Iex_CCall: {
		res = do_ccall(expr->Iex.CCall.cee, expr->Iex.CCall.args);
		break;
	}

	default:
		ppIRExpr(expr);
		throw NotImplementedException("Bad expression tag %x\n", expr->tag);
	}

	return res;
}

static unsigned long
redirectGuest(unsigned long rip)
{
	/* XXX hideous hack of hideousness */
	if (rip == 0xFFFFFFFFFF600400ul)
		return 0x38017e0d;
	else if (rip == 0xFFFFFFFFFF600000)
		throw NotImplementedException();
	else
		return rip;
}

IRSB *instrument_func(void *closure,
		      IRSB *sb_in,
		      VexGuestLayout *layout,
		      VexGuestExtents *vge,
		      IRType gWordTy,
		      IRType hWordTy);

class AddressSpaceGuestFetcher : public GuestMemoryFetcher {
	AddressSpace *aspace;
	unsigned long offset;
public:
	virtual UChar operator[](unsigned long idx) const {
		UChar res;
		aspace->readMemory(idx + offset, 1, &res);
		return res;
	}
	AddressSpaceGuestFetcher(AddressSpace *_aspace,
				 unsigned long _offset) :
		aspace(_aspace),
		offset(_offset)
	{
	}
};

void Thread::translateNextBlock(AddressSpace *addrSpace)
{
	regs.regs.guest_RIP = redirectGuest(regs.regs.guest_RIP);

	vexSetAllocModeTEMP_and_clear();

	VexArchInfo archinfo_guest;
	VexAbiInfo abiinfo_both;
	VexGuestExtents vge;
	LibVEX_default_VexArchInfo(&archinfo_guest);
	archinfo_guest.hwcaps =
		VEX_HWCAPS_AMD64_SSE3|
		VEX_HWCAPS_AMD64_CX16;
	LibVEX_default_VexAbiInfo(&abiinfo_both);
	abiinfo_both.guest_stack_redzone_size = 128;
	abiinfo_both.guest_amd64_assume_fs_is_zero = 1;
	class AddressSpaceGuestFetcher fetcher(addrSpace, regs.rip());
	IRSB *irsb = bb_to_IR(&vge,
			      NULL, /* Context for chase_into_ok */
			      disInstr_AMD64,
			      fetcher,
			      (Addr64)regs.rip(),
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
		throw InstructionDecodeFailedException();

	irsb = instrument_func(NULL, irsb, NULL, NULL, Ity_I64, Ity_I64);

	temporaries.setSize(irsb->tyenv->types_used);

	currentIRSB = irsb;
	currentIRSBOffset = 0;
}

ThreadEvent *
Thread::runToEvent(struct AddressSpace *addrSpace)
{
	while (1) {
		if (!currentIRSB)
			translateNextBlock(addrSpace);
		if (!currentIRSB)
			return new SignalEvent(11, regs.regs.guest_RIP);
		while (currentIRSBOffset < currentIRSB->stmts_used) {
			IRStmt *stmt = currentIRSB->stmts[currentIRSBOffset];
			currentIRSBOffset++;

			switch (stmt->tag) {
			case Ist_NoOp:
				break;
			case Ist_IMark:
#define PASTE(x, y) x ## y
#define GR(x) *(unsigned long *)(&regs.regs. PASTE(guest_, x))
				return new InstructionEvent(regs.regs.guest_RIP,
							    GR(FOOTSTEP_REG_0_NAME),
							    GR(FOOTSTEP_REG_1_NAME),
							    ((unsigned long *)regs.regs.guest_XMM0)[1],
							    GR(FOOTSTEP_REG_3_NAME),
							    GR(FOOTSTEP_REG_4_NAME));
#undef GR
#undef PASTE
			case Ist_AbiHint:
				break;
			case Ist_MBE:
				break;
			case Ist_WrTmp:
				temporaries[stmt->Ist.WrTmp.tmp] =
					eval_expression(stmt->Ist.WrTmp.data);
				break;

			case Ist_Store: {
				assert(stmt->Ist.Store.end == Iend_LE);
				assert(stmt->Ist.Store.resSC == IRTemp_INVALID);
				struct expression_result data =
					eval_expression(stmt->Ist.Store.data);
				struct expression_result addr =
					eval_expression(stmt->Ist.Store.addr);
				unsigned size = sizeofIRType(typeOfIRExpr(currentIRSB->tyenv,
									  stmt->Ist.Store.data));
				unsigned char dbuf[16];
				memset(dbuf, 0, 16);
				if (size <= 8) {
					memcpy(dbuf, &data.lo.v, size);
				} else if (size <= 16) {
					memcpy(dbuf, &data.lo.v, 8);
					memcpy(dbuf + 8, &data.hi.v, size - 8);
				} else {
					ppIRStmt(stmt);
					throw NotImplementedException();
				}
				return new StoreEvent(addr.lo.v, size, dbuf);
			}

			case Ist_CAS: {
				assert(stmt->Ist.CAS.details->oldHi == IRTemp_INVALID);
				assert(stmt->Ist.CAS.details->expdHi == NULL);
				assert(stmt->Ist.CAS.details->dataHi == NULL);
				assert(stmt->Ist.CAS.details->end == Iend_LE);
				struct expression_result data =
					eval_expression(stmt->Ist.CAS.details->dataLo);
				struct expression_result addr =
					eval_expression(stmt->Ist.CAS.details->addr);
				struct expression_result expected =
					eval_expression(stmt->Ist.CAS.details->expdLo);
				unsigned size = sizeofIRType(typeOfIRExpr(currentIRSB->tyenv,
									  stmt->Ist.CAS.details->dataLo));
				return new CasEvent(stmt->Ist.CAS.details->oldLo, addr, data, expected, size);
			}

			case Ist_Put: {
				unsigned byte_offset = stmt->Ist.Put.offset & 7;
				unsigned long *dest =
					get_reg(this,
						stmt->Ist.Put.offset - byte_offset);
				struct expression_result data =
					eval_expression(stmt->Ist.Put.data);
				switch (typeOfIRExpr(currentIRSB->tyenv, stmt->Ist.Put.data)) {
				case Ity_I8:
					*dest &= ~(0xFF << (byte_offset * 8));
					*dest |= data.lo.v << (byte_offset * 8);
					break;

				case Ity_I16:
					assert(!(byte_offset % 2));
					*dest &= ~(0xFFFFul << (byte_offset * 8));
					*dest |= data.lo.v << (byte_offset * 8);
					break;

				case Ity_I32:
				case Ity_F32:
					assert(!(byte_offset % 4));
					*dest &= ~(0xFFFFFFFFul << (byte_offset * 8));
					*dest |= data.lo.v << (byte_offset * 8);
					break;

				case Ity_I64:
				case Ity_F64:
					assert(byte_offset == 0);
					*dest = data.lo.v;
					break;

				case Ity_I128:
				case Ity_V128:
					assert(byte_offset == 0);
					*dest = data.lo.v;
					*get_reg(this,
						 stmt->Ist.Put.offset + 8) =
						data.hi.v;
					break;
				default:
					ppIRStmt(stmt);
					throw NotImplementedException();
				}
				break;
			}

			case Ist_Dirty: {
				ThreadEvent *evt;
				evt = do_dirty_call(stmt->Ist.Dirty.details);
				if (evt)
					return evt;
				break;
			}

			case Ist_Exit: {
				if (stmt->Ist.Exit.guard) {
					struct expression_result guard =
						eval_expression(stmt->Ist.Exit.guard);
					if (!guard.lo.v)
						break;
				}
				if (stmt->Ist.Exit.jk != Ijk_Boring) {
					assert(stmt->Ist.Exit.jk == Ijk_EmWarn);
					printf("EMULATION WARNING %x\n",
					       regs.regs.guest_EMWARN);
				}
				assert(stmt->Ist.Exit.dst->tag == Ico_U64);
				regs.regs.guest_RIP = stmt->Ist.Exit.dst->Ico.U64;
				goto finished_block;
			}

			default:
				printf("Don't know how to interpret statement ");
				ppIRStmt(stmt);
				throw NotImplementedException();
			}
		}
		
		assert(currentIRSB->jumpkind == Ijk_Boring ||
		       currentIRSB->jumpkind == Ijk_Call ||
		       currentIRSB->jumpkind == Ijk_Ret ||
		       currentIRSB->jumpkind == Ijk_Sys_syscall);
		
		{
			struct expression_result next_addr =
				eval_expression(currentIRSB->next);
			regs.regs.guest_RIP = next_addr.lo.v;
		}
		if (currentIRSB->jumpkind == Ijk_Sys_syscall) {
			translateNextBlock(addrSpace);
			return new SyscallEvent();
		}

finished_block:
		translateNextBlock(addrSpace);
	}
}

void Interpreter::replayLogfile(LogReader const *lf, LogReader::ptr ptr)
{
	while (1) {
		LogRecord *lr = lf->read(ptr, &ptr);
		if (!lr)
			break;

		PointerKeeper<LogRecord> k_lr(lr);
		Thread *thr = currentState->findThread(lr->thread());
		VexGcRoot thread_keeper((void **)&thr);
		ThreadEvent *evt = thr->runToEvent(currentState->addressSpace);
		PointerKeeper<ThreadEvent> k_evt(evt);

#if 0
		printf("Event %s in thread %d\n",
		       evt->name(), lr->thread()._tid());
#endif

		/* CAS events are annoyingly special, because they can
		   generate multiple records in the logfile (one for
		   the load and one for the store). */
		CasEvent *ce = dynamic_cast<CasEvent *>(evt);
		if (ce) {
			ce->replay(thr, lr, currentState,
				   lf, ptr, &ptr);
		} else {
			evt->replay(thr, lr, currentState);
		}

		/* Memory records are special and should always be
		   processed eagerly. */
		process_memory_records(currentState->addressSpace, lf, ptr,
				       &ptr);

	}
}
