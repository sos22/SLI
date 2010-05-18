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

template<typename ait>
static void
write_reg(Thread<ait> *state, unsigned offset, ait val)
{
	assert(!(offset % 8));
	state->regs.set_reg(offset / 8, val);
}

template<typename ait>
static ait
read_reg(Thread<ait> *state, unsigned offset)
{
	assert(!(offset % 8));
	return state->regs.get_reg(offset / 8);
}

template<typename ait>
static void
amd64g_dirtyhelper_CPUID_sse3_and_cx16(RegisterSet<ait> *regs)
{
#define SET_ABCD(_a,_b,_c,_d)				\
	do {						\
		regs->set_reg(REGISTER_IDX(RAX), _a);	\
		regs->set_reg(REGISTER_IDX(RBX), _b);	\
		regs->set_reg(REGISTER_IDX(RCX), _c);	\
		regs->set_reg(REGISTER_IDX(RDX), _d);	\
	} while (0)

	switch (0xFFFFFFFF & regs->get_reg(REGISTER_IDX(RAX))) {
	case 0x00000000:
		SET_ABCD(0x0000000a, 0x756e6547, 0x6c65746e, 0x49656e69);
		break;
	case 0x00000001:
		SET_ABCD(0x000006f6, 0x00020800, 0x0000e3bd, 0xbfebfbff);
		break;
	case 0x00000002:
		SET_ABCD(0x05b0b101, 0x005657f0, 0x00000000, 0x2cb43049);
		break;
	case 0x00000003:
		SET_ABCD(0x00000000, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x00000004: {
		switch (0xFFFFFFFF & regs->get_reg(REGISTER_IDX(RCX))) {
		case 0x00000000: SET_ABCD(0x04000121, 0x01c0003f,
					  0x0000003f, 0x00000001); break;
		case 0x00000001: SET_ABCD(0x04000122, 0x01c0003f,
					  0x0000003f, 0x00000001); break;
		case 0x00000002: SET_ABCD(0x04004143, 0x03c0003f,
					  0x00000fff, 0x00000001); break;
		default:         SET_ABCD(0x00000000, 0x00000000,
					  0x00000000, 0x00000000); break;
		}
		break;
	}
	case 0x00000005:
		SET_ABCD(0x00000040, 0x00000040, 0x00000003, 0x00000020);
		break;
	case 0x00000006:
		SET_ABCD(0x00000001, 0x00000002, 0x00000001, 0x00000000);
		break;
	case 0x00000007:
		SET_ABCD(0x00000000, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x00000008:
		SET_ABCD(0x00000400, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x00000009:
		SET_ABCD(0x00000000, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x0000000a:
	unhandled_eax_value:
		SET_ABCD(0x07280202, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x80000000:
		SET_ABCD(0x80000008, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x80000001:
		SET_ABCD(0x00000000, 0x00000000, 0x00000001, 0x20100800);
		break;
	case 0x80000002:
		SET_ABCD(0x65746e49, 0x2952286c, 0x726f4320, 0x4d542865);
		break;
	case 0x80000003:
		SET_ABCD(0x43203229, 0x20205550, 0x20202020, 0x20202020);
		break;
	case 0x80000004:
		SET_ABCD(0x30303636, 0x20402020, 0x30342e32, 0x007a4847);
		break;
	case 0x80000005:
		SET_ABCD(0x00000000, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x80000006:
		SET_ABCD(0x00000000, 0x00000000, 0x10008040, 0x00000000);
		break;
	case 0x80000007:
		SET_ABCD(0x00000000, 0x00000000, 0x00000000, 0x00000000);
		break;
	case 0x80000008:
		SET_ABCD(0x00003024, 0x00000000, 0x00000000, 0x00000000);
		break;
	default:         
		goto unhandled_eax_value;
	}
#undef SET_ABCD
}

template<typename ait>
ThreadEvent<ait> *
Thread<ait>::do_dirty_call(IRDirty *details)
{
	struct expression_result<ait> args[6];
	unsigned x;

	if (details->guard) {
		expression_result<ait> guard = eval_expression(details->guard);
		if (!guard.lo)
			return NULL;
	}
	for (x = 0; details->args[x]; x++) {
		assert(x < 6);
		args[x] = eval_expression(details->args[x]);
	}
	assert(!details->cee->regparms);

	if (!strcmp(details->cee->name, "amd64g_dirtyhelper_RDTSC")) {
		return new RdtscEvent<ait>(details->tmp);
	} else if (!strcmp(details->cee->name, "helper_load_8")) {
		return new LoadEvent<ait>(details->tmp, args[0].lo, 1);
	} else if (!strcmp(details->cee->name, "helper_load_16")) {
		return new LoadEvent<ait>(details->tmp, args[0].lo, 2);
	} else if (!strcmp(details->cee->name, "helper_load_32")) {
		return new LoadEvent<ait>(details->tmp, args[0].lo, 4);
	} else if (!strcmp(details->cee->name, "helper_load_64")) {
		return new LoadEvent<ait>(details->tmp, args[0].lo, 8);
	} else if (!strcmp(details->cee->name, "helper_load_128")) {
		return new LoadEvent<ait>(details->tmp, args[0].lo, 16);
	} else if (!strcmp(details->cee->name, "amd64g_dirtyhelper_CPUID_sse3_and_cx16")) {
		amd64g_dirtyhelper_CPUID_sse3_and_cx16(&regs);
		return NULL;
	} else {
		throw NotImplementedException("Unknown dirty call %s\n", details->cee->name);
	}
}

template<typename ait>
static void
calculate_condition_flags_XXX(ait op,
			      ait dep1,
			      ait dep2,
			      ait ndep,
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

template<typename ait>
expression_result<ait>
Thread<ait>::do_ccall_calculate_condition(struct expression_result<ait> *args)
{
	struct expression_result<ait> condcode = args[0];
	struct expression_result<ait> op       = args[1];
	struct expression_result<ait> dep1     = args[2];
	struct expression_result<ait> dep2     = args[3];
	struct expression_result<ait> ndep     = args[4];
	struct expression_result<ait> res;
	int inv;
	unsigned cf, zf, sf, of;

	calculate_condition_flags_XXX<ait>(op.lo,
					   dep1.lo,
					   dep2.lo,
					   ndep.lo,
					   cf,
					   zf,
					   sf,
					   of);

	inv = condcode.lo & 1;
	switch (condcode.lo & ~1) {
	case AMD64CondZ:
		res.lo = zf;
		break;
	case AMD64CondL:
		res.lo = sf ^ of;
		break;
	case AMD64CondLE:
		res.lo = (sf ^ of) | zf;
		break;
	case AMD64CondB:
		res.lo = cf;
		break;
	case AMD64CondBE:
		res.lo = cf | zf;
		break;
	case AMD64CondS:
		res.lo = sf;
		break;

	default:
		throw NotImplementedException("Strange cond code %ld (op %ld)\n", condcode.lo, op.lo);
	}

	if (inv)
		res.lo ^= 1;

	return res;
}

template<typename ait>
expression_result<ait>
Thread<ait>::do_ccall_calculate_rflags_c(expression_result<ait> *args)
{
	struct expression_result<ait> op   = args[0];
	struct expression_result<ait> dep1 = args[1];
	struct expression_result<ait> dep2 = args[2];
	struct expression_result<ait> ndep = args[3];
	struct expression_result<ait> res;
	unsigned cf, zf, sf, of;

	calculate_condition_flags_XXX(op.lo,
				      dep1.lo,
				      dep2.lo,
				      ndep.lo,
				      cf,
				      zf,
				      sf,
				      of);

	res.lo = cf;
	return res;
}

template<typename ait>
expression_result<ait>
Thread<ait>::do_ccall_generic(IRCallee *cee,
			      struct expression_result<ait> *rargs)
{
	struct expression_result<ait> res;

	res.lo = ((unsigned long (*)(unsigned long, unsigned long, unsigned long,
				       unsigned long, unsigned long, unsigned long))cee->addr)
		(rargs[0].lo, rargs[1].lo, rargs[2].lo, rargs[3].lo, rargs[4].lo,
		 rargs[5].lo);
	res.hi = 0;
	return res;
}

template<typename ait>
expression_result<ait>
Thread<ait>::do_ccall(IRCallee *cee,
		      IRExpr **args)
{
	struct expression_result<ait> rargs[6];
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
		if (strcmp(cee->name, "amd64g_calculate_rflags_all"))
			printf("Unknown clean call %s\n", cee->name);
		return do_ccall_generic(cee, rargs);
	}
}

/* Borrowed from gnucash */
template <typename ait>
static void
mulls64(struct expression_result<ait> *dest, const struct expression_result<ait> &src1,
	const struct expression_result<ait> &src2)
{
	bool isneg = false;
	ait a = src1.lo;
	ait b = src2.lo;
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
 
	dest->lo = d0 + (sum << 32);
	dest->hi = carry + e1 + f1 + g0 + (g1 << 32);
	if (isneg) {
		dest->lo = ~dest->lo;
		dest->hi = ~dest->hi;
		dest->lo++;
		if (dest->lo == 0)
			dest->hi++;
	}
}

template<typename ait>
expression_result<ait>
Thread<ait>::eval_expression(IRExpr *expr)
{
	struct expression_result<ait> res;
	struct expression_result<ait> *dest = &res;
	dest->lo = 0xdeadbeeff001f001;
	dest->hi = 0xaaaaaaaaaaaaaaaa;

	switch (expr->tag) {
	case Iex_Get: {
		unsigned long v1;
		unsigned sub_word_offset = expr->Iex.Get.offset & 7;
		v1 = read_reg(this,
			      expr->Iex.Get.offset - sub_word_offset);
		switch (expr->Iex.Get.ty) {
		case Ity_I64:
		case Ity_F64:
			assert(!sub_word_offset);
			dest->lo = v1;
			break;
		case Ity_V128:
			assert(!sub_word_offset);
			dest->lo = v1;
			dest->hi = read_reg(this,
					      expr->Iex.Get.offset - sub_word_offset + 8);
			break;
		case Ity_I32:
		case Ity_F32:
			assert(!(sub_word_offset % 4));
			dest->lo = (v1 >> (sub_word_offset * 8)) & 0xffffffff;
			break;
		case Ity_I16:
			assert(!(sub_word_offset % 2));
			dest->lo = (v1 >> (sub_word_offset * 8)) & 0xffff;
			break;
		case Ity_I8:
			dest->lo = (v1 >> (sub_word_offset * 8)) & 0xff;
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
			dest->lo = cnst->Ico.U1;
			break;
		case Ico_U8:
			dest->lo = cnst->Ico.U8;
			break;
		case Ico_U16:
			dest->lo = cnst->Ico.U16;
			break;
		case Ico_U32:
			dest->lo = cnst->Ico.U32;
			break;
		case Ico_U64:
		case Ico_F64:
		case Ico_F64i:
			dest->lo = cnst->Ico.U64;
			break;
		case Ico_V128:
			dest->lo = cnst->Ico.V128;
			dest->lo = dest->lo | (dest->lo << 16) | (dest->lo << 32) | (dest->lo << 48);
			dest->hi = dest->lo;
			break;
		default:
			ppIRExpr(expr);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_Binop: {
		struct expression_result<ait> arg1 = eval_expression(expr->Iex.Binop.arg1);
		struct expression_result<ait> arg2 = eval_expression(expr->Iex.Binop.arg2);
		switch (expr->Iex.Binop.op) {
		case Iop_Sub8:
		case Iop_Sub16:
		case Iop_Sub32:
		case Iop_Sub64:
			dest->lo = arg1.lo - arg2.lo;
			break;
		case Iop_Add8:
		case Iop_Add16:
		case Iop_Add32:
		case Iop_Add64:
			dest->lo = arg1.lo + arg2.lo;
			break;
		case Iop_Add64x2:
			dest->lo = arg1.lo + arg2.lo;
			dest->hi = arg1.hi + arg2.hi;
			break;
		case Iop_And64:
		case Iop_And32:
		case Iop_And16:
		case Iop_And8:
			dest->lo = arg1.lo & arg2.lo;
			break;
		case Iop_Or8:
		case Iop_Or16:
		case Iop_Or32:
		case Iop_Or64:
			dest->lo = arg1.lo | arg2.lo;
			break;
		case Iop_Shl32:
		case Iop_Shl64:
			dest->lo = arg1.lo << arg2.lo;
			break;
		case Iop_Sar64:
			dest->lo = (long)arg1.lo >> arg2.lo;
			break;
		case Iop_Shr32:
		case Iop_Shr64:
			dest->lo = arg1.lo >> arg2.lo;
			break;
		case Iop_XorV128:
		case Iop_Xor64:
		case Iop_Xor32:
		case Iop_Xor16:
		case Iop_Xor8:
			dest->lo = arg1.lo ^ arg2.lo;
			dest->hi = arg1.hi ^ arg2.hi;
			break;
		case Iop_CmpNE8:
			dest->lo = arg1.lo != arg2.lo;
			break;
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			dest->lo = arg1.lo == arg2.lo;
			break;
		case Iop_CmpNE32:
		case Iop_CasCmpNE32:
		case Iop_CmpNE64:
			dest->lo = arg1.lo != arg2.lo;
			break;
		case Iop_CmpLE64U:
			dest->lo = arg1.lo <= arg2.lo;
			break;
		case Iop_CmpLE64S:
			dest->lo = (long)arg1.lo <= (long)arg2.lo;
			break;
		case Iop_CmpLT64S:
			dest->lo = (long)arg1.lo < (long)arg2.lo;
			break;
		case Iop_CmpLT64U:
			dest->lo = arg1.lo < arg2.lo;
			break;
		case Iop_Mul64:
		case Iop_Mul32:
			dest->lo = arg1.lo * arg2.lo;
			break;

		case Iop_MullU32: {
			dest->lo = arg1.lo * arg2.lo;
			break;
		}
		case Iop_MullS32: {
			dest->lo = (long)(int)arg1.lo * (long)(int)arg2.lo;
			break;
		}

		case Iop_MullS64:
			mulls64(dest, arg1, arg2);
			break;

		case Iop_MullU64: {
			unsigned long a1, a2, b1, b2;
			dest->lo = arg1.lo * arg2.lo;
			a1 = arg1.lo & 0xffffffff;
			a2 = arg1.lo >> 32;
			b1 = arg2.lo & 0xffffffff;
			b2 = arg2.lo >> 32;
			dest->hi = a2 * b2 +
				( (a1 * b2 + a2 * b1 +
				   ((a1 * b1) >> 32)) >> 32);
			break;
		}
		case Iop_32HLto64:
			dest->lo = (arg1.lo << 32) | arg2.lo;
			break;

		case Iop_64HLtoV128:
		case Iop_64HLto128:
			dest->lo = arg2.lo;
			dest->hi = arg1.lo;
			break;

		case Iop_DivModU64to32:
			dest->lo = (arg1.lo / arg2.lo) |
				((arg1.lo % arg2.lo) << 32);
			break;

		case Iop_DivModS64to32: {
			long a1 = arg1.lo;
			long a2 = arg2.lo;
			dest->lo = ((a1 / a2) & 0xffffffff) |
				((a1 % a2) << 32);
			break;
		}

		case Iop_DivModU128to64:
			/* arg1 is a I128, arg2 is an I64, result is
			   128 bits and has the dividend in its low 64
			   bits and the modulus in its high 64
			   bits. */
			asm ("div %4\n"
			     : "=a" (dest->lo), "=d" (dest->hi)
			     : "0" (arg1.lo), "1" (arg1.hi), "r" (arg2.lo));
			break;

		case Iop_DivModS128to64:
			asm ("idiv %4\n"
			     : "=a" (dest->lo), "=d" (dest->hi)
			     : "0" (arg1.lo), "1" (arg1.hi), "r" (arg2.lo));
			break;

		case Iop_Add32x4:
			dest->lo = ((arg1.lo + arg2.lo) & 0xffffffff) +
				((arg1.lo & ~0xfffffffful) + (arg2.lo & ~0xfffffffful));
			dest->hi = ((arg1.hi + arg2.hi) & 0xffffffff) +
				((arg1.hi & ~0xfffffffful) + (arg2.hi & ~0xfffffffful));
			break;

		case Iop_InterleaveLO64x2:
			dest->lo = arg2.lo;
			dest->hi = arg1.lo;
			break;

		case Iop_InterleaveHI64x2:
			dest->lo = arg2.hi;
			dest->hi = arg1.hi;
			break;

		case Iop_InterleaveLO32x4:
			dest->lo = (arg2.lo & 0xffffffff) | (arg1.lo << 32);
			dest->hi = (arg2.lo >> 32) | (arg1.lo & 0xffffffff00000000ul);
			break;

		case Iop_InterleaveHI32x4:
			dest->lo = (arg2.hi & 0xffffffff) | (arg1.hi << 32);
			dest->hi = (arg2.hi >> 32) | (arg1.hi & 0xffffffff00000000ul);
			break;

		case Iop_ShrN64x2:
			dest->lo = arg1.lo >> arg2.lo;
			dest->hi = arg1.hi >> arg2.lo;
			break;

		case Iop_ShlN64x2:
			dest->lo = arg1.lo << arg2.lo;
			dest->hi = arg1.hi << arg2.lo;
			break;

		case Iop_CmpGT32Sx4:
			dest->lo = 0;
			dest->hi = 0;
			if ( (int)arg1.lo > (int)arg2.lo )
				dest->lo |= 0xffffffff;
			if ( (int)(arg1.lo >> 32) > (int)(arg2.lo >> 32) )
				dest->lo |= 0xffffffff00000000;
			if ( (int)arg1.hi > (int)arg2.hi )
				dest->hi |= 0xffffffff;
			if ( (int)(arg1.hi >> 32) > (int)(arg2.hi >> 32) )
				dest->hi |= 0xffffffff00000000;
			break;
			
		case Iop_I64toF64: {
			switch (arg1.lo) {
			case 0:
				/* Round to nearest even mode. */
				*(double *)&dest->lo = arg2.lo;
				break;
			default:
				throw NotImplementedException("unknown rounding mode %ld\n",
							      arg1.lo);
			}
			break;
		}

		case Iop_F64toI32: {
			switch (arg1.lo) {
			case 3:
				dest->lo = (unsigned)*(double *)&arg2.lo;
				break;
			default:
				throw NotImplementedException("unknown rounding mode %ld\n",
							      arg1.lo);
			}
			break;
		}

		case Iop_CmpF64: {
			double a1 = *(double *)&arg1.lo;
			double a2 = *(double *)&arg2.lo;
			if (a1 < a2)
				dest->lo = 1;
			else if (a1 == a2)
				dest->lo = 0x40;
			else if (a1 > a2)
				dest->lo = 0;
			else
				dest->lo = 0x45;
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
			dest->lo &= 1;
			dest->hi = 0;
			break;
		case Ity_I8:
			dest->lo &= 0xff;
			dest->hi = 0;
			break;
		case Ity_I16:
			dest->lo &= 0xffff;
			dest->hi = 0;
			break;
		case Ity_I32:
			dest->lo &= 0xffffffff;
			dest->hi = 0;
			break;
		case Ity_I64:
			dest->hi = 0;
			break;

			/* Floating types follow the same rule as the
			   integer ones (unused bits must be zero),
			   but it's not safe to enforce it with a
			   simple mask, so assert that it's already
			   true. */
		case Ity_F32:
			assert(!(dest->lo & ~0xfffffffful));
		case Ity_F64:
			assert(dest->hi == 0);
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
		struct expression_result<ait> arg = eval_expression(expr->Iex.Unop.arg);
		switch (expr->Iex.Unop.op) {
		case Iop_64HIto32:
			dest->lo = arg.lo >> 32;
			break;
		case Iop_64to32:
			dest->lo = arg.lo & 0xffffffff;
			break;
		case Iop_64to16:
			dest->lo = arg.lo & 0xffff;
			break;
		case Iop_64to8:
			dest->lo = arg.lo & 0xff;
			break;
		case Iop_128to64:
		case Iop_V128to64:
			dest->lo = arg.lo;
			break;
		case Iop_64UtoV128:
			dest->lo = arg.lo;
			dest->hi = 0;
			break;
		case Iop_64to1:
			dest->lo = arg.lo & 1;
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
			dest->lo = (long)(int)arg.lo;
			break;
		case Iop_8Sto64:
			dest->lo = (long)(signed char)arg.lo;
			break;
		case Iop_16Sto32:
			dest->lo = (unsigned)(signed short)arg.lo;
			break;
		case Iop_8Sto32:
			dest->lo = (unsigned)(signed char)arg.lo;
			break;
		case Iop_16Sto64:
			dest->lo = (long)(short)arg.lo;
			break;
		case Iop_128HIto64:
		case Iop_V128HIto64:
			dest->lo = arg.hi;
			break;

		case Iop_Not1:
			dest->lo = !arg.lo;
			break;

		case Iop_Not32:
			dest->lo = ~arg.lo & 0xffffffff;
			break;

		case Iop_Not64:
			dest->lo = ~arg.lo;
			break;
			
		case Iop_Clz64:
			dest->lo = 0;
			while (!(arg.lo & (1ul << (63 - dest->lo))) &&
			       dest->lo < 63)
				dest->lo++;
			break;

		case Iop_Ctz64:
			dest->lo = 0;
			while (!(arg.lo & (1ul << dest->lo)) &&
			       dest->lo < 63)
				dest->lo++;
			break;

		default:
			ppIRExpr(expr);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_Mux0X: {
		struct expression_result<ait> cond = eval_expression(expr->Iex.Mux0X.cond);
		struct expression_result<ait> res0 = eval_expression(expr->Iex.Mux0X.expr0);
		struct expression_result<ait> resX = eval_expression(expr->Iex.Mux0X.exprX);
		if (cond.lo == 0) {
			*dest = res0;
		} else {
			*dest = resX;
		}
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

template<typename ait>
void Thread<ait>::translateNextBlock(AddressSpace *addrSpace)
{
	regs.set_reg(REGISTER_IDX(RIP), redirectGuest(regs.rip()));

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

template<typename ait>
ThreadEvent<ait> *
Thread<ait>::runToEvent(struct AddressSpace *addrSpace)
{
	while (1) {
		if (!currentIRSB) {
			try {
				translateNextBlock(addrSpace);
			} catch (BadMemoryException excn) {
				return new SignalEvent<ait>(11, excn.ptr);
			}
			assert(currentIRSB);
		}
		while (currentIRSBOffset < currentIRSB->stmts_used) {
			IRStmt *stmt = currentIRSB->stmts[currentIRSBOffset];
			currentIRSBOffset++;

			switch (stmt->tag) {
			case Ist_NoOp:
				break;
			case Ist_IMark:
#define GR(x) regs.get_reg(REGISTER_IDX(x))
				return new InstructionEvent<ait>(regs.rip(),
								 GR(FOOTSTEP_REG_0_NAME),
								 GR(FOOTSTEP_REG_1_NAME),
								 regs.get_reg(REGISTER_IDX(XMM0) + 1),
								 GR(FOOTSTEP_REG_3_NAME),
								 GR(FOOTSTEP_REG_4_NAME));
#undef GR
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
				struct expression_result<ait> data =
					eval_expression(stmt->Ist.Store.data);
				struct expression_result<ait> addr =
					eval_expression(stmt->Ist.Store.addr);
				unsigned size = sizeofIRType(typeOfIRExpr(currentIRSB->tyenv,
									  stmt->Ist.Store.data));
				unsigned char dbuf[16];
				memset(dbuf, 0, 16);
				if (size <= 8) {
					memcpy(dbuf, &data.lo, size);
				} else if (size <= 16) {
					memcpy(dbuf, &data.lo, 8);
					memcpy(dbuf + 8, &data.hi, size - 8);
				} else {
					ppIRStmt(stmt);
					throw NotImplementedException();
				}
				return new StoreEvent<ait>(addr.lo, size, dbuf);
			}

			case Ist_CAS: {
				assert(stmt->Ist.CAS.details->oldHi == IRTemp_INVALID);
				assert(stmt->Ist.CAS.details->expdHi == NULL);
				assert(stmt->Ist.CAS.details->dataHi == NULL);
				assert(stmt->Ist.CAS.details->end == Iend_LE);
				struct expression_result<ait> data =
					eval_expression(stmt->Ist.CAS.details->dataLo);
				struct expression_result<ait> addr =
					eval_expression(stmt->Ist.CAS.details->addr);
				struct expression_result<ait> expected =
					eval_expression(stmt->Ist.CAS.details->expdLo);
				unsigned size = sizeofIRType(typeOfIRExpr(currentIRSB->tyenv,
									  stmt->Ist.CAS.details->dataLo));
				return new CasEvent<ait>(stmt->Ist.CAS.details->oldLo, addr, data, expected, size);
			}

			case Ist_Put: {
				unsigned byte_offset = stmt->Ist.Put.offset & 7;
				unsigned long dest =
					read_reg(this,
						 stmt->Ist.Put.offset - byte_offset);
				struct expression_result<ait> data =
					eval_expression(stmt->Ist.Put.data);
				switch (typeOfIRExpr(currentIRSB->tyenv, stmt->Ist.Put.data)) {
				case Ity_I8:
					dest &= ~(0xFF << (byte_offset * 8));
					dest |= data.lo << (byte_offset * 8);
					break;

				case Ity_I16:
					assert(!(byte_offset % 2));
					dest &= ~(0xFFFFul << (byte_offset * 8));
					dest |= data.lo << (byte_offset * 8);
					break;

				case Ity_I32:
				case Ity_F32:
					assert(!(byte_offset % 4));
					dest &= ~(0xFFFFFFFFul << (byte_offset * 8));
					dest |= data.lo << (byte_offset * 8);
					break;

				case Ity_I64:
				case Ity_F64:
					assert(byte_offset == 0);
					dest = data.lo;
					break;

				case Ity_I128:
				case Ity_V128:
					assert(byte_offset == 0);
					dest = data.lo;
					write_reg(this,
						  stmt->Ist.Put.offset + 8,
						  data.hi);
					break;
				default:
					ppIRStmt(stmt);
					throw NotImplementedException();
				}

				write_reg(this, stmt->Ist.Put.offset - byte_offset, dest);
				break;
			}

			case Ist_Dirty: {
				ThreadEvent<ait> *evt = do_dirty_call(stmt->Ist.Dirty.details);
				if (evt)
					return evt;
				break;
			}

			case Ist_Exit: {
				if (stmt->Ist.Exit.guard) {
					struct expression_result<ait> guard =
						eval_expression(stmt->Ist.Exit.guard);
					if (!guard.lo)
						break;
				}
				if (stmt->Ist.Exit.jk != Ijk_Boring) {
					assert(stmt->Ist.Exit.jk == Ijk_EmWarn);
					printf("EMULATION WARNING %lx\n",
					       regs.get_reg(REGISTER_IDX(EMWARN)));
				}
				assert(stmt->Ist.Exit.dst->tag == Ico_U64);
				regs.set_reg(REGISTER_IDX(RIP), stmt->Ist.Exit.dst->Ico.U64);
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
			struct expression_result<ait> next_addr =
				eval_expression(currentIRSB->next);
			regs.set_reg(REGISTER_IDX(RIP), next_addr.lo);
		}
		if (currentIRSB->jumpkind == Ijk_Sys_syscall) {
			currentIRSB = NULL;
			return new SyscallEvent<ait>();
		}

finished_block:
		currentIRSB = NULL;
	}
}

template<typename ait>
InterpretResult Interpreter<ait>::getThreadMemoryTrace(ThreadId tid, MemoryTrace **output, unsigned max_events)
{
	MemoryTrace *work = new MemoryTrace();
	*output = work;
	Thread<ait> *thr = currentState->findThread(tid);
	if (thr->cannot_make_progress)
		return InterpretResultIncomplete;
	while (max_events) {
		ThreadEvent<ait> *evt = thr->runToEvent(currentState->addressSpace);
		PointerKeeper<ThreadEvent<ait> > k_evt(evt);

		InterpretResult res = evt->fake(thr, currentState);
		if (res != InterpretResultContinue) {
			return res;
		}
		if (LoadEvent<ait> *lr = dynamic_cast<LoadEvent <ait> * > (evt)) {
		        work->push_back(new MemoryAccessLoad(tid, *lr));
	        } else if (StoreEvent<ait> *sr = dynamic_cast<StoreEvent<ait> *>(evt)) {
			work->push_back(new MemoryAccessStore(tid, *sr));
		}
		max_events--;
	}
	return InterpretResultTimedOut;
}

template<typename ait>
void Interpreter<ait>::runToAccessLoggingEvents(ThreadId tid, unsigned nr_accesses,
						LogWriter *output)
{
        Thread<ait> *thr = currentState->findThread(tid);
        while (1) {
                ThreadEvent<ait> *evt = thr->runToEvent(currentState->addressSpace);
                PointerKeeper<ThreadEvent<ait> > k_evt(evt);
                InterpretResult res = output->recordEvent(thr, currentState, evt);
		if (dynamic_cast<LoadEvent<ait> *>(evt) ||
		    dynamic_cast<StoreEvent<ait> *>(evt)) {
			nr_accesses--;
			if (nr_accesses == 0)
				return;
		}

		/* Caller should have made sure that we can actually
		   make progress. */
		assert(res == InterpretResultContinue);
	}
}

template<typename ait>
void Interpreter<ait>::runToFailure(ThreadId tid, LogWriter *output, unsigned max_events)
{
	bool have_event_limit = max_events != 0;
	Thread<ait> *thr = currentState->findThread(tid);
	while (!have_event_limit || max_events) {
		ThreadEvent<ait> *evt = thr->runToEvent(currentState->addressSpace);
		PointerKeeper<ThreadEvent<ait> > k_evt(evt);
		InterpretResult res = output->recordEvent(thr, currentState, evt);
		if (res != InterpretResultContinue) {
			thr->cannot_make_progress = true;
			return;
		}
		max_events--;
	}
}

template<typename ait>
void Interpreter<ait>::replayLogfile(LogReader const *lf, LogReader::ptr ptr,
				     LogReader::ptr *eof, LogWriter *lw)
{
	while (1) {
		LogRecord *lr = lf->read(ptr, &ptr);
		if (!lr)
			break;

		if (lw)
			lw->append(*lr);
		PointerKeeper<LogRecord> k_lr(lr);
		Thread<ait> *thr = currentState->findThread(lr->thread());
		ThreadEvent<ait> *evt = thr->runToEvent(currentState->addressSpace);
		PointerKeeper<ThreadEvent<ait> > k_evt(evt);

#if 0
		printf("Event %s in thread %d\n",
		       evt->name(), lr->thread()._tid());
#endif

		/* CAS events are annoyingly special, because they can
		   generate multiple records in the logfile (one for
		   the load and one for the store). */
		CasEvent<ait> *ce = dynamic_cast<CasEvent<ait> *>(evt);
		if (ce) {
			ce->replay(thr, lr, currentState,
				   lf, ptr, &ptr, lw);
		} else {
			evt->replay(thr, lr, currentState);
		}

		/* Memory records are special and should always be
		   processed eagerly. */
		process_memory_records(currentState->addressSpace, lf, ptr,
				       &ptr, lw);
	}
	if (eof)
		*eof = ptr;
}

#define MK_INTERPRETER(t)						\
	template ThreadEvent<t> *Thread<t>::runToEvent(AddressSpace *addrSpace); \
	template void Interpreter<t>::runToFailure(ThreadId tid,	\
						   LogWriter *output,	\
						   unsigned max_events); \
	template void Interpreter<t>::runToAccessLoggingEvents(ThreadId tid, \
							       unsigned nr_accesses, \
							       LogWriter *output); \
	template void Interpreter<t>::replayLogfile(LogReader const *lf, \
						    LogReader::ptr ptr,	\
						    LogReader::ptr *eof, \
						    LogWriter *lw);	\
	template InterpretResult Interpreter<t>::getThreadMemoryTrace(ThreadId tid, \
								      MemoryTrace **output, \
								      unsigned max_events)


