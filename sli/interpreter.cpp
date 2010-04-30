#include <math.h>
#include <string.h>

extern "C" {
#include "libvex.h"
#include "libvex_ir.h"
#include "libvex_emwarn.h"
#include "libvex_guest_amd64.h"
#include "guest_generic_bb_to_IR.h"
#include "guest_amd64_defs.h"

#undef NULL /* main_util redefines NULL, for some reason */
#include "main_util.h"
};

#define FOOTSTEP_REGS_ONLY
#include "ppres.h"

#include "sli.h"

static void eval_expression(struct expression_result *temporaries,
			    AddressSpace *addrSpace,
			    Thread *thr,
			    struct expression_result *dest,
			    IRExpr *expr);

static Bool chase_into_ok(void *ignore1, Addr64 ignore2)
{
	return False;
}

struct abstract_interpret_value {
	unsigned long v;
	abstract_interpret_value() : v(0) {}
};

struct expression_result {
	struct abstract_interpret_value lo;
	struct abstract_interpret_value hi;
};

#define REG_LAST 128

#define tl_assert(x) assert(x)
#define ASSUME assert

static unsigned long *
get_reg(Thread *state, unsigned offset)
{
	tl_assert(!(offset % 8));
	tl_assert(offset < sizeof(state->regs.regs));
	return &((unsigned long *)&state->regs.regs)[offset/8];
}

static const struct expression *
read_reg(Thread *state, unsigned offset, unsigned long *v)
{
	*v = *get_reg(state, offset);
	return NULL;
}

static unsigned long
do_dirtyhelper_rdtsc(const LogReader *lf, LogReader::ptr startOffset, LogReader::ptr *endOffset)
{
	LogRecord *lr = lf->read(startOffset, endOffset);
	LogRecordRdtsc *lrr = dynamic_cast<LogRecordRdtsc *>(lr);
	assert(lrr);
	return lrr->tsc;
}

static void
do_dirty_call(struct expression_result *temporaries,
	      AddressSpace *addressSpace,
	      Thread *thr,
	      IRSB *irsb,
	      IRDirty *details,
	      const LogReader *logfile,
	      LogReader::ptr logfilePtr,
	      LogReader::ptr *logfilePtrOut)
{
	struct expression_result guard;
	struct expression_result args[6];
	unsigned x;
	unsigned long res;

	if (details->guard) {
		eval_expression(temporaries, addressSpace, thr, &guard, details->guard);
		if (!guard.lo.v)
			return;
	}
	for (x = 0; details->args[x]; x++) {
		tl_assert(x < 6);
		eval_expression(temporaries, addressSpace, thr, &args[x], details->args[x]);
	}
	tl_assert(!details->cee->regparms);

	if (!strcmp(details->cee->name, "amd64g_dirtyhelper_RDTSC")) {
		temporaries[details->tmp].lo.v =
			do_dirtyhelper_rdtsc(logfile, logfilePtr, logfilePtrOut);
	} else {
		printf("Unknown dirty call %s\n", details->cee->name);
		if (details->needsBBP) {
			res = ((unsigned long (*)(VexGuestAMD64State *,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long,
						  unsigned long))(details->cee->addr))
				(&thr->regs.regs, args[0].lo.v, args[1].lo.v, args[2].lo.v, args[3].lo.v,
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
		printf("Strange operation code %ld\n", op);
		abort();
	}

	of &= 1;
	sf &= 1;
	zf &= 1;
	cf &= 1;
}

static void
do_ccall_calculate_condition(struct expression_result *temporaries,
			     AddressSpace *addrSpace,
			     Thread *thr,
			     struct expression_result *dest,
			     IRType retty,
			     IRExpr **args)
{
	struct expression_result condcode = {};
	struct expression_result op = {};
	struct expression_result dep1 = {};
	struct expression_result dep2 = {};
	struct expression_result ndep = {};
	int inv;
	unsigned cf, zf, sf, of;

	eval_expression(temporaries, addrSpace, thr, &condcode, args[0]);
	eval_expression(temporaries, addrSpace, thr, &op, args[1]);
	eval_expression(temporaries, addrSpace, thr, &dep1, args[2]);
	eval_expression(temporaries, addrSpace, thr, &dep2, args[3]);
	eval_expression(temporaries, addrSpace, thr, &ndep, args[4]);

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
		dest->lo.v = zf;
		break;
	case AMD64CondL:
		dest->lo.v = sf ^ of;
		break;
	case AMD64CondLE:
		dest->lo.v = (sf ^ of) | zf;
		break;
	case AMD64CondB:
		dest->lo.v = cf;
		break;
	case AMD64CondBE:
		dest->lo.v = cf | zf;
		break;
	case AMD64CondS:
		dest->lo.v = sf;
		break;

	default:
		printf("Strange cond code %ld (op %ld)\n", condcode.lo.v, op.lo.v);
		abort();
	}

	if (inv)
		dest->lo.v ^= 1;
}

static void
do_ccall_calculate_rflags_c(struct expression_result *temporaries,
			    AddressSpace *addrSpace,
			    Thread *thr,
			    struct expression_result *dest,
			    IRType retty,
			    IRExpr **args)
{
	struct expression_result op = {};
	struct expression_result dep1 = {};
	struct expression_result dep2 = {};
	struct expression_result ndep = {};
	unsigned cf, zf, sf, of;

	eval_expression(temporaries, addrSpace, thr, &op, args[0]);
	eval_expression(temporaries, addrSpace, thr, &dep1, args[1]);
	eval_expression(temporaries, addrSpace, thr, &dep2, args[2]);
	eval_expression(temporaries, addrSpace, thr, &ndep, args[3]);

	calculate_condition_flags_XXX(op.lo.v,
				      dep1.lo.v,
				      dep2.lo.v,
				      ndep.lo.v,
				      cf,
				      zf,
				      sf,
				      of);

	dest->lo.v = cf;
}

static void
do_ccall_generic(struct expression_result *temporaries,
		 AddressSpace *addrSpace,
		 Thread *thr,
		 struct expression_result *dest,
		 IRCallee *cee,
		 IRType retty,
		 IRExpr **args)
{
	struct expression_result rargs[6];
	unsigned x;

	tl_assert(cee->regparms == 0);
	for (x = 0; args[x]; x++) {
		tl_assert(x < 6);
		eval_expression(temporaries, addrSpace, thr, &rargs[x], args[x]);
	}
	dest->lo.v = ((unsigned long (*)(unsigned long, unsigned long, unsigned long,
				       unsigned long, unsigned long, unsigned long))cee->addr)
		(rargs[0].lo.v, rargs[1].lo.v, rargs[2].lo.v, rargs[3].lo.v, rargs[4].lo.v,
		 rargs[5].lo.v);
	dest->hi.v = 0;
}

static void
do_ccall(struct expression_result *temporaries,
	 AddressSpace *addrSpace,
	 Thread *thr,
	 struct expression_result *dest,
	 IRCallee *cee,
	 IRType retty,
	 IRExpr **args)
{
	if (!strcmp(cee->name, "amd64g_calculate_condition")) {
		do_ccall_calculate_condition(temporaries, addrSpace, thr, dest, retty, args);
	} else if (!strcmp(cee->name, "amd64g_calculate_rflags_c")) {
		do_ccall_calculate_rflags_c(temporaries, addrSpace, thr, dest, retty, args);
	} else {
		printf("Unknown clean call %s\n", cee->name);
		do_ccall_generic(temporaries, addrSpace, thr, dest, cee, retty, args);
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

static void
eval_expression(struct expression_result *temporaries,
		AddressSpace *addrSpace,
		Thread *thr,
		struct expression_result *dest,
		IRExpr *expr)
{
	dest->lo.v = 0xdeadbeeff001f001;
	dest->hi.v = 0xaaaaaaaaaaaaaaaa;

	switch (expr->tag) {
	case Iex_Get: {
		unsigned long v1;
		const struct expression *src1;
		unsigned sub_word_offset = expr->Iex.Get.offset & 7;
		src1 = read_reg(thr,
				expr->Iex.Get.offset - sub_word_offset,
				&v1);
		switch (expr->Iex.Get.ty) {
		case Ity_I64:
		case Ity_F64:
			tl_assert(!sub_word_offset);
			dest->lo.v = v1;
			break;
		case Ity_V128:
			tl_assert(!sub_word_offset);
			dest->lo.v = v1;
			read_reg(thr,
				 expr->Iex.Get.offset - sub_word_offset + 8,
				 &dest->hi.v);
			break;
		case Ity_I32:
		case Ity_F32:
			tl_assert(!(sub_word_offset % 4));
			dest->lo.v = (v1 >> (sub_word_offset * 8)) & 0xffffffff;
			break;
		case Ity_I16:
			tl_assert(!(sub_word_offset % 2));
			dest->lo.v = (v1 >> (sub_word_offset * 8)) & 0xffff;
			break;
		case Ity_I8:
			dest->lo.v = (v1 >> (sub_word_offset * 8)) & 0xff;
			break;
		default:
			ppIRExpr(expr);
			abort();
		}
		break;
	}

	case Iex_RdTmp:
		*dest = temporaries[expr->Iex.RdTmp.tmp];
		break;

	case Iex_Load: {
		assert(!expr->Iex.Load.isLL);
		assert(expr->Iex.Load.end == Iend_LE);
		struct expression_result addr;
		eval_expression(temporaries, addrSpace, thr, &addr, expr->Iex.Load.addr);
		unsigned size = sizeofIRType(expr->Iex.Load.ty);
		if (size <= 8) {
			dest->lo.v = 0;
			addrSpace->readMemory(addr.lo.v, size, &dest->lo.v);
		} else if (size == 16) {
			addrSpace->readMemory(addr.lo.v, 8, &dest->lo.v);
			addrSpace->readMemory(addr.lo.v + 8, 8, &dest->hi.v);
		} else {
			abort();
		}
		break;
	}

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
			ASSUME(0);
		}
		break;
	}

	case Iex_Binop: {
		struct expression_result arg1;
		struct expression_result arg2;
		eval_expression(temporaries, addrSpace, thr, &arg1, expr->Iex.Binop.arg1);
		eval_expression(temporaries, addrSpace, thr, &arg2, expr->Iex.Binop.arg2);
		switch (expr->Iex.Binop.op) {
		case Iop_Sub64:
			dest->lo.v = arg1.lo.v - arg2.lo.v;
			break;
		case Iop_Sub32:
			dest->lo.v = (arg1.lo.v - arg2.lo.v) & 0xffffffff;
			break;
		case Iop_Sub8:
			dest->lo.v = (arg1.lo.v - arg2.lo.v) & 0xff;
			break;
		case Iop_Sub16:
			dest->lo.v = (arg1.lo.v - arg2.lo.v) & 0xffff;
			break;
		case Iop_Add64:
			dest->lo.v = arg1.lo.v + arg2.lo.v;
			break;
		case Iop_Add64x2:
			dest->lo.v = arg1.lo.v + arg2.lo.v;
			dest->hi.v = arg1.hi.v + arg2.hi.v;
			break;
		case Iop_Add8:
			dest->lo.v = (arg1.lo.v + arg2.lo.v) & 0xff;
			break;
		case Iop_Add16:
			dest->lo.v = (arg1.lo.v + arg2.lo.v) & 0xffff;
			break;
		case Iop_Add32:
			dest->lo.v = (arg1.lo.v + arg2.lo.v) & 0xffffffff;
			break;
		case Iop_And64:
		case Iop_And32:
		case Iop_And16:
		case Iop_And8:
			dest->lo.v = arg1.lo.v & arg2.lo.v;
			break;
		case Iop_Or8:
		case Iop_Or32:
		case Iop_Or64:
			dest->lo.v = arg1.lo.v | arg2.lo.v;
			break;
		case Iop_Shl32:
			dest->lo.v = (arg1.lo.v << arg2.lo.v) & 0xffffffff;
			break;
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
		case Iop_Xor64:
		case Iop_Xor32:
		case Iop_Xor8:
			dest->lo.v = arg1.lo.v ^ arg2.lo.v;
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
			dest->lo.v = arg1.lo.v * arg2.lo.v;
			break;

		case Iop_Mul32:
			dest->lo.v = (arg1.lo.v * arg2.lo.v) & 0xffffffff;
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
			
		case Iop_XorV128:
			dest->lo.v = arg1.lo.v ^ arg2.lo.v;
			dest->hi.v = arg1.hi.v ^ arg2.hi.v;
			break;

		case Iop_I64toF64: {
			switch (arg1.lo.v) {
			case 0:
				/* Round to nearest even mode. */
				*(double *)&dest->lo.v = arg2.lo.v;
				break;
			default:
				printf("unknown rounding mode %ld\n",
				       arg1.lo.v);
				abort();
				break;
			}
			break;
		}

		case Iop_F64toI32: {
			switch (arg1.lo.v) {
			case 3:
				dest->lo.v = (unsigned)*(double *)&arg2.lo.v;
				break;
			default:
				abort();
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
			abort();
		}
		break;
	}

	case Iex_Unop: {
		struct expression_result arg;
		eval_expression(temporaries, addrSpace, thr, &arg, expr->Iex.Unop.arg);
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
			abort();
		}
		break;
	}

	case Iex_Mux0X: {
		struct expression_result cond;
		struct expression_result res0;
		struct expression_result resX;
		struct expression_result *choice;
		eval_expression(temporaries, addrSpace, thr, &cond, expr->Iex.Mux0X.cond);
		eval_expression(temporaries, addrSpace, thr, &res0, expr->Iex.Mux0X.expr0);
		eval_expression(temporaries, addrSpace, thr, &resX, expr->Iex.Mux0X.exprX);
		if (cond.lo.v == 0) {
			choice = &res0;
		} else {
			choice = &resX;
		}
		*dest = *choice;
		break;
	}

	case Iex_CCall: {
		do_ccall(temporaries, addrSpace, thr, dest, expr->Iex.CCall.cee,
			 expr->Iex.CCall.retty, expr->Iex.CCall.args);
		break;
	}

	default:
		printf("Bad expression tag %x\n", expr->tag);
		ppIRExpr(expr);
		abort();
	}
}

static unsigned long
redirectGuest(unsigned long rip)
{
	/* XXX hideous hack of hideousness */
	if (rip == 0xFFFFFFFFFF600400ul)
		return 0x38017e0d;
	else if (rip == 0xFFFFFFFFFF600000)
		abort();
	else
		return rip;
}

void Interpreter::replayFootstep(const LogRecordFootstep &lrf,
				 const LogReader *lr,
				 LogReader::ptr startOffset,
				 LogReader::ptr *endOffset)
{
	Thread *thr = currentState->findThread(lrf.thread());
	AddressSpace *addrSpace = currentState->addressSpace;

	thr->regs.regs.guest_RIP = redirectGuest(thr->regs.rip());

	if (thr->regs.rip() != lrf.rip)
		throw ReplayFailedBadRip(thr->regs.rip(), lrf.rip);

#define ID(x) x
#define PASTE(x, y) x ## y
#define PASTE2(x, y) PASTE(x, y)
#define STRING(x) #x
#define STRING2(x) STRING(x)
#define FR_REG_NAME(x)				\
	PASTE2(PASTE2(FOOTSTEP_REG_, x), _NAME)
#define GUEST_REG(x) PASTE2(guest_, FR_REG_NAME(x))
#define CHECK_REGISTER(x)						\
	do {								\
		if (*(unsigned long *)&thr->regs.regs. GUEST_REG(x) != lrf. reg ## x) \
			throw ReplayFailedBadRegister(			\
				STRING2( FR_REG_NAME(x)),		\
				*(unsigned long *)&thr->regs.regs.GUEST_REG(x), \
				lrf. reg ## x);				\
	} while (0)
	CHECK_REGISTER(0);
	CHECK_REGISTER(1);
//	CHECK_REGISTER(2);
	do {								
		if ( ((unsigned long *)&thr->regs.regs.guest_XMM0)[1] != lrf.reg2) 
			throw ReplayFailedBadRegister(			
				"xmm0b",		
				((unsigned long *)&thr->regs.regs.guest_XMM0)[1], 
				lrf. reg2);				
	} while (0);
	CHECK_REGISTER(3);
	CHECK_REGISTER(4);

	const void *code = addrSpace->getRawPointerUnsafe(thr->regs.rip());

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
	IRSB *irsb = bb_to_IR(&vge,
			      NULL, /* Context for chase_into_ok */
			      disInstr_AMD64,
			      (UChar *)code,
			      (Addr64)thr->regs.rip(),
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

	struct expression_result *temporaries = new expression_result[irsb->tyenv->types_used];
	memset(temporaries,
	       0,
	       sizeof(temporaries[0]) * irsb->tyenv->types_used);
	PointerKeeperArr<expression_result> pkt(temporaries);

	for (int stmt_nr = 0; stmt_nr < irsb->stmts_used; stmt_nr++) {
		IRStmt *stmt = irsb->stmts[stmt_nr];
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			break;
		case Ist_AbiHint:
			break;
		case Ist_MBE:
			break;
		case Ist_WrTmp:
			eval_expression(temporaries,
					addrSpace,
					thr,
					&temporaries[stmt->Ist.WrTmp.tmp],
					stmt->Ist.WrTmp.data);
			break;

		case Ist_Store: {
			assert(stmt->Ist.Store.end == Iend_LE);
			assert(stmt->Ist.Store.resSC == IRTemp_INVALID);
			struct expression_result data;
			struct expression_result addr;
			eval_expression(temporaries, addrSpace, thr, &data, stmt->Ist.Store.data);
			eval_expression(temporaries, addrSpace, thr, &addr, stmt->Ist.Store.addr);
			unsigned size = sizeofIRType(typeOfIRExpr(irsb->tyenv,
								  stmt->Ist.Store.data));
			if (size <= 8) {
				addrSpace->writeMemory(addr.lo.v,
						       size,
						       &data.lo.v,
						       false,
						       thr);
			} else if (size == 16) {
				addrSpace->writeMemory(addr.lo.v,
						       8,
						       &data.lo.v,
						       false,
						       thr);
				addrSpace->writeMemory(addr.lo.v + 8,
						       8,
						       &data.hi.v,
						       false,
						       thr);
			} else {
				abort();
			}
			break;
		}

		case Ist_CAS: {
			assert(stmt->Ist.CAS.details->oldHi == IRTemp_INVALID);
			assert(stmt->Ist.CAS.details->expdHi == NULL);
			assert(stmt->Ist.CAS.details->dataHi == NULL);
			assert(stmt->Ist.CAS.details->end == Iend_LE);
			struct expression_result data;
			struct expression_result addr;
			struct expression_result expected;
			eval_expression(temporaries, addrSpace, thr, &data, stmt->Ist.CAS.details->dataLo);
			eval_expression(temporaries, addrSpace, thr, &addr, stmt->Ist.CAS.details->addr);
			eval_expression(temporaries, addrSpace, thr, &expected, stmt->Ist.CAS.details->expdLo);
			unsigned size = sizeofIRType(typeOfIRExpr(irsb->tyenv,
								  stmt->Ist.CAS.details->dataLo));
			struct expression_result seen;
			if (size <= 8) {
				addrSpace->readMemory(addr.lo.v, size, &seen.lo.v);
			} else if (size == 16) {
				addrSpace->readMemory(addr.lo.v, 8, &seen.lo.v);
				addrSpace->readMemory(addr.lo.v + 8, 8, &seen.hi.v);
			} else {
				abort();
			}
			if (expected.lo.v == seen.lo.v &&
			    (size <= 8 || expected.hi.v == seen.hi.v)) {
				if (size <= 8) {
					addrSpace->writeMemory(addr.lo.v,
							       size,
							       &data.lo.v,
							       false,
							       thr);
				} else {
					addrSpace->writeMemory(addr.lo.v,
							       8,
							       &data.lo.v,
							       false,
							       thr);
					addrSpace->writeMemory(addr.lo.v + 8,
							       8,
							       &data.hi.v,
							       false,
							       thr);
				}
			}
			temporaries[stmt->Ist.CAS.details->oldLo] = seen;
			break;
		}

		case Ist_Put: {
			unsigned byte_offset = stmt->Ist.Put.offset & 7;
			unsigned long *dest =
				get_reg(thr,
					stmt->Ist.Put.offset - byte_offset);
			struct expression_result data;

			eval_expression(temporaries, addrSpace, thr, &data, stmt->Ist.Put.data);
			switch (typeOfIRExpr(irsb->tyenv, stmt->Ist.Put.data)) {
			case Ity_I8:
				*dest &= ~(0xFF << (byte_offset * 8));
				*dest |= data.lo.v << (byte_offset * 8);
				break;

			case Ity_I16:
				tl_assert(!(byte_offset % 2));
				*dest &= ~(0xFFFFul << (byte_offset * 8));
				*dest |= data.lo.v << (byte_offset * 8);
				break;

			case Ity_I32:
			case Ity_F32:
				tl_assert(!(byte_offset % 4));
				*dest &= ~(0xFFFFFFFFul << (byte_offset * 8));
				*dest |= data.lo.v << (byte_offset * 8);
				break;

			case Ity_I64:
			case Ity_F64:
				tl_assert(byte_offset == 0);
				*dest = data.lo.v;
				break;

			case Ity_I128:
			case Ity_V128:
				tl_assert(byte_offset == 0);
				*dest = data.lo.v;
				*get_reg(thr,
					 stmt->Ist.Put.offset + 8) =
					data.hi.v;
				break;
			default:
				abort();
			}
			break;
		}

		case Ist_Dirty: {
			do_dirty_call(temporaries, addrSpace, thr, irsb, stmt->Ist.Dirty.details,
				      lr, startOffset, endOffset);
			break;
		}

		case Ist_Exit: {
			struct expression_result guard;
			if (stmt->Ist.Exit.guard) {
				eval_expression(temporaries, addrSpace, thr, &guard, stmt->Ist.Exit.guard);
				if (!guard.lo.v)
					break;
			}
			if (stmt->Ist.Exit.jk != Ijk_Boring) {
				assert(stmt->Ist.Exit.jk == Ijk_EmWarn);
				printf("EMULATION WARNING %x\n",
				       thr->regs.regs.guest_EMWARN);
			}
			tl_assert(stmt->Ist.Exit.dst->tag == Ico_U64);
			thr->regs.regs.guest_RIP = stmt->Ist.Exit.dst->Ico.U64;
			goto finished_block;
		}

		default:
			printf("Don't know how to interpret statement ");
			ppIRStmt(stmt);
			abort();
			break;
		}
	}

	assert(irsb->jumpkind == Ijk_Boring ||
	       irsb->jumpkind == Ijk_Call ||
	       irsb->jumpkind == Ijk_Ret ||
	       irsb->jumpkind == Ijk_Sys_syscall);

	{
		struct expression_result next_addr;
		eval_expression(temporaries, addrSpace, thr, &next_addr, irsb->next);
		thr->regs.regs.guest_RIP = next_addr.lo.v;
	}

	if (irsb->jumpkind == Ijk_Sys_syscall)
		replay_syscall(lr, startOffset, endOffset, addrSpace, thr,
			       currentState);

finished_block:
	return;
}

void Interpreter::replayLogfile(LogReader const *lf, LogReader::ptr ptr)
{
	LogRecord *lr;

	while (1) {
		lr = lf->read(ptr, &ptr);
		if (!lr)
			break;
		PointerKeeper<LogRecord> k(lr);
		if (LogRecordFootstep *lrf = dynamic_cast<LogRecordFootstep *>(lr))
			replayFootstep(*lrf, lf, ptr, &ptr);
		else
			abort();
	}
}

Thread::Thread(LogRecordInitialRegisters const&lrir)
	: tid(ThreadId(1)),
	  regs(lrir.regs),
	  clear_child_tid(0),
	  robust_list(0),
	  set_child_tid(0),
	  exitted(false)
{
}
