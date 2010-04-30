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
	void *origin;
	abstract_interpret_value() : v(0), origin(NULL) {}
};

struct expression_result {
	struct abstract_interpret_value lo;
	struct abstract_interpret_value hi;
};

#define REG_LAST 128

#define tl_assert(x) assert(x)
#define expr_const(x) NULL
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
do_ccall_calculate_condition(struct expression_result *temporaries,
			     AddressSpace *addrSpace,
			     Thread *thr,
			     struct expression_result *dest,
			     IRCallee *cee,
			     IRType retty,
			     IRExpr **args)
{
	struct expression_result condcode = {};
	struct expression_result op = {};
	struct expression_result dep1 = {};
	struct expression_result dep2 = {};
	struct expression_result ndep = {};
	int inv;

	tl_assert(retty == Ity_I64);
	tl_assert(cee->regparms == 0);

	eval_expression(temporaries, addrSpace, thr, &condcode, args[0]);
	eval_expression(temporaries, addrSpace, thr, &op, args[1]);

	eval_expression(temporaries, addrSpace, thr, &dep1, args[2]);
	eval_expression(temporaries, addrSpace, thr, &dep2, args[3]);
	eval_expression(temporaries, addrSpace, thr, &ndep, args[4]);
	inv = condcode.lo.v & 1;
	switch (condcode.lo.v & ~1) {
	case AMD64CondZ:
		switch (op.lo.v) {
		case AMD64G_CC_OP_LOGICB:
		case AMD64G_CC_OP_LOGICW:
		case AMD64G_CC_OP_LOGICL:
		case AMD64G_CC_OP_LOGICQ:
			dest->lo.v = dep1.lo.v == 0;
			break;
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBW:
		case AMD64G_CC_OP_SUBL:
		case AMD64G_CC_OP_SUBQ:
			dest->lo.v = dep1.lo.v == dep2.lo.v;
			break;

		case AMD64G_CC_OP_ADDL:
			dest->lo.v = (unsigned)(dep1.lo.v + dep2.lo.v) == 0;
			break;

		case AMD64G_CC_OP_ADDQ:
			dest->lo.v = dep1.lo.v + dep2.lo.v == 0;
			break;

		case AMD64G_CC_OP_INCB:
		case AMD64G_CC_OP_INCW:
		case AMD64G_CC_OP_INCL:
		case AMD64G_CC_OP_INCQ:
		case AMD64G_CC_OP_DECB:
		case AMD64G_CC_OP_DECW:
		case AMD64G_CC_OP_DECL:
		case AMD64G_CC_OP_DECQ:
		case AMD64G_CC_OP_SHRL:
		case AMD64G_CC_OP_SHRQ:
			dest->lo.v = dep1.lo.v == 0;
			break;
		default:
			printf("Strange operation code %ld\n", op.lo.v);
			abort();
		}
		break;

	case AMD64CondL:
		switch (op.lo.v) {
		case AMD64G_CC_OP_SUBB:
			dest->lo.v = (char)dep1.lo.v < (char)dep2.lo.v;
			break;
		case AMD64G_CC_OP_SUBL:
			dest->lo.v = (int)dep1.lo.v < (int)dep2.lo.v;
			break;
		case AMD64G_CC_OP_SUBQ:
			dest->lo.v = (long)dep1.lo.v < (long)dep2.lo.v;
			break;
		default:
			printf("Strange operation code %ld for lt\n", op.lo.v);
			abort();
		}
		break;

	case AMD64CondLE:
		switch (op.lo.v) {
		case AMD64G_CC_OP_SUBB:
			dest->lo.v = (signed char)dep1.lo.v <= (signed char)dep2.lo.v;
			break;
		case AMD64G_CC_OP_SUBL:
			dest->lo.v = (int)dep1.lo.v <= (int)dep2.lo.v;
			break;
		case AMD64G_CC_OP_SUBQ:
			dest->lo.v = (long)dep1.lo.v <= (long)dep2.lo.v;
			break;
		case AMD64G_CC_OP_LOGICL:
			dest->lo.v = (unsigned)(dep1.lo.v + 0x80000000) <= 0x80000000 ;
			break;
		case AMD64G_CC_OP_LOGICQ:
			dest->lo.v = (long)dep1.lo.v <= 0;
			break;
		default:
			printf("Strange operation code %ld for le\n", op.lo.v);
			abort();
		}
		break;
	case AMD64CondB:
		switch (op.lo.v) {
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBL:
		case AMD64G_CC_OP_SUBQ:
			dest->lo.v = dep1.lo.v < dep2.lo.v;
			break;
		case AMD64G_CC_OP_ADDQ:
			dest->lo.v = dep1.lo.v + dep2.lo.v < dep1.lo.v;
			break;
		default:
			printf("Strange operation code %ld for b\n", op.lo.v);
			abort();
		}
		break;
	case AMD64CondBE:
		switch (op.lo.v) {
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBL:
		case AMD64G_CC_OP_SUBQ:
			dest->lo.v = dep1.lo.v <= dep2.lo.v;
			break;
		default:
			printf("Strange operation code %ld for be\n", op.lo.v);
			abort();
		}
		break;

	case AMD64CondS:
		switch (op.lo.v) {
		case AMD64G_CC_OP_ADDQ:
			dest->lo.v = (dep1.lo.v + dep2.lo.v) >> 63;
			break;
		case AMD64G_CC_OP_LOGICB:
			dest->lo.v = dep1.lo.v >> 7;
			break;
		case AMD64G_CC_OP_LOGICW:
			dest->lo.v = dep1.lo.v >> 15;
			break;
		case AMD64G_CC_OP_LOGICL:
			dest->lo.v = dep1.lo.v >> 31;
			break;
		case AMD64G_CC_OP_LOGICQ:
			dest->lo.v = dep1.lo.v >> 63;
			break;
		case AMD64G_CC_OP_SUBB:
			dest->lo.v = (char)dep1.lo.v < (char)dep2.lo.v;
			break;
		case AMD64G_CC_OP_SUBW:
			dest->lo.v = (short)dep1.lo.v < (short)dep2.lo.v;
			break;
		case AMD64G_CC_OP_SUBL:
			dest->lo.v = (int)dep1.lo.v < (int)dep2.lo.v;
			break;
		case AMD64G_CC_OP_SUBQ:
			dest->lo.v = (long)dep1.lo.v < (long)dep2.lo.v;
			break;
		default:
			printf("Strange operation code %ld for s\n", op.lo.v);
			abort();
		}
		break;

	default:
		printf("Strange cond code %ld (op %ld)\n", condcode.lo.v, op.lo.v);
		abort();
	}

	if (inv) {
		dest->lo.v ^= 1;
	}
}

static void
do_ccall_calculate_rflags_c(struct expression_result *temporaries,
			    AddressSpace *addrSpace,
			    Thread *thr,
			    struct expression_result *dest,
			    IRCallee *cee,
			    IRType retty,
			    IRExpr **args)
{
	struct expression_result op = {};
	struct expression_result dep1 = {};
	struct expression_result dep2 = {};
	struct expression_result ndep = {};

	tl_assert(retty == Ity_I64);
	tl_assert(cee->regparms == 0);

	eval_expression(temporaries, addrSpace, thr, &op, args[0]);

	eval_expression(temporaries, addrSpace, thr, &dep1, args[1]);
	eval_expression(temporaries, addrSpace, thr, &dep2, args[2]);
	eval_expression(temporaries, addrSpace, thr, &ndep, args[3]);

	switch (op.lo.v) {
	case AMD64G_CC_OP_INCB:
	case AMD64G_CC_OP_INCW:
	case AMD64G_CC_OP_INCL:
	case AMD64G_CC_OP_INCQ:
	case AMD64G_CC_OP_DECB:
	case AMD64G_CC_OP_DECW:
	case AMD64G_CC_OP_DECL:
	case AMD64G_CC_OP_DECQ:
		dest->lo.v = ndep.lo.v & 1;
		break;

	case AMD64G_CC_OP_SUBB:
		dest->lo.v = (unsigned char)dep1.lo.v < (unsigned char)dep2.lo.v;
		break;

	case AMD64G_CC_OP_SUBW:
		dest->lo.v = (unsigned short)dep1.lo.v < (unsigned short)dep2.lo.v;
		break;

	case AMD64G_CC_OP_SUBL:
		dest->lo.v = (unsigned)dep1.lo.v < (unsigned)dep2.lo.v;
		break;

	case AMD64G_CC_OP_SUBQ:
		dest->lo.v = dep1.lo.v  < dep2.lo.v;
		break;

	case AMD64G_CC_OP_LOGICB:
	case AMD64G_CC_OP_LOGICW:
	case AMD64G_CC_OP_LOGICL:
	case AMD64G_CC_OP_LOGICQ:
		/* XXX Why doesn't the Valgrind optimiser remove
		 * these? */
		dest->lo.v = 0;
		break;

	case AMD64G_CC_OP_SHRB:
	case AMD64G_CC_OP_SHRW:
	case AMD64G_CC_OP_SHRL:
	case AMD64G_CC_OP_SHRQ:
		dest->lo.v = dep2.lo.v & 1;
		break;

	default:
		printf("Can't calculate C flags for op %ld\n",
		       op.lo.v);
		abort();
	}
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
		do_ccall_calculate_condition(temporaries, addrSpace, thr, dest, cee, retty, args);
	} else if (!strcmp(cee->name, "amd64g_calculate_rflags_c")) {
		do_ccall_calculate_rflags_c(temporaries, addrSpace, thr, dest, cee, retty, args);
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
#define ORIGIN(x)

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
		dest->lo.origin = NULL;
		dest->hi.origin = NULL;
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
			dest->hi.origin = expr_const(dest->hi.v);
			break;
		default:
			ASSUME(0);
		}
		dest->lo.origin = expr_const(dest->lo.v);
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
			ORIGIN(expr_sub(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Sub32:
			dest->lo.v = (arg1.lo.v - arg2.lo.v) & 0xffffffff;
			ORIGIN(expr_and(expr_sub(arg1.lo.origin, arg2.lo.origin),
					expr_const(0xffffffff)));
			break;
		case Iop_Sub8:
			dest->lo.v = (arg1.lo.v - arg2.lo.v) & 0xff;
			ORIGIN(expr_and(expr_sub(arg1.lo.origin, arg2.lo.origin),
					expr_const(0xff)));
			break;
		case Iop_Sub16:
			dest->lo.v = (arg1.lo.v - arg2.lo.v) & 0xffff;
			break;
		case Iop_Add64:
			dest->lo.v = arg1.lo.v + arg2.lo.v;
			ORIGIN(expr_add(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Add64x2:
			dest->lo.v = arg1.lo.v + arg2.lo.v;
			dest->hi.v = arg1.hi.v + arg2.hi.v;
			break;
		case Iop_Add8:
			dest->lo.v = (arg1.lo.v + arg2.lo.v) & 0xff;
			break;
		case Iop_Add32:
			dest->lo.v = (arg1.lo.v + arg2.lo.v) & 0xffffffff;
			ORIGIN(expr_and(expr_add(arg1.lo.origin, arg2.lo.origin),
					expr_const(0xffffffff)));
			break;
		case Iop_And64:
		case Iop_And32:
		case Iop_And16:
		case Iop_And8:
			dest->lo.v = arg1.lo.v & arg2.lo.v;
			ORIGIN(expr_and(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Or8:
		case Iop_Or32:
		case Iop_Or64:
			dest->lo.v = arg1.lo.v | arg2.lo.v;
			ORIGIN(expr_or(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Shl32:
			dest->lo.v = (arg1.lo.v << arg2.lo.v) & 0xffffffff;
			ORIGIN(expr_and(expr_shl(arg1.lo.origin, arg2.lo.origin),
					expr_const(0xffffffff)));
			break;
		case Iop_Shl64:
			dest->lo.v = arg1.lo.v << arg2.lo.v;
			ORIGIN(expr_shl(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Sar64:
			dest->lo.v = (long)arg1.lo.v >> arg2.lo.v;
			ORIGIN(expr_shra(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Shr32:
		case Iop_Shr64:
			dest->lo.v = arg1.lo.v >> arg2.lo.v;
			ORIGIN(expr_shrl(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Xor64:
		case Iop_Xor32:
		case Iop_Xor8:
			dest->lo.v = arg1.lo.v ^ arg2.lo.v;
			ORIGIN(expr_xor(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_CmpNE8:
			dest->lo.v = arg1.lo.v != arg2.lo.v;
			ORIGIN(expr_not(expr_eq(arg1.lo.origin, arg2.lo.origin)));
			break;
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			dest->lo.v = arg1.lo.v == arg2.lo.v;
			ORIGIN(expr_eq(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_CmpNE32:
		case Iop_CasCmpNE32:
		case Iop_CmpNE64:
			dest->lo.v = arg1.lo.v != arg2.lo.v;
			ORIGIN(expr_not(expr_eq(arg1.lo.origin, arg2.lo.origin)));
			break;
		case Iop_CmpLE64U:
			dest->lo.v = arg1.lo.v <= arg2.lo.v;
			ORIGIN(expr_be(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_CmpLE64S:
			dest->lo.v = (long)arg1.lo.v <= (long)arg2.lo.v;
			ORIGIN(expr_le(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_CmpLT64S:
			dest->lo.v = (long)arg1.lo.v < (long)arg2.lo.v;
			ORIGIN(expr_and(expr_le(arg1.lo.origin, arg2.lo.origin),
					expr_not(expr_eq(arg1.lo.origin, arg2.lo.origin))));
			break;
		case Iop_CmpLT64U:
			dest->lo.v = arg1.lo.v < arg2.lo.v;
			ORIGIN(expr_b(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Mul64:
			dest->lo.v = arg1.lo.v * arg2.lo.v;
			ORIGIN(expr_mul(arg1.lo.origin, arg2.lo.origin));
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
			ORIGIN(expr_or(expr_shl(arg1.lo.origin,
						expr_const(32)),
				       arg2.lo.origin));
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
			ORIGIN(expr_shrl(arg.lo.origin, expr_const(32)));
			break;
		case Iop_64to32:
			dest->lo.v = arg.lo.v & 0xffffffff;
			ORIGIN(expr_and(arg.lo.origin, expr_const(0xfffffffful)));
			break;
		case Iop_64to16:
			dest->lo.v = arg.lo.v & 0xffff;
			ORIGIN(expr_and(arg.lo.origin, expr_const(0xffff)));
			break;
		case Iop_64to8:
			dest->lo.v = arg.lo.v & 0xff;
			ORIGIN(expr_and(arg.lo.origin, expr_const(0xff)));
			break;
		case Iop_128to64:
		case Iop_V128to64:
			dest->lo.v = arg.lo.v;
			ORIGIN(arg.lo.origin);
			break;
		case Iop_64to1:
			dest->lo.v = arg.lo.v & 1;
			ORIGIN(expr_and(arg.lo.origin, expr_const(1)));
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
			ORIGIN(expr_shra(expr_shl(arg.lo.origin,
						  expr_const(32)),
					 expr_const(32)));
			break;
		case Iop_8Sto64:
			dest->lo.v = (long)(signed char)arg.lo.v;
			ORIGIN(expr_shra(expr_shl(arg.lo.origin,
						  expr_const(56)),
					 expr_const(56)));
			break;
		case Iop_16Sto32:
			dest->lo.v = (unsigned)(signed short)arg.lo.v;
			break;
		case Iop_8Sto32:
			dest->lo.v = (unsigned)(signed char)arg.lo.v;
			ORIGIN(expr_and(expr_shra(expr_shl(arg.lo.origin,
							   expr_const(56)),
						  expr_const(56)),
					expr_const(0xffffffff)));
			break;
		case Iop_16Sto64:
			dest->lo.v = (long)(short)arg.lo.v;
			ORIGIN(expr_shra(expr_shl(arg.lo.origin,
						  expr_const(48)),
					 expr_const(48)));
			break;
		case Iop_128HIto64:
		case Iop_V128HIto64:
			dest->lo.v = arg.hi.v;
			ORIGIN(arg.hi.origin);
			break;

		case Iop_Not1:
			dest->lo.v = !arg.lo.v;
			ORIGIN(expr_and(expr_not(arg.lo.origin),
					expr_const(1)));
			break;

		case Iop_Not32:
			dest->lo.v = ~arg.lo.v & 0xffffffff;
			ORIGIN(expr_and(expr_not(arg.lo.origin),
					expr_const(0xffffffff)));
			break;

		case Iop_Not64:
			dest->lo.v = ~arg.lo.v;
			ORIGIN(expr_not(arg.lo.origin));
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
#undef ORIGIN
}

void Interpreter::replayFootstep(const LogRecordFootstep &lrf,
				 const LogReader *lr,
				 LogReader::ptr startOffset,
				 LogReader::ptr *endOffset)
{
	Thread *thr = currentState->findThread(lrf.thread());
	AddressSpace *addrSpace = currentState->addressSpace;

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
				*dest &= ~(0xFFFF << (byte_offset * 8));
				*dest |= data.lo.v << (byte_offset * 8);
				break;

			case Ity_I64:
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
			tl_assert(stmt->Ist.Exit.jk == Ijk_Boring);
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
		tl_assert(next_addr.hi.origin == NULL);
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
	: regs(lrir.regs),
	  clear_child_tid(0)
{
}
