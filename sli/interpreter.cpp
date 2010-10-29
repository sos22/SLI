#include <string.h>
#include <asm/unistd.h>

#include "libvex.h"
#include "libvex_ir.h"
#include "libvex_emwarn.h"
#include "libvex_guest_amd64.h"
#include "guest_generic_bb_to_IR.h"
#include "guest_generic_x87.h"
#include "guest_amd64_defs.h"
#include "main_util.h"

#define FOOTSTEP_REGS_ONLY
#include "ppres.h"

#include "sli.h"

static bool loud_mode;

#define DBG(x, args...) do { if (loud_mode) printf("%s:%d:%d: " x, __FILE__, __LINE__, ths->tid._tid(), ##args); } while (0)

static Bool chase_into_ok(void *ignore1, Addr64 ignore2)
{
	return False;
}

static unsigned long signed_shift_right(unsigned long x, unsigned long y)
{
	return (long)x >> y;
}

static unsigned long signed_le(unsigned long x, unsigned long y)
{
	return (long)x <= (long)y;
}
	
static unsigned long signed_l(unsigned long x, unsigned long y)
{
	return (long)x < (long)y;
}

#define REG_LAST 128

static void
write_reg(Thread *state, unsigned offset, unsigned long val)
{
	assert(!(offset % 8));
	state->regs.set_reg(offset / 8, val);
}

static unsigned long
read_reg(Thread *state, unsigned offset)
{
	assert(!(offset % 8));
	return state->regs.get_reg(offset / 8);
}

static void
amd64g_dirtyhelper_CPUID_sse3_and_cx16(RegisterSet *regs)
{
#define SET_ABCD(_a,_b,_c,_d)						\
	do {								\
		regs->set_reg(REGISTER_IDX(RAX), (_a));	\
		regs->set_reg(REGISTER_IDX(RBX), (_b));	\
		regs->set_reg(REGISTER_IDX(RCX), (_c));	\
		regs->set_reg(REGISTER_IDX(RDX), (_d));	\
	} while (0)

	switch (0xFFFFFFFFul & regs->get_reg(REGISTER_IDX(RAX))) {
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
		switch (0xFFFFFFFFul & regs->get_reg(REGISTER_IDX(RCX))) {
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

void
Thread::amd64g_dirtyhelper_loadF80le(MachineState *ms, IRTemp tmp, unsigned long addr)
{
	unsigned long buf[10];
	ms->addressSpace->readMemory(addr, 10, buf, false, this, NULL);
	UChar buf2[10];
	for (unsigned x = 0; x < 10; x++)
		buf2[x] = buf[x];
	ULong f64;
	convert_f80le_to_f64le(buf2, (UChar*)&f64);
	temporaries[tmp].lo = (f64);
	temporaries[tmp].hi = 0ul;
}

void
Thread::amd64g_dirtyhelper_storeF80le(MachineState *ms, unsigned long addr, unsigned long _f64)
{
	unsigned long f64 = _f64;
	unsigned char buf[10];
	unsigned long buf2[10];
	unsigned x;

	convert_f64le_to_f80le((UChar *)&f64, (UChar *)buf);

	for (x = 0; x < 10; x++)
		buf2[x] = (buf[x]);
	ms->addressSpace->writeMemory(addr,
				      10,
				      buf2,
				      false,
				      this);
}

ThreadEvent *
Thread::do_load(IRTemp tmp, unsigned long addr, unsigned size, MachineState *ms,
		EventRecorder *er)
{
	if (ms->addressSpace->isReadable(addr, size, this)) {
		er->load(this, addr);
		return LoadEvent::get(tid, tmp, addr, size);
	} else
		return SignalEvent::get(tid, 11, addr);
}

ThreadEvent *
Thread::do_dirty_call(IRDirty *details, MachineState *ms, EventRecorder *er)
{
	struct expression_result args[6];
	unsigned x;

	if (details->guard) {
		expression_result guard = eval_expression(details->guard);
		if (!guard.lo)
			return NULL;
	}
	for (x = 0; details->args[x]; x++) {
		assert(x < 6);
		args[x] = eval_expression(details->args[x]);
	}
	assert(!details->cee->regparms);

	if (!strcmp(details->cee->name, "amd64g_dirtyhelper_RDTSC")) {
		return RdtscEvent::get(tid, details->tmp);
	} else if (!strcmp(details->cee->name, "helper_load_8")) {
		return do_load(details->tmp, args[0].lo, 1, ms, er);
	} else if (!strcmp(details->cee->name, "helper_load_16")) {
		return do_load(details->tmp, args[0].lo, 2, ms, er);
	} else if (!strcmp(details->cee->name, "helper_load_32")) {
		return do_load(details->tmp, args[0].lo, 4, ms, er);
	} else if (!strcmp(details->cee->name, "helper_load_64")) {
		return do_load(details->tmp, args[0].lo, 8, ms, er);
	} else if (!strcmp(details->cee->name, "helper_load_128")) {
		return do_load(details->tmp, args[0].lo, 16, ms, er);
	} else if (!strcmp(details->cee->name, "amd64g_dirtyhelper_CPUID_sse3_and_cx16")) {
		amd64g_dirtyhelper_CPUID_sse3_and_cx16(&regs);
		return NULL;
	} else if (!strcmp(details->cee->name, "amd64g_dirtyhelper_storeF80le")) {
		amd64g_dirtyhelper_storeF80le(ms, args[0].lo, args[1].lo);
		return NULL;
	} else if (!strcmp(details->cee->name, "amd64g_dirtyhelper_loadF80le")) {
		amd64g_dirtyhelper_loadF80le(ms, details->tmp, args[0].lo);
		return NULL;
	} else {
		throw NotImplementedException("Unknown dirty call %s\n", details->cee->name);
	}
}

static const UChar parity_table[256] = {
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0,
    1, 0, 0, 1, 0, 1, 1, 0,
    0, 1, 1, 0, 1, 0, 0, 1,
};

static void
calculate_condition_flags_XXX(unsigned long op,
			      unsigned long dep1,
			      unsigned long dep2,
			      unsigned long ndep,
			      unsigned long &cf,
			      unsigned long &zf,
			      unsigned long &sf,
			      unsigned long &of,
			      unsigned long &pf)
{
	pf = cf = zf = sf = of = 0ul;

	switch (op) {
	case AMD64G_CC_OP_COPY:
		cf = dep1;
		zf = dep1 >> 6ul;
		sf = dep1 >> 7ul;
		of = dep1 >> 11ul;
		pf = dep1 >> 2ul;
		break;

#define DO_ACT(name, type_tag, bits)					\
		case AMD64G_CC_OP_ ## name ## type_tag:			\
			ACTIONS_ ## name ((bits));		\
		        break
#define ACTION(name)							\
		DO_ACT(name, B, 7);					\
		DO_ACT(name, W, 15);					\
		DO_ACT(name, L, 31);					\
		DO_ACT(name, Q, 63)
/* A shift of 64 bits in a 64 bit type is undefined, so we can't just
   go (1ul << 64).  However, (1ul << 63) * 2 does the right thing. */
#define MASK(bits) ((1ul << bits) * 2ul - 1ul)
#define ACTIONS_ADD(bits)						\
		do {							\
			unsigned long res;					\
			res = (dep1 + dep2) & MASK(bits);		\
			cf = res < (dep1 & MASK(bits));			\
			zf = (res == 0ul);			\
			sf = (res >> bits);				\
			of = (~(dep1 ^ dep2) &				\
			      (dep1 ^ res)) >> bits;			\
			pf = (parity_table[(UChar)res]); \
		} while (0)
#define ACTIONS_ADC(bits)	 		                        \
		do {							\
			unsigned long oldC = ndep & (AMD64G_CC_MASK_C); \
			unsigned long argR = dep2 ^ oldC;				\
			unsigned long res = ((dep1 + argR) + oldC) & MASK(bits);	\
			if (oldC)				\
				cf = res <= (dep1 & MASK(bits));	\
			else						\
				cf = res < (dep1 & MASK(bits));		\
			zf = res == 0ul;			\
			sf = res >> bits;				\
			of = (~(dep1 ^ argR) & (dep1 ^ res)) >> bits;	\
			pf = (parity_table[(UChar)res]); \
		} while (0)
#define ACTIONS_SUB(bits)						\
		do {							\
			unsigned long res;					\
			res = (dep1 - dep2) & MASK(bits);		\
			cf = (dep1 & MASK(bits)) < (dep2 & MASK(bits));	\
			zf = (res == 0ul);			\
			sf = res >> bits;				\
			of = ( (dep1 ^ dep2) &				\
			       (dep1 ^ res) ) >> bits;			\
			pf = (parity_table[(UChar)res]); \
		} while (0)
#define ACTIONS_LOGIC(bits)						\
		do {							\
			cf = 0ul;				\
			zf = (dep1 & MASK(bits)) == 0ul;	\
			sf = (dep1 & MASK(bits)) >> bits;		\
			of = 0ul;				\
			pf = (parity_table[(UChar)dep1]); \
		} while (0)
#define ACTIONS_INC(bits)			                        \
		do {				                        \
			unsigned long res = dep1 & MASK(bits);			\
			cf = ndep & 1ul;			\
			zf = (res == 0ul);			\
			sf = res >> bits;				\
			of = res == (1ul << bits);		\
			pf = (parity_table[(UChar)res]); \
		} while (0)
#define ACTIONS_DEC(bits)			                        \
		do {				                        \
			unsigned long res = dep1 & MASK(bits);			\
			cf = ndep & 1ul;			\
			zf = (res == 0ul);			\
			sf = res >> bits;				\
			of = ((res + 1ul) & MASK(bits)) == (1ul << bits); \
			pf = (parity_table[(UChar)res]); \
		} while (0)
#define ACTIONS_SHR(bits)			                        \
		do {				                        \
			cf = dep2 & 1ul;			\
			zf = (dep1 == 0ul);			\
			sf = dep1 >> bits;				\
			of = (dep1 ^ dep2) >> bits;			\
			pf = (parity_table[(UChar)dep1]); \
		} while (0)
	ACTION(ADD);
	ACTION(SUB);
	ACTION(LOGIC);
	ACTION(INC);
	ACTION(DEC);
	ACTION(SHR);
	ACTION(ADC);
#undef DO_ACT
#undef ACTION
#undef ACTIONS_ADD
#undef ACTIONS_SUB
#undef ACTIONS_LOGIC
#undef ACTIONS_INC
#undef ACTIONS_DEC
#undef ACTIONS_SHR
#undef ACTIONS_ADC
	default:
		throw NotImplementedException("Strange operation code %ld\n", op);
	}

	of &= 1ul;
	sf &= 1ul;
	zf &= 1ul;
	cf &= 1ul;
}

expression_result
Thread::do_ccall_calculate_condition(struct expression_result *args)
{
	struct expression_result condcode = args[0];
	struct expression_result op       = args[1];
	struct expression_result dep1     = args[2];
	struct expression_result dep2     = args[3];
	struct expression_result ndep     = args[4];
	struct expression_result res;
	unsigned long inv;
	unsigned long cf, zf, sf, of, pf;

	calculate_condition_flags_XXX(op.lo,
					   dep1.lo,
					   dep2.lo,
					   ndep.lo,
					   cf,
					   zf,
					   sf,
					   of,
					   pf);

	inv = condcode.lo & 1ul;
	switch (condcode.lo & ~1ul) {
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
	case AMD64CondP:
		res.lo = pf;
		break;

	default:
		throw NotImplementedException("Strange cond code %ld (op %ld)\n", condcode.lo, op.lo);
	}

	res.lo ^= inv;

	return res;
}

expression_result
Thread::do_ccall_calculate_rflags_c(expression_result *args)
{
	struct expression_result op   = args[0];
	struct expression_result dep1 = args[1];
	struct expression_result dep2 = args[2];
	struct expression_result ndep = args[3];
	struct expression_result res;
	unsigned long cf, zf, sf, of, pf;

	calculate_condition_flags_XXX(op.lo,
				      dep1.lo,
				      dep2.lo,
				      ndep.lo,
				      cf,
				      zf,
				      sf,
				      of,
				      pf);

	res.lo = cf;
	return res;
}

expression_result
Thread::do_ccall_generic(IRCallee *cee,
			      struct expression_result *rargs)
{
	struct expression_result res;

	res.lo = ((unsigned long (*)(unsigned long, unsigned long, unsigned long,
				     unsigned long, unsigned long, unsigned long))cee->addr)
		(rargs[0].lo,
		 rargs[1].lo,
		 rargs[2].lo,
		 rargs[3].lo,
		 rargs[4].lo,
		 rargs[5].lo);
	res.hi = 0ul;
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
		if (strcmp(cee->name, "amd64g_calculate_rflags_all"))
			printf("Unknown clean call %s\n", cee->name);
		return do_ccall_generic(cee, rargs);
	}
}

/* Borrowed from gnucash */
static void mulls64(struct expression_result *dest, const struct expression_result &src1,
		    const struct expression_result &src2)
{
	bool isneg = false;
	unsigned long a = src1.lo;
	unsigned long b = src2.lo;
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

expression_result
Thread::eval_expression(IRExpr *expr)
{
	struct expression_result res;
	struct expression_result *dest = &res;
	unsigned getOffset;
	IRType getType;

	res.lo = 0ul;
	res.hi = 0ul;
	
	switch (expr->tag) {
	case Iex_Get: {
		getOffset = expr->Iex.Get.offset;
		getType = expr->Iex.Get.ty;

		do_get:
		unsigned long v1;
		unsigned sub_word_offset = getOffset & 7;
		v1 = read_reg(this, getOffset - sub_word_offset);
		switch (getType) {
		case Ity_I64:
		case Ity_F64:
			assert(!sub_word_offset);
			dest->lo = v1;
			break;
		case Ity_V128:
			assert(!sub_word_offset);
			dest->lo = v1;
			dest->hi = read_reg(this, getOffset - sub_word_offset + 8);
			break;
		case Ity_I32:
		case Ity_F32:
			assert(!(sub_word_offset % 4));
			dest->lo = (v1 >> (sub_word_offset * 8)) & 0xfffffffful;
			break;
		case Ity_I16:
			assert(!(sub_word_offset % 2));
			dest->lo = (v1 >> (sub_word_offset * 8)) & 0xfffful;
			break;
		case Ity_I8:
			dest->lo = (v1 >> (sub_word_offset * 8)) & 0xfful;
			break;
		default:
			ppIRExpr(expr);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_GetI: {
		getOffset = eval_expression(expr->Iex.GetI.ix).lo;
		getOffset += expr->Iex.GetI.bias;
		getOffset %= expr->Iex.GetI.descr->nElems;
		getOffset *= sizeofIRType(expr->Iex.GetI.descr->elemTy);
		getOffset += expr->Iex.GetI.descr->base;
		getType = expr->Iex.GetI.descr->elemTy;
		goto do_get;
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
			dest->lo = (cnst->Ico.U1);
			break;
		case Ico_U8:
			dest->lo = (cnst->Ico.U8);
			break;
		case Ico_U16:
			dest->lo = (cnst->Ico.U16);
			break;
		case Ico_U32:
			dest->lo = (cnst->Ico.U32);
			break;
		case Ico_U64:
		case Ico_F64:
		case Ico_F64i:
			dest->lo = (cnst->Ico.U64);
			break;
		case Ico_V128: {
			unsigned long r = cnst->Ico.V128;
			r = r | (r << 16) | (r << 32) | (r << 48);
			dest->lo = (r);
			dest->hi = dest->lo;
			break;
		}
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
		case Iop_AndV128:
			dest->hi = arg1.hi & arg2.hi;
		case Iop_And64:
		case Iop_And32:
		case Iop_And16:
		case Iop_And8:
			dest->lo = arg1.lo & arg2.lo;
			break;
		case Iop_OrV128:
			dest->hi = arg1.hi | arg2.hi;
		case Iop_Or8:
		case Iop_Or16:
		case Iop_Or32:
		case Iop_Or64:
			dest->lo = arg1.lo | arg2.lo;
			break;
		case Iop_Shl16:
		case Iop_Shl32:
		case Iop_Shl64:
			dest->lo = arg1.lo << arg2.lo;
			break;
		case Iop_Sar64:
			dest->lo = signed_shift_right(arg1.lo, arg2.lo);
			break;
		case Iop_Shr16:
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
			dest->lo = signed_le(arg1.lo, arg2.lo);
			break;
		case Iop_CmpLT64S:
			dest->lo = signed_l(arg1.lo, arg2.lo);
			break;
		case Iop_CmpLT64U:
			dest->lo = arg1.lo < arg2.lo;
			break;
		case Iop_Mul64:
		case Iop_Mul32:
			dest->lo = arg1.lo * arg2.lo;
			break;

		case Iop_MullU32:
			dest->lo = arg1.lo * arg2.lo;
			break;
		case Iop_MullS32:
			dest->lo =
				(long)(int)arg1.lo * (long)(int)arg2.lo;
			break;

		case Iop_MullS64:
			mulls64(dest, arg1, arg2);
			break;

		case Iop_MullU64: {
			unsigned long a1, a2, b1, b2;
			dest->lo = arg1.lo * arg2.lo;
			a1 = arg1.lo & 0xfffffffful;
			a2 = arg1.lo >> 32ul;
			b1 = arg2.lo & 0xfffffffful;
			b2 = arg2.lo >> 32ul;
			dest->hi = a2 * b2 +
				( (a1 * b2 + a2 * b1 +
				   ((a1 * b1) >> 32ul)) >> 32ul);
			break;
		}
		case Iop_32HLto64:
			dest->lo = (arg1.lo << 32ul) | arg2.lo;
			break;

		case Iop_64HLtoV128:
		case Iop_64HLto128:
			dest->lo = arg2.lo;
			dest->hi = arg1.lo;
			break;

		case Iop_DivModU64to32:
			dest->lo = (arg1.lo / arg2.lo) |
				((arg1.lo % arg2.lo) << 32ul);
			break;

		case Iop_DivModS64to32: {
			long a1 = arg1.lo;
			long a2 = arg2.lo;
			dest->lo = 
				((a1 / a2) & 0xffffffff) | ((a1 % a2) << 32);
			break;
		}

		case Iop_DivModU128to64: {
			/* arg1 is a I128, arg2 is an I64, result is
			   128 bits and has the dividend in its low 64
			   bits and the modulus in its high 64
			   bits. */
			unsigned long dlo, dhi;
			asm ("div %4\n"
			     : "=a" (dlo), "=d" (dhi)
			     : "0" (arg1.lo), "1" (arg1.hi), "r" (arg2.lo));
			dest->lo = (dlo);
			dest->hi = (dhi);
			break;
		}

		case Iop_DivModS128to64: {
			unsigned long dlo;
			unsigned long dhi;
			asm ("idiv %4\n"
			     : "=a" (dlo), "=d" (dhi)
			     : "0" (arg1.lo), "1" (arg1.hi), "r" (arg2.lo));
			dest->lo = (dlo);
			dest->hi = (dhi);
			break;
		}

		case Iop_Add32x4:
			dest->lo = ((arg1.lo + arg2.lo) & 0xfffffffful) +
				((arg1.lo & (~0xfffffffful)) + (arg2.lo & (~0xfffffffful)));
			dest->hi = ((arg1.hi + arg2.hi) & 0xfffffffful) +
				((arg1.hi & (~0xfffffffful)) + (arg2.hi & (~0xfffffffful)));
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
			dest->lo = (arg2.lo & 0xfffffffful) | (arg1.lo << 32ul);
			dest->hi = (arg2.lo >> 32ul) | (arg1.lo & (0xffffffff00000000ul));
			break;

		case Iop_InterleaveHI32x4:
			dest->lo = (arg2.hi & 0xfffffffful) | (arg1.hi << 32ul);
			dest->hi = (arg2.hi >> 32ul) | (arg1.hi & (0xffffffff00000000ul));
			break;

		case Iop_ShrN64x2:
			dest->lo = arg1.lo >> arg2.lo;
			dest->hi = arg1.hi >> arg2.lo;
			break;

		case Iop_ShlN64x2:
			dest->lo = arg1.lo << arg2.lo;
			dest->hi = arg1.hi << arg2.lo;
			break;

		case Iop_CmpGT32Sx4: {
			unsigned long a1l = arg1.lo;
			unsigned long a2l = arg2.lo;
			unsigned long a1h = arg1.hi;
			unsigned long a2h = arg2.hi;
			if ( (int)a1l > (int)a2l )
				dest->lo |= 0xfffffffful;
			if ( (int)(a1l >> 32) > (int)(a2l >> 32) )
				dest->lo |= 0xffffffff00000000ul;
			if ( (int)a1h > (int)a2h )
				dest->hi |= 0xfffffffful;
			if ( (int)(a1h >> 32) > (int)(a2h >> 32) )
				dest->hi |= 0xffffffff00000000ul;
			break;
		}

		case Iop_I64toF64: {
			switch (arg1.lo) {
			case 0:
				/* Round to nearest even mode. */
				union {
					double d;
					unsigned long l;
				} r;
				r.d = (long)arg2.lo;
				dest->lo = (r.l);
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
				union {
					double d;
					long l;
				} r;
				r.l = (long)arg2.lo;
				dest->lo = (unsigned)r.d;
				break;
			default:
				throw NotImplementedException("unknown rounding mode %ld\n",
							      arg1.lo);
			}
			break;
		}

		case Iop_F64toI64: {
			switch (arg1.lo) {
			case 3:
				union {
					double d;
					unsigned long l;
				} r;
				r.l = arg2.lo;
				dest->lo = (r.d);
				break;
			default:
				throw NotImplementedException("unknown rounding mode %ld\n",
							      arg1.lo);
			}
			break;
		}

		case Iop_F64toF32: {
			union {
				double d;
				unsigned long l;
			} in;
			union {
				float f;
				unsigned l;
			} out;
			in.l = arg2.lo;
			out.f = in.d;
			dest->lo = (out.l);
			break;
		}

		case Iop_CmpF64: {
			union {
				double d;
				unsigned long l;
			} r1, r2;
			r1.l = arg1.lo;
			r2.l = arg2.lo;
			double a1 = r1.d;
			double a2 = r2.d;
			unsigned long r;
			if (a1 < a2)
				r = 1;
			else if (a1 == a2)
				r = 0x40;
			else if (a1 > a2)
				r = 0;
			else
				r = 0x45;
			dest->lo = (r);
			break;
		}

		case Iop_SinF64: {
			union {
				unsigned long l;
				double d;
			} in, out;
			in.l = arg2.lo;
			asm ("fsin\n"
			     : "=t" (out.d)
			     : "0" (in.d));
			dest->lo = (out.l);
			break;
		}

		case Iop_CosF64: {
			union {
				unsigned long l;
				double d;
			} in, out;
			in.l = arg2.lo;
			asm ("fcos\n"
			     : "=t" (out.d)
			     : "0" (in.d));
			dest->lo = (out.l);
			break;
		}

		case Iop_SetV128lo64:
			dest->hi = arg1.hi;
			dest->lo = arg2.lo;
			break;

#define _F0x2op(name, op)						\
			case Iop_ ## name ## 64F0x2: {			\
				union {					\
					unsigned long l;		\
					double d;			\
				} in1, in2, out;			\
				in1.l = arg1.lo;			\
				in2.l = arg2.lo;			\
				out.d = op;				\
				dest->lo = (out.l);		\
				break;					\
			}
#define F0x2op(name, op) _F0x2op(name, in1.d op in2.d)

#define _F0x4op(name, op)						\
			case Iop_ ## name ## 32F0x4: {			\
				union {					\
					unsigned l;			\
					float d;			\
				} in1, in2, out;			\
				in1.l = arg1.lo;			\
				in2.l = arg2.lo;			\
				out.d = op;				\
				dest->lo =				\
					(arg1.lo & (0xffffffff00000000ul)) | \
					(out.l);		\
				break;					\
			}
#define F0x4op(name, op) _F0x4op(name, in1.d op in2.d)

#define doit(op, _op)						\
			op(Add, +)		                \
			op(Sub, -)	                        \
			op(Div, /)	                        \
			op(Mul, *)			        \
			_op(Max, in1.d > in2.d ? in1.d : in2.d)	\
			_op(Min, in1.d > in2.d ? in1.d : in2.d)	\
			_op(CmpEQ, in1.d == in2.d)		\
			_op(CmpLT, in1.d < in2.d)		\
			_op(CmpLE, in1.d <= in2.d)
		doit(F0x2op, _F0x2op)
		doit(F0x4op, _F0x4op)
#undef doit
#undef F0x2op
#undef _F0x2op
#undef F0x4op
#undef _F0x4op
#undef _F0xYop
			
		default:
			printf("WARNING: can't handle ");
			ppIRExpr(expr);
			printf("\n");
			if (arg1.lo)
				*dest = arg1;
			else
				*dest = arg2;
			break;
		}

		IRType t, ign1, ign2, ign3, ign4;
		typeOfPrimop(expr->Iex.Binop.op, &t, &ign1, &ign2, &ign3, &ign4);
		switch (t) {
		case Ity_I1:
			dest->lo &= 1ul;
			break;
		case Ity_I8:
			dest->lo &= 0xfful;
			break;
		case Ity_I16:
			dest->lo &= 0xfffful;
			break;
		case Ity_I32:
			dest->lo &= 0xfffffffful;
			break;
		case Ity_I64:
			break;

		case Ity_F32:
		case Ity_F64:
			break;

		case Ity_I128:
		case Ity_V128:
			break;

		default:
			throw NotImplementedException();
		}
		break;
	}

	case Iex_Unop: {
		struct expression_result arg = eval_expression(expr->Iex.Unop.arg);
		switch (expr->Iex.Unop.op) {
		case Iop_64HIto32:
			dest->lo = arg.lo >> 32ul;
			break;
		case Iop_64to32:
			dest->lo = arg.lo & 0xfffffffful;
			break;
		case Iop_64to16:
		case Iop_32to16:
			dest->lo = arg.lo & 0xfffful;
			break;
		case Iop_64to8:
		case Iop_32to8:
		case Iop_16to8:
			dest->lo = arg.lo & 0xfful;
			break;
		case Iop_128to64:
		case Iop_V128to64:
			dest->lo = arg.lo;
			break;
		case Iop_32UtoV128:
		case Iop_64UtoV128:
			dest->lo = arg.lo;
			break;
		case Iop_64to1:
			dest->lo = arg.lo & 1ul;
			break;
		case Iop_32Uto64:
		case Iop_16Uto64:
		case Iop_16Uto32:
		case Iop_1Uto64:
		case Iop_1Uto8:
		case Iop_8Uto16:
		case Iop_8Uto32:
		case Iop_8Uto64:
		case Iop_ReinterpF64asI64:
		case Iop_ReinterpI64asF64:
		case Iop_ReinterpF32asI32:
		case Iop_ReinterpI32asF32:
			*dest = arg;
			break;
		case Iop_8Sto16:
			dest->lo = signed_shift_right(arg.lo << 56ul, 56ul) & 0xfffful;
			break;
		case Iop_8Sto32:
			dest->lo = signed_shift_right(arg.lo << 56ul, 56ul) & 0xfffffffful;
			break;
		case Iop_8Sto64:
			dest->lo = signed_shift_right(arg.lo << 56ul, 56ul);
			break;
		case Iop_16Sto32:
			dest->lo = signed_shift_right(arg.lo << 48ul, 48ul) & 0xfffffffful;
			break;
		case Iop_16Sto64:
			dest->lo = signed_shift_right(arg.lo << 48ul, 48ul);
			break;
		case Iop_32Sto64:
			dest->lo = signed_shift_right(arg.lo << 32ul, 32ul);
			break;
		case Iop_128HIto64:
		case Iop_V128HIto64:
			dest->lo = arg.hi;
			break;

		case Iop_I32toF64: {
			union {
				long l;
				double d;
			} out;
			out.d = (int)arg.lo;
			dest->lo = (out.l);
			break;
		}

		case Iop_F32toF64: {
			union {
				float f;
				int l;
			} in;
			union {
				double d;
				unsigned long l;
			} out;
			in.l = arg.lo;
			out.d = in.f;
			dest->lo = (out.l);
			break;
		}

		case Iop_Not1:
			dest->lo = !arg.lo;
			break;

		case Iop_Not32:
			dest->lo = ~arg.lo & 0xfffffffful;
			break;

		case Iop_Not64:
			dest->lo = ~arg.lo;
			break;

		case Iop_NotV128:
			dest->lo = ~arg.lo;
			dest->hi = ~arg.hi;
			break;
			
		case Iop_Clz64: {
			unsigned long v = arg.lo;
			unsigned res = 0;
			while (!(v & (1ul << (63 - res))) &&
			       res < 63)
				res++;
			dest->lo = (res);
			break;
		}

		case Iop_Ctz64: {
			unsigned long v = arg.lo;
			unsigned res = 0;
			while (!(v & (1ul << res)) &&
			       res < 63)
				res++;
			dest->lo = (res);
			break;
		}

		case Iop_Sqrt64F0x2: {
			union {
				unsigned long l;
				double d;
			} in, out;
			in.l = arg.lo;
			asm ("fsqrt\n"
			     : "=t" (out.d)
			     : "0" (in.d));
			dest->lo = (out.l);
			break;
		}

		default:
			printf("WARNING: can't handle ");
			ppIRExpr(expr);
			printf("; guessing\n");
			*dest = arg;
			break;
		}
		break;
	}

	case Iex_Triop: {
		struct expression_result arg1 = eval_expression(expr->Iex.Triop.arg1);
		struct expression_result arg2 = eval_expression(expr->Iex.Triop.arg2);
		struct expression_result arg3 = eval_expression(expr->Iex.Triop.arg3);
		switch (expr->Iex.Triop.op) {
		case Iop_PRemF64: {
			union {
				double d;
				unsigned long l;
			} a1, a2, res;
			a1.l = arg2.lo;
			a2.l = arg3.lo;
			asm ("fprem\n"
			     : "=t" (res.d)
			     : "0" (a1.d), "u" (a2.d));
			dest->lo = (res.l);
			break;
		}
		case Iop_PRemC3210F64: {
			union {
				double d;
				unsigned long l;
			} a1, a2, clobber;
			unsigned short res;
			a1.l = arg2.lo;
			a2.l = arg3.lo;
			asm ("fprem\nfstsw %%ax\n"
			     : "=t" (clobber.d), "=a" (res)
			     : "0" (a1.d), "u" (a2.d));
			dest->lo =
				((res >> 8) & 7) | ((res & 0x400) >> 11);
			break;
		}
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
		if (cond.lo == 0ul) {
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

	if (loud_mode) {
		printf("eval ");
		ppIRExpr(expr);
		printf(" -> %s\n", dest->name());
	}

	return res;
}

void
Thread::redirectGuest(unsigned long rip)
{
	if (rip == 0x4382f8)
		inInfrastructure = true;
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
	mutable UChar cache[16];
	mutable unsigned long cache_start;
	mutable bool have_cache;
public:
	virtual UChar operator[](unsigned long idx) const
	{
		unsigned long desired = idx + offset;
		if (have_cache && desired >= cache_start && desired < cache_start + sizeof(cache))
			return cache[desired - cache_start];
		cache_start = desired;
		unsigned long v[16];
		aspace->readMemory(desired, 16, v, false, NULL);
		for (unsigned x = 0; x < sizeof(cache); x++)
			cache[x] = v[x];
		have_cache = true;
		return cache[0];
	}
	AddressSpaceGuestFetcher(AddressSpace *_aspace,
				 unsigned long _offset) :
		GuestMemoryFetcher(_offset),
		aspace(_aspace),
		offset(_offset),
		cache_start(0),
		have_cache(false)
	{
	}
};

IRSB *
AddressSpace::getIRSBForAddress(unsigned long rip)
{
	if (rip == ASSERT_FAILED_ADDRESS)
		throw ForceFailureException(rip);

	WeakRef<IRSB> *cacheSlot = searchDecodeCache(rip);
	assert(cacheSlot != NULL);
	IRSB *irsb = cacheSlot->get();
	if (!irsb) {
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
		AddressSpaceGuestFetcher fetcher(this, rip);
		irsb = bb_to_IR(&vge,
				NULL, /* Context for chase_into_ok */
				disInstr_AMD64,
				fetcher,
				(Addr64)rip,
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

		cacheSlot->set(irsb);
	}

	return irsb;
}

void
Thread::translateNextBlock(VexPtr<Thread > &ths,
				VexPtr<AddressSpace > &addrSpace,
				VexPtr<MachineState > &ms,
				const LogReaderPtr &ptr,
				unsigned long rip,
				GarbageCollectionToken t)
{
	ths->redirectGuest(rip);

	if (ths->currentIRSBRip == 0xc822b0)
		ths->inInfrastructure = false;

	if (ths->decode_counter != 0 && !ths->inInfrastructure)
		ths->controlLog.push(Thread::control_log_entry(ths->currentIRSBRip, ths->currentIRSBOffset));


	ths->decode_counter++;

	if (ths->decode_counter % 10000 == 0) {
		ths->snapshotLog.push(Thread::snapshot_log_entry(ms, ptr));
		ms = ms->dupeSelf();
	}

	ths->currentIRSBRip = rip;

	unsigned long _rip = rip;
	vexSetAllocModeTEMP_and_clear(t);

	IRSB *irsb = addrSpace->getIRSBForAddress(_rip);

	ths->temporaries.setSize(irsb->tyenv->types_used);

	ths->currentIRSB = irsb;
	ths->currentIRSBOffset = 0;

	if (loud_mode)
		ppIRSB(irsb);

	/* First statement in block should be a mark */
	assert(ths->currentIRSB->stmts[0]->tag == Ist_IMark);
	/* Should be a mark for the IRSB rip */
	assert(ths->currentIRSB->stmts[0]->Ist.IMark.addr ==
	       ths->currentIRSBRip);
}

unsigned long
extract_call_follower(IRSB *irsb)
{
	/* We expect a call to look like this:

	   0:   ------ IMark(0x7fde5bdd85a7, 5) ------
	   1:   t0 = Sub64(GET:I64(32),0x8:I64)
	   2:   PUT(32) = t0
	   3:   STle(t0) = 0x7fde5bdd85ac:I64
	   4:   t1 = 0x7fde5be62750:I64
	   5:   ====== AbiHint(Sub64(t0,0x80:I64), 128, t1) ======
	   goto {Call} 0x7fde5be62750:I64
   
	   Or so.  The WrTmp at statement 4 is optional, but the rest
	   has to be there.  We process statements in reverse order
	   from the end, checking that things match as we go. */
	int idx = irsb->stmts_used - 1;

	if (idx < 0 ||
	    irsb->stmts[idx]->tag != Ist_AbiHint)
		abort();
	idx--;
	if (idx < 0)
		abort();
	if (irsb->stmts[idx]->tag == Ist_WrTmp)
		idx--;
	if (idx < 0)
		abort();
	if (irsb->stmts[idx]->tag != Ist_Store)
		abort();
	if (irsb->stmts[idx]->Ist.Store.data->tag != Iex_Const)
		abort();
	return irsb->stmts[idx]->Ist.Store.data->Iex.Const.con->Ico.U64;
}

ThreadEvent *
Thread::runToEvent(VexPtr<Thread > &ths,
		   VexPtr<MachineState > &ms,
		   const LogReaderPtr &ptr,
		   GarbageCollectionToken t,
		   VexPtr<EventRecorder> &er)
{
	unsigned put_offset;
	struct expression_result put_data;
	IRType put_type;

	while (1) {
		if (!ths->currentIRSB) {
			try {
				VexPtr<AddressSpace > as(ms->addressSpace);
			        ths->translateNextBlock(ths, as, ms, ptr, ths->regs.rip(), t);
			} catch (BadMemoryException excn) {
				return SignalEvent::get(ths->tid, 11, excn.ptr);
			} catch (ForceFailureException ffe) {
				return new DetectedErrorEvent(ths->tid, ffe.rip);
			}
			assert(ths->currentIRSB);
		}
		while (ths->currentIRSBOffset < ths->currentIRSB->stmts_used) {
			IRStmt *stmt = ths->currentIRSB->stmts[ths->currentIRSBOffset];
			ths->currentIRSBOffset++;

			switch (stmt->tag) {
			case Ist_NoOp:
				break;
			case Ist_IMark:
				ths->regs.set_reg(REGISTER_IDX(RIP),
						  (stmt->Ist.IMark.addr));
				er->instruction(ths,
						ths->regs.get_reg(REGISTER_IDX(RIP)),
						ms);
				return NULL;
			case Ist_AbiHint:
				break;
			case Ist_MBE:
				break;
			case Ist_WrTmp:
				ths->temporaries[stmt->Ist.WrTmp.tmp] =
					ths->eval_expression(stmt->Ist.WrTmp.data);
				DBG("wrtmp %d -> %s",
				    stmt->Ist.WrTmp.tmp,
				    ths->temporaries[stmt->Ist.WrTmp.tmp].name());
				break;

			case Ist_Store: {
				assert(stmt->Ist.Store.end == Iend_LE);
				assert(stmt->Ist.Store.resSC == IRTemp_INVALID);
				struct expression_result data =
					ths->eval_expression(stmt->Ist.Store.data);
				struct expression_result addr =
					ths->eval_expression(stmt->Ist.Store.addr);
				unsigned size = sizeofIRType(typeOfIRExpr(ths->currentIRSB->tyenv,
									  stmt->Ist.Store.data));
				if (ms->addressSpace->isWritable(addr.lo, size, ths)) {
					DBG("Store %s to %s\n", data.name(), addr.name());
					er->store(ths, addr.lo, data.lo);
					return StoreEvent::get(ths->tid, addr.lo, size, data);
				}
				return SignalEvent::get(ths->tid, 11, addr.lo);
			}

			case Ist_CAS: {
				assert(stmt->Ist.CAS.details->oldHi == IRTemp_INVALID);
				assert(stmt->Ist.CAS.details->expdHi == NULL);
				assert(stmt->Ist.CAS.details->dataHi == NULL);
				assert(stmt->Ist.CAS.details->end == Iend_LE);
				struct expression_result data =
					ths->eval_expression(stmt->Ist.CAS.details->dataLo);
				struct expression_result addr =
					ths->eval_expression(stmt->Ist.CAS.details->addr);
				struct expression_result expected =
					ths->eval_expression(stmt->Ist.CAS.details->expdLo);
				unsigned size = sizeofIRType(typeOfIRExpr(ths->currentIRSB->tyenv,
									  stmt->Ist.CAS.details->dataLo));
				return CasEvent::get(ths->tid, stmt->Ist.CAS.details->oldLo, addr, data, expected, size);
			}

			case Ist_Put: {
				put_offset = stmt->Ist.Put.offset;
				put_data = ths->eval_expression(stmt->Ist.Put.data);
				put_type = typeOfIRExpr(ths->currentIRSB->tyenv, stmt->Ist.Put.data);
				do_put:
				DBG("put offset %d type %d -> %s",
				    put_offset, put_type, put_data.name());
				unsigned byte_offset = put_offset & 7;
				unsigned long dest = read_reg(&*ths, put_offset - byte_offset);
				switch (put_type) {
				case Ity_I8:
					dest &= ~(0xFF << (byte_offset * 8));
					dest |= put_data.lo << (byte_offset * 8);
					break;

				case Ity_I16:
					assert(!(byte_offset % 2));
					dest &= ~(0xFFFFul << (byte_offset * 8));
					dest |= put_data.lo << (byte_offset * 8);
					break;

				case Ity_I32:
				case Ity_F32:
					assert(!(byte_offset % 4));
					dest &= ~(0xFFFFFFFFul << (byte_offset * 8));
					dest |= put_data.lo << (byte_offset * 8);
					break;

				case Ity_I64:
				case Ity_F64:
					assert(byte_offset == 0);
					dest = put_data.lo;
					break;

				case Ity_I128:
				case Ity_V128:
					assert(byte_offset == 0);
					dest = put_data.lo;
					write_reg(&*ths,
						  put_offset + 8,
						  put_data.hi);
					break;
				default:
					ppIRStmt(stmt);
					throw NotImplementedException();
				}

				write_reg(&*ths, put_offset - byte_offset, dest);
				break;
			}

			case Ist_PutI: {
				struct expression_result idx = ths->eval_expression(stmt->Ist.PutI.ix);

				/* Crazy bloody encoding scheme */
				idx.lo =
					((idx.lo + stmt->Ist.PutI.bias) %
					 stmt->Ist.PutI.descr->nElems) *
					sizeofIRType(stmt->Ist.PutI.descr->elemTy) +
					stmt->Ist.PutI.descr->base;

				put_offset = idx.lo;
				put_data = ths->eval_expression(stmt->Ist.PutI.data);
				put_type = stmt->Ist.PutI.descr->elemTy;
				goto do_put;
			}

			case Ist_Dirty: {
				ThreadEvent *evt = ths->do_dirty_call(stmt->Ist.Dirty.details, ms, er);
				if (evt)
					return evt;
				break;
			}

			case Ist_Exit: {
				if (stmt->Ist.Exit.guard) {
					struct expression_result guard =
						ths->eval_expression(stmt->Ist.Exit.guard);
					if (!guard.lo)
						break;
				}
				if (stmt->Ist.Exit.jk != Ijk_Boring) {
					assert(stmt->Ist.Exit.jk == Ijk_EmWarn);
					printf("EMULATION WARNING %lx\n",
					       ths->regs.get_reg(REGISTER_IDX(EMWARN)));
				}
				assert(stmt->Ist.Exit.dst->tag == Ico_U64);
				ths->regs.set_reg(REGISTER_IDX(RIP),
						  stmt->Ist.Exit.dst->Ico.U64);
				ths->currentIRSB = NULL;
				goto finished_block;
			}

			default:
				printf("Don't know how to interpret statement ");
				ppIRStmt(stmt);
				throw NotImplementedException();
			}
		}

		ths->currentIRSBOffset++;
		
		assert(ths->currentIRSB->jumpkind == Ijk_Boring ||
		       ths->currentIRSB->jumpkind == Ijk_Call ||
		       ths->currentIRSB->jumpkind == Ijk_Ret ||
		       ths->currentIRSB->jumpkind == Ijk_Sys_syscall ||
		       ths->currentIRSB->jumpkind == Ijk_Yield ||
		       ths->currentIRSB->jumpkind == Ijk_ClientReq);

		/* Yields are boring, and the only kind of clientreq
		   which we support is changing thread priority, which
		   is equally boring. */
		if (ths->currentIRSB->jumpkind == Ijk_Yield ||
		    ths->currentIRSB->jumpkind == Ijk_ClientReq)
			ths->currentIRSB->jumpkind = Ijk_Boring;

		{
			bool is_syscall = ths->currentIRSB->jumpkind == Ijk_Sys_syscall;
			{
				struct expression_result next_addr =
					ths->eval_expression(ths->currentIRSB->next);
				ths->regs.set_reg(REGISTER_IDX(RIP),
						  next_addr.lo);
				if (ths->currentIRSB->jumpkind == Ijk_Ret) {
					/* Because of longjmp() etc.,
					   the return address won't
					   necessarily be the top
					   thing on the stack.
					   Account for that. */
					int x;
					for (x = ths->currentCallStack.size() - 1;
					     x >= 0;
					     x--) {
						if (ths->currentCallStack[x] ==
						    ths->regs.rip()) {
							ths->currentCallStack.resize(x);
							break;
						}
					}
					if (x == -1) {
						printf("WARNING: couldn't find where to return to (looking for %lx, stack [",
						       ths->regs.rip());
						for (int x = 0;
						     x < (int)ths->currentCallStack.size();
						     x++)
							printf("%lx ", ths->currentCallStack[x]);
						printf("])\n");
						ths->currentCallStack.clear();
					}
				} else if (ths->currentIRSB->jumpkind == Ijk_Call) {
					ths->currentCallStack.push_back(
						extract_call_follower(ths->currentIRSB));
				}
				ths->currentIRSB = NULL;
			}
			if (is_syscall)
				return SyscallEvent::get(ths->tid);
		}

finished_block:
		;
	}
}

void Interpreter::replayLogfile(VexPtr<LogReader> &lf,
				LogReaderPtr ptr,
				GarbageCollectionToken t,
				LogReaderPtr *eof,
				VexPtr<LogWriter> &lw,
				VexPtr<EventRecorder> &er)
{
	unsigned long event_counter = 0;
	VexPtr<LogRecord> lr;
	bool appendedRecord = false;
	bool finished = false;
	LogReaderPtr ptr2 = ptr;

	/* Memory records are special and should always be
	   processed eagerly. */
	{
		VexPtr<AddressSpace > as(currentState->addressSpace);
		process_memory_records(as, lf, ptr, &ptr, lw, t);
		if (eof)
			*eof = ptr;
		ptr2 = ptr;
	}

	while (!finished) {
		event_counter++;
		if (event_counter % 100000 == 0)
			printf("event %ld\n", event_counter);

		if (!lr) {
			lr = lf->read(ptr, &ptr);
			appendedRecord = false;
		}
		if (!lr)
			break;

		if (loud_mode)
			printf("lr %s\n", lr->name());

		VexPtr<Thread > thr(currentState->findThread(lr->thread()));
		assert(thr);
		assert(!thr->exitted);
		ThreadEvent *evt = thr->runToEvent(thr, currentState, ptr2, t, er);

		while (evt && lr) {
			if (loud_mode)
				printf("Event %s in thread %d, lr %s\n",
				       evt->name(), lr->thread()._tid(),
				       lr->name());

			ThreadEvent *oldEvent = evt;
			bool consumed = true;
			evt = oldEvent->replay(lr, &currentState.get(), consumed, ptr);
			if (consumed) {
				if (lw && !appendedRecord) {
					lw->append(lr);
					appendedRecord = true;
				}
				if (!lw) {
					if (!er) {
						LibVEX_free(oldEvent);
						oldEvent = NULL;
					}
					LibVEX_free(lr);
				}
				lr = NULL;
				if (eof)
					*eof = ptr;
				ptr2 = ptr;
				if (evt) {
					appendedRecord = false;
					lr = lf->read(ptr, &ptr);
				}
			}

			if (!er && oldEvent)
				LibVEX_free(oldEvent);
		}

		if (!lr) {
			/* Memory records are special and should always be
			   processed eagerly. */
			VexPtr<AddressSpace > as(currentState->addressSpace);
	                process_memory_records(as, lf, ptr, &ptr, lw, t);
			if (eof)
				*eof = ptr;
			ptr2 = ptr;
	        }
	}
	printf("Done replay, counter %ld\n", event_counter);
}

#define MK_INTERPRETER(t)
