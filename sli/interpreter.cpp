#include <string.h>
#include <asm/unistd.h>
#include <sys/time.h>

#include "sli.h"

#include "libvex.h"
#include "libvex_ir.h"
#include "libvex_emwarn.h"
#include "libvex_guest_amd64.h"
#include "guest_generic_bb_to_IR.h"
#include "guest_generic_x87.h"
#include "guest_amd64_defs.h"
#include "main_util.h"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"

#define FOOTSTEP_REGS_ONLY
#include "ppres.h"

#include "sli.h"

static bool loud_mode;

static Bool chase_into_ok(void *, Addr64 )
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
write_reg(RegisterSet *regs, unsigned offset, unsigned long val)
{
	assert(!(offset % 8));
	regs->set_reg(offset / 8, val);
}

static unsigned long
read_reg(const RegisterSet *state, unsigned offset)
{
	assert(!(offset % 8));
	return state->get_reg(offset / 8);
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
Thread::amd64g_dirtyhelper_loadF80le(MachineState *ms, threadAndRegister tmp, unsigned long addr)
{
	unsigned long buf[10];
	ms->addressSpace->readMemory(addr, 10, buf, false, this, NULL);
	UChar buf2[10];
	for (unsigned x = 0; x < 10; x++)
		buf2[x] = buf[x];
	ULong f64;
	convert_f80le_to_f64le(buf2, (UChar*)&f64);
	if (tmp.isTemp()) {
		temporaries[tmp.asTemp()].lo = f64;
		temporaries[tmp.asTemp()].hi = 0ul;
	} else {
		write_reg(&regs, tmp.asReg(), f64);
	}
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
Thread::do_load(threadAndRegister tmp, unsigned long addr, unsigned size, MachineState *ms,
		EventRecorder *er, ReplayEngineTimer &ret)
{
	if (ms->addressSpace->isReadable(addr, size, this)) {
		if (er) {
			ret.suspend();
			er->load(this, addr);
			ret.unsuspend();
		}
		return LoadEvent::get(tid, tmp, addr, size);
	} else
		return SignalEvent::get(tid, 11, addr);
}

ThreadEvent *
Thread::do_dirty_call(IRDirty *details, MachineState *ms, EventRecorder *er, ReplayEngineTimer &ret)
{
	struct expression_result args[6];
	unsigned x;

	if (details->guard) {
		expression_result guard = eval_expression(&regs, details->guard, temporaries.content);
		if (!guard.lo)
			return NULL;
	}
	for (x = 0; details->args[x]; x++) {
		assert(x < 6);
		args[x] = eval_expression(&regs, details->args[x], temporaries.content);
	}
	assert(!details->cee->regparms);

	if (!strcmp(details->cee->name, "amd64g_dirtyhelper_RDTSC")) {
		return RdtscEvent::get(tid, details->tmp);
	} else if (!strcmp(details->cee->name, "helper_load_8")) {
		return do_load(details->tmp, args[0].lo, 1, ms, er, ret);
	} else if (!strcmp(details->cee->name, "helper_load_16")) {
		return do_load(details->tmp, args[0].lo, 2, ms, er, ret);
	} else if (!strcmp(details->cee->name, "helper_load_32")) {
		return do_load(details->tmp, args[0].lo, 4, ms, er, ret);
	} else if (!strcmp(details->cee->name, "helper_load_64")) {
		return do_load(details->tmp, args[0].lo, 8, ms, er, ret);
	} else if (!strcmp(details->cee->name, "helper_load_128")) {
		return do_load(details->tmp, args[0].lo, 16, ms, er, ret);
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

static expression_result
do_ccall_calculate_condition(struct expression_result *args)
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

static expression_result
do_ccall_calculate_rflags_c(expression_result *args)
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

static expression_result
do_ccall_generic(IRCallee *cee,
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

static expression_result
do_ccall(const RegisterSet *rs, IRCallee *cee, IRExpr **args, const std::vector<expression_result> &temporaries)
{
	struct expression_result rargs[6];
	unsigned x;

	assert(cee->regparms == 0);
	for (x = 0; args[x]; x++) {
		assert(x < 6);
		rargs[x] = eval_expression(rs, args[x], temporaries);
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
eval_expression(const RegisterSet *rs,
		IRExpr *expr,
		const std::vector<expression_result> &temporaries)
{
	struct expression_result res;
	struct expression_result *dest = &res;
	unsigned getOffset;
	IRType getType;

	res.lo = 0ul;
	res.hi = 0ul;
	
	switch (expr->tag) {
	case Iex_Get: {
		{
			IRExprGet *e = (IRExprGet *)expr;
			if (e->reg.isTemp()) {
				*dest = temporaries[e->reg.asTemp()];
				break;
			}
			getOffset = e->reg.asReg();
			getType = e->ty;
		}

		do_get:
		unsigned long v1;
		unsigned sub_word_offset = getOffset & 7;
		v1 = read_reg(rs, getOffset - sub_word_offset);
		switch (getType) {
		case Ity_I64:
			assert(!sub_word_offset);
			dest->lo = v1;
			break;
		case Ity_I128:
			assert(!sub_word_offset);
			dest->lo = v1;
			dest->hi = read_reg(rs, getOffset - sub_word_offset + 8);
			break;
		case Ity_I32:
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
			ppIRExpr(expr, stderr);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_GetI: {
		IRExprGetI *e = (IRExprGetI *)expr;
		getOffset = eval_expression(rs, e->ix, temporaries).lo;
		getOffset += e->bias;
		getOffset %= e->descr->nElems;
		getOffset *= sizeofIRType(e->descr->elemTy);
		getOffset += e->descr->base;
		getType = e->descr->elemTy;
		goto do_get;
	}

	case Iex_Load:
		throw SliException("transform_expr failed to remove all load expressions\n");

	case Iex_Const: {
		IRExprConst *cnst = (IRExprConst *)expr;
		switch (cnst->ty) {
		case Ity_I1:
			dest->lo = (cnst->Ico.U1);
			break;
		case Ity_I8:
			dest->lo = (cnst->Ico.U8);
			break;
		case Ity_I16:
			dest->lo = (cnst->Ico.U16);
			break;
		case Ity_I32:
			dest->lo = (cnst->Ico.U32);
			break;
		case Ity_I64:
			dest->lo = (cnst->Ico.U64);
			break;
		case Ity_I128:
			dest->lo = cnst->Ico.U128.lo;
			dest->lo = cnst->Ico.U128.hi;
			break;
		default:
			ppIRExpr(expr, stderr);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_Binop: {
		IRExprBinop *e = (IRExprBinop *)expr;
		struct expression_result arg1 = eval_expression(rs, e->arg1, temporaries);
		struct expression_result arg2 = eval_expression(rs, e->arg2, temporaries);
		switch (e->op) {
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
			if (arg1.lo == 0 || 1) {
				dlo = dhi = 0;
			} else {
				asm ("div %4\n"
				     : "=a" (dlo), "=d" (dhi)
				     : "0" (arg1.lo), "1" (arg1.hi), "r" (arg2.lo));
			}
			dest->lo = (dlo);
			dest->hi = (dhi);
			break;
		}

		case Iop_DivModS128to64: {
			unsigned long dlo;
			unsigned long dhi;
			if (arg1.lo == 0 || 1) {
				dlo = dhi = 0;
			} else {
				asm ("idiv %4\n"
				     : "=a" (dlo), "=d" (dhi)
				     : "0" (arg1.lo), "1" (arg1.hi), "r" (arg2.lo));
			}
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
		        ppIRExpr(expr, stdout);
			printf("\n");
			if (arg1.lo)
				*dest = arg1;
			else
				*dest = arg2;
			break;
		}

		IRType t, ign1, ign2, ign3, ign4;
		typeOfPrimop(e->op, &t, &ign1, &ign2, &ign3, &ign4);
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

		case Ity_I128:
			break;

		default:
			throw NotImplementedException();
		}
		break;
	}

	case Iex_Unop: {
		IRExprUnop *e = (IRExprUnop *)expr;
		struct expression_result arg = eval_expression(rs, e->arg, temporaries);
		switch (e->op) {
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
			ppIRExpr(expr, stdout);
			printf("; guessing\n");
			*dest = arg;
			break;
		}
		break;
	}

	case Iex_Triop: {
		IRExprTriop *e = (IRExprTriop *)expr;
		struct expression_result arg1 = eval_expression(rs, e->arg1, temporaries);
		struct expression_result arg2 = eval_expression(rs, e->arg2, temporaries);
		struct expression_result arg3 = eval_expression(rs, e->arg3, temporaries);
		switch (e->op) {
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
			ppIRExpr(expr, stderr);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_Mux0X: {
		IRExprMux0X *e = (IRExprMux0X *)expr;
		struct expression_result cond = eval_expression(rs, e->cond, temporaries);
		struct expression_result res0 = eval_expression(rs, e->expr0, temporaries);
		struct expression_result resX = eval_expression(rs, e->exprX, temporaries);
		if (cond.lo == 0ul) {
			*dest = res0;
		} else {
			*dest = resX;
		}
		break;
	}

	case Iex_CCall: {
		IRExprCCall *e = (IRExprCCall *)expr;
		res = do_ccall(rs, e->cee, e->args, temporaries);
		break;
	}
	  
	case Iex_Associative: {
		IRExprAssociative *e = (IRExprAssociative *)expr;
		switch (e->op) {
#define do_op(name, operator, base)					\
	        case Iop_ ## name ## 8:	   			        \
		case Iop_ ## name ## 16:				\
		case Iop_ ## name ## 32:				\
		case Iop_ ## name ## 64:				\
			dest->lo = base;				\
		        for (int x = 0;					\
			     x < e->nr_arguments;	\
			     x++) {					\
				struct expression_result a =		\
					eval_expression(		\
						rs,			\
						e->contents[x], \
						temporaries);		\
				dest->lo = dest->lo operator a.lo;	\
			}						\
			break
			do_op(Add, +, 0);
		case Iop_Or1:
			do_op(Or, |, 0);
		case Iop_Xor1:
			do_op(Xor, ^, 0);
		case Iop_And1:
			do_op(And, &, 0xfffffffffffffffful);
#undef do_op
		default:
			ppIRExpr(expr, stderr);
			throw NotImplementedException("Associative op %d\n", e->op);
		}
		break;
	}
	default:
		ppIRExpr(expr, stderr);
		throw NotImplementedException("Bad expression tag %x\n", expr->tag);
	}

	if (loud_mode) {
		printf("eval ");
		ppIRExpr(expr, stdout);
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
				 const ThreadRip &_offset) :
		GuestMemoryFetcher(_offset),
		aspace(_aspace),
		offset(_offset.rip.unwrap_vexrip()),
		cache_start(0),
		have_cache(false)
	{
	}
};

class DecodeCache : public GarbageCollected<DecodeCache, &ir_heap> {
	class DecodeCacheEntry : public GarbageCollected<DecodeCacheEntry, &ir_heap> {
	public:
		DecodeCacheEntry *next;
		ThreadRip key;
		IRSB *irsb;

		void visit(HeapVisitor &) { abort(); }

		NAMED_CLASS
	};

	static const unsigned nr_slots = 2053;
	DecodeCacheEntry *slots[nr_slots];
	static unsigned long rip_hash(const ThreadRip &tr)
	{
		unsigned long hash = tr.hash();
		while (hash >= nr_slots)
			hash = (hash % nr_slots) ^ (hash / nr_slots);
		return hash;
	}

public:
	IRSB **search(const ThreadRip &tr);

	void visit(HeapVisitor &) { abort(); }
	NAMED_CLASS
};
IRSB **
DecodeCache::search(const ThreadRip &tr)
{
	DecodeCacheEntry **pdce, *dce;
	unsigned hash = rip_hash(tr);
	pdce = &slots[hash];
	while (*pdce && (*pdce)->key != tr)
		pdce = &(*pdce)->next;
	dce = *pdce;
	if (dce) {
		*pdce = dce->next;
	} else {
		dce = new DecodeCacheEntry();
		dce->key = tr;
	}
	dce->next = slots[hash];
	slots[hash] = dce;
	return &dce->irsb;
}

static VexPtr<WeakRef<DecodeCache, &ir_heap>, &ir_heap> decode_cache;

/* Do some very basic optimisations directly on the IRSB, to keep
   everything else a bit simpler.  This relies on the fact that IRSBs
   are single-entry. */
static void
optimiseIRSB(IRSB *irsb)
{
	irsb->sanity_check();
	/* First, basic copy propagation. */
	std::map<threadAndRegister, IRExpr *> tmps;
	struct : public IRExprTransformer {
		std::map<threadAndRegister, IRExpr *> *tmps;
		IRExpr *transformIex(IRExprGet *what) {
			auto it = tmps->find(((IRExprGet *)what)->reg);
			if (it == tmps->end() || what->type() > it->second->type())
				return what;
			else
				return coerceTypes(what->type(), it->second);
		}
		void operator()(IRExpr **k) {
			if (*k)
				*k = doit(*k);
		}
	} useTmps;
	useTmps.tmps = &tmps;
	struct {
		struct mentionsRegister : public IRExprTransformer {
			const threadAndRegister &tr;
			mentionsRegister(const threadAndRegister &_tr)
				: tr(_tr)
			{}
			IRExpr *transformIex(IRExprGet *ieg) {
				if (ieg->reg == tr)
					abortTransform();
				return ieg;
			}
			bool operator()(IRExpr *a) {
				aborted = false;
				doit(a);
				return aborted;
			}
		};
		std::map<threadAndRegister, IRExpr *> *tmps;
		void operator()(const threadAndRegister &tr) {
			mentionsRegister mr(tr);
			for (auto it = tmps->begin(); it != tmps->end(); ) {
				if (mr(it->second))
					tmps->erase(it++);
				else
					it++;
			}
		}
	} invalidateTmp = {&tmps};
	for (int i = 0; i < irsb->stmts_used; i++) {
		IRStmt *stmt = irsb->stmts[i];
		stmt->sanity_check();
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			break;
		case Ist_AbiHint:
			useTmps(&((IRStmtAbiHint *)stmt)->base);
			useTmps(&((IRStmtAbiHint *)stmt)->nia);
			break;
		case Ist_Put: {
			IRStmtPut *p = (IRStmtPut *)stmt;
			useTmps(&p->data);
			tmps[p->target] = p->data;
			invalidateTmp(p->target);
			break;
		}
		case Ist_PutI:
			useTmps(&((IRStmtPutI *)stmt)->ix);
			useTmps(&((IRStmtPutI *)stmt)->data);
			break;
		case Ist_Store:
			useTmps(&((IRStmtStore *)stmt)->addr);
			useTmps(&((IRStmtStore *)stmt)->data);
			break;
		case Ist_CAS:
			useTmps(&((IRStmtCAS *)stmt)->details->addr);
			useTmps(&((IRStmtCAS *)stmt)->details->expdLo);
			useTmps(&((IRStmtCAS *)stmt)->details->dataLo);
			invalidateTmp( ((IRStmtCAS *)stmt)->details->oldLo);
			break;
		case Ist_Dirty: {
			IRStmtDirty *d = (IRStmtDirty *)stmt;
			useTmps(&d->details->guard);
			useTmps(&d->details->mAddr);
			for (int i = 0; d->details->args[i]; i++)
				useTmps(&d->details->args[i]);
			invalidateTmp(d->details->tmp);
			break;
		}
		case Ist_MBE:
			break;
		case Ist_Exit:
			useTmps(&((IRStmtExit *)stmt)->guard);
			break;
		case Ist_StartAtomic:
			break;
		case Ist_EndAtomic:
			break;
		}
		stmt->sanity_check();
	}

	if (!irsb->next_is_const)
		useTmps(&irsb->next_nonconst);

	/* Now do deadcode and local IRExpr optimisation. */
	IRStmt *noop = NULL;
	std::set<threadAndRegister> neededRegs;
	struct : public IRExprTransformer {
		std::set<threadAndRegister> *neededRegs;
		IRExpr *transformIex(IRExprGet *ieg) {
			neededRegs->insert(ieg->reg);
			return ieg;
		}
		void operator()(IRExpr **i) {
			if (*i) {
				*i = simplifyIRExpr(*i, AllowableOptimisations::defaultOptimisations);
				doit(*i);
			}
		}
	} useExpr;
	useExpr.neededRegs = &neededRegs;
	if (!irsb->next_is_const)
		useExpr(&irsb->next_nonconst);

	for (int i = irsb->stmts_used - 1; i >= 0; i--) {
		IRStmt *stmt = irsb->stmts[i];
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			break;
		case Ist_AbiHint:
			useExpr(&((IRStmtAbiHint *)stmt)->base);
			useExpr(&((IRStmtAbiHint *)stmt)->nia);
			break;
		case Ist_Put: {
			IRStmtPut *p = (IRStmtPut *)stmt;
			if (p->target.isTemp() && !neededRegs.count(p->target)) {
				if (noop == NULL)
					noop = IRStmt_NoOp();
				irsb->stmts[i] = noop;
			} else {
				neededRegs.erase(p->target);
				useExpr(&p->data);
			}
			break;
		}
		case Ist_PutI:
			useExpr(&((IRStmtPutI *)stmt)->ix);
			useExpr(&((IRStmtPutI *)stmt)->data);
			break;
		case Ist_Store:
			useExpr(&((IRStmtStore *)stmt)->addr);
			useExpr(&((IRStmtStore *)stmt)->data);
			break;
		case Ist_CAS:
			neededRegs.erase(((IRStmtCAS *)stmt)->details->oldLo);
			useExpr(&((IRStmtCAS *)stmt)->details->addr);
			useExpr(&((IRStmtCAS *)stmt)->details->expdLo);
			useExpr(&((IRStmtCAS *)stmt)->details->dataLo);
			break;
		case Ist_Dirty: {
			IRStmtDirty *d = (IRStmtDirty *)stmt;
			neededRegs.erase(d->details->tmp);
			useExpr(&d->details->guard);
			useExpr(&d->details->mAddr);
			for (int i = 0; d->details->args[i]; i++)
				useExpr(&d->details->args[i]);
			break;
		}
		case Ist_MBE:
			break;
		case Ist_Exit:
			useExpr(&((IRStmtExit *)stmt)->guard);
			break;
		case Ist_StartAtomic:
			break;
		case Ist_EndAtomic:
			break;
		}
		stmt->sanity_check();
	}

	/* And now kill off any noop statements. */
	int in = 0;
	int out = 0;
	while (in < irsb->stmts_used) {
		if (irsb->stmts[in]->tag != Ist_NoOp) {
			irsb->stmts[out] = irsb->stmts[in];
			out++;
		}
		in++;
	}
	irsb->stmts_used = out;
}

IRSB *
AddressSpace::getIRSBForAddress(const ThreadRip &tr, bool singleInstr)
{
	unsigned tid = tr.thread;

	if (tr.rip.unwrap_vexrip() == ASSERT_FAILED_ADDRESS)
		throw ForceFailureException(ASSERT_FAILED_ADDRESS);

	if (!decode_cache.get())
		decode_cache.set(new WeakRef<DecodeCache, &ir_heap>());
	DecodeCache *dc = decode_cache.get()->get();
	if (!dc) {
		dc = new DecodeCache();
		decode_cache.get()->set(dc);
	}
	IRSB **cacheSlot = dc->search(tr);
	assert(cacheSlot != NULL);
	IRSB *irsb = *cacheSlot;
	if (!irsb) {
		VexArchInfo archinfo_guest;
		VexAbiInfo abiinfo_both;
		LibVEX_default_VexArchInfo(&archinfo_guest);
		archinfo_guest.hwcaps =
			VEX_HWCAPS_AMD64_SSE3|
			VEX_HWCAPS_AMD64_CX16;
		LibVEX_default_VexAbiInfo(&abiinfo_both);
		abiinfo_both.guest_stack_redzone_size = 128;
		abiinfo_both.guest_amd64_assume_fs_is_zero = 1;
		AddressSpaceGuestFetcher fetcher(this, tr);
		irsb = bb_to_IR(tid,
				NULL, /* Context for chase_into_ok */
				disInstr_AMD64,
				fetcher,
				tr,
				chase_into_ok,
				False, /* host bigendian */
				&archinfo_guest,
				&abiinfo_both,
				False, /* do_self_check */
				NULL,
				singleInstr);
		if (!irsb)
			throw InstructionDecodeFailedException();

		irsb->sanity_check();

		irsb = instrument_func(tid, NULL, irsb, NULL, NULL, Ity_I64, Ity_I64);

		optimiseIRSB(irsb);

		*cacheSlot = irsb;
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
	LibVEX_maybe_gc(t);

	IRSB *irsb = addrSpace->getIRSBForAddress(ThreadRip(ths->tid._tid(), VexRip::invent_vex_rip(_rip)), false);

	ths->temporaries.setSize(irsb->tyenv->types_used);

	ths->currentIRSB.set(irsb);
	ths->currentIRSBOffset = 0;

	if (loud_mode)
		ppIRSB(irsb, stdout);

	/* First statement in block should be a mark */
	assert(ths->currentIRSB->stmts[0]->tag == Ist_IMark);
	/* Should be a mark for the IRSB rip */
	assert(((IRStmtIMark *)ths->currentIRSB->stmts[0])->addr.rip.unwrap_vexrip() ==
	       ths->currentIRSBRip);
}

VexRip
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
	if (irsb->stmts[idx]->tag == Ist_Put)
		idx--;
	if (idx < 0)
		abort();
	if (irsb->stmts[idx]->tag != Ist_Store)
		abort();
	IRStmtStore *s = (IRStmtStore *)irsb->stmts[idx];
	if (s->data->tag != Iex_Const)
		abort();
	while (idx >= 0 && irsb->stmts[idx]->tag != Ist_IMark)
		idx--;
	assert(idx >= 0);
	VexRip r( ((IRStmtIMark *)irsb->stmts[idx])->addr.rip );
	r.jump(((IRExprConst *)s->data)->Ico.U64);
	return r;
}

void
put_stmt(RegisterSet *rs, unsigned put_offset, struct expression_result put_data, IRType put_type)
{
	unsigned byte_offset = put_offset & 7;
	unsigned long dest = read_reg(rs, put_offset - byte_offset);
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
		assert(!(byte_offset % 4));
		dest &= ~(0xFFFFFFFFul << (byte_offset * 8));
		dest |= put_data.lo << (byte_offset * 8);
		break;

	case Ity_I64:
		assert(byte_offset == 0);
		dest = put_data.lo;
		break;

	case Ity_I128:
		assert(byte_offset == 0);
		dest = put_data.lo;
		write_reg(rs,
			  put_offset + 8,
			  put_data.hi);
		break;
	default:
		throw NotImplementedException();
	}

	write_reg(rs, put_offset - byte_offset, dest);
}

ThreadEvent *
interpretStatement(IRStmt *stmt,
		   Thread *thr,
		   EventRecorder *er,
		   MachineState *ms,
		   ReplayEngineTimer &ret)
{
	switch (stmt->tag) {
	case Ist_NoOp:
		return NULL;

	case Ist_IMark: {
		IRStmtIMark *s = (IRStmtIMark *)stmt;
		thr->regs.set_reg(REGISTER_IDX(RIP),
				  (s->addr.rip.unwrap_vexrip()));
		if (er) {
			ret.suspend();
			er->instruction(thr,
					thr->regs.get_reg(REGISTER_IDX(RIP)),
					ms);
			ret.unsuspend();
		}
		HandleMallocFree(thr, ms->addressSpace);
		return DUMMY_EVENT;
	}
	case Ist_AbiHint:
		return NULL;

	case Ist_MBE:
		return NULL;

	case Ist_Store: {
		IRStmtStore *s = (IRStmtStore *)stmt;
		struct expression_result data =
			eval_expression(&thr->regs, s->data, thr->temporaries.content);
		struct expression_result addr =
			eval_expression(&thr->regs, s->addr, thr->temporaries.content);
		unsigned size = sizeofIRType(s->data->type());
		if (ms->addressSpace->isWritable(addr.lo, size, thr)) {
			if (er) {
				ret.suspend();
				er->store(thr, addr.lo, data.lo, ms);
				ret.unsuspend();
			}
			return StoreEvent::get(thr->tid, addr.lo, size, data);
		}
		return SignalEvent::get(thr->tid, 11, addr.lo);
	}

	case Ist_CAS: {
		IRStmtCAS *s = (IRStmtCAS *)stmt;
		assert(s->details->oldHi.isInvalid());
		assert(s->details->expdHi == NULL);
		assert(s->details->dataHi == NULL);
		struct expression_result data =
			eval_expression(&thr->regs, s->details->dataLo, thr->temporaries.content);
		struct expression_result addr =
			eval_expression(&thr->regs, s->details->addr, thr->temporaries.content);
		struct expression_result expected =
			eval_expression(&thr->regs, s->details->expdLo, thr->temporaries.content);
		unsigned size = sizeofIRType(s->details->dataLo->type());
		return CasEvent::get(thr->tid, s->details->oldLo, addr, data, expected, size);
	}

	case Ist_Put: {
		IRStmtPut *s = (IRStmtPut *)stmt;
		if (s->target.isTemp()) {
			thr->temporaries[s->target.asTemp()] =
				eval_expression(&thr->regs, s->data, thr->temporaries.content);
		} else {
			put_stmt(&thr->regs,
				 s->target.asReg(),
				 eval_expression(&thr->regs, s->data, thr->temporaries.content),
				 s->data->type());
		}
		return NULL;
	}
	case Ist_PutI: {
		IRStmtPutI *s = (IRStmtPutI *)stmt;
		struct expression_result idx = eval_expression(&thr->regs, s->ix, thr->temporaries.content);

		/* Crazy bloody encoding scheme */
		idx.lo =
			((idx.lo + s->bias) %
			 s->descr->nElems) *
			sizeofIRType(s->descr->elemTy) +
			s->descr->base;

		put_stmt(&thr->regs,
			 idx.lo,
			 eval_expression(&thr->regs, s->data, thr->temporaries.content),
			 s->descr->elemTy);
		return NULL;
	}

	case Ist_Dirty: {
		IRStmtDirty *s = (IRStmtDirty *)stmt;
		return thr->do_dirty_call(s->details, ms, er, ret);
	}
	case Ist_Exit: {
		IRStmtExit *s = (IRStmtExit *)stmt;
		if (s->guard) {
			struct expression_result guard =
				eval_expression(&thr->regs, s->guard, thr->temporaries.content);
			if (!guard.lo)
				return NULL;
		}
		if (s->jk != Ijk_Boring) {
			assert(s->jk == Ijk_EmWarn);
			printf("EMULATION WARNING %lx\n",
			       thr->regs.get_reg(REGISTER_IDX(EMWARN)));
		}
		thr->regs.set_reg(REGISTER_IDX(RIP),
				  s->dst.rip.unwrap_vexrip());
		thr->currentIRSB = NULL;
		return FINISHED_BLOCK;
	}

	default:
		printf("Don't know how to interpret statement ");
		ppIRStmt(stmt, stderr);
		throw NotImplementedException();
	}
}

ThreadEvent *
Thread::runToEvent(VexPtr<Thread > &ths,
		   VexPtr<MachineState > &ms,
		   const LogReaderPtr &ptr,
		   GarbageCollectionToken t,
		   VexPtr<EventRecorder> &er,
		   ReplayEngineTimer &ret)
{
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

			ThreadEvent *evt = interpretStatement(stmt, ths, er, ms, ret);
			if (evt == DUMMY_EVENT)
				return NULL;
			else if (evt == FINISHED_BLOCK)
				goto finished_block;
			else if (evt != NULL)
				return evt;
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
				struct expression_result next_addr;
				if (ths->currentIRSB->next_is_const) {
					next_addr.lo = ths->currentIRSB->next_const.rip.unwrap_vexrip();
				} else {
					next_addr = eval_expression(&ths->regs, ths->currentIRSB->next_nonconst, ths->temporaries.content);
				}
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
						extract_call_follower(ths->currentIRSB).unwrap_vexrip());
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
	ReplayEngineTimer ret;

	unsigned long event_counter = 0;
	VexPtr<LogRecord, &ir_heap> lr;
	bool appendedRecord = false;
	bool finished = false;
	LogReaderPtr ptr2 = ptr;

	/* Memory records are special and should always be
	   processed eagerly. */
	{
		VexPtr<AddressSpace > as(currentState->addressSpace);
		process_memory_records(as, lf, ptr, &ptr, lw, t, ret);
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
		ThreadEvent *evt = thr->runToEvent(thr, currentState, ptr2, t, er, ret);

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
					ret.suspend();
					lw->append(lr);
					ret.unsuspend();
					appendedRecord = true;
				}
				if (!lw) {
					if (!er) {
						LibVEX_free(oldEvent);
						oldEvent = NULL;
					}
					LibVEX_free(lr.get());
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
	                process_memory_records(as, lf, ptr, &ptr, lw, t, ret);
			if (eof)
				*eof = ptr;
			ptr2 = ptr;
	        }
	}
	printf("Done replay, counter %ld\n", event_counter);
}

#if 0
static double replayTime;
class __foo {
public:
	~__foo() {
		printf("Replay time: %f\n", replayTime);
	}
};
static __foo ___foo;
#endif

ReplayEngineTimer::ReplayEngineTimer(void)
{
	//	replayTime -= now();
}

ReplayEngineTimer::~ReplayEngineTimer(void)
{
	//	replayTime += now();
}
