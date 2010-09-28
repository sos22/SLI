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
#define SET_ABCD(_a,_b,_c,_d)						\
	do {								\
		regs->set_reg(REGISTER_IDX(RAX), mkConst<ait>(_a));	\
		regs->set_reg(REGISTER_IDX(RBX), mkConst<ait>(_b));	\
		regs->set_reg(REGISTER_IDX(RCX), mkConst<ait>(_c));	\
		regs->set_reg(REGISTER_IDX(RDX), mkConst<ait>(_d));	\
	} while (0)

	switch (force(mkConst<ait>(0xFFFFFFFF) & regs->get_reg(REGISTER_IDX(RAX)))) {
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
		switch (force(mkConst<ait>(0xFFFFFFFF) & regs->get_reg(REGISTER_IDX(RCX)))) {
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

template<typename ait> void
Thread<ait>::amd64g_dirtyhelper_loadF80le(MachineState<ait> *ms, IRTemp tmp, ait addr)
{
	ait buf[10];
	ms->addressSpace->readMemory(addr, 10, buf, false, this, NULL);
	UChar buf2[10];
	for (unsigned x = 0; x < 10; x++)
		buf2[x] = force(buf[x]);
	ULong f64;
	convert_f80le_to_f64le(buf2, (UChar*)&f64);
	temporaries[tmp].lo = mkConst<ait>(f64);
	temporaries[tmp].hi = mkConst<ait>(0);
}

template <typename ait> void
Thread<ait>::amd64g_dirtyhelper_storeF80le(MachineState<ait> *ms, ait addr, ait _f64)
{
	unsigned long f64 = force(_f64);
	unsigned char buf[10];
	ait buf2[10];
	unsigned x;

	convert_f64le_to_f80le((UChar *)&f64, (UChar *)buf);

	for (x = 0; x < 10; x++)
		buf2[x] = mkConst<ait>(buf[x]);
	ms->addressSpace->writeMemory(EventTimestamp(tid, nrEvents, ms->nrEvents,
						     force(regs.rip())),
				      addr,
				      10,
				      buf2,
				      false,
				      this);
}

template <typename ait> ThreadEvent<ait> *
Thread<ait>::do_load(EventTimestamp when, IRTemp tmp, ait addr, unsigned size,
		     MachineState<ait> *ms)
{
	if (ms->addressSpace->isReadable(addr, size, this))
		return LoadEvent<ait>::get(when, tmp, addr, size);
	else
		return SignalEvent<ait>::get(when, 11, addr);
}

template<typename ait>
ThreadEvent<ait> *
Thread<ait>::do_dirty_call(IRDirty *details, MachineState<ait> *ms)
{
	struct expression_result<ait> args[6];
	unsigned x;

	if (details->guard) {
		expression_result<ait> guard = eval_expression(details->guard);
		if (force(!guard.lo))
			return NULL;
	}
	for (x = 0; details->args[x]; x++) {
		assert(x < 6);
		args[x] = eval_expression(details->args[x]);
	}
	assert(!details->cee->regparms);

	if (!strcmp(details->cee->name, "amd64g_dirtyhelper_RDTSC")) {
		return RdtscEvent<ait>::get(bumpEvent(ms), details->tmp);
	} else if (!strcmp(details->cee->name, "helper_load_8")) {
		return do_load(bumpEvent(ms), details->tmp, args[0].lo, 1, ms);
	} else if (!strcmp(details->cee->name, "helper_load_16")) {
		return do_load(bumpEvent(ms), details->tmp, args[0].lo, 2, ms);
	} else if (!strcmp(details->cee->name, "helper_load_32")) {
		return do_load(bumpEvent(ms), details->tmp, args[0].lo, 4, ms);
	} else if (!strcmp(details->cee->name, "helper_load_64")) {
		return do_load(bumpEvent(ms), details->tmp, args[0].lo, 8, ms);
	} else if (!strcmp(details->cee->name, "helper_load_128")) {
		return do_load(bumpEvent(ms), details->tmp, args[0].lo, 16, ms);
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

template<typename ait>
static void
calculate_condition_flags_XXX(ait op,
			      ait dep1,
			      ait dep2,
			      ait ndep,
			      ait &cf,
			      ait &zf,
			      ait &sf,
			      ait &of,
			      ait &pf)
{
	sanity_check_ait(op);
	sanity_check_ait(dep1);
	sanity_check_ait(dep2);
	sanity_check_ait(ndep);
	pf = cf = zf = sf = of = mkConst<ait>(0);

	switch (force(op)) {
	case AMD64G_CC_OP_COPY:
		cf = dep1;
		zf = dep1 >> mkConst<ait>(6);
		sf = dep1 >> mkConst<ait>(7);
		of = dep1 >> mkConst<ait>(11);
		pf = dep1 >> mkConst<ait>(2);
		break;

#define DO_ACT(name, type_tag, bits)					\
		case AMD64G_CC_OP_ ## name ## type_tag:			\
			ACTIONS_ ## name (mkConst<ait>(bits));		\
		        break
#define ACTION(name)							\
		DO_ACT(name, B, 7);					\
		DO_ACT(name, W, 15);					\
		DO_ACT(name, L, 31);					\
		DO_ACT(name, Q, 63)
/* A shift of 64 bits in a 64 bit type is undefined, so we can't just
   go (1ul << 64).  However, (1ul << 63) * 2 does the right thing. */
#define MASK(bits) ((mkConst<ait>(1) << bits) * mkConst<ait>(2) - mkConst<ait>(1))
#define ACTIONS_ADD(bits)						\
		do {							\
			ait res;					\
			res = (dep1 + dep2) & MASK(bits);		\
			cf = res < (dep1 & MASK(bits));			\
			zf = (res == mkConst<ait>(0));			\
			sf = (res >> bits);				\
			of = (~(dep1 ^ dep2) &				\
			      (dep1 ^ res)) >> bits;			\
			pf = mkConst<ait>(parity_table[(UChar)force(res)]); \
		} while (0)
#define ACTIONS_ADC(bits)	 		                        \
		do {							\
			ait oldC = ndep & mkConst<ait>(AMD64G_CC_MASK_C); \
			ait argR = dep2 ^ oldC;				\
			ait res = ((dep1 + argR) + oldC) & MASK(bits);	\
			if (force(oldC))				\
				cf = res <= (dep1 & MASK(bits));	\
			else						\
				cf = res < (dep1 & MASK(bits));		\
			zf = res == mkConst<ait>(0);			\
			sf = res >> bits;				\
			of = (~(dep1 ^ argR) & (dep1 ^ res)) >> bits;	\
			pf = mkConst<ait>(parity_table[(UChar)force(res)]); \
		} while (0)
#define ACTIONS_SUB(bits)						\
		do {							\
			ait res;					\
			res = (dep1 - dep2) & MASK(bits);		\
			sanity_check_ait(res);				\
			cf = (dep1 & MASK(bits)) < (dep2 & MASK(bits));	\
			zf = (res == mkConst<ait>(0));			\
			sanity_check_ait(zf);				\
			sf = res >> bits;				\
			of = ( (dep1 ^ dep2) &				\
			       (dep1 ^ res) ) >> bits;			\
			pf = mkConst<ait>(parity_table[(UChar)force(res)]); \
		} while (0)
#define ACTIONS_LOGIC(bits)						\
		do {							\
			cf = mkConst<ait>(0);				\
			zf = (dep1 & MASK(bits)) == mkConst<ait>(0);	\
			sf = (dep1 & MASK(bits)) >> bits;		\
			of = mkConst<ait>(0);				\
			pf = mkConst<ait>(parity_table[(UChar)force(dep1)]); \
		} while (0)
#define ACTIONS_INC(bits)			                        \
		do {				                        \
			ait res = dep1 & MASK(bits);			\
			cf = ndep & mkConst<ait>(1);			\
			zf = (res == mkConst<ait>(0));			\
			sf = res >> bits;				\
			of = res == (mkConst<ait>(1) << bits);		\
			pf = mkConst<ait>(parity_table[(UChar)force(res)]); \
		} while (0)
#define ACTIONS_DEC(bits)			                        \
		do {				                        \
			ait res = dep1 & MASK(bits);			\
			cf = ndep & mkConst<ait>(1);			\
			zf = (res == mkConst<ait>(0));			\
			sf = res >> bits;				\
			of = ((res + mkConst<ait>(1)) & MASK(bits)) == (mkConst<ait>(1) << bits); \
			pf = mkConst<ait>(parity_table[(UChar)force(res)]); \
		} while (0)
#define ACTIONS_SHR(bits)			                        \
		do {				                        \
			cf = dep2 & mkConst<ait>(1);			\
			zf = (dep1 == mkConst<ait>(0));			\
			sf = dep1 >> bits;				\
			of = (dep1 ^ dep2) >> bits;			\
			pf = mkConst<ait>(parity_table[(UChar)force(dep1)]); \
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
		throw NotImplementedException("Strange operation code %ld\n", force(op));
	}

	of &= mkConst<ait>(1);
	sf &= mkConst<ait>(1);
	zf &= mkConst<ait>(1);
	cf &= mkConst<ait>(1);

	sanity_check_ait(of);
	sanity_check_ait(sf);
	sanity_check_ait(zf);
	sanity_check_ait(cf);
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
	ait inv;
	ait cf, zf, sf, of, pf;

	calculate_condition_flags_XXX<ait>(op.lo,
					   dep1.lo,
					   dep2.lo,
					   ndep.lo,
					   cf,
					   zf,
					   sf,
					   of,
					   pf);

	inv = condcode.lo & mkConst<ait>(1);
	switch (force(condcode.lo & ~mkConst<ait>(1))) {
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
		throw NotImplementedException("Strange cond code %ld (op %ld)\n", force(condcode.lo), force(op.lo));
	}

	res.lo ^= inv;

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
	ait cf, zf, sf, of, pf;

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

template<typename ait>
expression_result<ait>
Thread<ait>::do_ccall_generic(IRCallee *cee,
			      struct expression_result<ait> *rargs)
{
	struct expression_result<ait> res;

	res.lo = mkConst<ait>(((unsigned long (*)(unsigned long, unsigned long, unsigned long,
						  unsigned long, unsigned long, unsigned long))cee->addr)
			      (force(rargs[0].lo),
			       force(rargs[1].lo),
			       force(rargs[2].lo),
			       force(rargs[3].lo),
			       force(rargs[4].lo),
			       force(rargs[5].lo)));
	res.hi = mkConst<ait>(0);
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
static void mulls64(struct expression_result<ait> *dest, const struct expression_result<ait> &src1,
		    const struct expression_result<ait> &src2);

template <>
void mulls64(struct expression_result<unsigned long> *dest, const struct expression_result<unsigned long> &src1,
	     const struct expression_result<unsigned long> &src2)
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

template<typename ait>
expression_result<ait>
Thread<ait>::eval_expression(IRExpr *expr)
{
	struct expression_result<ait> res;
	struct expression_result<ait> *dest = &res;
	unsigned getOffset;
	IRType getType;

	res.lo = mkConst<ait>(0);
	res.hi = mkConst<ait>(0);
	
	switch (expr->tag) {
	case Iex_Get: {
		getOffset = expr->Iex.Get.offset;
		getType = expr->Iex.Get.ty;

		do_get:
		ait v1;
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
			dest->lo = (v1 >> mkConst<ait>(sub_word_offset * 8)) & mkConst<ait>(0xffffffff);
			break;
		case Ity_I16:
			assert(!(sub_word_offset % 2));
			dest->lo = (v1 >> mkConst<ait>(sub_word_offset * 8)) & mkConst<ait>(0xffff);
			break;
		case Ity_I8:
			dest->lo = (v1 >> mkConst<ait>(sub_word_offset * 8)) & mkConst<ait>(0xff);
			break;
		default:
			ppIRExpr(expr);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_GetI: {
		getOffset = force(eval_expression(expr->Iex.GetI.ix).lo);
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
			dest->lo = mkConst<ait>(cnst->Ico.U1);
			break;
		case Ico_U8:
			dest->lo = mkConst<ait>(cnst->Ico.U8);
			break;
		case Ico_U16:
			dest->lo = mkConst<ait>(cnst->Ico.U16);
			break;
		case Ico_U32:
			dest->lo = mkConst<ait>(cnst->Ico.U32);
			break;
		case Ico_U64:
		case Ico_F64:
		case Ico_F64i:
			dest->lo = mkConst<ait>(cnst->Ico.U64);
			break;
		case Ico_V128: {
			unsigned long r = cnst->Ico.V128;
			r = r | (r << 16) | (r << 32) | (r << 48);
			dest->lo = mkConst<ait>(r);
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
				mkConst<ait>((long)(int)force(arg1.lo) * (long)(int)force(arg2.lo));
			break;

		case Iop_MullS64:
			mulls64(dest, arg1, arg2);
			break;

		case Iop_MullU64: {
			ait a1, a2, b1, b2;
			dest->lo = arg1.lo * arg2.lo;
			a1 = arg1.lo & mkConst<ait>(0xffffffff);
			a2 = arg1.lo >> mkConst<ait>(32);
			b1 = arg2.lo & mkConst<ait>(0xffffffff);
			b2 = arg2.lo >> mkConst<ait>(32);
			dest->hi = a2 * b2 +
				( (a1 * b2 + a2 * b1 +
				   ((a1 * b1) >> mkConst<ait>(32))) >> mkConst<ait>(32));
			break;
		}
		case Iop_32HLto64:
			dest->lo = (arg1.lo << mkConst<ait>(32)) | arg2.lo;
			break;

		case Iop_64HLtoV128:
		case Iop_64HLto128:
			dest->lo = arg2.lo;
			dest->hi = arg1.lo;
			break;

		case Iop_DivModU64to32:
			dest->lo = (arg1.lo / arg2.lo) |
				((arg1.lo % arg2.lo) << mkConst<ait>(32));
			break;

		case Iop_DivModS64to32: {
			long a1 = force(arg1.lo);
			long a2 = force(arg2.lo);
			dest->lo = mkConst<ait>(
				((a1 / a2) & 0xffffffff) | ((a1 % a2) << 32));
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
			     : "0" (force(arg1.lo)), "1" (force(arg1.hi)), "r" (force(arg2.lo)));
			dest->lo = mkConst<ait>(dlo);
			dest->hi = mkConst<ait>(dhi);
			break;
		}

		case Iop_DivModS128to64: {
			unsigned long dlo;
			unsigned long dhi;
			asm ("idiv %4\n"
			     : "=a" (dlo), "=d" (dhi)
			     : "0" (force(arg1.lo)), "1" (force(arg1.hi)), "r" (force(arg2.lo)));
			dest->lo = mkConst<ait>(dlo);
			dest->hi = mkConst<ait>(dhi);
			break;
		}

		case Iop_Add32x4:
			dest->lo = ((arg1.lo + arg2.lo) & mkConst<ait>(0xffffffff)) +
				((arg1.lo & mkConst<ait>(~0xfffffffful)) + (arg2.lo & mkConst<ait>(~0xfffffffful)));
			dest->hi = ((arg1.hi + arg2.hi) & mkConst<ait>(0xffffffff)) +
				((arg1.hi & mkConst<ait>(~0xfffffffful)) + (arg2.hi & mkConst<ait>(~0xfffffffful)));
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
			dest->lo = (arg2.lo & mkConst<ait>(0xffffffff)) | (arg1.lo << mkConst<ait>(32));
			dest->hi = (arg2.lo >> mkConst<ait>(32)) | (arg1.lo & mkConst<ait>(0xffffffff00000000ul));
			break;

		case Iop_InterleaveHI32x4:
			dest->lo = (arg2.hi & mkConst<ait>(0xffffffff)) | (arg1.hi << mkConst<ait>(32));
			dest->hi = (arg2.hi >> mkConst<ait>(32)) | (arg1.hi & mkConst<ait>(0xffffffff00000000ul));
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
			unsigned long a1l = force(arg1.lo);
			unsigned long a2l = force(arg2.lo);
			unsigned long a1h = force(arg1.hi);
			unsigned long a2h = force(arg2.hi);
			if ( (int)a1l > (int)a2l )
				dest->lo |= mkConst<ait>(0xffffffff);
			if ( (int)(a1l >> 32) > (int)(a2l >> 32) )
				dest->lo |= mkConst<ait>(0xffffffff00000000);
			if ( (int)a1h > (int)a2h )
				dest->hi |= mkConst<ait>(0xffffffff);
			if ( (int)(a1h >> 32) > (int)(a2h >> 32) )
				dest->hi |= mkConst<ait>(0xffffffff00000000);
			break;
		}

		case Iop_I64toF64: {
			switch (force(arg1.lo)) {
			case 0:
				/* Round to nearest even mode. */
				union {
					double d;
					unsigned long l;
				} r;
				r.d = (long)force(arg2.lo);
				dest->lo = mkConst<ait>(r.l);
				break;
			default:
				throw NotImplementedException("unknown rounding mode %ld\n",
							      force(arg1.lo));
			}
			break;
		}

		case Iop_F64toI32: {
			switch (force(arg1.lo)) {
			case 3:
				union {
					double d;
					long l;
				} r;
				r.l = (long)force(arg2.lo);
				dest->lo = mkConst<ait>((unsigned)r.d);
				break;
			default:
				throw NotImplementedException("unknown rounding mode %ld\n",
							      force(arg1.lo));
			}
			break;
		}

		case Iop_F64toI64: {
			switch (force(arg1.lo)) {
			case 3:
				union {
					double d;
					unsigned long l;
				} r;
				r.l = force(arg2.lo);
				dest->lo = mkConst<ait>(r.d);
				break;
			default:
				throw NotImplementedException("unknown rounding mode %ld\n",
							      force(arg1.lo));
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
			in.l = force(arg2.lo);
			out.f = in.d;
			dest->lo = mkConst<ait>(out.l);
			break;
		}

		case Iop_CmpF64: {
			union {
				double d;
				unsigned long l;
			} r1, r2;
			r1.l = force(arg1.lo);
			r2.l = force(arg2.lo);
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
			dest->lo = mkConst<ait>(r);
			break;
		}

		case Iop_SinF64: {
			union {
				unsigned long l;
				double d;
			} in, out;
			in.l = force(arg2.lo);
			asm ("fsin\n"
			     : "=t" (out.d)
			     : "0" (in.d));
			dest->lo = mkConst<ait>(out.l);
			break;
		}

		case Iop_CosF64: {
			union {
				unsigned long l;
				double d;
			} in, out;
			in.l = force(arg2.lo);
			asm ("fcos\n"
			     : "=t" (out.d)
			     : "0" (in.d));
			dest->lo = mkConst<ait>(out.l);
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
				in1.l = force(arg1.lo);			\
				in2.l = force(arg2.lo);			\
				out.d = op;				\
				dest->lo = mkConst<ait>(out.l);		\
				break;					\
			}
#define F0x2op(name, op) _F0x2op(name, in1.d op in2.d)

#define _F0x4op(name, op)						\
			case Iop_ ## name ## 32F0x4: {			\
				union {					\
					unsigned l;			\
					float d;			\
				} in1, in2, out;			\
				in1.l = force(arg1.lo);			\
				in2.l = force(arg2.lo);			\
				out.d = op;				\
				dest->lo =				\
					(arg1.lo & mkConst<ait>(0xffffffff00000000ul)) | \
					mkConst<ait>(out.l);		\
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
			ppIRExpr(expr);
			throw NotImplementedException();
		}

		IRType t, ign1, ign2, ign3, ign4;
		typeOfPrimop(expr->Iex.Binop.op, &t, &ign1, &ign2, &ign3, &ign4);
		switch (t) {
		case Ity_I1:
			dest->lo &= mkConst<ait>(1);
			break;
		case Ity_I8:
			dest->lo &= mkConst<ait>(0xff);
			break;
		case Ity_I16:
			dest->lo &= mkConst<ait>(0xffff);
			break;
		case Ity_I32:
			dest->lo &= mkConst<ait>(0xffffffff);
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
			ppIRType(t);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_Unop: {
		struct expression_result<ait> arg = eval_expression(expr->Iex.Unop.arg);
		switch (expr->Iex.Unop.op) {
		case Iop_64HIto32:
			dest->lo = arg.lo >> mkConst<ait>(32);
			break;
		case Iop_64to32:
			dest->lo = arg.lo & mkConst<ait>(0xffffffff);
			break;
		case Iop_64to16:
		case Iop_32to16:
			dest->lo = arg.lo & mkConst<ait>(0xffff);
			break;
		case Iop_64to8:
		case Iop_32to8:
		case Iop_16to8:
			dest->lo = arg.lo & mkConst<ait>(0xff);
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
			dest->lo = arg.lo & mkConst<ait>(1);
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
			dest->lo = signed_shift_right(arg.lo << mkConst<ait>(56), mkConst<ait>(56)) & mkConst<ait>(0xffff);
			break;
		case Iop_8Sto32:
			dest->lo = signed_shift_right(arg.lo << mkConst<ait>(56), mkConst<ait>(56)) & mkConst<ait>(0xffffffff);
			break;
		case Iop_8Sto64:
			dest->lo = signed_shift_right(arg.lo << mkConst<ait>(56), mkConst<ait>(56));
			break;
		case Iop_16Sto32:
			dest->lo = signed_shift_right(arg.lo << mkConst<ait>(48), mkConst<ait>(48)) & mkConst<ait>(0xffffffff);
			break;
		case Iop_16Sto64:
			dest->lo = signed_shift_right(arg.lo << mkConst<ait>(48), mkConst<ait>(48));
			break;
		case Iop_32Sto64:
			dest->lo = signed_shift_right(arg.lo << mkConst<ait>(32), mkConst<ait>(32));
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
			out.d = (int)force(arg.lo);
			dest->lo = mkConst<ait>(out.l);
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
			in.l = force(arg.lo);
			out.d = in.f;
			dest->lo = mkConst<ait>(out.l);
			break;
		}

		case Iop_Not1:
			dest->lo = !arg.lo;
			break;

		case Iop_Not32:
			dest->lo = ~arg.lo & mkConst<ait>(0xffffffff);
			break;

		case Iop_Not64:
			dest->lo = ~arg.lo;
			break;

		case Iop_NotV128:
			dest->lo = ~arg.lo;
			dest->hi = ~arg.hi;
			break;
			
		case Iop_Clz64: {
			unsigned long v = force(arg.lo);
			unsigned res = 0;
			while (!(v & (1ul << (63 - res))) &&
			       res < 63)
				res++;
			dest->lo = mkConst<ait>(res);
			break;
		}

		case Iop_Ctz64: {
			unsigned long v = force(arg.lo);
			unsigned res = 0;
			while (!(v & (1ul << res)) &&
			       res < 63)
				res++;
			dest->lo = mkConst<ait>(res);
			break;
		}

		case Iop_Sqrt64F0x2: {
			union {
				unsigned long l;
				double d;
			} in, out;
			in.l = force(arg.lo);
			asm ("fsqrt\n"
			     : "=t" (out.d)
			     : "0" (in.d));
			dest->lo = mkConst<ait>(out.l);
			break;
		}

		default:
			ppIRExpr(expr);
			throw NotImplementedException();
		}
		break;
	}

	case Iex_Triop: {
		struct expression_result<ait> arg1 = eval_expression(expr->Iex.Triop.arg1);
		struct expression_result<ait> arg2 = eval_expression(expr->Iex.Triop.arg2);
		struct expression_result<ait> arg3 = eval_expression(expr->Iex.Triop.arg3);
		switch (expr->Iex.Triop.op) {
		case Iop_PRemF64: {
			union {
				double d;
				unsigned long l;
			} a1, a2, res;
			a1.l = force(arg2.lo);
			a2.l = force(arg3.lo);
			asm ("fprem\n"
			     : "=t" (res.d)
			     : "0" (a1.d), "u" (a2.d));
			dest->lo = mkConst<ait>(res.l);
			break;
		}
		case Iop_PRemC3210F64: {
			union {
				double d;
				unsigned long l;
			} a1, a2, clobber;
			unsigned short res;
			a1.l = force(arg2.lo);
			a2.l = force(arg3.lo);
			asm ("fprem\nfstsw %%ax\n"
			     : "=t" (clobber.d), "=a" (res)
			     : "0" (a1.d), "u" (a2.d));
			dest->lo =
				mkConst<ait>(((res >> 8) & 7) | ((res & 0x400) >> 11));
			break;
		}
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
		if (force(cond.lo == mkConst<ait>(0))) {
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

/* vsyscalls are weird (the redirection target effectively moves), and
 * cause a number of RIP mismatches during replay.  Skank it up. */
template <typename ait> void
Thread<ait>::redirectGuest(ait rip)
{
	if (force(rip == mkConst<ait>(0xFFFFFFFFFF600400ul) ||
		  rip == mkConst<ait>(0xffffffffff600000ul)))
		allowRipMismatch = true;
}

IRSB *instrument_func(void *closure,
		      IRSB *sb_in,
		      VexGuestLayout *layout,
		      VexGuestExtents *vge,
		      IRType gWordTy,
		      IRType hWordTy);

template <typename ait>
class AddressSpaceGuestFetcher : public GuestMemoryFetcher {
	AddressSpace<ait> *aspace;
	unsigned long offset;
	VexGcVisitor<AddressSpaceGuestFetcher<ait> > visitor;
	mutable UChar cache[16];
	mutable unsigned long cache_start;
public:
	virtual UChar operator[](unsigned long idx) const
	{
		unsigned long desired = idx + offset;
		if (desired >= cache_start && desired < cache_start + sizeof(cache))
			return cache[desired - cache_start];
		cache_start = desired;
		ait v[16];
		aspace->readMemory(mkConst<ait>(desired), 16, v, false, NULL);
		for (unsigned x = 0; x < sizeof(cache); x++)
			cache[x] = force(v[x]);
		return cache[0];
	}
	AddressSpaceGuestFetcher(AddressSpace<ait> *_aspace,
				 unsigned long _offset) :
		aspace(_aspace),
		offset(_offset),
		visitor(this, "AddressSpaceGuestFetcher"),
		cache_start(0)
	{
	}
	void visit(HeapVisitor &hv) { hv(aspace); }
};

template<typename ait> IRSB *
AddressSpace<ait>::getIRSBForAddress(unsigned long rip)
{
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
		class AddressSpaceGuestFetcher<ait> fetcher(this, rip);
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

template<typename ait> void
Thread<ait>::translateNextBlock(VexPtr<Thread<ait> > &ths,
				VexPtr<AddressSpace<ait> > &addrSpace,
				VexPtr<MachineState<ait> > &ms,
				const LogReaderPtr &ptr,
				ait rip,
				GarbageCollectionToken t)
{
	ths->decode_counter++;
	ths->redirectGuest(rip);

	ths->controlLog.push(Thread<ait>::control_log_entry(force(ths->currentIRSBRip), ths->currentIRSBOffset));

	if (ths->decode_counter % 10000 == 0) {
		ths->snapshotLog.push(Thread<ait>::snapshot_log_entry(ms, ptr));
		ms = ms->dupeSelf();
	}

	ths->currentIRSBRip = rip;

	unsigned long _rip = force(rip);
	vexSetAllocModeTEMP_and_clear(t);

	IRSB *irsb = addrSpace->getIRSBForAddress(_rip);

	ths->temporaries.setSize(irsb->tyenv->types_used);

	ths->currentIRSB = irsb;
	ths->currentIRSBOffset = 0;

	ths->currentControlCondition = mkConst<ait>(1);

	if (loud_mode)
		ppIRSB(irsb);

	/* First statement in block should be a mark */
	assert(ths->currentIRSB->stmts[0]->tag == Ist_IMark);
	/* Should be a mark for the IRSB rip */
	assert(ths->currentIRSB->stmts[0]->Ist.IMark.addr ==
	       force(ths->currentIRSBRip));
}

template<typename ait>
ThreadEvent<ait> *
Thread<ait>::runToEvent(VexPtr<Thread<ait> > &ths,
			VexPtr<MachineState<ait> > &ms,
			const LogReaderPtr &ptr,
			GarbageCollectionToken t)
{
	unsigned put_offset;
	struct expression_result<ait> put_data;
	IRType put_type;

	while (1) {
		if (!ths->currentIRSB) {
			try {
				VexPtr<AddressSpace<ait> > as(ms->addressSpace);
			        ths->translateNextBlock(ths, as, ms, ptr, ths->regs.rip(), t);
			} catch (BadMemoryException<ait> excn) {
				return SignalEvent<ait>::get(ths->bumpEvent(ms), 11, excn.ptr);
			}
			assert(ths->currentIRSB);
		}
	        assert(force(ths->currentControlCondition));
		while (ths->currentIRSBOffset < ths->currentIRSB->stmts_used) {
			IRStmt *stmt = ths->currentIRSB->stmts[ths->currentIRSBOffset];
			ths->currentIRSBOffset++;

			assert(force(ths->currentControlCondition));

			switch (stmt->tag) {
			case Ist_NoOp:
				break;
			case Ist_IMark:
				if (force(ths->regs.rip() == ms->addressSpace->client_free))
					ms->addressSpace->client_freed(ths->bumpEvent(ms),
								       ths->regs.get_reg(REGISTER_IDX(RDI)));
				ths->regs.set_reg(REGISTER_IDX(RIP),
						  mkConst<ait>(stmt->Ist.IMark.addr));
#define GR(x) ths->regs.get_reg(REGISTER_IDX(x))
				return InstructionEvent<ait>::get(ths->bumpEvent(ms),
								  GR(RIP),
								  GR(FOOTSTEP_REG_0_NAME),
								  GR(FOOTSTEP_REG_1_NAME),
								  ths->regs.get_reg(REGISTER_IDX(XMM0) + 1),
								  GR(FOOTSTEP_REG_3_NAME),
								  GR(FOOTSTEP_REG_4_NAME),
								  ths->allowRipMismatch);
#undef GR

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
				struct expression_result<ait> data =
					ths->eval_expression(stmt->Ist.Store.data);
				struct expression_result<ait> addr =
					ths->eval_expression(stmt->Ist.Store.addr);
				unsigned size = sizeofIRType(typeOfIRExpr(ths->currentIRSB->tyenv,
									  stmt->Ist.Store.data));
				if (ms->addressSpace->isWritable(addr.lo, size, ths)) {
					DBG("Store %s to %s\n", data.name(), addr.name());
					return StoreEvent<ait>::get(ths->bumpEvent(ms), addr.lo, size, data);
				}
				EventTimestamp et;
				ait free_addr;
				if (ms->addressSpace->isOnFreeList(addr.lo, addr.lo + mkConst<ait>(size), ths->tid, &et,
								   &free_addr))
					return UseFreeMemoryEvent<ait>::get(ths->bumpEvent(ms), 
									    addr.lo,
									    free_addr,
									    et);
				else
					return SignalEvent<ait>::get(ths->bumpEvent(ms), 11, addr.lo);
			}

			case Ist_CAS: {
				assert(stmt->Ist.CAS.details->oldHi == IRTemp_INVALID);
				assert(stmt->Ist.CAS.details->expdHi == NULL);
				assert(stmt->Ist.CAS.details->dataHi == NULL);
				assert(stmt->Ist.CAS.details->end == Iend_LE);
				struct expression_result<ait> data =
					ths->eval_expression(stmt->Ist.CAS.details->dataLo);
				struct expression_result<ait> addr =
					ths->eval_expression(stmt->Ist.CAS.details->addr);
				struct expression_result<ait> expected =
					ths->eval_expression(stmt->Ist.CAS.details->expdLo);
				unsigned size = sizeofIRType(typeOfIRExpr(ths->currentIRSB->tyenv,
									  stmt->Ist.CAS.details->dataLo));
				return CasEvent<ait>::get(ths->bumpEvent(ms), stmt->Ist.CAS.details->oldLo, addr, data, expected, size);
			}

			case Ist_Put: {
				put_offset = stmt->Ist.Put.offset;
				put_data = ths->eval_expression(stmt->Ist.Put.data);
				put_type = typeOfIRExpr(ths->currentIRSB->tyenv, stmt->Ist.Put.data);
				do_put:
				DBG("put offset %d type %d -> %s",
				    put_offset, put_type, put_data.name());
				unsigned byte_offset = put_offset & 7;
				ait dest = read_reg(&*ths, put_offset - byte_offset);
				switch (put_type) {
				case Ity_I8:
					dest &= mkConst<ait>(~(0xFF << (byte_offset * 8)));
					dest |= put_data.lo << mkConst<ait>(byte_offset * 8);
					break;

				case Ity_I16:
					assert(!(byte_offset % 2));
					dest &= mkConst<ait>(~(0xFFFFul << (byte_offset * 8)));
					dest |= put_data.lo << mkConst<ait>(byte_offset * 8);
					break;

				case Ity_I32:
				case Ity_F32:
					assert(!(byte_offset % 4));
					dest &= mkConst<ait>(~(0xFFFFFFFFul << (byte_offset * 8)));
					dest |= put_data.lo << mkConst<ait>(byte_offset * 8);
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
				struct expression_result<ait> idx = ths->eval_expression(stmt->Ist.PutI.ix);

				/* Crazy bloody encoding scheme */
				idx.lo =
					mkConst<ait>(((force(idx.lo) + stmt->Ist.PutI.bias) %
						      stmt->Ist.PutI.descr->nElems) *
						     sizeofIRType(stmt->Ist.PutI.descr->elemTy) +
						     stmt->Ist.PutI.descr->base);

				put_offset = force(idx.lo);
				put_data = ths->eval_expression(stmt->Ist.PutI.data);
				put_type = stmt->Ist.PutI.descr->elemTy;
				goto do_put;
			}

			case Ist_Dirty: {
				ThreadEvent<ait> *evt = ths->do_dirty_call(stmt->Ist.Dirty.details, ms);
				if (evt)
					return evt;
				break;
			}

			case Ist_Exit: {
				if (stmt->Ist.Exit.guard) {
					struct expression_result<ait> guard =
						ths->eval_expression(stmt->Ist.Exit.guard);
					bool controlCondIsConstant = isConstant(ths->currentControlCondition);
					sanity_check_ait(ths->currentControlCondition);
					sanity_check_ait(guard.lo);
					if (force(!guard.lo)) {
						ait inv_guard = !guard.lo;
						assert(force(inv_guard) == 1);
						ths->currentControlCondition =
							ths->currentControlCondition && inv_guard;
						sanity_check_ait(ths->currentControlCondition);
						if (!controlCondIsConstant)
							assert(!isConstant(ths->currentControlCondition));
						assert(force(ths->currentControlCondition));
						break;
					}
					ait inv_inv_guard = !!guard.lo;
					assert(force(inv_inv_guard) == 1);
					ths->currentControlCondition =
						ths->currentControlCondition && inv_inv_guard;
					sanity_check_ait(ths->currentControlCondition);
					if (!controlCondIsConstant)
						assert(!isConstant(ths->currentControlCondition));
					assert(force(ths->currentControlCondition));
				}
				if (stmt->Ist.Exit.jk != Ijk_Boring) {
					assert(stmt->Ist.Exit.jk == Ijk_EmWarn);
					printf("EMULATION WARNING %lx\n",
					       force(ths->regs.get_reg(REGISTER_IDX(EMWARN))));
				}
				assert(force(ths->currentControlCondition));
				assert(stmt->Ist.Exit.dst->tag == Ico_U64);
				sanity_check_ait(ths->currentControlCondition);
				ths->regs.set_reg(REGISTER_IDX(RIP),
						  ternary(ths->currentControlCondition,
							  mkConst<ait>(stmt->Ist.Exit.dst->Ico.U64),
							  mkConst<ait>(0xdeadbeef)));
				ths->currentIRSB = NULL;
				goto finished_block;
			}

			default:
				printf("Don't know how to interpret statement ");
				ppIRStmt(stmt);
				throw NotImplementedException();
			}

			assert(force(ths->currentControlCondition));
		}

		ths->currentIRSBOffset++;
		
		assert(ths->currentIRSB->jumpkind == Ijk_Boring ||
		       ths->currentIRSB->jumpkind == Ijk_Call ||
		       ths->currentIRSB->jumpkind == Ijk_Ret ||
		       ths->currentIRSB->jumpkind == Ijk_Sys_syscall ||
		       ths->currentIRSB->jumpkind == Ijk_Yield);

		if (ths->currentIRSB->jumpkind == Ijk_Yield)
			ths->currentIRSB->jumpkind = Ijk_Boring;

		if (ths->currentIRSB->jumpkind == Ijk_Ret)
			ths->allowRipMismatch = false;

		{
			bool is_syscall = ths->currentIRSB->jumpkind == Ijk_Sys_syscall;
			{
				struct expression_result<ait> next_addr =
					ths->eval_expression(ths->currentIRSB->next);
				sanity_check_ait(ths->currentControlCondition);
				sanity_check_ait(next_addr.lo);
				assert(force(ths->currentControlCondition));
				ths->regs.set_reg(REGISTER_IDX(RIP),
						  ternary(ths->currentControlCondition,
							  next_addr.lo,
							  mkConst<ait>(0xdeadbeef)));
				ths->currentIRSB = NULL;
			}
			if (is_syscall)
				return SyscallEvent<ait>::get(ths->bumpEvent(ms));
		}

finished_block:
		assert(force(ths->currentControlCondition));
		;
	}
}

template<typename ait>
InterpretResult Interpreter<ait>::getThreadMemoryTrace(ThreadId tid, MemoryTrace<ait> **output, unsigned max_events,
						       GarbageCollectionToken t)
{
	VexPtr<MemoryTrace<ait> > work(new MemoryTrace<ait>());
	VexPtr<Thread<ait> > thr(currentState->findThread(tid));
	if (thr->cannot_make_progress) {
		*output = work;
		return InterpretResultIncomplete;
	}
	while (max_events && thr->runnable() &&

	       /* Since we're running the thread in isolation, if it
		  goes idle it's unlikely to ever wake up again. */
	       !thr->idle) {
		ThreadEvent<ait> *evt = thr->runToEvent(thr, currentState, LogReaderPtr(), t);

		InterpretResult res = evt->fake(currentState);
		if (res != InterpretResultContinue) {
			printf("Stop memory trace because can't fake %s\n", evt->name());
			*output = work;
			return res;
		}
		if (LoadEvent<ait> *lr = dynamic_cast<LoadEvent <ait> * > (evt)) {
			if (address_is_interesting(thr->tid, force(lr->addr)))
				work->push_back(new MemoryAccessLoad<ait>(*lr));
	        } else if (StoreEvent<ait> *sr = dynamic_cast<StoreEvent<ait> *>(evt)) {
			if (address_is_interesting(thr->tid, force(sr->addr)))
				work->push_back(new MemoryAccessStore<ait>(*sr));
		}
		max_events--;
	}
	*output = work;
	if (max_events)
		return InterpretResultExit;
	return InterpretResultTimedOut;
}

template<typename ait>
void Interpreter<ait>::runToAccessLoggingEvents(ThreadId tid,
						unsigned nr_accesses,
						GarbageCollectionToken t,
						VexPtr<LogWriter<ait> > &output)
{
        VexPtr<Thread<ait> > thr(currentState->findThread(tid));
        while (1) {
                ThreadEvent<ait> *evt = thr->runToEvent(thr, currentState, LogReaderPtr(), t);
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
		(void)res;
	}
}

template<typename ait>
void Interpreter<ait>::runToFailure(ThreadId tid,
				    VexPtr<LogWriter<ait> > &output,
				    GarbageCollectionToken t,
				    unsigned max_events)
{
	bool have_event_limit = max_events != 0;
	VexPtr<Thread<ait> > thr(currentState->findThread(tid));
	while ((!have_event_limit || max_events) && thr->runnable()) {
		VexPtr<MachineState<ait> > cs(currentState);
		ThreadEvent<ait> *evt = thr->runToEvent(thr, cs, LogReaderPtr(), t);
		InterpretResult res = output->recordEvent(thr, currentState, evt);
		if (res != InterpretResultContinue) {
			thr->cannot_make_progress = true;
			return;
		}
		max_events--;
		if (thr->blocked) {
			if (max_events >= 1000)
				max_events -= 1000;
			else
				max_events = 0;
		}
	}
}

template<typename ait>
void Interpreter<ait>::replayLogfile(VexPtr<LogReader<ait> > &lf,
				     LogReaderPtr ptr,
				     GarbageCollectionToken t,
				     LogReaderPtr *eof,
				     VexPtr<LogWriter<ait> > &lw,
				     VexPtr<EventRecorder<ait> > &er,
				     EventTimestamp *lastEvent)
{
	unsigned long event_counter = 0;
	VexPtr<LogRecord<ait> > lr;
	bool appendedRecord;
	bool finished = false;
	LogReaderPtr ptr2 = ptr;

	while (!finished) {
		event_counter++;
		if (event_counter % 100000 == 0)
			printf("event %ld\n", event_counter);
		if (event_counter > 1700000 && 0)
			loud_mode = true;

		if (!lr) {
			lr = lf->read(ptr, &ptr);
			appendedRecord = false;
		}
		if (!lr)
			break;

		VexPtr<Thread<ait> > thr(currentState->findThread(lr->thread()));
		assert(thr);
		assert(!thr->exitted);
		ThreadEvent<ait> *evt = thr->runToEvent(thr, currentState, ptr2, t);

		while (evt) {
			if (lastEvent && evt->when == *lastEvent)
				finished = true;
			if (er)
				er->record(thr, evt, currentState);
			if (loud_mode)
				printf("Event %s in thread %d, lr %s\n",
				       evt->name(), lr->thread()._tid(),
				       lr->name());

			ThreadEvent<ait> *oldEvent = evt;
			bool consumed = true;
			evt = evt->replay(lr, currentState, consumed);
			if (consumed) {
				if (lw && !appendedRecord) {
					lw->append(lr, oldEvent->when.idx);
					appendedRecord = true;
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
		}

		if (!lr) {
			/* Memory records are special and should always be
			   processed eagerly. */
			VexPtr<AddressSpace<ait> > as(currentState->addressSpace);
	                process_memory_records(as, lf, ptr, &ptr, lw, t);
			if (eof)
				*eof = ptr;
			ptr2 = ptr;
	        }
	}
}

template<typename ait>
void Interpreter<ait>::runToEvent(EventTimestamp end,
				  VexPtr<LogReader<ait> > &lf,
				  LogReaderPtr ptr,
				  GarbageCollectionToken t, LogReaderPtr *eof)
{
	LogReaderPtr ptr2 = ptr;
	VexPtr<LogRecord<ait> > lr;
	/* Mostly a debugging aide */
	volatile static unsigned long event_counter;

	bool finished = false;
	while (!finished) {
		event_counter++;
		printf("event %ld\n", event_counter);

		if (!lr)
			lr = lf->read(ptr, &ptr);
		if (!lr)
			break;

		VexPtr<Thread<ait> > thr(currentState->findThread(lr->thread()));
		assert(thr->runnable());
		ThreadEvent<ait> *evt = thr->runToEvent(thr, currentState, ptr2, t);

		while (evt && !finished) {
			if (evt->when == end)
				finished = true;
			bool consumed = true;
			evt = evt->replay(lr, currentState, consumed);
			if (consumed) {
				lr = NULL;
				if (eof)
					*eof = ptr;
				ptr2 = ptr;
			}
			if (!finished && evt && !lr)
				lr = lf->read(ptr, &ptr);
		}

		/* Memory records are special and should always be
		   processed eagerly. */
		VexPtr<AddressSpace<ait> > as(currentState->addressSpace);
	        VexPtr<LogWriter<ait> > dummy(NULL);
		process_memory_records(as, lf, ptr, &ptr, dummy, t);
				if (eof)
					*eof = ptr;
				ptr2 = ptr;
	}
}

template <typename ait> void visit_expression_result_array(void *_ctxt,
							   HeapVisitor &hv)
{
	unsigned nr_entries = *(unsigned *)_ctxt;
	expression_result<ait> *arr = (expression_result<ait> *)((unsigned *)_ctxt + 1);
	for (unsigned x = 0; x < nr_entries; x++)
		arr[x].visit(hv);
}

template <typename ait> void destruct_expression_result_array(void *_ctxt)
{
	unsigned nr_entries = *(unsigned *)_ctxt;
	expression_result<ait> *arr = (expression_result<ait> *)((unsigned *)_ctxt + 1);
	for (unsigned x = 0; x < nr_entries; x++)
		arr[x].~expression_result<ait>();
}

#define MK_INTERPRETER(t)						\
	template void Interpreter<t>::runToFailure(ThreadId tid,	\
						   VexPtr<LogWriter<t> > &output, \
						   GarbageCollectionToken, \
						   unsigned max_events); \
	template void Interpreter<t>::runToAccessLoggingEvents(ThreadId tid, \
							       unsigned nr_accesses, \
							       GarbageCollectionToken, \
							       VexPtr<LogWriter<t> > &output); \
	template void Interpreter<t>::replayLogfile(VexPtr<LogReader<t> > &lf, \
						    LogReaderPtr ptr,	\
						    GarbageCollectionToken, \
						    LogReaderPtr *eof,	\
						    VexPtr<LogWriter<t> > &lw, \
						    VexPtr<EventRecorder<t> > &er,\
						    EventTimestamp *);	\
	template InterpretResult Interpreter<t>::getThreadMemoryTrace(ThreadId tid, \
								      MemoryTrace<t> **output, \
								      unsigned max_events, \
								      GarbageCollectionToken); \
	template void Interpreter<t>::runToEvent(EventTimestamp end,	\
						 VexPtr<LogReader<t> > &lf, \
						 LogReaderPtr ptr,	\
						 GarbageCollectionToken, \
						 LogReaderPtr *eof)


