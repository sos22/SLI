#include <time.h>

#include "sli.h"
#include "state_machine.hpp"

#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"
#include "cnf.hpp"

#include "libvex_guest_offsets.h"
#include "libvex_prof.hpp"
#include "../VEX/priv/guest_generic_bb_to_IR.h"
#include "../VEX/priv/guest_amd64_defs.h"

/* Returns true if the operation definitely commutes, or false if
 * we're not sure. */
static bool
operationCommutes(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) ||
		(op >= Iop_CmpEQ8 && op <= Iop_CmpEQ64) ||
		(op == Iop_And1) ||
		(op == Iop_Or1) ||
		(op == Iop_Xor1);
}

/* Returns true if the operation definitely associates in the sense
 * that (a op b) op c == a op (b op c), or false if we're not sure. */
static bool
operationAssociates(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) || (op == Iop_And1) ||
		(op >= Iop_And8 && op <= Iop_And64) || (op >= Iop_Xor8 && op <= Iop_Xor64) ||
		(op >= Iop_Or8 && op <= Iop_Or64) || (op == Iop_Or1) ||
		(op == Iop_Xor1)
		;
}

bool
physicallyEqual(const IRConst *a, const IRConst *b)
{
	if (a->tag != b->tag)
		return false;
	switch (a->tag) {
#define do_case(t)					\
		case Ico_ ## t:				\
			return a->Ico. t == b->Ico. t
		do_case(U1);
		do_case(U8);
		do_case(U16);
		do_case(U32);
		do_case(U64);
		do_case(F64);
		do_case(F64i);
		do_case(V128);
#undef do_case
	}
	abort();
}

static bool
physicallyEqual(const IRRegArray *a, const IRRegArray *b)
{
	return a->base == b->base && a->elemTy == b->elemTy && a->nElems == b->nElems;
}

static bool
physicallyEqual(const IRCallee *a, const IRCallee *b)
{
	return a->addr == b->addr;
}

static bool
physicallyEqual(const IRExpr *_a, const IRExpr *_b)
{
	if (_a == _b)
		return true;
	if (_a->tag != _b->tag)
		return false;
	switch (_a->tag) {
#define hdr(type)							\
	case Iex_ ## type : {					        \
		const IRExpr ## type *a = (const IRExpr ## type *)_a,	\
			*b = (const IRExpr ## type *)_b;
#define footer() }
	hdr(Get)
		return threadAndRegister::fullEq(a->reg, b->reg) && a->ty == b->ty;
	footer()
	hdr(GetI)
		return a->bias == b->bias &&
			physicallyEqual(a->descr,
					b->descr) &&
			physicallyEqual(a->ix,
					b->ix);
	footer()
	hdr(Qop)
		return a->op == b->op &&
		       physicallyEqual(a->arg1, b->arg1) &&
		       physicallyEqual(a->arg2, b->arg2) &&
		       physicallyEqual(a->arg3, b->arg3) &&
		       physicallyEqual(a->arg4, b->arg4);
	footer()
	hdr(Triop)
		return a->op == b->op &&
		       physicallyEqual(a->arg1, b->arg1) &&
		       physicallyEqual(a->arg2, b->arg2) &&
		       physicallyEqual(a->arg3, b->arg3);
	footer()
	hdr(Binop)
		return a->op == b->op &&
		       physicallyEqual(a->arg1, b->arg1) &&
		       physicallyEqual(a->arg2, b->arg2);
	footer()
	hdr(Unop)
		return a->op == b->op &&
		       physicallyEqual(a->arg, b->arg);
	footer()
	hdr(Load)
		return a->ty == b->ty &&
			physicallyEqual(a->addr, b->addr);
	footer();
	hdr(Const)
		return physicallyEqual(a->con, b->con);
	footer()
	hdr(CCall)
		if (a->retty != b->retty || !physicallyEqual(a->cee, b->cee))
			return false;
		int x;
		for (x = 0; a->args[x]; x++) {
			if (!b->args[x])
				return false;
			if (!physicallyEqual(a->args[x],
					     b->args[x]))
				return false;
		}
		if (b->args[x])
			return false;
		return true;
	footer()
	hdr(Mux0X)
		return physicallyEqual(a->cond,
				       b->cond) &&
			physicallyEqual(a->expr0,
					b->expr0) &&
			physicallyEqual(a->exprX,
					b->exprX);
	footer()
	hdr(Associative)
		if (a->op != b->op ||
		    a->nr_arguments != b->nr_arguments)
			return false;
		for (int x = 0; x < a->nr_arguments; x++)
			if (!physicallyEqual(a->contents[x],
					     b->contents[x]))
				return false;
		return true;
	footer()
	hdr(FreeVariable)
		return a->key == b->key;
	footer()
	hdr(ClientCall)
		if (a->calledRip != b->calledRip ||
		    a->callSite != b->callSite)
			return false;
		for (int i = 0; ; i++) {
			if (!a->args[i]) {
				if (!b->args[i])
					return true;
				else
					return false;
			} else if (!b->args[i])
				return false;
			if (!physicallyEqual(a->args[i],
					     b->args[i]))
				return false;
		}
		abort();
	footer()
	hdr(ClientCallFailed)
		return physicallyEqual(a->target,
				       b->target);
	footer()
	hdr(HappensBefore)
		return a->before == b->before &&
			a->after == b->after;
	footer()
#undef footer
#undef hdr
	}
	abort();
}

static IRExpr *
optimise_condition_calculation(
	IRExpr *_cond,
	IRExpr *cc_op,
	IRExpr *dep1,
	IRExpr *dep2,
	IRExpr *ndep,
	const AllowableOptimisations &opt)
{
	unsigned long cond;
	IRExpr *res;
	bool invert;
	IRExpr *sf, *cf, *zf, *of;
	unsigned long op;

	/* We only handle a few very special cases here. */
	if (_cond->tag != Iex_Const || cc_op->tag != Iex_Const)
		return NULL;
	cond = ((IRExprConst *)_cond)->con->Ico.U64;
	op = ((IRExprConst *)cc_op)->con->Ico.U64;
	invert = cond & 1;
	cond &= ~1ul;
	res = NULL;
	sf = cf = zf = of = NULL;

	switch (op) {
	case AMD64G_CC_OP_SUBB:
		zf = IRExpr_Binop(Iop_CmpEQ8, dep1, dep2);
		break;
	case AMD64G_CC_OP_SUBW:
		zf = IRExpr_Binop(Iop_CmpEQ16, dep1, dep2);
		break;
	case AMD64G_CC_OP_SUBL:
	case AMD64G_CC_OP_SUBQ:
		zf = IRExpr_Binop(
			Iop_CmpEQ64,
			dep1,
			dep2);
		cf = IRExpr_Binop(
			Iop_CmpLT64U,
			dep1,
			dep2);
		sf = IRExpr_Binop(
			Iop_CmpLT64S,
			dep1,
			dep2);
		of = IRExpr_Binop(
			Iop_CC_OverflowSub,
			dep1,
			dep2);
		break;
	case AMD64G_CC_OP_LOGICB:
	case AMD64G_CC_OP_LOGICL:
	case AMD64G_CC_OP_LOGICQ:
		zf = IRExpr_Binop(
			Iop_CmpEQ64,
			dep1,
			IRExpr_Const(IRConst_U64(0)));
		sf = IRExpr_Binop(
			Iop_CmpLT64S,
			dep1,
			IRExpr_Const(IRConst_U32(0)));
		of = IRExpr_Const(IRConst_U1(0));
		break;
	case AMD64G_CC_OP_ADDW:
		sf = IRExpr_Binop(
			Iop_CmpLT32S,
			IRExpr_Binop(
				Iop_Add16,
				dep1,
				dep2),
			IRExpr_Const(IRConst_U16(0)));
		break;
	default:
		printf("Unknown CC op %lx\n", op);
		break;
	}

	switch (cond) {
	case AMD64CondZ:
		res = zf;
		break;
	case AMD64CondB:
		res = cf;
		break;
	case AMD64CondBE:
		if (cf && zf)
			res = IRExpr_Binop(
				Iop_Or1,
				cf,
				zf);
		break;
	case AMD64CondS:
		res = sf;
		break;
	case AMD64CondL:
		if (sf && of)
			res = IRExpr_Binop(
				Iop_Xor1,
				sf,
				of);
		else
			printf("CondL needs both sf and of; op %lx\n", op);
		break;
	case AMD64CondLE:
		if (sf && of && zf)
			res = IRExpr_Binop(
				Iop_Or1,
				IRExpr_Binop(
					Iop_Xor1,
					sf,
					of),
				zf);
		else
			printf("CondLE needs sf, of, and zf; op %lx\n", op);
		break;
	default:
		break;
	}
	if (!res)
		printf("Cannot handle CC condition %ld, op %lx\n",
		       cond, op);
	if (res && invert)
		res = IRExpr_Unop(Iop_Not1, res);
	return res;
}

/* Wherever we have a choice as to the ordering of an expression's
   sub-expressions, we sort them into ascending order of complexity,
   where complexity is defined by this function.  The main requirement
   is that if both x and -x occur in the argument list, x will occur
   before -x. */
/* If two expressions have the same complexity, we use a lexicographic
   ordering to distinguish them. */
int
exprComplexity(const IRExpr *e)
{
	class _ : public IRExprTransformer {
	public:
		int res;
		_() : res(0) {}
		IRExpr *transformIex(IRExprGet *e) {
			res += 20;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprGetI *e) {
			res += 20;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprQop *e) {
			res += 10;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprTriop *e) {
			res += 10;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprBinop *e) {
			res += 10;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprUnop *e) {
			res += 10;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprLoad *e) {
			res += 10;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprConst *e) {
			return NULL;
		}
		IRExpr *transformIex(IRExprMux0X *e) {
			res += 10;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprCCall *e) {
			res += 50;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprAssociative *e) {
			res += 10;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprFreeVariable *e) {
			res += 100;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprClientCall *e) {
			res += 100;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprClientCallFailed *e) {
			res += 1000;
			return IRExprTransformer::transformIex(e);
		}
		IRExpr *transformIex(IRExprHappensBefore *e) {
			res += 100;
			return IRExprTransformer::transformIex(e);
		}
	} t;
	t.transformIRExpr((IRExpr *)e);
	return t.res;
}

static int
ordering_iex_tag(IRExprTag a)
{
	switch (a) {
	case Iex_Const: return 0;
	case Iex_Get: return 2;
	case Iex_GetI: return 3;
	case Iex_FreeVariable: return 5;
	case Iex_Unop: return 6;
	case Iex_Binop: return 7;
	case Iex_Triop: return 8;
	case Iex_Qop: return 9;
	case Iex_Associative: return 10;
	case Iex_Mux0X: return 11;
	case Iex_Load: return 12;
	case Iex_CCall: return 13;
	case Iex_ClientCall: return 14;
	case Iex_ClientCallFailed: return 15;
	case Iex_HappensBefore: return 16;
	}
	abort();
}

static bool
IexTagLessThan(IRExprTag a, IRExprTag b)
{
	if (a == b)
		return false;

	int _a = ordering_iex_tag(a);
	int _b = ordering_iex_tag(b);
	return _a < _b;
}

static bool
sortIRConsts(IRConst *a, IRConst *b)
{
	if (a->tag < b->tag)
		return true;
	if (a->tag > b->tag)
		return false;
	switch (a->tag) {
#define do_type(t)					\
		case Ico_ ## t :			\
			return a->Ico. t < b->Ico. t
		do_type(U1);
		do_type(U8);
		do_type(U16);
		do_type(U32);
		do_type(U64);
		do_type(F64);
		do_type(F64i);
		do_type(V128);
#undef do_type
	}
	abort();
}

static bool
sortIRExprs(IRExpr *_a, IRExpr *_b)
{
	int ac = exprComplexity(_a);
	int bc = exprComplexity(_b);
	if (ac < bc)
		return true;
	if (ac > bc)
		return false;
	if (IexTagLessThan(_a->tag, _b->tag)) {
		return true;
	} else if (IexTagLessThan(_b->tag, _a->tag)) {
		return false;
	}
	assert(_a->tag == _b->tag);

	switch (_a->tag) {
#define hdr1(t)								\
		case Iex_ ## t:	{					\
			IRExpr ## t *a = (IRExpr ## t *)_a,		\
				*b = (IRExpr ## t *)_b;
	hdr1(Get)
#define hdr(t) } hdr1(t)
		return threadAndRegister::fullCompare()(a->reg, b->reg);
	hdr(GetI)
		return sortIRExprs(a->ix, b->ix);
	hdr(Qop)
		if (a->op < b->op)
			return true;
		if (a->op > b->op)
			return false;
		if (sortIRExprs(a->arg1, b->arg1))
			return true;
		else if (sortIRExprs(b->arg1, a->arg1))
			return false;
		else if (sortIRExprs(a->arg2, b->arg2))
			return true;
		else if (sortIRExprs(b->arg2, a->arg2))
			return false;
		else if (sortIRExprs(a->arg3, b->arg3))
			return true;
		else if (sortIRExprs(b->arg3, a->arg3))
			return false;
		else 
			return sortIRExprs(a->arg4, b->arg4);
	hdr(Triop)
		if (a->op < b->op)
			return true;
		if (a->op > b->op)
			return false;
		if (sortIRExprs(a->arg1, b->arg1))
			return true;
		else if (sortIRExprs(b->arg1, a->arg1))
			return false;
		else if (sortIRExprs(a->arg2, b->arg2))
			return true;
		else if (sortIRExprs(b->arg2, a->arg2))
			return false;
		else 
			return sortIRExprs(a->arg3, b->arg3);
	hdr(Binop)
		if (a->op < b->op)
			return true;
		if (a->op > b->op)
			return false;
		if (sortIRExprs(a->arg1, b->arg1))
			return true;
		else if (sortIRExprs(b->arg1, a->arg1))
			return false;
		else
			return sortIRExprs(a->arg2, b->arg2);
	hdr(Unop)
		if (a->op < b->op)
			return true;
		if (a->op > b->op)
			return false;
		return sortIRExprs(a->arg, b->arg);
	hdr(Load)
		return sortIRExprs(a->addr, b->addr);
	hdr(Const)
		return sortIRConsts(a->con, b->con);
	hdr(CCall) {
		int r = strcmp(a->cee->name,
			       b->cee->name);
		if (r < 0)
			return true;
		else if (r > 0)
			return false;
		for (int x = 0; 1; x++) {
			if (!a->args[x] && !b->args[x])
				return false;
			if (!a->args[x])
				return true;
			if (!b->args[x])
				return false;
			if (sortIRExprs(a->args[x], b->args[x]))
				return true;
			if (sortIRExprs(b->args[x], a->args[x]))
				return false;
		}
	}
	hdr(Mux0X)
		if (sortIRExprs(a->cond, b->cond))
			return true;
		else if (sortIRExprs(b->cond, a->cond))
			return false;
		else if (sortIRExprs(a->expr0, b->expr0))
			return true;
		else if (sortIRExprs(b->expr0, a->expr0))
			return false;
		else
			return sortIRExprs(a->exprX, b->exprX);
	hdr(Associative) {
		if (a->op < b->op)
			return true;
		if (a->op > b->op)
			return false;
		int x;
		x = 0;
		while (1) {
			if (x == a->nr_arguments &&
			    x == b->nr_arguments)
				return false;
			if (x == a->nr_arguments)
				return true;
			if (x == b->nr_arguments)
				return false;
			if (sortIRExprs(a->contents[x], b->contents[x]))
				return true;
			else if (sortIRExprs(b->contents[x], a->contents[x]))
				return false;
			x++;
		}
	}
	hdr(FreeVariable)
		return a->key < b->key;
	hdr(ClientCall)
		if (a->callSite < b->callSite)
			return true;
		else if (a->callSite > b->callSite)
			return false;
		for (int x = 0; 1; x++) {
			if (!a->args[x] && !b->args[x])
				return false;
			if (!a->args[x])
				return true;
			if (!b->args[x])
				return false;
			if (sortIRExprs(a->args[x], b->args[x]))
				return true;
			else if (sortIRExprs(b->args[x], a->args[x]))
				return false;
		}
	hdr(ClientCallFailed)
		return sortIRExprs(a->target,
				   b->target);
	hdr(HappensBefore)
		if (a->before < b->before)
			return true;
		if (a->before > b->before)
			return false;
		return a->after < b->after;
	}
#undef hdr
	}

	abort();
}

template <typename t> void
merge(t &out, const t &inp1, const t&inp2, bool (*lessThan)(typename t::member_t a, typename t::member_t b))
{
	assert(out.size() == inp1.size() + inp2.size());
	unsigned x, y, z;
	x = 0;
	y = 0;
	z = 0;
	while (x < inp1.size() && y < inp2.size()) {
		if (lessThan(inp1[x], inp2[y])) {
			out[z++] = inp1[x++];
		} else {
			out[z++] = inp2[y++];
		}
	}
	while (x < inp1.size())
		out[z++] = inp1[x++];
	while (y < inp2.size())
		out[z++] = inp2[y++];
}

template <typename t> void
merge_sort(t &out, const t &inp, bool (*lessThan)(typename t::member_t a, typename t::member_t b))
{
	assert(out.size() == inp.size());
	if (inp.size() == 0)
		return;
	if (inp.size() == 1) {
		out = inp;
		return;
	}
	unsigned div = inp.size() / 2;

	t sublist1(div);
	t sublist2(inp.size() - div);
	merge_sort(sublist1, inp.slice(0, div), lessThan);
	merge_sort(sublist2, inp.slice(div, inp.size()), lessThan);
	merge(out, sublist1, sublist2, lessThan);
}

template <typename t>
class vector_slice {
	std::vector<t> dummy;
public:
	typedef t member_t;
	std::vector<t> &underlying;
	unsigned start; /* inclusive */
	unsigned end; /* exclusive */
	vector_slice(std::vector<t> &_underlying)
		: underlying(_underlying), start(0), end(_underlying.size())
	{}
	vector_slice(std::vector<t> &_underlying, unsigned _start, unsigned _end)
		: underlying(_underlying), start(_start), end(_end)
	{
		assert(start <= underlying.size());
		assert(end <= underlying.size());
		assert(start <= end);
	}
	vector_slice(unsigned sz)
		: underlying(dummy), start(0), end(sz)
	{
		dummy.resize(sz);
	}
	const vector_slice<t> slice(unsigned new_start, unsigned new_end) const
	{
		assert(new_end >= new_start);
		assert(new_end + start <= end);
		assert(new_start + start <= end);
		return vector_slice(underlying, new_start + start, new_end + start);
	}
	vector_slice<t> slice(unsigned new_start, unsigned new_end)
	{
		assert(new_end >= new_start);
		assert(new_end + start <= end);
		assert(new_start + start <= end);
		return vector_slice(underlying, new_start + start, new_end + start);
	}
	const t&operator[](unsigned idx) const {
		assert(idx < size());
		return underlying[idx + start];
	}
	t &operator[](unsigned idx) {
		assert(idx < size());
		return underlying[idx + start];
	}
	unsigned size() const { return end - start; }
	void operator = (const vector_slice<t> &other) {
		assert(size() == other.size());
		for (unsigned x = 0; x < size(); x++)
			(*this)[x] = other[x];
	}
};

void
addArgumentToAssoc(IRExprAssociative *e, IRExpr *arg)
{
	assert( (e->optimisationsApplied & ~arg->optimisationsApplied) == 0);
	if (e->nr_arguments == e->nr_arguments_allocated) {
		e->nr_arguments_allocated += 8;
		e->contents = (IRExpr **)
			LibVEX_realloc(&ir_heap,
				       e->contents,
				       sizeof(IRExpr *) * e->nr_arguments_allocated);
	}
	e->contents[e->nr_arguments] = arg;
	e->nr_arguments++;
}

static void
purgeAssocArgument(IRExprAssociative *e, int idx)
{
	assert(idx < e->nr_arguments);
	memmove(e->contents + idx,
		e->contents + idx + 1,
		sizeof(IRExpr *) * (e->nr_arguments - idx - 1));
	e->nr_arguments--;
}

static IRExpr *optimiseIRExpr(IRExpr *src, const AllowableOptimisations &opt, bool *done_something);

IRExpr *
optimiseIRExprFP(IRExpr *e, const AllowableOptimisations &opt, bool *done_something)
{
#if MANUAL_PROFILING
	static ProfilingSite __site("optimiseIRExprFP");
	static bool live;
	bool do_profiling;
	do_profiling = !live;
	unsigned long s = do_profiling ? SetProfiling::rdtsc() : 0;
	live = true;
#endif

	bool progress;
	progress = false;
	e = optimiseIRExpr(e, opt, &progress);
	if (progress) {
		*done_something = true;
		while (progress) {
			if (TIMEOUT) {
#if MANUAL_PROFILING
				live = false;
#endif
				return e;
			}
			progress = false;
			e = optimiseIRExpr(e, opt, &progress);
		}
	}
	e->optimisationsApplied |= opt.asUnsigned();
#if MANUAL_PROFILING
	if (do_profiling) {
		__site.accumulated_ticks += SetProfiling::rdtsc() - s;
		__site.nr_sites++;
		live = false;
	}
#endif
	return e;
}

static IRExpr *
optimiseIRExpr(IRExpr *src, const AllowableOptimisations &opt, bool *done_something)
{
	if (TIMEOUT)
		return src;

	if (!(opt.asUnsigned() & ~src->optimisationsApplied))
		return src;

	class _ : public IRExprTransformer {
		const AllowableOptimisations &opt;
		bool *done_something;

		IRExpr *transformIex(IRExprCCall *e) {
#define hdr(type)							\
			IRExpr *res = IRExprTransformer::transformIex(e); \
			if (res) {					\
				if (IRExpr ## type *e2 = dynamic_cast<IRExpr ## type *>(res)) \
					e = e2;				\
				else					\
					return res;			\
			} else {					\
				res = e;				\
			}
			hdr(CCall)
			if (!strcmp(e->cee->name, "amd64g_calculate_condition")) {
				return optimise_condition_calculation(
					e->args[0],
					e->args[1],
					e->args[2],
					e->args[3],
					e->args[4],
					opt);
			}
			return res;
		}
		IRExpr *transformIex(IRExprAssociative *e) {
			hdr(Associative)
			__set_profiling(optimise_associative);

			/* Drag up nested associatives. */
			bool haveNestedAssocs = false;
			for (int x = 0; !haveNestedAssocs && x < e->nr_arguments; x++)
				if (e->contents[x]->tag == Iex_Associative &&
				    ((IRExprAssociative *)e->contents[x])->op == e->op)
					haveNestedAssocs = true;
			if (haveNestedAssocs) {
				__set_profiling(pull_up_nested_associatives);
				IRExprAssociative *ne = (IRExprAssociative *)IRExpr_Associative(e->op, NULL);
				for (int x = 0; x < e->nr_arguments; x++) {
					IRExpr *arg = e->contents[x];
					if (arg->tag == Iex_Associative &&
					    ((IRExprAssociative *)arg)->op == e->op) {
						IRExprAssociative *_arg = (IRExprAssociative *)arg;
						for (int y = 0; y < _arg->nr_arguments; y++)
							addArgumentToAssoc(ne, _arg->contents[y]);
					} else {
						addArgumentToAssoc(ne, arg);
					}
				}
				return ne;
			}

			/* Sort IRExprs so that ``related'' expressions are likely to
			 * be close together. */
			if (operationCommutes(e->op)) {
				__set_profiling(sort_associative_arguments);
				std::vector<IRExpr *> c;
				c.resize(e->nr_arguments);
				for (int x = 0; x < e->nr_arguments; x++)
					c[x] = e->contents[x];
				std::vector<IRExpr *> out;
				out.resize(e->nr_arguments);
				vector_slice<IRExpr *> out_slice(out);
				vector_slice<IRExpr *> inp_slice(c);
				merge_sort(out_slice, inp_slice, sortIRExprs);
				for (int x = 0; x < e->nr_arguments; x++)
					e->contents[x] = out[x];
			}
			/* Fold together constants.  For commutative
			   operations they'll all be at the beginning, but
			   don't assume that associativity implies
			   commutativity. */
			{
				__set_profiling(associative_constant_fold);
				for (int x = 0; x + 1 < e->nr_arguments; x++) {
					IRExpr *a, *b;
					a = e->contents[x];
					b = e->contents[x+1];
					if (a->tag == Iex_Const && b->tag == Iex_Const) {
						IRExpr *res;
						IRConst *l, *r;
						l = ((IRExprConst *)a)->con;
						r = ((IRExprConst *)b)->con;
						switch (e->op) {
						case Iop_Add8:
							res = IRExpr_Const(
								IRConst_U8((l->Ico.U8 + r->Ico.U8) & 0xff));
							break;
						case Iop_Add16:
							res = IRExpr_Const(
								IRConst_U16((l->Ico.U16 + r->Ico.U16) & 0xffff));
							break;
						case Iop_Add32:
							res = IRExpr_Const(
								IRConst_U32((l->Ico.U32 + r->Ico.U32) & 0xffffffff));
							break;
						case Iop_Add64:
							res = IRExpr_Const(IRConst_U64(l->Ico.U64 + r->Ico.U64));
							break;
						case Iop_And1:
							res = IRExpr_Const(IRConst_U1(!!(l->Ico.U1 & r->Ico.U1)));
							break;
						case Iop_Or1:
							res = IRExpr_Const(IRConst_U1(!!(l->Ico.U1 | r->Ico.U1)));
							break;
						case Iop_And8:
							res = IRExpr_Const(IRConst_U8(l->Ico.U8 & r->Ico.U8));
							break;
						case Iop_And16:
							res = IRExpr_Const(IRConst_U16(l->Ico.U16 & r->Ico.U16));
							break;
						case Iop_And32:
							res = IRExpr_Const(IRConst_U32(l->Ico.U32 & r->Ico.U32));
							break;
						case Iop_Or32:
							res = IRExpr_Const(IRConst_U32(l->Ico.U32 | r->Ico.U32));
							break;
						case Iop_And64:
							res = IRExpr_Const(IRConst_U64(l->Ico.U64 & r->Ico.U64));
							break;
						case Iop_Xor8:
							res = IRExpr_Const(IRConst_U32(l->Ico.U8 ^ r->Ico.U8));
							break;
						case Iop_Xor32:
							res = IRExpr_Const(IRConst_U32(l->Ico.U32 ^ r->Ico.U32));
							break;
						default:
							printf("Warning: can't constant-fold associative op %d\n", e->op);
							res = NULL;
							break;
						}
						if (res) {
							memmove(e->contents + x + 1,
								e->contents + x + 2,
								sizeof(IRExpr *) * (e->nr_arguments - x - 2));
							e->nr_arguments--;
							e->contents[x] = res;
							*done_something = true;
							x--;
						}
					} else if (!operationCommutes(e->op)) {
						break;
					}
				}
			}
			/* Some special cases for And1: 1 & x -> x, 0 & x -> 0 */
			if (e->op == Iop_And1) {
				__set_profiling(optimise_assoc_and1);
				/* If there are any constants, they'll be at the start. */
				while (e->nr_arguments > 1 &&
				       e->contents[0]->tag == Iex_Const) {
					IRConst *c = ((IRExprConst *)e->contents[0])->con;
					*done_something = true;
					if (c->Ico.U1) {
						purgeAssocArgument(e, 0);
					} else {
						return e->contents[0];
					}
				}
			}
			/* Likewise for Or1 */
			if (e->op == Iop_Or1) {
				__set_profiling(optimise_assoc_or1);
				while (e->nr_arguments > 1 &&
				       e->contents[0]->tag == Iex_Const) {
					IRConst *c = ((IRExprConst *)e->contents[0])->con;
					*done_something = true;
					if (!c->Ico.U1) {
						purgeAssocArgument(e, 0);
					} else {
						return e->contents[0];
					}
				}
			}
			/* And for Add */
			if (e->op == Iop_Add64) {
				if (e->nr_arguments > 1 &&
				    e->contents[0]->tag == Iex_Const &&
				    ((IRExprConst *)e->contents[0])->con->Ico.U64 == 0) {
					purgeAssocArgument(e, 0);
					*done_something = true;
				}
			}
			/* x & x -> x, for any and-like operator */
			if (e->op >= Iop_And8 && e->op <= Iop_And64) {
				__set_profiling(optimise_assoc_x_and_x);
				for (int it1 = 0;
				     it1 < e->nr_arguments;
				     it1++) {
					for (int it2 = it1 + 1;
					     it2 < e->nr_arguments;
						) {
						if (definitelyEqual(e->contents[it1],
								    e->contents[it2],
								    opt)) {
							*done_something = true;
							purgeAssocArgument(e, it2);
						} else {
							it2++;
						}
					}
				}
			}

			/* a <-< b || b <-< a is definitely true. */
			if (e->op == Iop_Or1) {
				__set_profiling(optimise_assoc_happens_before);
				for (int i1 = 0; i1 < e->nr_arguments; i1++) {
					if (e->contents[i1]->tag != Iex_HappensBefore)
						continue;
					IRExprHappensBefore *a1 = (IRExprHappensBefore *)e->contents[i1];
					for (int i2 = i1 + 1; i2 < e->nr_arguments; i2++) {
						if (e->contents[i2]->tag != Iex_HappensBefore)
							continue;
						IRExprHappensBefore *a2 =
							(IRExprHappensBefore *)e->contents[i2];
						if ( a1->before == a2->after &&
						     a1->after == a2->before )
							return IRExpr_Const(IRConst_U1(1));
					}
				}
			}

			/* x + -x -> 0, for any plus-like operator, so remove
			 * both x and -x from the list. */
			/* Also do x & ~x -> 0, x ^ x -> 0, while we're here. */
			if (opt.xPlusMinusX) {
				__set_profiling(optimise_assoc_xplusminusx);
				bool plus_like;
				bool and_like;
				bool xor_like;
				plus_like = e->op >= Iop_Add8 && e->op <= Iop_Add64;
				and_like = (e->op >= Iop_And8 && e->op <= Iop_And64) ||
					e->op == Iop_And1;
				xor_like = e->op >= Iop_Xor8 && e->op <= Iop_Xor64;
				if (plus_like || and_like || xor_like) {
					for (int it1 = 0;
					     it1 < e->nr_arguments;
						) {
						IRExpr *l = e->contents[it1];
						int it2;
						for (it2 = 0;
						     it2 < e->nr_arguments;
						     it2++) {
							if (it2 == it1)
								continue;
							IRExpr *r = e->contents[it2];
							bool purge;
							if (plus_like) {
								if (r->tag == Iex_Unop) {
									IROp op = ((IRExprUnop *)r)->op;
									purge = op >= Iop_Neg8 &&
										op <= Iop_Neg64;
								} else {
									purge = false;
								}
								if (purge)
									purge = l == ((IRExprUnop *)r)->arg;
							} else if (and_like) {
								if (r->tag == Iex_Unop) {
									IROp op = ((IRExprUnop *)r)->op;
									purge = (op >= Iop_Not8 &&
										 op <= Iop_Not64) ||
										op == Iop_Not1;
								} else
									purge = false;
								if (purge)
									purge = l == ((IRExprUnop *)r)->arg;
							} else {
								assert(xor_like);
								purge = l == r;
							}

							if (purge) {
								*done_something = true;
								if (and_like) {
									/* x & ~x -> 0 and eliminates the entire expression. */
									switch (e->op) {
									case Iop_And8:
										return IRExpr_Const(IRConst_U8(0));
									case Iop_And16:
										return IRExpr_Const(IRConst_U16(0));
									case Iop_And32:
										return IRExpr_Const(IRConst_U32(0));
									case Iop_And64:
										return IRExpr_Const(IRConst_U64(0));
									case Iop_And1:
										return IRExpr_Const(IRConst_U1(0));
									default:
										abort();
									}
								}

								/* Careful: do the largest index first so that the
								   other index remains valid. */
								if (it1 < it2) {
									purgeAssocArgument(e, it2);
									e->contents[it1] =
										IRExpr_Const(IRConst_U64(0));
								} else {
									purgeAssocArgument(e, it1);
									e->contents[it2] =
										IRExpr_Const(IRConst_U64(0));
								}
								break;
							}
						}
						if (it2 == e->nr_arguments)
							it1++;
					}
				}
				if (e->nr_arguments == 0) {
					*done_something = true;
					switch (e->op) {
					case Iop_Add8:
					case Iop_Xor8:
						return IRExpr_Const(IRConst_U8(0));
					case Iop_Add16:
					case Iop_Xor16:
						return IRExpr_Const(IRConst_U16(0));
					case Iop_Add32:
					case Iop_Xor32:
						return IRExpr_Const(IRConst_U32(0));
					case Iop_Add64:
					case Iop_Xor64:
						return IRExpr_Const(IRConst_U64(0));

					case Iop_And1:
						return IRExpr_Const(IRConst_U1(1));
					case Iop_And8:
						return IRExpr_Const(IRConst_U8(0xff));
					case Iop_And16:
						return IRExpr_Const(IRConst_U16(0xffff));
					case Iop_And32:
						return IRExpr_Const(IRConst_U32(0xffffffff));
					case Iop_And64:
						return IRExpr_Const(IRConst_U64(0xfffffffffffffffful));

					case Iop_Or1:
						return IRExpr_Const(IRConst_U1(0));

					default:
						abort();
					}
				}
			}

			/* If the size is reduced to one, eliminate the assoc list */
			if (e->nr_arguments == 1) {
				*done_something = true;
				return e->contents[0];
			}

			return res;
		}

		IRExpr *transformIex(IRExprUnop *e) {
			hdr(Unop)
			__set_profiling(optimise_unop);
			if (e->op == Iop_64to1 &&
			    ((e->arg->tag == Iex_Associative &&
			      (((IRExprAssociative *)e->arg)->op == Iop_And1 ||
			       ((IRExprAssociative *)e->arg)->op == Iop_Or1)) ||
			     (e->arg->tag == Iex_Binop &&
			      ((((IRExprBinop *)e->arg)->op >= Iop_CmpEQ8 &&
				((IRExprBinop *)e->arg)->op <= Iop_CmpNE64) ||
			       (((IRExprBinop *)e->arg)->op >= Iop_CmpLT32S &&
				((IRExprBinop *)e->arg)->op <= Iop_CmpLE64U))))) {
				/* This can happen sometimes because of the
				   way we simplify condition codes.  Very easy
				   fix: strip off the outer 64to1. */
				*done_something = true;
				return e->arg;
			}

			if ((e->op >= Iop_8Uto16 &&
			     e->op <= Iop_32Uto64) ||
			    e->op == Iop_1Uto8) {
				/* Get rid of unsigned upcasts; they tend to
				   show up where you don't want them, and they
				   don't actually do anything useful. */
				*done_something = true;
				return e->arg;
			}

			if (e->op == Iop_Not1 &&
			    e->arg->tag == Iex_Unop &&
			    ((IRExprUnop *)e->arg)->op == e->op) {
				return ((IRExprUnop *)e->arg)->arg;
			}

			if (e->op == Iop_Not1 &&
			    e->arg->tag == Iex_Associative &&
			    (((IRExprAssociative *)e->arg)->op == Iop_And1 ||
			     ((IRExprAssociative *)e->arg)->op == Iop_Or1)) {
				/* Convert ~(x & y) to ~x | ~y */
				IRExprAssociative *a =
					(IRExprAssociative *)IRExpr_Associative((IRExprAssociative *)e->arg);
				for (int i = 0;
				     i < a->nr_arguments;
				     i++) {
					a->contents[i] =
						optimiseIRExprFP(
							IRExpr_Unop(
								Iop_Not1,
								a->contents[i]),
							opt,
							done_something);
				}
				if (a->op == Iop_And1)
					a->op = Iop_Or1;
				else
					a->op = Iop_And1;
				return a;
			}
			if (e->op == Iop_BadPtr) {
				if (e->arg->tag == Iex_Associative &&
				    ((IRExprAssociative *)e->arg)->op == Iop_Add64 &&
				    ((IRExprAssociative *)e->arg)->nr_arguments == 2 &&
				    ((IRExprAssociative *)e->arg)->contents[0]->tag == Iex_Const) {
					/* BadPtr(k + x) -> BadPtr(x) if k is
					 * a constant.  That's not strictly
					 * speaking true, because it's always
					 * possible that k is enough to push
					 * you over the boundary between valid
					 * and invalid memory, but that's so
					 * rare that I'm willing to ignore
					 * it. */
					*done_something = true;
					e->arg = ((IRExprAssociative *)e->arg)->contents[1];
					return e;
				}
				if (e->arg->tag == Iex_Get &&
				    !((IRExprGet *)e->arg)->reg.isTemp() &&
				    (((IRExprGet *)e->arg)->reg.asReg() == offsetof(VexGuestAMD64State, guest_FS_ZERO) ||
				     ((IRExprGet *)e->arg)->reg.asReg() == offsetof(VexGuestAMD64State, guest_RSP))) {
					/* The FS and RSP registers are
					   assumed to always point at valid
					   memory. */
					return IRExpr_Const(IRConst_U1(0));
				}
			}
			if (e->arg->tag == Iex_Const) {
				IRConst *c = ((IRExprConst *)e->arg)->con;
				switch (e->op) {
				case Iop_Neg8:
					return IRExpr_Const(IRConst_U8(-c->Ico.U8));
				case Iop_Neg16:
					return IRExpr_Const(IRConst_U16(-c->Ico.U16));
				case Iop_Neg32:
					return IRExpr_Const(IRConst_U32(-c->Ico.U32));
				case Iop_Neg64:
					return IRExpr_Const(IRConst_U64(-c->Ico.U64));
				case Iop_Not1:
					return IRExpr_Const(IRConst_U1(!c->Ico.U1));
				case Iop_32Uto64:
					return IRExpr_Const(IRConst_U64(c->Ico.U32));
				case Iop_32Sto64:
					return IRExpr_Const(IRConst_U64((int)c->Ico.U32));
				case Iop_1Uto8:
					return IRExpr_Const(IRConst_U8(c->Ico.U1));
				case Iop_64to1:
					return IRExpr_Const(IRConst_U1(!!c->Ico.U64));
				case Iop_64to32:
					return IRExpr_Const(IRConst_U32(c->Ico.U64));
				case Iop_BadPtr:
					if (c->Ico.U64 < 4096) {
						return IRExpr_Const(IRConst_U1(1));
					}
					{
						/* We assume here that
						   anything which has a fixed
						   address must come out of
						   one of the binaries which
						   we've mapped.  That's not
						   *completely* sound, but
						   it's a pretty good
						   approximation, because
						   anything which is
						   dynamically allocated will
						   have a dynamic base, and
						   hence will never have a
						   constant address, and so
						   won't show up here.  If
						   it's not dynamically
						   allocated then it must have
						   come out of the binary, so
						   we'll know its address. */
						/* (This works for libraries,
						   as well: if it's an
						   internal reference then we
						   must have loaded the
						   library, so we'll be able
						   to tell whether it provides
						   a particular address; if
						   it's inter-module, then you
						   won't know the address of
						   the referrent when
						   compiling the referee, so
						   it won't show up as a
						   constant.) */
						bool t;
						if (opt.addressAccessible(c->Ico.U64, &t)) {
							return IRExpr_Const(IRConst_U1(!t));
						}
					}
					break;
				default:
					printf("Cannot constant fold unop %d\n", e->op);
					break;
				}
			}
			return res;
		}

		IRExpr *transformIex(IRExprBinop *e) {
			hdr(Binop)
			__set_profiling(optimise_binop);
			IRExpr *l = e->arg1;
			IRExpr *r = e->arg2;
			if (e->op == Iop_Xor1) {
				/* Convert A ^ B to (A & ~B) | (~A & B).  It's
				   bigger, but it's worth it just normalise
				   things. */
				*done_something = true;
				return optimiseIRExpr(
					IRExpr_Associative(
						Iop_Or1,
						IRExpr_Associative(
							Iop_And1,
							l,
							IRExpr_Unop(Iop_Not1, r),
							NULL),
						IRExpr_Associative(
							Iop_And1,
							r,
							IRExpr_Unop(Iop_Not1, l),
							NULL),
						NULL),
					opt,
					done_something);
			}
			if (e->op >= Iop_Sub8 &&
			    e->op <= Iop_Sub64) {
				/* Replace a - b with a + (-b), so as to
				   eliminate binary -. */
				*done_something = true;
				e->op = (IROp)(e->op - Iop_Sub8 + Iop_Add8);
				r = e->arg2 =
					optimiseIRExprFP(
						IRExpr_Unop( (IROp)((e->op - Iop_Add8) + Iop_Neg8),
							     r ),
						opt,
						done_something);
			}
			if (operationAssociates(e->op)) {
				/* Convert to an associative operation. */
				*done_something = true;
				return optimiseIRExpr(
					IRExpr_Associative(
						e->op,
						l,
						r,
						NULL),
					opt,
					done_something);
			}
			/* If a op b commutes, sort the arguments. */
			if (operationCommutes(e->op) &&
			    sortIRExprs(r, l)) {
				e->arg1 = r;
				e->arg2 = l;
				l = e->arg1;
				r = e->arg2;
				*done_something = true;
			}

			/* x << 0 -> x */
			if (e->op >= Iop_Shl8 && e->op <= Iop_Shl64 &&
			    r->tag == Iex_Const &&
			    ((IRExprConst *)r)->con->Ico.U8 == 0) {
				*done_something = true;
				return l;
			}

			/* We simplify == expressions with sums on the left
			   and right by trying to move all of the constants to
			   the left and all of the non-constants to the
			   right. */
			if (e->op == Iop_CmpEQ64) {
				if (l->tag == Iex_Const &&
				    ((IRExprConst *)l)->con->Ico.U64 == 0) {
					/* 0 == x is equivalent to just !x */
					*done_something = true;
					return IRExpr_Unop(
						Iop_Not1,
						r);
				}

				if (r->tag == Iex_Associative &&
				    ((IRExprAssociative *)r)->op == Iop_Add64 &&
				    ((IRExprAssociative *)r)->contents[0]->tag == Iex_Const) {
					assert(((IRExprAssociative *)r)->nr_arguments > 1);
					/* a == C + b -> -C + a == b */
					IRExpr *cnst = ((IRExprAssociative *)r)->contents[0];
					IRExprAssociative *newRight = (IRExprAssociative *)IRExpr_Associative((IRExprAssociative *)r);
					purgeAssocArgument(newRight, 0);
					IRExpr *newLeft = IRExpr_Associative(
						Iop_Add64,
						IRExpr_Unop(
							Iop_Neg64,
							cnst),
						l,
						NULL);
					l = e->arg1 = optimiseIRExprFP(newLeft, opt, done_something);
					r = e->arg2 = optimiseIRExprFP(newRight, opt, done_something);
					*done_something = true;
				}
				if (l->tag == Iex_Associative &&
				    ((IRExprAssociative *)l)->op == Iop_Add64) {
					/* C + a == b -> C == b - a */
					assert(((IRExprAssociative *)l)->nr_arguments > 1);
					IRExprAssociative *newR =
						(IRExprAssociative *)IRExpr_Associative(Iop_Add64, r, NULL);
					for (int it = 1;
					     it < ((IRExprAssociative *)l)->nr_arguments;
					     it++)
						addArgumentToAssoc(newR,
								   IRExpr_Unop(
									   Iop_Neg64,
									   ((IRExprAssociative *)l)->contents[it]));
					IRExpr *cnst = ((IRExprAssociative *)l)->contents[0];
					if (cnst->tag != Iex_Const) {
						addArgumentToAssoc(newR,
								   IRExpr_Unop(
									   Iop_Neg64,
									   cnst));
						cnst = IRExpr_Const(IRConst_U64(0));
					}
					l = e->arg1 = cnst;
					r = e->arg2 = optimiseIRExprFP(newR, opt, done_something);
					*done_something = true;
				}
				/* If, in a == b, a and b are physically
				 * identical, the result is a constant 1. */
				if (physicallyEqual(l, r)) {
					*done_something = true;
					return IRExpr_Const(IRConst_U1(1));
				}

				/* Otherwise, a == b -> 0 == b - a, provided that a is not a constant. */
				if (l->tag != Iex_Const) {
					e->arg1 = IRExpr_Const(IRConst_U64(0));
					e->arg2 =
						IRExpr_Binop(
							Iop_Add64,
							r,
							IRExpr_Unop(
								Iop_Neg64,
								l));
					*done_something = true;
					return e;
				}
			}

			/* And another one: -x == c -> x == -c if c is a constant. */
			if (e->op == Iop_CmpEQ64 &&
			    l->tag == Iex_Unop &&
			    ((IRExprUnop *)l)->op == Iop_Neg64 &&
			    r->tag == Iex_Const) {
				e->arg1 = ((IRExprUnop *)l)->arg;
				e->arg2 = IRExpr_Const(
					IRConst_U64(-((IRExprConst *)r)->con->Ico.U64));
				*done_something = true;
				return e;
			}

			/* If enabled, assume that the stack is ``private'',
			   in the sense that it doesn't alias with any global
			   variables, and is therefore never equal to any
			   constants which are present in the machine code. */
			if (opt.assumePrivateStack &&
			    e->op == Iop_CmpEQ64 &&
			    r->tag == Iex_Get &&
			    !((IRExprGet *)r)->reg.isTemp() &&
			    ((IRExprGet *)r)->reg.asReg() == OFFSET_amd64_RSP &&
			    l->tag == Iex_Const) {
				*done_something = true;
				return IRExpr_Const(IRConst_U1(0));
			}

			/* If both arguments are constant, try to constant
			 * fold everything away. */
			if (l->tag == Iex_Const &&
			    r->tag == Iex_Const) {
				switch (e->op) {
				case Iop_CmpEQ32:
					*done_something = true;
					return IRExpr_Const(
						IRConst_U1(
							((IRExprConst *)l)->con->Ico.U32 ==
							((IRExprConst *)r)->con->Ico.U32));
				case Iop_CmpLT64S:
					*done_something = true;
					return IRExpr_Const(
						IRConst_U1(
							(long)((IRExprConst *)l)->con->Ico.U64 <
							(long)((IRExprConst *)r)->con->Ico.U64));
				case Iop_CmpLT64U:
					*done_something = true;
					return IRExpr_Const(
						IRConst_U1(
							((IRExprConst *)l)->con->Ico.U64 <
							((IRExprConst *)r)->con->Ico.U64));
				case Iop_CmpEQ8:
					*done_something = true;
					return IRExpr_Const(
						IRConst_U1(
							((IRExprConst *)l)->con->Ico.U8 ==
							((IRExprConst *)r)->con->Ico.U8));
				case Iop_CmpEQ16:
					*done_something = true;
					return IRExpr_Const(
						IRConst_U1(
							((IRExprConst *)l)->con->Ico.U16 ==
							((IRExprConst *)r)->con->Ico.U16));
				case Iop_CmpEQ64:
					*done_something = true;
					return IRExpr_Const(
						IRConst_U1(
							((IRExprConst *)l)->con->Ico.U64 ==
							((IRExprConst *)r)->con->Ico.U64));
				case Iop_Sar32:
					*done_something = true;
					return IRExpr_Const(
						IRConst_U32(
							(int)((IRExprConst *)l)->con->Ico.U32 >>
							((IRExprConst *)r)->con->Ico.U8));
				case Iop_Sar64:
					*done_something = true;
					return IRExpr_Const(
						IRConst_U64(
							(long)((IRExprConst *)l)->con->Ico.U64 >>
							((IRExprConst *)r)->con->Ico.U8));
				case Iop_Shl64:
					*done_something = true;
					return IRExpr_Const(
						IRConst_U64(
							((IRExprConst *)l)->con->Ico.U64 <<
							((IRExprConst *)r)->con->Ico.U8));
				case Iop_CC_OverflowSub: {
					unsigned long a = ((IRExprConst *)l)->con->Ico.U64;
					unsigned long b = ((IRExprConst *)r)->con->Ico.U64;
					return IRExpr_Const(
						IRConst_U1(
							((a ^ b) & (a ^ (a - b))) >> 63));
				}
				case Iop_32HLto64:
					return IRExpr_Const(
						IRConst_U64(
							((unsigned long)((IRExprConst *)l)->con->Ico.U32 << 32) |
							((IRExprConst *)r)->con->Ico.U32));
				default:
					printf("Cannot constant fold binop %d\n", e->op);
					break;
				}
			}
			return res;
		}

		IRExpr *transformIex(IRExprMux0X *e) {
			hdr(Mux0X)
			if (e->cond->tag == Iex_Const) {
				*done_something = true;
				if (((IRExprConst *)e->cond)->con->Ico.U1)
					return e->exprX;
				else
					return e->expr0;
			}
			return res;
		}
#undef hdr
	public:
		_(const AllowableOptimisations &_opt,
		  bool *_done_something)
			: opt(_opt), done_something(_done_something)
		{}
	} t(opt, done_something);
	return t.transformIRExpr(src, done_something);
}

static IRExpr *
optimiseIRExpr(IRExpr *e, const AllowableOptimisations &opt)
{
	bool ign;
	ign = false;
	e = optimiseIRExprFP(e, opt, &ign);
	e = simplifyIRExprAsBoolean(e, &ign);
	e = optimiseIRExprFP(e, opt, &ign);
	return e;
}

IRExpr *
simplifyIRExpr(IRExpr *a, const AllowableOptimisations &opt)
{
	__set_profiling(simplifyIRExpr);
	bool done_something;

	do {
		done_something = false;
		if (TIMEOUT)
			return a;
		a = optimiseIRExpr(a, opt, &done_something);
		a = simplifyIRExprAsBoolean(a, &done_something);
	} while (done_something);

	return a;
}

bool
definitelyEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt)
{
	IRExpr *r = optimiseIRExpr(IRExpr_Binop(Iop_CmpEQ64, a, b), opt);
	return r->tag == Iex_Const && ((IRExprConst *)r)->con->Ico.U1;
}
bool
definitelyNotEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt)
{
	IRExpr *r = optimiseIRExpr(IRExpr_Binop(Iop_CmpEQ64, a, b), opt);
	return r->tag == Iex_Const && !((IRExprConst *)r)->con->Ico.U1;
}

bool
isBadAddress(IRExpr *e, const AllowableOptimisations &opt, OracleInterface *oracle)
{
	return e->tag == Iex_Const &&
		(long)((IRExprConst *)e)->con->Ico.U64 < 4096;
}

bool
definitelyUnevaluatable(IRExpr *e, const AllowableOptimisations &opt, OracleInterface *oracle)
{
	if (TIMEOUT)
		return false;
	class _ : public IRExprTransformer {
	public:
		bool res;
		const AllowableOptimisations &opt;
		OracleInterface *oracle;

		IRExpr *transformIex(IRExprLoad *e) {
			if (isBadAddress(e->addr, opt, oracle))
				res = true;
			return IRExprTransformer::transformIex(e);
		}
		_(const AllowableOptimisations &_opt,
		  OracleInterface *_oracle)
			: res(false), opt(_opt), oracle(_oracle)
		{}
	} t(opt, oracle);
	t.transformIRExpr(e);
	return t.res;
}

