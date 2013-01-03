#include <time.h>

#include "sli.h"
#include "state_machine.hpp"

#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"
#include "query_cache.hpp"
#include "allowable_optimisations.hpp"

#include "libvex_guest_offsets.h"
#include "libvex_prof.hpp"
#include "../VEX/priv/guest_generic_bb_to_IR.h"
#include "../VEX/priv/guest_amd64_defs.h"

#ifndef NDEBUG
static bool debug_optimise_irexpr = false;
#else
#define debug_optimise_irexpr false
#endif

/* Returns true if the operation definitely commutes, or false if
 * we're not sure. */
static bool
operationCommutes(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) ||
		(op >= Iop_CmpEQ8 && op <= Iop_CmpEQ64) ||
		(op >= Iop_And8 && op <= Iop_And64) ||
		(op >= Iop_Or8 && op <= Iop_Or64) ||
		(op >= Iop_Xor8 && op <= Iop_Xor64) ||
		(op == Iop_And1) ||
		(op == Iop_Or1) ||
		(op == Iop_CmpEQ1);
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

bool
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
		return a->reg == b->reg && a->ty == b->ty;
	footer()
	hdr(FreeVariable)
		return a->id == b->id && a->ty == b->ty;
	footer()
	hdr(EntryPoint)
		return *a == *b;
	footer()
	hdr(ControlFlow)
		return *a == *b;
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
		return eqIRExprConst(a, b);
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
	IRExpr *dep2)
{
	unsigned long cond;
	IRExpr *res;
	bool invert;
	IRExpr *sf, *cf, *zf, *of;
	unsigned long op;

	/* We only handle a few very special cases here. */
	if (_cond->tag != Iex_Const || cc_op->tag != Iex_Const)
		return NULL;
	cond = ((IRExprConst *)_cond)->Ico.U64;
	op = ((IRExprConst *)cc_op)->Ico.U64;
	invert = cond & 1;
	cond &= ~1ul;
	res = NULL;
	sf = cf = zf = of = NULL;

	switch (op) {
	case AMD64G_CC_OP_COPY:
		sf = IRExpr_Unop(
			Iop_64to1,
			IRExpr_Binop(
				Iop_Shr64,
				dep1,
				IRExpr_Const_U8(7)));
		cf = IRExpr_Unop(
			Iop_64to1, dep1);
		zf = IRExpr_Unop(
			Iop_64to1,
			IRExpr_Binop(
				Iop_Shr64,
				dep1,
				IRExpr_Const_U8(6)));
		of = IRExpr_Unop(
			Iop_64to1,
			IRExpr_Binop(
				Iop_Shr64,
				dep1,
				IRExpr_Const_U1(11)));
		break;
#define coerce8(x) IRExpr_Unop(Iop_64to8, (x))
#define coerce16(x) IRExpr_Unop(Iop_64to16, (x))
#define coerce32(x) IRExpr_Unop(Iop_64to32, (x))
#define coerce64(x) (x)
#define _do_sub(type, coerce)						\
		zf = IRExpr_Binop(					\
			Iop_CmpEQ ## type,				\
			coerce(dep1),					\
			coerce(dep2));					\
		cf = IRExpr_Binop(					\
			Iop_CmpLT ## type ## U,				\
			coerce(dep1),					\
			coerce(dep2));					\
		sf = IRExpr_Binop(					\
			Iop_CmpLT ## type ## S,				\
			coerce(dep1),					\
			coerce(dep2));					\
		of = IRExpr_Binop(					\
			Iop_Or1,					\
			IRExpr_Binop(					\
				Iop_And1,				\
				cf,					\
				sf),					\
			IRExpr_Binop(					\
				Iop_And1,				\
				IRExpr_Unop(Iop_Not1, cf),		\
				IRExpr_Unop(Iop_Not1, sf)));
#define do_sub(type) _do_sub(type, coerce ## type)
	case AMD64G_CC_OP_SUBB:
		do_sub(8);
		break;
	case AMD64G_CC_OP_SUBW:
		do_sub(16);
		break;
	case AMD64G_CC_OP_SUBL:
		do_sub(32);
		break;
	case AMD64G_CC_OP_SUBQ:
		do_sub(64);
		break;
#undef do_sub
#undef _do_sub
#define _do_logic(type, coerce)					\
		zf = IRExpr_Binop(				\
			Iop_CmpEQ ## type ,			\
			coerce(dep1),				\
			IRExpr_Const_U ## type(0));		\
		sf = IRExpr_Binop(				\
			Iop_CmpLT ## type ## S,			\
			coerce(dep1),				\
			IRExpr_Const_U ## type(0));	\
		of = IRExpr_Const_U1(0)
#define do_logic(type) _do_logic(type, coerce ## type)
	case AMD64G_CC_OP_LOGICB:
		do_logic(8);
		break;
	case AMD64G_CC_OP_LOGICW:
		do_logic(16);
		break;
	case AMD64G_CC_OP_LOGICL:
		do_logic(32);
		break;
	case AMD64G_CC_OP_LOGICQ:
		do_logic(64);
		break;
#undef do_logic
#undef _do_logic

#define _do_add(type, coerce)						\
		do {							\
			IRExpr *res = IRExpr_Binop(			\
				Iop_Add ## type ,			\
				coerce(dep1),				\
				coerce(dep2));				\
			IRExpr *zero =					\
				IRExpr_Const_U ## type (0);		\
			cf = IRExpr_Binop(Iop_CmpLT ## type ## U,	\
					  res,				\
					  coerce(dep1));		\
			zf = IRExpr_Binop(Iop_CmpEQ ## type ,		\
					  res,				\
					  zero);			\
			sf = IRExpr_Binop(Iop_CmpLT ## type ## S,	\
					  res,				\
					  zero);			\
		} while (0)
#define do_add(type) _do_add(type, coerce ## type)
	case AMD64G_CC_OP_ADDB:
		do_add(8);
		break;
	case AMD64G_CC_OP_ADDW:
		do_add(16);
		break;
	case AMD64G_CC_OP_ADDL:
		do_add(32);
		break;
	case AMD64G_CC_OP_ADDQ:
		do_add(64);
		break;
#undef do_add
#undef _do_add
#undef coerce64
#undef coerce32
#undef coerce16
#undef coerce8

	default:
		warning("Unknown CC op %lx\n", op);
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
				Iop_Or1,
				IRExpr_Binop(
					Iop_And1,
					sf,
					of),
				IRExpr_Binop(
					Iop_And1,
					IRExpr_Unop(Iop_Not1, sf),
					IRExpr_Unop(Iop_Not1, of)));
		else
			warning("CondL needs both sf and of; op %lx\n", op);
		break;
	case AMD64CondLE:
		if (sf && of && zf)
			res = IRExpr_Associative(
				Iop_Or1,
				zf,
				IRExpr_Binop(
					Iop_And1,
					sf,
					of),
				IRExpr_Binop(
					Iop_And1,
					IRExpr_Unop(Iop_Not1, sf),
					IRExpr_Unop(Iop_Not1, of)),
				NULL);
		else
			warning("CondLE needs sf, of, and zf; op %lx\n", op);
		break;
	default:
		break;
	}
	if (!res)
		warning("Cannot handle CC condition %ld, op %lx\n",
		       cond, op);
	if (res && invert)
		res = IRExpr_Unop(Iop_Not1, res);
	if (res)
		res = IRExpr_Unop(Iop_1Uto64, res);
	return res;
}

class sort_ordering {
public:
	enum _val {
		lt,
		eq,
		gt,
		bad
	} val;
	explicit sort_ordering(_val __val)
		: val(__val)
	{}
	sort_ordering()
		: val(bad)
	{}

	bool operator!=(sort_ordering o) const {
		return val != o.val;
	}

	bool operator==(sort_ordering o) const {
		return val == o.val;
	}
};
static const sort_ordering less_than(sort_ordering::lt);
static const sort_ordering equal_to(sort_ordering::eq);
static const sort_ordering greater_than(sort_ordering::gt);

template <typename t> static sort_ordering
_sortIntegers(t a, t b)
{
	if (a < b)
		return less_than;
	else if (a == b)
		return equal_to;
	else
		return greater_than;
}

static sort_ordering
_sortIRConsts(const IRExprConst *a, const IRExprConst *b)
{
	if (a->ty < b->ty)
		return less_than;
	if (a->ty > b->ty)
		return greater_than;
	switch (a->ty) {
#define do_type(t)							\
		case Ity_I ## t :					\
			return _sortIntegers(a->Ico.U ## t, b->Ico.U ## t)
		do_type(1);
		do_type(8);
		do_type(16);
		do_type(32);
		do_type(64);
#undef do_type
	case Ity_I128: {
		sort_ordering h = _sortIntegers(a->Ico.U128.hi,
						b->Ico.U128.hi);
		if (h == equal_to)
			return _sortIntegers(a->Ico.U128.lo,
					     b->Ico.U128.lo);
		else
			return h;
	}
	case Ity_INVALID:
		break;
	}
	abort();
}

static bool
isEqualityTest(const IRExpr *a)
{
	if (a->tag != Iex_Binop)
		return false;
	const IRExprBinop *ab = (const IRExprBinop *)a;
	return (ab->op >= Iop_CmpEQ8 && ab->op <= Iop_CmpEQ64) ||
		ab->op == Iop_CmpEQ1;
}

static bool
isVariableLike(const IRExpr *a)
{
	return a->tag == Iex_Get || a->tag == Iex_Load ||
		a->tag == Iex_FreeVariable || a->tag == Iex_EntryPoint ||
		a->tag == Iex_ControlFlow;
}

/* Simple sort function.  Ordering looks like this:

   Constants
   Equality tests
   Other boolean expressions
   Variable-like expressions:
     Registers and temporaries
     Loads
     Call expressions
     Failed call expressions
   Everything else.

   We arrange that equal expressions are always sorted together.
   Returns true if @a should be before @b. */
static sort_ordering
_sortIRExprs(const IRExpr *_a, const IRExpr *_b)
{
	if (_a == _b)
		return equal_to;

	sort_ordering s;

	if (_a->tag == Iex_Const && _b->tag == Iex_Const) {
		IRExprConst *a = (IRExprConst *)_a;
		IRExprConst *b = (IRExprConst *)_b;
		return _sortIRConsts(a, b);
	}
	if (_a->tag == Iex_Const)
		return less_than;
	if (_b->tag == Iex_Const)
		return greater_than;
	{
		bool a_is_eq_test = isEqualityTest(_a);
		bool b_is_eq_test = isEqualityTest(_b);
		if (a_is_eq_test && !b_is_eq_test)
			return less_than;
		if (b_is_eq_test && !a_is_eq_test)
			return greater_than;
	}
	{
		IRType a_type = _a->type();
		IRType b_type = _b->type();
		if (a_type == Ity_I1 && b_type != Ity_I1)
			return less_than;
		if (b_type == Ity_I1 && a_type != Ity_I1)
			return greater_than;
	}
	{
		bool a_is_var_like = isVariableLike(_a);
		bool b_is_var_like = isVariableLike(_b);
		if (a_is_var_like && !b_is_var_like)
			return less_than;
		if (b_is_var_like && !a_is_var_like)
			return greater_than;
	}

	/* None of the special rules fired -> use fallback
	 * ordering. */
	s = _sortIntegers(_a->tag, _b->tag);
	if (s != equal_to)
		return s;

	switch (_a->tag) {
#define hdr1(t)								\
		case Iex_ ## t:	{					\
			IRExpr ## t *a = (IRExpr ## t *)_a,		\
				*b = (IRExpr ## t *)_b;
	hdr1(Get)
#define hdr(t) } hdr1(t)
		if (a->reg < b->reg)
			return less_than;
		else if (b->reg < a->reg)
			return greater_than;
		else
			return equal_to;
	hdr(GetI)
		return _sortIRExprs(a->ix, b->ix);
	hdr(FreeVariable)
		if ((s = _sortIntegers(a->id, b->id)) != equal_to)
			return s;
		else
			return _sortIntegers(a->ty, b->ty);
	hdr(EntryPoint)
		if (*a < *b)
			return less_than;
		else if (*a == *b)
			return equal_to;
		else
			return greater_than;
	hdr(ControlFlow)
		if (*a < *b)
			return less_than;
		else if (*a == *b)
			return equal_to;
		else
			return greater_than;
	hdr(Qop)
		if (a->op < b->op)
			return less_than;
		if (a->op > b->op)
			return greater_than;
		if ((s = _sortIRExprs(a->arg1, b->arg1)) != equal_to)
			return s;
		else if ((s = _sortIRExprs(a->arg2, b->arg2)) != equal_to)
			return s;
		else if ((s = _sortIRExprs(a->arg3, b->arg3)) != equal_to)
			return s;
		else 
			return _sortIRExprs(a->arg4, b->arg4);
	hdr(Triop)
		if (a->op < b->op)
			return less_than;
		if (a->op > b->op)
			return greater_than;
		if ((s = _sortIRExprs(a->arg1, b->arg1)) != equal_to)
			return s;
		else if ((s = _sortIRExprs(a->arg2, b->arg2)) != equal_to)
			return s;
		else 
			return _sortIRExprs(a->arg3, b->arg3);
	hdr(Binop)
		if (a->op < b->op)
			return less_than;
		if (a->op > b->op)
			return greater_than;
		/* Special case: if we're comparing two equality
		   tests, and both have a constant on the LHS, sort on
		   the RHS.  Otherwise, we'd sort on the value of the
		   constant, which is a bit useless. */
		if (a->op >= Iop_CmpEQ8 && a->op <= Iop_CmpEQ64 &&
		    a->arg1->tag == Iex_Const && b->arg1->tag == Iex_Const) {
			if ((s = _sortIRExprs(a->arg2, b->arg2)) != equal_to)
				return s;
			else
				return _sortIRExprs(a->arg1, b->arg1);
		} else {
			if ((s = _sortIRExprs(a->arg1, b->arg1)) != equal_to)
				return s;
			else
				return _sortIRExprs(a->arg2, b->arg2);
		}
	hdr(Unop)
		if (a->op < b->op)
			return less_than;
		if (a->op > b->op)
			return greater_than;
		return _sortIRExprs(a->arg, b->arg);
	hdr(Load)
		return _sortIRExprs(a->addr, b->addr);
	hdr(Const)
		return _sortIRConsts(a, b);
	hdr(CCall) {
		int r = strcmp(a->cee->name,
			       b->cee->name);
		if (r < 0)
			return less_than;
		else if (r > 0)
			return greater_than;
		for (int x = 0; 1; x++) {
			if (!a->args[x] && !b->args[x])
				return equal_to;
			if (!a->args[x])
				return less_than;
			if (!b->args[x])
				return greater_than;
			if ((s = _sortIRExprs(a->args[x], b->args[x])) != equal_to)
				return s;
		}
	}
	hdr(Mux0X)
		if ((s = _sortIRExprs(a->cond, b->cond)) != equal_to)
			return s;
		else if ((s = _sortIRExprs(a->expr0, b->expr0)) != equal_to)
			return s;
		else
			return _sortIRExprs(a->exprX, b->exprX);
	hdr(Associative) {
		if (a->op < b->op)
			return less_than;
		if (a->op > b->op)
			return greater_than;
		int x;
		x = 0;
		while (1) {
			if (x == a->nr_arguments &&
			    x == b->nr_arguments)
				return equal_to;
			if (x == a->nr_arguments)
				return less_than;
			if (x == b->nr_arguments)
				return greater_than;
			if ((s = _sortIRExprs(a->contents[x], b->contents[x])) != equal_to)
				return s;
			x++;
		}
	}
	hdr(HappensBefore)
		if ((s = _sortIntegers(a->before, b->before)) != equal_to)
			return s;
	        return _sortIntegers(a->after, b->after);

#undef hdr
	}
        }
	abort();
}

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
	e->optimisationsApplied = 0;
}

static IRExpr *optimiseIRExpr(IRExpr *src, const IRExprOptimisations &opt, bool *done_something);

IRExpr *
optimiseIRExprFP(IRExpr *e, const IRExprOptimisations &opt, bool *done_something)
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

	if (!(opt.asUnsigned() & ~e->optimisationsApplied))
		return e;

	if (debug_optimise_irexpr)
		printf("optimise(%s, %s) -> ", nameIRExpr(e), opt.name());

#ifndef NDEBUG
	e->sanity_check();
#endif
	progress = false;
	IRExpr *e2;
	e2 = optimiseIRExpr(e, opt, &progress);
	if (e2 != e)
		progress = true;
	e = e2;
	if (progress) {
		*done_something = true;
		while (progress) {
			if (TIMEOUT) {
#if MANUAL_PROFILING
				live = false;
#endif
				if (debug_optimise_irexpr)
					printf("TIMEOUT\n");
				return e;
			}
			progress = false;
			e2 = optimiseIRExpr(e, opt, &progress);
			if (e2 != e)
				progress = true;
			e = e2;
		}
	}
	if (TIMEOUT)
		return e;
	e->optimisationsApplied |= opt.asUnsigned();
#if MANUAL_PROFILING
	if (do_profiling) {
		__site.accumulated_ticks += SetProfiling::rdtsc() - s;
		__site.nr_sites++;
		live = false;
	}
#endif
#ifndef NDEBUG
	e->sanity_check();
#endif
	if (debug_optimise_irexpr)
		printf("%s\n", nameIRExpr(e));

	return e;
}

template <bool ordering(const IRExpr *, const IRExpr *)> static void
performInsertion(IRExpr **list, int nr_items, IRExpr *newItem)
{
        /* Linear scan to find the place to insert.  Could use a
         * binary chop, but they're a bit more fiddly to get right and
         * I don't expect this to be a bottleneck. */
        int idx;
        for (idx = 0; idx < nr_items; idx++)
                if (!ordering(list[idx], newItem))
                        break;
        assert(idx != nr_items);
        /* list[idx] is greater than newItem, so need to insert to the
           left of list[idx] */
        memmove(list + idx + 1, list+idx, sizeof(IRExpr *) * (nr_items - idx));
        list[idx] = newItem;
}

template <bool ordering(const IRExpr *, const IRExpr *)> static void
_sortAssociativeArguments(IRExprAssociative *ae, bool *done_something)
{
        /* All indexes [0, first_unsorted) are definitely already sorted */
        int first_unsorted;

        first_unsorted = 1;
        while (first_unsorted < ae->nr_arguments) {
                if (ordering(ae->contents[first_unsorted],
			     ae->contents[first_unsorted-1])) {
                        /* Not already in right place -> need to go
                           and insert it. */
                        *done_something = true;
                        performInsertion<ordering>(ae->contents,
						   first_unsorted,
						   ae->contents[first_unsorted]);
                }
		first_unsorted++;
        }
}

static sort_ordering
_arith_addition_sort(const IRExpr *a1, const IRExpr *b1)
{
	/* Strip off Iop_Neg operators when sorting addition
	   associative operations, which helps a bit with
	   normalisation. */
	const IRExpr *a = a1, *b = b1;
	bool inv_a = false;
	bool inv_b = false;

	while (a->tag == Iex_Unop) {
		const IRExprUnop *ua = (IRExprUnop *)a;
		if (ua->op < Iop_Neg8 || ua->op > Iop_Neg64)
			break;
		inv_a = !inv_a;
		a = ua->arg;
	}
	while (b->tag == Iex_Unop) {
		const IRExprUnop *ub = (IRExprUnop *)b;
		if (ub->op < Iop_Neg8 || ub->op > Iop_Neg64)
			break;
		inv_b = !inv_b;
		b = ub->arg;
	}
	sort_ordering order = _sortIRExprs(a, b);
	if (order == equal_to)
		return _sortIntegers(inv_b, inv_a);
	else
		return order;
}

static sort_ordering
_cnf_disjunction_sort(const IRExpr *a1, const IRExpr *b1)
{
	/* The disjunction order is essentially the same as the normal
	   sortIRExprs order, except that we strip off leading
	   Iop_Not1 operations, so that A and ~A always sort together,
	   and then do a little bit extra so that ~A is always after
	   A. */
	const IRExpr *a = a1;
	const IRExpr *b = b1;
	bool inv_a = false;
	bool inv_b = false;
	while (a->tag == Iex_Unop) {
		const IRExprUnop *ua = (IRExprUnop *)a;
		if (ua->op != Iop_Not1)
			break;
		inv_a = !inv_a;
		a = ua->arg;
	}
	while (b->tag == Iex_Unop) {
		const IRExprUnop *ub = (IRExprUnop *)b;
		if (ub->op != Iop_Not1)
			break;
		inv_b = !inv_b;
		b = ub->arg;
	}
	sort_ordering order = _sortIRExprs(a, b);
	if (order == equal_to) {
		return _sortIntegers(inv_a, inv_b);
	} else {
		return _sortIRExprs(a1, b1);
	}
}

static sort_ordering
_cnf_conjunction_sort(const IRExpr *a, const IRExpr *b)
{
	/* Conjunction ordering treats every argument as an Iop_Or1
	   disjunction (if it isn't one already, we treat it as a
	   single-argument one).  The order is then:

	   -- If a is a subset of b, a is before b.
	   -- If b is a subset of a, a is after b.
	   -- If a is smaller than b (i.e. has fewer elements), a is before b.
	   -- If b is smaller than a, a is after b.
	   -- Otherwise, use dictionary disjunction ordering.

	   We assume that the arguments are themselves sorted
	   according to the disjunction ordering.  We also assume that
	   disjunctions always have at least two arguments.

	   The first two rules are referred to as the subsetting
	   relation, the second two as the size relation, and the
	   final one as the dictionary relation.
	*/
	const IRExprAssociative *ae, *be;
	ae = NULL;
	be = NULL;
	if (a->tag == Iex_Associative) {
		ae = (IRExprAssociative *)a;
		if (ae->op != Iop_Or1)
			ae = NULL;
	}
	if (b->tag == Iex_Associative) {
		be = (IRExprAssociative *)b;
		if (be->op != Iop_Or1)
			be = NULL;
	}
	if (!ae && !be)
		return _cnf_disjunction_sort(a, b);

	if (ae && !be) {
		/* @a is a disjunction but @b isn't.  In this case,
		   there are only two interesting cases:
		   
		   -- @b is a member of @a (i.e. @be is a subset of @ae), or
		   -- @b is not in @a.

		   In the first case, @a is after @b by the subsetting
		   rule.  In the second case, @ae is necessarily
		   larger than @be (as @be is size 1 and @ae is
		   assumed to be size >1), so @a is still after @b.
		   In either case, @a goes after @b and the result is
		   greater_than. */
		return greater_than;
	}
	if (!ae && be) {
		/* Symmetric case */
		return less_than;
	}

	/* Both a and b are non-trivial disjunctions.  Now we need to
	   move on and check the sub-setting rule. */
	int idx;
	idx = 0;
	while (idx < ae->nr_arguments && idx < be->nr_arguments) {
		sort_ordering o = _cnf_disjunction_sort(ae->contents[idx],
							be->contents[idx]);
		if (o == less_than) {
			/* This element in @ae is less than the
			   matching element in @be i.e. this element
			   of @ae is definitely not present in @be and
			   there is no way that @ae could be a subset
			   of @be.  We still need to check whether @be
			   is a subset of @ae, though. */

			if (ae->nr_arguments < be->nr_arguments) {
				/* @a is smaller than @b, and so @b is
				   definitely not a subset of @a.  No
				   subset relationships hold, and so
				   we decide based entirely on the
				   size of the arguments.  @a is
				   smaller, so it is also less than
				   @b. */
				return less_than;
			}
			if (ae->nr_arguments == be->nr_arguments) {
				/* @ae and @be are the same size, and
				   we know that at least one element
				   of @ae is not present in @be.
				   Therefore there is at least one
				   element of @be not present in @ae,
				   by the pigeon hole principle.
				   Therefore, neither the subset nor
				   size-based rules fire, and we use a
				   dictionary order.  In this case, we
				   know that, for the first non-equal
				   item, @ae is smaller, so @ae is
				   smaller overall. */
				return less_than;
			}

			/* Subsetting-wise, we know that either @be is
			 * a subset of @ae or they are unordered with
			 * respect to each other.  In the first case,
			 * we'll return greater_than.  In the second
			 * case, we look at their relative sizes.  We
			 * know that @ae has more arguments than @be,
			 * because of the tests above, and in that
			 * case we still return greater_than.  So we
			 * just need to return greater_than and we're
			 * done.
			 */
			return greater_than;
		} else if (o == greater_than) {
			/* Symmetric case.  This item is definitely
			 * present in @be but not in @ae, so @be
			 * cannot be a subset of @ae. */
			if (be->nr_arguments < ae->nr_arguments) {
				/* @be and @ae are unordered with
				 * respect to the subset relation, so
				 * we use the size relation. */
				return greater_than;
			}
			if (be->nr_arguments == ae->nr_arguments) {
				/* @be and @ae are unordered with
				 * respect to the subset and size
				 * relations, so we use the dictionary
				 * relation. */
				return greater_than;
			}
			return less_than;
		} else {
			assert(o == equal_to);
			idx++;
		}
	}

	if (ae->nr_arguments == be->nr_arguments) {
		assert(idx == ae->nr_arguments);
		return equal_to;
	}
	if (ae->nr_arguments < be->nr_arguments) {
		/* @a is a subset of @b */
		return less_than;
	} else {
		return greater_than;
	}
}

/* These are only non-static because they're used as template
 * arguments; sigh. */
bool
sortIRExprs(const IRExpr *a, const IRExpr *b)
{
	return _sortIRExprs(a, b) == less_than;
}
bool
cnf_disjunction_sort(const IRExpr *a, const IRExpr *b)
{
	return _cnf_disjunction_sort(a, b) == less_than;
}
bool
cnf_conjunction_sort(const IRExpr *a, const IRExpr *b)
{
	return _cnf_conjunction_sort(a, b) == less_than;
}
bool
arith_addition_sort(const IRExpr *a, const IRExpr *b)
{
	return _arith_addition_sort(a, b) == less_than;
}

static void
sortAssociativeArguments(IRExprAssociative *ae, bool *done_something)
{
        __set_profiling(sort_associative_arguments);

        /* Use insertion sort here, because:

           -- the number of arguments is probably small,
           -- they're probably nearly sorted already, and
           -- we need an easy way of checking whether we've actually made
              any changes.
        */

	/* We have three different orderings available, depending on
	   the type of thing which we're sorting.  The aim here is to
	   produce the same ordering as CNF conversion would, since
	   that makes optimisation much easier. */
	if (ae->op == Iop_Or1)
		_sortAssociativeArguments<cnf_disjunction_sort>(ae, done_something);
	else if (ae->op == Iop_And1)
		_sortAssociativeArguments<cnf_conjunction_sort>(ae, done_something);
	else if (ae->op >= Iop_Add8 && ae->op <= Iop_Add64)
		_sortAssociativeArguments<arith_addition_sort>(ae, done_something);
	else
		_sortAssociativeArguments<sortIRExprs>(ae, done_something);
}

/* CNF subsetting relationship.  Essentially, does @a imply @b.  We
 * only care about the case where @a and @b are CNF disjunctions
 * here. */
static bool
isCnfSubset(const IRExpr *a, const IRExpr *b)
{
	const IRExprAssociative *a_disjunct, *b_disjunct;
top:
	a_disjunct = NULL;
	if (a->tag == Iex_Associative) {
		a_disjunct = (IRExprAssociative *)a;
		if (a_disjunct->op != Iop_Or1)
			a_disjunct = NULL;
		else if (a_disjunct->nr_arguments == 1) {
			a = a_disjunct->contents[0];
			goto top;
		}
	}
	if (a_disjunct && a_disjunct->nr_arguments == 0) {
		/* @a is an empty disjunction -> it's effectively just
		   false, and false implies everything. */
		return true;
	}
top2:
	b_disjunct = NULL;
	if (b->tag == Iex_Associative) {
		b_disjunct = (IRExprAssociative *)b;
		if (b_disjunct->op != Iop_Or1)
			b_disjunct = NULL;
		else if (b_disjunct->nr_arguments == 1) {
			b = b_disjunct->contents[0];
			goto top2;
		}
	}
	if (!a_disjunct && !b_disjunct)
		return _cnf_disjunction_sort(a, b) == equal_to;
	if (!b_disjunct) {
		/* @a has multiple elements but @b only has one -> @a
		   cannot be a subset of @b. */
		if (a_disjunct->nr_arguments <= 1)
			abort();
		return false;
	}
	if (!a_disjunct) {
		for (int idx = 0; idx < b_disjunct->nr_arguments; idx++) {
			sort_ordering o = _cnf_disjunction_sort(a, b_disjunct->contents[idx]);
			if (o == equal_to)
				return true;
			if (o == greater_than)
				return false;
		}
		return false;
	}
	if (a_disjunct->nr_arguments > b_disjunct->nr_arguments)
		return false;
	int a_idx = 0;
	int b_idx = 0;
	while (a_idx < a_disjunct->nr_arguments &&
	       b_idx < b_disjunct->nr_arguments) {
		sort_ordering o = _cnf_disjunction_sort(a_disjunct->contents[a_idx],
							b_disjunct->contents[b_idx]);
		if (o == less_than) {
			/* This element of @a does not appear in @b ->
			   @a is not a subset of @b. */
			return false;
		} else if (o == equal_to) {
			a_idx++;
			b_idx++;
		} else {
			assert(o == greater_than);
			/* This element of @b does not appear in @a,
			   which is absolutely fine; just skip to the
			   next one. */
			b_idx++;
		}
	}
	if (a_idx == a_disjunct->nr_arguments) {
		/* Every element of @a has a matching element in @b ->
		   @a is a subset of @b. */
		return true;
	} else {
		/* Otherwise, something in @a has no pair in @b, so @a
		   can't be a subset of @b. */
		return false;
	}
}

/* We know from context that @assumption is true when evaluating @iex,
   and with fairly high probability @iex is a CNF disjunction.
   Optimise under that assumption. */
static IRExpr *
optimiseAssuming(IRExpr *iex, const IRExpr *assumption, bool *done_something)
{
	if (iex->tag == Iex_Const) {
		/* Nothing to do in this case, and an early exit means
		   that we won't set *done_something and cause an
		   infinite loop. */
		return iex;
	}
	bool invertAssumption;
	invertAssumption = false;
	if (assumption->tag == Iex_Unop) {
		const IRExprUnop *u = (IRExprUnop *)assumption;
		if (u->op == Iop_Not1) {
			assumption = u->arg;
			invertAssumption = true;
		}
	}

	if (_sortIRExprs(iex, assumption) == equal_to) {
		*done_something = true;
		return IRExpr_Const_U1(!invertAssumption);
	}
	if (iex->tag == Iex_Unop) {
		const IRExprUnop *u = (IRExprUnop *)iex;
		if (u->op == Iop_Not1 &&
		    _sortIRExprs(u->arg, assumption) == equal_to) {
			*done_something = true;
			return IRExpr_Const_U1(invertAssumption);
		}
		return iex;
	}
	if (iex->tag != Iex_Associative)
		return iex;
	IRExprAssociative *assoc = (IRExprAssociative *)iex;
	if (assoc->op != Iop_Or1)
		return iex;

	for (int i = 0; i < assoc->nr_arguments; ) {
		if (_sortIRExprs(assoc->contents[i], assumption) == equal_to) {
			*done_something = true;
			if (invertAssumption) {
				/* We're assuming ~X and this
				   expression is X|Y, so just reduce
				   to Y. */
				assoc = dynamic_cast<IRExprAssociative *>(IRExpr_Associative(assoc));
				purgeAssocArgument(assoc, i);
			} else {
				/* We're assuming X, and this
				   expression is X|Y, so reduce to
				   constant 1. */
				return IRExpr_Const_U1(true);
			}
		} else if (assoc->contents[i]->tag == Iex_Unop) {
			IRExprUnop *u = (IRExprUnop *)assoc->contents[i];
			if (u->op == Iop_Not1 &&
			    _sortIRExprs(u->arg, assumption) == equal_to) {
				*done_something = true;
				if (invertAssumption) {
					/* We're assuming ~x and we
					   found ~x|y -> result is
					   constant 1. */
					return IRExpr_Const_U1(true);
				} else {
					/* We'are assuming X and found
					   ~X|Y, so just turn it into
					   Y. */
					assoc = dynamic_cast<IRExprAssociative *>(IRExpr_Associative(assoc));
					purgeAssocArgument(assoc, i);
				}
			} else {
				i++;
			}
		} else {
			i++;
		}
	}

	return assoc;
}

IRExpr *
optimiseAssuming(IRExpr *iex, const IRExpr *assumption)
{
	bool p = true;
	while (p) {
		p = false;
		iex = optimiseAssuming(iex, assumption, &p);
	}
	return iex;
}

IROp
coerceTypesOp(IRType from, IRType to)
{
	switch (from) {
	case Ity_I64:
		switch (to) {
		case Ity_I8:
			return Iop_64to8;
		case Ity_I16:
			return Iop_64to16;
		case Ity_I32:
			return Iop_64to32;
		case Ity_I64:
			return Iop_Noop64;
		default:
			break;
		}
		break;
	case Ity_I32:
		switch (to) {
		case Ity_I8:
			return Iop_32to8;
		case Ity_I16:
			return Iop_32to16;
		case Ity_I32:
			return Iop_Noop32;
		default:
			break;
		}
		break;
	case Ity_I16:
		switch (to) {
		case Ity_I8:
			return Iop_16to8;
		case Ity_I16:
			return Iop_Noop16;
		default:
			break;
		}
		break;
	case Ity_I8:
		switch (to) {
		case Ity_I1:
			return Iop_8to1;
		case Ity_I8:
			return Iop_Noop8;
		default:
			break;
		}
		break;
	case Ity_I128:
		switch (to) {
		case Ity_I64:
			return Iop_128to64;
		case Ity_I32:
			return Iop_V128to32;
		case Ity_I128:
			return Iop_Noop128;
		default:
			break;
		}
	default:
		break;
	}
	abort();
}

/* Down-cast @expr so that it is of type @desiredType. */
IRExpr *
coerceTypes(IRType desiredType, IRExpr *expr)
{
	return IRExpr_Unop(coerceTypesOp(expr->type(), desiredType), expr);
}

static bool
isZero(const IRExprConst *iec)
{
	switch (iec->ty) {
#define do_tag(n)				\
		case Ity_I ## n :		\
			return iec->Ico.U ## n == 0
		do_tag(1);
		do_tag(8);
		do_tag(16);
		do_tag(32);
		do_tag(64);
#undef do_tag
	case Ity_I128:
		return iec->Ico.U128.hi == 0 &&
			iec->Ico.U128.lo == 0;
	case Ity_INVALID:
		break;
	}
	abort();
}

/* Should we rewrite a to b or be to a, or neither?  Return lt for
   b->a, gt for a->b, or eq for neither. */
static sort_ordering
_rewriteOrdering(IRExpr *a, IRExpr *b)
{
	/* Prefer constants to anything else. */
#define tag_test(n)				\
	if (a->tag == Iex_ ## n)		\
		return less_than;		\
	if (b->tag == Iex_ ## n)		\
		return greater_than
	tag_test(Const);
	/* Prefer simple variables to anything apart from constants. */
	tag_test(EntryPoint);
	tag_test(ControlFlow);
	tag_test(HappensBefore);
	tag_test(Get);
	tag_test(FreeVariable);
	/* Now do loads */
	if (a->tag == Iex_Load) {
		if (b->tag != Iex_Load)
			return less_than;
		return _rewriteOrdering( ((IRExprLoad *)a)->addr,
					((IRExprLoad *)b)->addr);
	}
	if (b->tag == Iex_Load)
		return greater_than;
	/* Binops are usually pretty useful, so preserve them. */
	tag_test(Binop);
	/* For assocs, pick the one with fewest arguments */
	if (a->tag == Iex_Associative) {
		if (b->tag != Iex_Associative)
			return less_than;
		if ( ((IRExprAssociative *)a)->nr_arguments < ((IRExprAssociative *)b)->nr_arguments )
			return less_than;
		else if ( ((IRExprAssociative *)a)->nr_arguments > ((IRExprAssociative *)b)->nr_arguments )
			return greater_than;
		else
			return equal_to;
	}
	if (b->tag == Iex_Associative)
		return greater_than;
	tag_test(Unop);
	tag_test(Mux0X);
	tag_test(Triop);
	tag_test(Qop);
	tag_test(CCall);
	tag_test(GetI);
#undef tag_test
	/* That should have covered everything. */
	abort();
}

static bool
occursCheck(const IRExpr *needle, const IRExpr *haystack)
{
	if (haystack == needle)
		return true;
	switch (haystack->tag) {
	case Iex_Get:
		return false;
	case Iex_GetI:
		return occursCheck( needle, ((const IRExprGetI *)haystack)->ix);
	case Iex_Qop:
		if (occursCheck(needle, ((const IRExprQop *)haystack)->arg4))
			return true;
		/* Fall through */
	case Iex_Triop:
		if (occursCheck(needle, ((const IRExprTriop *)haystack)->arg3))
			return true;
		/* Fall through */
	case Iex_Binop:
		if (occursCheck(needle, ((const IRExprBinop *)haystack)->arg2))
			return true;
		/* Fall through */
	case Iex_Unop:
		return occursCheck(needle, ((const IRExprUnop *)haystack)->arg);
	case Iex_Const:
		return false;
	case Iex_Mux0X:
		return occursCheck(needle, ((const IRExprMux0X *)haystack)->cond) ||
			occursCheck(needle, ((const IRExprMux0X *)haystack)->expr0) ||
			occursCheck(needle, ((const IRExprMux0X *)haystack)->exprX);
	case Iex_CCall: {
		const IRExprCCall *cc = (const IRExprCCall *)haystack;
		for (int i = 0; cc->args[i]; i++)
			if (occursCheck(needle, cc->args[i]))
				return true;
		return false;
	}
	case Iex_Associative: {
		const IRExprAssociative *a = (const IRExprAssociative *)haystack;
		for (int i = 0; i < a->nr_arguments; i++)
			if (occursCheck(needle, a->contents[i]))
				return true;
		return false;
	}
	case Iex_Load:
		return occursCheck(needle, ((const IRExprLoad *)haystack)->addr);
	case Iex_HappensBefore:
		return false;
	case Iex_FreeVariable:
		return false;
	case Iex_EntryPoint:
		return false;
	case Iex_ControlFlow:
		return false;
	}
	abort();
}

static sort_ordering
rewriteOrdering(IRExpr *a, IRExpr *b)
{
	switch (_rewriteOrdering(a, b).val) {
	case sort_ordering::lt:
		if (occursCheck(b, a))
			return equal_to;
		else
			return less_than;
	case sort_ordering::eq:
		return equal_to;
	case sort_ordering::gt:
		if (occursCheck(a, b))
			return equal_to;
		else
			return greater_than;
	case sort_ordering::bad:
		abort();
	}
	abort();
}

static IRExpr *
rewriteBoolean(IRExpr *expr, bool val, IRExpr *inp, bool *done_something)
{
	struct : public IRExprTransformer {
		IRExpr *from;
		bool to;
		IRExpr *_to;
		IRExpr *rewriteFrom;
		IRExpr *rewriteTo;
		IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
			if (physicallyEqual(e, from)) {
				if (!_to)
					_to = IRExpr_Const_U1(to);
				*done_something = true;
				return _to;
			}
			if (rewriteFrom && physicallyEqual(e, rewriteFrom)) {
				*done_something = true;
				return rewriteTo;
			}
			if (to &&
			    from->tag == Iex_EntryPoint &&
			    e->tag == Iex_EntryPoint &&
			    ((IRExprEntryPoint *)e)->thread == ((IRExprEntryPoint *)from)->thread &&
			    ((IRExprEntryPoint *)e)->label != ((IRExprEntryPoint *)from)->label) {
				*done_something = true;
				return IRExpr_Const_U1(false);
			}
			if (!rewriteFrom && e->type() != Ity_I1 && e->tag != Iex_Mux0X)
				return e;
			return IRExprTransformer::transformIRExpr(e, done_something);
		}
	} doit;
	if (expr->tag == Iex_Unop) {
		IRExprUnop *e = (IRExprUnop *)expr;
		if (e->op == Iop_Not1) {
			val = !val;
			expr = e->arg;
		}
	}
	doit.from = expr;
	doit.to = val;
	doit._to = NULL;
	doit.rewriteFrom = NULL;
	doit.rewriteTo = NULL;
	if (val && expr->tag == Iex_Binop) {
		IRExprBinop *ieb = (IRExprBinop *)expr;
		if (ieb->op >= Iop_CmpEQ8 &&
		    ieb->op <= Iop_CmpEQ64) {
			switch (rewriteOrdering(ieb->arg1, ieb->arg2).val) {
			case sort_ordering::lt:
				doit.rewriteFrom = ieb->arg2;
				doit.rewriteTo = ieb->arg1;
				break;
			case sort_ordering::eq:
				doit.rewriteFrom = NULL;
				doit.rewriteTo = NULL;
				break;
			case sort_ordering::gt:
				doit.rewriteFrom = ieb->arg1;
				doit.rewriteTo = ieb->arg2;
				break;
			case sort_ordering::bad:
				abort();
			}
		}
	}
	return doit.doit(inp, done_something);
}

static IRExpr *
optimiseIRExpr(IRExpr *src, const IRExprOptimisations &opt, bool *done_something)
{
	if (TIMEOUT)
		return src;

	if (!(opt.asUnsigned() & ~src->optimisationsApplied))
		return src;

top:
	bool progress = false;
	IRExpr *res = src;
	switch (src->tag) {
	case Iex_CCall: {
		IRExprCCall *c = (IRExprCCall *)src;
		for (int i = 0; c->args[i]; i++)
			c->args[i] = optimiseIRExpr(c->args[i], opt, done_something);
		if (!strcmp(c->cee->name, "amd64g_calculate_condition")) {
			IRExpr *a = optimise_condition_calculation(
				c->args[0],
				c->args[1],
				c->args[2],
				c->args[3]);
			if (a)
				res = a;
		}
		break;
	}
	case Iex_Associative: {
		IRExprAssociative *e = (IRExprAssociative *)res;
		for (int i = 0; i < e->nr_arguments; i++)
			e->contents[i] = optimiseIRExpr(e->contents[i], opt, done_something);
		__set_profiling(optimise_associative);

		/* Rewrite to pull muxes up: Mux0X(a, b, c) + d ->
		 * Mux0X(a, b + d, c + d) */
		{
			bool p = false;
			for (int x = 0; !p && x < e->nr_arguments; x++) {
				if (e->contents[x]->tag == Iex_Mux0X) {
					IRExprMux0X *mux = (IRExprMux0X *)e->contents[x];
					IRExprAssociative *assoc0 = (IRExprAssociative *)IRExpr_Associative(e);
					IRExprAssociative *assocX = (IRExprAssociative *)IRExpr_Associative(e);
					assoc0->optimisationsApplied = 0;
					assocX->optimisationsApplied = 0;
					for (int y = 0; y < e->nr_arguments; y++) {
						if (e->contents[y]->tag == Iex_Mux0X) {
							IRExprMux0X *mux2 = (IRExprMux0X *)e->contents[y];
							if (mux2->cond == mux->cond) {
								assoc0->contents[y] = mux2->expr0;
								assocX->contents[y] = mux2->exprX;
							}
						}
					}
					res = IRExpr_Mux0X(mux->cond, assoc0, assocX);
					p = true;
				}
			}
			if (p)
				break;
		}
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
			res = ne;
			e = ne;
		}

		/* Sort IRExprs so that ``related'' expressions are likely to
		 * be close together. */
		if (operationCommutes(e->op))
			sortAssociativeArguments(e, &progress);

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
					IRExprConst *l, *r;
					l = (IRExprConst *)a;
					r = (IRExprConst *)b;
					switch (e->op) {
#define do_sized_op(name, sz, op)					\
						case Iop_ ## name ## sz: \
							res = IRExpr_Const_U ## sz( \
								l->Ico.U ## sz op r->Ico.U ## sz); \
							break
#define do_op(name, op)							\
						do_sized_op(name, 8, op); \
						do_sized_op(name, 16, op); \
						do_sized_op(name, 32, op); \
						do_sized_op(name, 64, op)
						do_op(Add, +);
						do_op(Sub, -);
						do_op(And, &);
						do_op(Or, |);
						do_op(Xor, ^);
#undef do_op
#undef do_sized_op
					case Iop_And1:
						res = IRExpr_Const_U1(l->Ico.U1 & r->Ico.U1);
						break;
					case Iop_Or1:
						res = IRExpr_Const_U1(l->Ico.U1 | r->Ico.U1);
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
						progress = true;
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
			if (e->nr_arguments > 1 &&
			    e->contents[0]->tag == Iex_Const) {
				auto c = (IRExprConst *)e->contents[0];
				if (c->Ico.U1) {
					progress = true;
					purgeAssocArgument(e, 0);
				} else {
					res = e->contents[0];
					break;
				}
			}
		}
		/* Likewise for Or1 */
		if (e->op == Iop_Or1) {
			__set_profiling(optimise_assoc_or1);
			if (e->nr_arguments > 1 &&
			    e->contents[0]->tag == Iex_Const) {
				auto c = (IRExprConst *)e->contents[0];
				if (!c->Ico.U1) {
					progress = true;
					purgeAssocArgument(e, 0);
				} else {
					res = e->contents[0];
					break;
				}
			}
		}
		/* And for Add */
		if (e->op == Iop_Add64) {
			if (e->nr_arguments > 1 &&
			    e->contents[0]->tag == Iex_Const &&
			    ((IRExprConst *)e->contents[0])->Ico.U64 == 0) {
				purgeAssocArgument(e, 0);
				progress = true;
			}
		}
		/* x & x -> x, for any and-like or or-like
		   operator. */
		if ((e->op >= Iop_And8 && e->op <= Iop_And64) ||
		    (e->op >= Iop_Or8 && e->op <= Iop_Or64) ||
		    e->op == Iop_And1 ||
		    e->op == Iop_Or1) {
			__set_profiling(optimise_assoc_x_and_x);
			for (int it1 = 0;
			     it1 < e->nr_arguments - 1;
				) {
				if (_sortIRExprs(e->contents[it1], e->contents[it1 + 1]) == equal_to) {
					progress = true;
					purgeAssocArgument(e, it1 + 1);
				} else {
					it1++;
				}
			}
		}

		/* a <-< b || b <-< a is definitely true. */
		if (e->op == Iop_Or1) {
			__set_profiling(optimise_assoc_happens_before);
			bool p = false;
			for (int i1 = 0; !p && i1 < e->nr_arguments; i1++) {
				if (e->contents[i1]->tag != Iex_HappensBefore)
					continue;
				IRExprHappensBefore *a1 = (IRExprHappensBefore *)e->contents[i1];
				for (int i2 = i1 + 1; !p && i2 < e->nr_arguments; i2++) {
					if (e->contents[i2]->tag != Iex_HappensBefore)
						continue;
					IRExprHappensBefore *a2 =
						(IRExprHappensBefore *)e->contents[i2];
					if ( a1->before == a2->after &&
					     a1->after == a2->before ) {
						res = IRExpr_Const_U1(true);
						p = true;
					}
				}
			}
			if (p)
				break;
		}

		/* x || ~x -> 1.  We know by the ordering that
		   if any such pairs are present then they'll
		   be adjacent and x will be before ~x, which
		   is handy. */
		if (e->op == Iop_Or1) {
			__set_profiling(optimise_assoc_x_or_not_x);
			bool p = false;
			for (int i = 0; !p && i < e->nr_arguments - 1; i++) {
				if (e->contents[i+1]->tag == Iex_Unop &&
				    ((IRExprUnop *)e->contents[i+1])->op == Iop_Not1 &&
				    _sortIRExprs(((IRExprUnop *)e->contents[i+1])->arg,
						 e->contents[i]) == equal_to) {
					res = IRExpr_Const_U1(true);
					p = true;
				}
			}
			if (p)
				break;
		}

		if (e->op == Iop_And1) {
			/* Assume here that the expression is
			   in conjunctive normal form.  Now
			   search for arguments X and Y such
			   that X implies Y.  If we find any,
			   we can purge Y from the arguments
			   list.  Since we're assuming that
			   we're in CNF, X implies Y is
			   equivalent to saying that X is a
			   subset of Y, and, by the CNF
			   conjunction ordering, X occurs
			   before Y in the list. */
			/* (i.e. take anything which says
			   X&(X|Y) and turn it into just X) */
			for (int idx1 = 0; idx1 < e->nr_arguments - 1; idx1++) {
				for (int idx2 = idx1 + 1; idx2 < e->nr_arguments; ) {
					if (isCnfSubset(e->contents[idx1], e->contents[idx2])) {
						purgeAssocArgument(e, idx2);
						progress = true;
					} else {
						idx2++;
					}
				}

				/* While we're here, we can
				   also check that we don't
				   have anything like
				   X&(~X|Y).  If we do, turn
				   it into just X&Y. */
				if (e->contents[idx1]->tag != Iex_Associative ||
				    ((IRExprAssociative *)e->contents[idx1])->op != Iop_Or1) {
					for (int idx2 = idx1 + 1; idx2 < e->nr_arguments; idx2++)
						e->contents[idx2] = optimiseAssuming(e->contents[idx2],
										     e->contents[idx1],
										     &progress);
				}
			}
		}

		if (e->op == Iop_Or1) {
			for (int idx1 = 0; idx1 < e->nr_arguments - 1; idx1++)
				for (int idx2 = idx1 + 1; idx2 < e->nr_arguments; idx2++)
					e->contents[idx2] = rewriteBoolean(e->contents[idx1],
									   false,
									   e->contents[idx2],
									   &progress);
		}

		if (e->op == Iop_And1) {
			for (int idx1 = 0; idx1 < e->nr_arguments - 1; idx1++)
				for (int idx2 = idx1 + 1; idx2 < e->nr_arguments; idx2++)
					e->contents[idx2] = rewriteBoolean(e->contents[idx1],
									   true,
									   e->contents[idx2],
									   &progress);
		}

		/* x + -x -> 0, for any plus-like operator, so remove
		 * both x and -x from the list. */
		/* Also do x & ~x -> 0, x ^ x -> 0, while we're here. */
		{
			__set_profiling(optimise_assoc_xplusminusx);
			bool plus_like;
			bool and_like;
			bool xor_like;
			bool p = false;
			plus_like = e->op >= Iop_Add8 && e->op <= Iop_Add64;
			and_like = (e->op >= Iop_And8 && e->op <= Iop_And64) ||
				e->op == Iop_And1;
			xor_like = e->op >= Iop_Xor8 && e->op <= Iop_Xor64;
			if (plus_like || and_like || xor_like) {
				for (int it1 = 0;
				     !p && it1 < e->nr_arguments;
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
								purge = physicallyEqual(l, ((IRExprUnop *)r)->arg);
						} else if (and_like) {
							if (r->tag == Iex_Unop) {
								IROp op = ((IRExprUnop *)r)->op;
								purge = (op >= Iop_Not8 &&
									 op <= Iop_Not64) ||
									op == Iop_Not1;
							} else
								purge = false;
							if (purge)
								purge = physicallyEqual(l, ((IRExprUnop *)r)->arg);
						} else {
							assert(xor_like);
							purge = physicallyEqual(l, r);
						}

						if (purge) {
							progress = true;
							IRExprConst *result;
							switch (e->op) {
							case Iop_And8:
							case Iop_Xor8:
							case Iop_Add8:
								result = IRExpr_Const_U8(0);
								break;
							case Iop_And16:
							case Iop_Xor16:
							case Iop_Add16:
								result = IRExpr_Const_U16(0);
								break;
							case Iop_And32:
							case Iop_Xor32:
							case Iop_Add32:
								result = IRExpr_Const_U32(0);
								break;
							case Iop_And64:
							case Iop_Xor64:
							case Iop_Add64:
								result = IRExpr_Const_U64(0);
								break;
							case Iop_And1:
								result = IRExpr_Const_U1(0);
								break;
							default:
								abort();
							}
							if (and_like) {
								/* x & ~x -> 0 and eliminates the entire expression. */
								res = result;
								p = true;
								break;
							}

							/* Careful: do the largest index first so that the
							   other index remains valid. */
							if (it1 < it2) {
								purgeAssocArgument(e, it2);
								e->contents[it1] = result;
							} else {
								purgeAssocArgument(e, it1);
								e->contents[it2] = result;
							}
							break;
						}
					}
					if (it2 == e->nr_arguments)
						it1++;
				}
			}
			if (e->nr_arguments == 0) {
				p = true;
				switch (e->op) {
				case Iop_Add8:
				case Iop_Xor8:
					res = IRExpr_Const_U8(0);
					break;
				case Iop_Add16:
				case Iop_Xor16:
					res = IRExpr_Const_U16(0);
					break;
				case Iop_Add32:
				case Iop_Xor32:
					res = IRExpr_Const_U32(0);
					break;
				case Iop_Add64:
				case Iop_Xor64:
					res = IRExpr_Const_U64(0);
					break;
				case Iop_And1:
					res = IRExpr_Const_U1(true);
					break;
				case Iop_And8:
					res = IRExpr_Const_U8(0xff);
					break;
				case Iop_And16:
					res = IRExpr_Const_U16(0xffff);
					break;
				case Iop_And32:
					res = IRExpr_Const_U32(0xffffffff);
					break;
				case Iop_And64:
					res = IRExpr_Const_U64(0xfffffffffffffffful);
					break;
				case Iop_Or1:
					res = IRExpr_Const_U1(0);
					break;
				default:
					abort();
				}
			}
			if (p)
				break;
		}

		/* If the size is reduced to one, eliminate the assoc list */
		if (e->nr_arguments == 1)
			res = e->contents[0];

		break;
	}

	case Iex_Unop: {
		IRExprUnop *e = (IRExprUnop *)res;
		e->arg = optimiseIRExpr(e->arg, opt, done_something);
		__set_profiling(optimise_unop);

		if (e->arg->tag == Iex_Unop) {
			IRExprUnop *argu = (IRExprUnop *)e->arg;
			if (inverseUnops(e->op, argu->op)) {
				res = argu->arg;
				break;
			}
			IROp ss;
			if (shortCircuitableUnops(e->op, argu->op, &ss)) {
				res = optimiseIRExprFP(IRExpr_Unop(ss, argu->arg),
						       opt,
						       &progress);
				break;
			}
		}

		if (e->arg->tag == Iex_Get) {
			IRExprGet *argg = (IRExprGet *)e->arg;
			if (e->op == Iop_64to32) {
				res = IRExpr_Get(argg->reg, Ity_I32);
				break;
			}
			if (e->op == Iop_64to16 || e->op == Iop_32to16) {
				res = IRExpr_Get(argg->reg, Ity_I16);
				break;
			}
			if (e->op == Iop_64to8 || e->op == Iop_32to8 || e->op == Iop_16to8) {
				res = IRExpr_Get(argg->reg, Ity_I8);
				break;
			}
			if (e->op == Iop_V128to32) {
				res = IRExpr_Get(argg->reg, Ity_I32);
				break;
			}
			if (e->op == Iop_ReinterpI32asF32) {
				res = IRExpr_Get(argg->reg, Ity_I32);
				break;
			}
		}

		if (e->arg->tag == Iex_Load) {
			IRExprLoad *argl = (IRExprLoad *)e->arg;
			if (e->op == Iop_64to32) {
				res = IRExpr_Load(Ity_I32, argl->addr);
				break;
			}
			if (e->op == Iop_ReinterpI32asF32) {
				res = IRExpr_Load(Ity_I32, argl->addr);
				break;
			}
		}

		if (e->arg->tag == Iex_Associative) {
			IRExprAssociative *arga = (IRExprAssociative *)e->arg;
			if ((e->op == Iop_Not1 && (arga->op == Iop_And1 || arga->op == Iop_Or1)) ||
			    (e->op == Iop_Neg64 && arga->op == Iop_Add64)) {
				/* Convert ~(x & y) to ~x | ~y and -(x + y) to -x + -y. */
				IRExprAssociative *a =
					(IRExprAssociative *)IRExpr_Associative(arga);
				for (int i = 0;
				     i < a->nr_arguments;
				     i++) {
					a->contents[i] =
						optimiseIRExprFP(
							IRExpr_Unop(
								e->op,
								a->contents[i]),
							opt,
							&progress);
				}
				if (a->op == Iop_And1)
					a->op = Iop_Or1;
				else if (a->op == Iop_Or1)
					a->op = Iop_And1;
				else if (a->op == Iop_Add64)
					a->op = Iop_Add64;
				else
					abort();
				res = a;
				break;
			}
			bool isOr = arga->op >= Iop_Or8 && arga->op <= Iop_Or64;
			bool isAnd = arga->op >= Iop_And8 && arga->op <= Iop_And64;
			bool isXor = arga->op >= Iop_Xor8 && arga->op <= Iop_Xor64;
			bool isAdd = arga->op >= Iop_Add8 && arga->op <= Iop_Add64;
			bool isDowncast = 
				e->op == Iop_64to32 || e->op == Iop_64to16 || e->op == Iop_64to8 ||
				e->op == Iop_32to16 || e->op == Iop_32to8 ||
				e->op == Iop_16to8;
			bool isUnsignedUpcast =
				e->op == Iop_8Uto64  || e->op == Iop_8Uto32  || e->op == Iop_8Uto16 ||
				e->op == Iop_16Uto64 || e->op == Iop_16Uto32 ||
				e->op == Iop_32Uto64;

			if ( (isDowncast && (isOr || isAnd || isXor || isAdd) ) ||
			     (isUnsignedUpcast && (isOr || isAnd || isXor) ) ) {
				/* Push downcasts through and/or/xor/add operations,
				   and unsigned upcasts through and/or/xor ones. */
				IRExprAssociative *a =
					(IRExprAssociative *)IRExpr_Associative(arga);
				for (int i = 0; i < a->nr_arguments; i++)
					a->contents[i] =
						optimiseIRExprFP(
							IRExpr_Unop(
								e->op,
								a->contents[i]),
							opt,
							&progress);
				IROp base_op = Iop_INVALID;
#define do_op(name)							\
				if (arga->op >= Iop_ ## name ## 8	\
				    && arga->op <= Iop_ ## name ## 64)	\
					base_op = Iop_ ## name ## 8
				do_op(Or);
				do_op(And);
				do_op(Xor);
				do_op(Add);
#undef do_op
				assert(base_op != Iop_INVALID);
				IROp op = Iop_INVALID;
				switch (a->contents[0]->type()) {
				case Ity_I8:
					op = base_op;
					break;
				case Ity_I16:
					op = (IROp)(base_op + 1);
					break;
				case Ity_I32:
					op = (IROp)(base_op + 2);
					break;
				case Ity_I64:
					op = (IROp)(base_op + 3);
					break;						
				default:
					break;
				}
				assert(op != Iop_INVALID);
				a->op = op;
				res = a;
				break;
			}
		}

		if (e->op == Iop_BadPtr) {
			if (opt.allPointersGood()) {
				res = IRExpr_Const_U1(false);
				break;
			}
			if (e->arg->tag == Iex_Associative &&
			    ((IRExprAssociative *)e->arg)->op == Iop_Add64 &&
			    ((IRExprAssociative *)e->arg)->nr_arguments == 2 &&
			    ((IRExprAssociative *)e->arg)->contents[0]->tag == Iex_Const) {
				/* Simplify BadPtr(k+x) a
				 * little bit if k is a
				 * constant.  The basic rule
				 * is to round k down to a
				 * multiple of 4MiB.  The idea
				 * is that if X is a valid
				 * pointer then X+8, say, is
				 * probably also a valid
				 * pointer to the same
				 * structure, so we can mosh
				 * them together. */
				IRExprAssociative *assoc = (IRExprAssociative *)e->arg;
				IRExprConst *cnst = (IRExprConst *)assoc->contents[0];
				unsigned long old_delta = cnst->Ico.U64;
				unsigned long new_delta = old_delta & ~((1ul << 22) - 1);
				if (assoc->contents[1]->tag == Iex_Get &&
				    ((IRExprGet *)assoc->contents[1])->reg.isReg() &&
				    (((IRExprGet *)assoc->contents[1])->reg.asReg() == offsetof(VexGuestAMD64State, guest_FS_ZERO) ||
				     ((IRExprGet *)assoc->contents[1])->reg.asReg() == offsetof(VexGuestAMD64State, guest_RSP))) {
					/* Special case: BadPtr(k+x) is always false
					   if x == RSP or x == FS_ZERO */
					res = IRExpr_Const_U1(false);
					break;
				}

				if (old_delta != new_delta) {
					if (new_delta == 0)
						e->arg = assoc->contents[1];
					else
						e->arg =
							IRExpr_Binop(
								Iop_Add64,
								IRExpr_Const_U64(
									cnst->Ico.U64 & ~((1ul << 22) - 1)),
								assoc->contents[1]);
					progress = true;
					break;
				}
			}
			if (e->arg->tag == Iex_Get &&
			    !((IRExprGet *)e->arg)->reg.isTemp() &&
			    (((IRExprGet *)e->arg)->reg.asReg() == offsetof(VexGuestAMD64State, guest_FS_ZERO) ||
			     ((IRExprGet *)e->arg)->reg.asReg() == offsetof(VexGuestAMD64State, guest_RSP))) {
				/* The FS and RSP registers are
				   assumed to always point at valid
				   memory. */
				res = IRExpr_Const_U1(false);
				break;
			}
		}

		if (e->arg->tag == Iex_Mux0X) {
			IRExprMux0X *arg = (IRExprMux0X *)e->arg;
			res = IRExpr_Mux0X(arg->cond,
					   IRExpr_Unop(
						   e->op,
						   arg->expr0),
					   IRExpr_Unop(
						   e->op,
						   arg->exprX));
			break;
		}

		if (e->arg->tag == Iex_Const) {
			IRExprConst *c = (IRExprConst *)e->arg;
			switch (e->op) {
			case Iop_Neg8:
				res = IRExpr_Const_U8(-c->Ico.U8);
				break;
			case Iop_Neg16:
				res = IRExpr_Const_U16(-c->Ico.U16);
				break;
			case Iop_Neg32:
				res = IRExpr_Const_U32(-c->Ico.U32);
				break;
			case Iop_Neg64:
				res = IRExpr_Const_U64(-c->Ico.U64);
				break;
			case Iop_Not8:
				res = IRExpr_Const_U8(~c->Ico.U8);
				break;
			case Iop_Not16:
				res = IRExpr_Const_U16(~c->Ico.U16);
				break;
			case Iop_Not32:
				res = IRExpr_Const_U32(~c->Ico.U32);
				break;
			case Iop_Not64:
				res = IRExpr_Const_U64(~c->Ico.U64);
				break;
			case Iop_Not1:
				res = IRExpr_Const_U1(!c->Ico.U1);
				break;
			case Iop_1Uto8:
				res = IRExpr_Const_U8(c->Ico.U1);
				break;
			case Iop_1Uto32:
				res = IRExpr_Const_U32(c->Ico.U1);
				break;
			case Iop_1Uto64:
				res = IRExpr_Const_U64(c->Ico.U1);
				break;
			case Iop_8Uto16:
				res = IRExpr_Const_U16(c->Ico.U8);
				break;
			case Iop_8Uto32:
				res = IRExpr_Const_U32(c->Ico.U8);
				break;
			case Iop_8Uto64:
				res = IRExpr_Const_U64(c->Ico.U8);
				break;
			case Iop_16Uto32:
				res = IRExpr_Const_U32(c->Ico.U16);
				break;
			case Iop_16Uto64:
				res = IRExpr_Const_U64(c->Ico.U16);
				break;
			case Iop_32Uto64:
				res = IRExpr_Const_U64(c->Ico.U32);
				break;
			case Iop_64to32:
				res = IRExpr_Const_U32(c->Ico.U64);
				break;
			case Iop_64to16:
				res = IRExpr_Const_U16(c->Ico.U64);
				break;
			case Iop_64to8:
				res = IRExpr_Const_U8(c->Ico.U64);
				break;
			case Iop_64to1:
				res = IRExpr_Const_U1(c->Ico.U64 & 1);
				break;
			case Iop_32to16:
				res = IRExpr_Const_U16(c->Ico.U32);
				break;
			case Iop_32to8:
				res = IRExpr_Const_U8(c->Ico.U32);
				break;
			case Iop_32to1:
				res = IRExpr_Const_U1(c->Ico.U32 & 1);
				break;
			case Iop_16to8:
				res = IRExpr_Const_U8(c->Ico.U16);
				break;
			case Iop_16to1:
				res = IRExpr_Const_U1(c->Ico.U16 & 1);
				break;
			case Iop_8to1:
				res = IRExpr_Const_U1(c->Ico.U8 & 1);
				break;
			case Iop_8Sto16:
				res = IRExpr_Const_U16( (char)c->Ico.U8);
				break;
			case Iop_8Sto32:
				res = IRExpr_Const_U32( (char)c->Ico.U8);
				break;
			case Iop_8Sto64:
				res = IRExpr_Const_U64( (char)c->Ico.U8);
				break;
			case Iop_16Sto32:
				res = IRExpr_Const_U32( (short)c->Ico.U16);
				break;
			case Iop_16Sto64:
				res = IRExpr_Const_U64( (short)c->Ico.U16);
				break;
			case Iop_32Sto64:
				res = IRExpr_Const_U64( (int)c->Ico.U32);
				break;
			case Iop_BadPtr:
				if (c->Ico.U64 < 4096) {
					res = IRExpr_Const_U1(true);
				} else {
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
					if (opt.addressAccessible(c->Ico.U64, &t))
						res = IRExpr_Const_U1(!t);
				}
				break;
			default:
				warning("cannot constant fold unop %d\n", e->op);
				printf("Cannot constant fold unop %d (", e->op);
				ppIROp(e->op, stdout);
				printf(")\n");
				break;
			}
		}
		break;
	}
	
	case Iex_Binop: {
		IRExprBinop *e = (IRExprBinop *)src;
		e->arg1 = optimiseIRExpr(e->arg1, opt, done_something);
		e->arg2 = optimiseIRExpr(e->arg2, opt, done_something);
		__set_profiling(optimise_binop);
		IRExpr *l = e->arg1;
		IRExpr *r = e->arg2;
		if (e->op >= Iop_Sub8 &&
		    e->op <= Iop_Sub64) {
			/* Replace a - b with a + (-b), so as to
			   eliminate binary -. */
			progress = true;
			e->op = (IROp)(e->op - Iop_Sub8 + Iop_Add8);
			r = e->arg2 =
				optimiseIRExprFP(
					IRExpr_Unop( (IROp)((e->op - Iop_Add8) + Iop_Neg8),
						     r ),
					opt,
					&progress);
		}
		if (operationAssociates(e->op)) {
			/* Convert to an associative operation. */
			res = optimiseIRExpr(
				IRExpr_Associative(
					e->op,
					l,
					r,
					NULL),
				opt,
				&progress);
			break;
		}
		/* If a op b commutes, sort the arguments. */
		if (operationCommutes(e->op) &&
		    sortIRExprs(r, l)) {
			e->arg1 = r;
			e->arg2 = l;
			l = e->arg1;
			r = e->arg2;
			progress = true;
		}

		/* 0 << x -> 0, and x << 0 -> x */
		if (((e->op >= Iop_Shl8 && e->op <= Iop_Shl64) ||
		     (e->op >= Iop_Shr8 && e->op <= Iop_Shr64) ||
		     (e->op >= Iop_Sar8 && e->op <= Iop_Sar64)) &&
		    ((r->tag == Iex_Const && ((IRExprConst *)r)->Ico.U8 == 0) ||
		     (l->tag == Iex_Const && ((IRExprConst *)l)->Ico.U64 == 0))) {
			res = l;
		}

		/* If, in a == b, a and b are physically
		 * identical, the result is a constant 1. */
		if ( (e->op == Iop_CmpEQ1 ||
		      e->op == Iop_CmpEQF32 ||
		      e->op == Iop_CmpEQF64 ||
		      e->op == Iop_CmpEQI128 ||
		      e->op == Iop_CmpEQV128 ||
		      (e->op >= Iop_CmpEQ8 && e->op <= Iop_CmpEQ64)) &&
		     physicallyEqual(l, r) ) {
			res = IRExpr_Const_U1(true);
			break;
		}

		if (e->op == Iop_CmpEQ1 &&
		    e->arg1->tag == Iex_Unop &&
		    e->arg2->tag == Iex_Unop &&
		    ((IRExprUnop *)e->arg1)->op == Iop_Not1 &&
		    ((IRExprUnop *)e->arg2)->op == Iop_Not1) {
			l = e->arg1 = ((IRExprUnop *)e->arg1)->arg;
			r = e->arg2 = ((IRExprUnop *)e->arg2)->arg;
			progress = true;
		}

		if ( e->op >= Iop_CmpLT8S &&
		     e->op <= Iop_CmpLT64S &&
		     physicallyEqual(e->arg1,e->arg2) ) {
			res = IRExpr_Const_U1(false);
			break;
		}

		/* !x != x, for any x */
		if (e->op == Iop_CmpEQ1 &&
		    ((e->arg1->tag == Iex_Unop &&
		      ((IRExprUnop *)e->arg1)->op == Iop_Not1 &&
		      ((IRExprUnop *)e->arg1)->arg == e->arg2) ||
		     (e->arg2->tag == Iex_Unop &&
		      ((IRExprUnop *)e->arg2)->op == Iop_Not1 &&
		      ((IRExprUnop *)e->arg2)->arg == e->arg1))) {
			res = IRExpr_Const_U1(false);
			break;
		}
		     
		if (e->op == Iop_CmpF64 &&
		    e->arg1->tag == Iex_Unop &&
		    e->arg2->tag == Iex_Unop &&
		    ((IRExprUnop *)e->arg1)->op == Iop_F32toF64 &&
		    ((IRExprUnop *)e->arg2)->op == Iop_F32toF64) {
			res = IRExpr_Binop(Iop_CmpF32, ((IRExprUnop *)e->arg1)->arg, ((IRExprUnop *)e->arg2)->arg);
			break;
		}

		if ( (e->op == Iop_CmpF32 || e->op == Iop_CmpF64) &&
		     physicallyEqual(e->arg1, e->arg2) ) {
			res = IRExpr_Const_U32(0x40);
			break;
		}

		/* We simplify == expressions with sums on the left
		   and right by trying to move all of the constants to
		   the left and all of the non-constants to the
		   right. */
		if (e->op >= Iop_CmpEQ8 && e->op <= Iop_CmpEQ64) {
			if (r->tag == Iex_Associative &&
			    ((IRExprAssociative *)r)->op >= Iop_Add8 &&
			    ((IRExprAssociative *)r)->op <= Iop_Add64 &&
			    ((IRExprAssociative *)r)->contents[0]->tag == Iex_Const) {
				assert(((IRExprAssociative *)r)->nr_arguments > 1);
				/* a == C + b -> -C + a == b */
				IRExpr *cnst = ((IRExprAssociative *)r)->contents[0];
				IRExprAssociative *newRight = (IRExprAssociative *)IRExpr_Associative((IRExprAssociative *)r);
				purgeAssocArgument(newRight, 0);
				IRExpr *newLeft = IRExpr_Associative(
					((IRExprAssociative *)r)->op,
					IRExpr_Unop(
						(IROp)(Iop_Neg8 + (((IRExprAssociative *)r)->op - Iop_Add8)),
						cnst),
					l,
					NULL);
				l = e->arg1 = optimiseIRExprFP(newLeft, opt, &progress);
				r = e->arg2 = optimiseIRExprFP(newRight, opt, &progress);
				progress = true;
			}
			if (l->tag == Iex_Associative &&
			    ((IRExprAssociative *)l)->op >= Iop_Add8 &&
			    ((IRExprAssociative *)l)->op <= Iop_Add64) {
				/* C + a == b -> C == b - a */
				assert(((IRExprAssociative *)l)->nr_arguments > 1);
				IRExprAssociative *newR =
					(IRExprAssociative *)IRExpr_Associative(((IRExprAssociative *)l)->op, r, NULL);
				for (int it = 1;
				     it < ((IRExprAssociative *)l)->nr_arguments;
				     it++)
					addArgumentToAssoc(newR,
							   IRExpr_Unop(
								   (IROp)(Iop_Neg8 + (((IRExprAssociative *)l)->op - Iop_Add8)),
								   ((IRExprAssociative *)l)->contents[it]));
				IRExpr *cnst = ((IRExprAssociative *)l)->contents[0];
				if (cnst->tag != Iex_Const) {
					switch (((IRExprAssociative *)l)->op) {
					case Iop_Add8:
						addArgumentToAssoc(newR,
								   IRExpr_Unop(
									   Iop_Neg8,
									   cnst));
						cnst = IRExpr_Const_U8(0);
						break;
					case Iop_Add16:
						addArgumentToAssoc(newR,
								   IRExpr_Unop(
									   Iop_Neg16,
									   cnst));
						cnst = IRExpr_Const_U16(0);
						break;
					case Iop_Add32:
						addArgumentToAssoc(newR,
								   IRExpr_Unop(
									   Iop_Neg32,
									   cnst));
						cnst = IRExpr_Const_U32(0);
						break;
					case Iop_Add64:
						addArgumentToAssoc(newR,
								   IRExpr_Unop(
									   Iop_Neg64,
									   cnst));
						cnst = IRExpr_Const_U64(0);
						break;
					default:
						abort();
					}
				}
				l = e->arg1 = cnst;
				r = e->arg2 = optimiseIRExprFP(newR, opt, &progress);
				progress = true;
			}

			/* Otherwise, a == b -> 0 == b - a, provided that a is not a constant. */
			if (l->tag != Iex_Const && e->op == Iop_CmpEQ64) {
				e->arg1 = IRExpr_Const_U64(0);
				e->arg2 =
					IRExpr_Binop(
						Iop_Add64,
						r,
						IRExpr_Unop(
							Iop_Neg64,
							l));
				progress = true;
			}

			/* Special case: const:64 == {b}to64(X)
			   can be optimised a bit by
			   converting the constant to type b
			   and then removing the conversion.
			   In some cases, the conversion will
			   show that there is now way for it
			   to be true, which simplifies things
			   a bit further. */
			if (l->tag == Iex_Const &&
			    r->tag == Iex_Unop &&
			    e->op == Iop_CmpEQ64) {
				IRExprConst *lc = (IRExprConst *)l;
				IRExprUnop *ru = (IRExprUnop *)r;
				assert(lc->ty == Ity_I64);
				/* Only consider the cases b =
				 * 1U and b = 32U */
				if (ru->op == Iop_1Uto64) {
					if (lc->Ico.U64 & 0xfffffffffffffffeul) {
						res = IRExpr_Const_U1(false);
					} else {
						progress = true;
						e->op = Iop_CmpEQ1;
						e->arg1 = IRExpr_Const_U1(lc->Ico.U64);
						e->arg2 = ru->arg;
					}
					break;
				}
				if (ru->op == Iop_32Uto64) {
					if (lc->Ico.U64 & 0xffffffff00000000ul) {
						res = IRExpr_Const_U1(false);
					} else {
						progress = true;
						e->op = Iop_CmpEQ32;
						e->arg1 = IRExpr_Const_U32(lc->Ico.U64);
						e->arg2 = ru->arg;
					}
					break;
				}

				/* Another special case: if
				   you have k = -(foo), where
				   k is a constant, it's
				   better to convert that to
				   -k = foo */
				if (ru->op == Iop_Neg64) {
					e->arg1 = IRExpr_Const_U64(-lc->Ico.U64);
					e->arg2 = ru->arg;
					progress = true;
					break;
				}
			}

			/* Another special case: const =
			   rsp:t1 - rsp:t2 is always false, if
			   t1 != t2 and we have
			   assumePrivateStacks set. */
			if (opt.assumePrivateStack() &&
			    e->op == Iop_CmpEQ64 &&
			    l->tag == Iex_Const &&
			    r->tag == Iex_Associative) {
				IRExprAssociative *ra = (IRExprAssociative *)r;
				if (ra->op == Iop_Add64 &&
				    ra->nr_arguments == 2 &&
				    ra->contents[0]->tag == Iex_Get &&
				    ra->contents[1]->tag == Iex_Unop) {
					IRExprGet *ra0 = (IRExprGet *)ra->contents[0];
					IRExprUnop *ra1 = (IRExprUnop *)ra->contents[1];
					if (ra0->reg.isReg() &&
					    ra0->reg.asReg() == OFFSET_amd64_RSP &&
					    ra1->op == Iop_Neg64 &&
					    ra1->arg->tag == Iex_Get) {
						IRExprGet *ra1a = (IRExprGet *)ra1->arg;
						if (ra1a->reg.isReg() &&
						    ra1a->reg.asReg() == OFFSET_amd64_RSP &&
						    ra1a->reg.tid() != ra0->reg.tid()) {
							res = IRExpr_Const_U1(false);
							break;
						}
					}
				}
			}
					    
		}

		/* Another special case: if we have k == -X +
		   Y then we turn it into -k == X + -Y
		   (i.e. normalise so that the leading term of
		   additions isn't negated, if possible). */
		if (e->op >= Iop_CmpEQ8 && e->op <= Iop_CmpEQ64 &&
		    l->tag == Iex_Const && r->tag == Iex_Associative) {
			IRExprAssociative *ra = (IRExprAssociative *)r;
			if (ra->op >= Iop_Add8 && ra->op <= Iop_Add64 &&
			    ra->nr_arguments > 0 &&
			    ra->contents[0]->tag == Iex_Unop) {
				IRExprUnop *leader = (IRExprUnop *)ra->contents[0];
				assert(!(opt.asUnsigned() & ~leader->optimisationsApplied));
				if (leader->op >= Iop_Neg8 && leader->op <= Iop_Neg64) {
					/* Do it */
					IRExprAssociative *new_r = new IRExprAssociative(*ra);
					for (int i = 0; i < new_r->nr_arguments; i++) {
						IRExpr *a = new_r->contents[i];
						assert(!(opt.asUnsigned() & ~a->optimisationsApplied));
						if (a->tag == Iex_Unop &&
						    ((IRExprUnop *)a)->op == leader->op)
							new_r->contents[i] = ((IRExprUnop *)a)->arg;
						else
							new_r->contents[i] =
								IRExpr_Unop(
									leader->op,
									a);
					}
					new_r->optimisationsApplied = 0;
					IRExprConst *new_l;
					IRExprConst *lc = (IRExprConst *)l;
					switch (e->op) {
					case Iop_CmpEQ8:
						new_l = IRExpr_Const_U8(
							-lc->Ico.U8);
						break;
					case Iop_CmpEQ16:
						new_l = IRExpr_Const_U16(
							-lc->Ico.U16);
						break;
					case Iop_CmpEQ32:
						new_l = IRExpr_Const_U32(
							-lc->Ico.U32);
						break;
					case Iop_CmpEQ64:
						new_l = IRExpr_Const_U64(
							-lc->Ico.U64);
						break;
					default:
						abort();
					}
					l = e->arg1 = new_l;
					r = e->arg2 = new_r;
					progress = true;
				}
			}
		}
		/* 0 == x -> !x if we're at the type U1. 1 == x is just x. */
		if (e->op == Iop_CmpEQ1 &&
		    l->tag == Iex_Const) {
			if ( ((IRExprConst *)l)->Ico.U1 )
				res = r;
			else
				res = IRExpr_Unop(Iop_Not1, r);
			break;
		}
		/* Slight generalisation of that:
		   0:X == 1UtoX(x) -> !x for any type X, and
		   1:X == 1UtoX(x) -> x */
		if (l->tag == Iex_Const &&
		    e->op >= Iop_CmpEQ8 &&
		    e->op <= Iop_CmpEQ64 &&
		    r->tag == Iex_Unop &&
		    ((IRExprUnop *)r)->op >= Iop_1Uto8 &&
		    ((IRExprUnop *)r)->op <= Iop_1Uto64) {
			IRExprConst *lc = (IRExprConst *)l;
			IRExprUnop *ru = (IRExprUnop *)r;
			if (lc->Ico.U1)
				res = ru->arg;
			else
				res = IRExpr_Unop(Iop_Not1, ru->arg);
			break;
		}

		/* And another one: -x == c -> x == -c if c is a constant. */
		if (e->op == Iop_CmpEQ64 &&
		    l->tag == Iex_Unop &&
		    ((IRExprUnop *)l)->op == Iop_Neg64 &&
		    r->tag == Iex_Const) {
			e->arg1 = ((IRExprUnop *)l)->arg;
			e->arg2 = IRExpr_Const_U64(
				-((IRExprConst *)r)->Ico.U64);
			progress = true;
			break;
		}

		/* If enabled, assume that the stack is ``private'',
		   in the sense that it doesn't alias with any global
		   variables, and is therefore never equal to any
		   constants which are present in the machine code. */
		if (opt.assumePrivateStack() &&
		    e->op == Iop_CmpEQ64 &&
		    r->tag == Iex_Get &&
		    !((IRExprGet *)r)->reg.isTemp() &&
		    ((IRExprGet *)r)->reg.asReg() == OFFSET_amd64_RSP &&
		    l->tag == Iex_Const) {
			res = IRExpr_Const_U1(false);
			break;
		}

		/* Convert CmpLE into CmpLT and CmpEQ */
		if (e->op == Iop_CmpLE32S || e->op == Iop_CmpLE64S ||
		    e->op == Iop_CmpLE32U || e->op == Iop_CmpLE64U) {
			res = IRExpr_Binop(
				Iop_Or1,
				IRExpr_Binop(
					(e->op == Iop_CmpLE32S ||
					 e->op == Iop_CmpLE32U) ?
					Iop_CmpEQ32 : Iop_CmpEQ64,
					e->arg1,
					e->arg2),
				IRExpr_Binop(
					e->op == Iop_CmpLE32S ? Iop_CmpLT32S :
					(e->op == Iop_CmpLE32U ? Iop_CmpLE32U :
					 (e->op == Iop_CmpLE64S ? Iop_CmpLT64S :
					  Iop_CmpLT64U)),
					e->arg1,
					e->arg2));
			break;
		}

		/* A couple of special rules: cmp_ltXu(0, x)
		   is just x != 0, and cmp_ltXu(x, 0) is just
		   false. */
		if (e->op >= Iop_CmpLT8U && e->op <= Iop_CmpLT64U) {
			if (e->arg1->tag == Iex_Const &&
			    isZero( (IRExprConst *)e->arg1 ) ) {
				res = IRExpr_Unop(
					Iop_Not1,
					IRExpr_Binop(
						(IROp)((int)Iop_CmpEQ8 +
						       (int)e->op -
						       (int)Iop_CmpLT8U),
						e->arg1,
						e->arg2));
				break;
			}
			if (e->arg2->tag == Iex_Const &&
			    isZero( (IRExprConst *)e->arg2 ) ) {
				res = IRExpr_Const_U1(false);
				break;
			}
		}

		if (l->tag == Iex_Mux0X) {
			IRExprMux0X *lm = (IRExprMux0X *)l;
			if (r->tag == Iex_Mux0X) {
				IRExprMux0X *rm = (IRExprMux0X *)r;
				if (physicallyEqual(lm->cond, rm->cond)) {
					res = IRExpr_Mux0X(
						lm->cond,
						IRExpr_Binop(e->op,
							     lm->expr0,
							     rm->expr0),
						IRExpr_Binop(e->op,
							     lm->exprX,
							     rm->exprX));
					break;
				}
			} else {
				res = IRExpr_Mux0X(
					lm->cond,
					IRExpr_Binop(
						e->op,
						lm->expr0,
						r),
					IRExpr_Binop(
						e->op,
						lm->exprX,
						r));
				break;
			}
		} else if (r->tag == Iex_Mux0X) {
			IRExprMux0X *rm = (IRExprMux0X *)r;
			progress = true;
			res = IRExpr_Mux0X(
				rm->cond,
				IRExpr_Binop(
					e->op,
					l,
					rm->expr0),
				IRExpr_Binop(
					e->op,
					l,
					rm->exprX));
			break;
		}

		/* If both arguments are constant, try to constant
		 * fold everything away. */
		if (l->tag == Iex_Const &&
		    r->tag == Iex_Const) {
			switch (e->op) {
			case Iop_CmpEQ32:
				res = IRExpr_Const_U1(
					((IRExprConst *)l)->Ico.U32 ==
					((IRExprConst *)r)->Ico.U32);
				break;
			case Iop_CmpLT64S:
				res = IRExpr_Const_U1(
					(long)((IRExprConst *)l)->Ico.U64 <
					(long)((IRExprConst *)r)->Ico.U64);
				break;
			case Iop_CmpLT64U:
				res = IRExpr_Const_U1(
					((IRExprConst *)l)->Ico.U64 <
					((IRExprConst *)r)->Ico.U64);
				break;
			case Iop_CmpLE64U:
				res = IRExpr_Const_U1(
					((IRExprConst *)l)->Ico.U64 <=
					((IRExprConst *)r)->Ico.U64);
				break;
			case Iop_CmpLT16U:
				res = IRExpr_Const_U1(
					((IRExprConst *)l)->Ico.U16 <
					((IRExprConst *)r)->Ico.U16);
				break;
			case Iop_CmpLT16S:
				res = IRExpr_Const_U1(
					(short)((IRExprConst *)l)->Ico.U16 <
					(short)((IRExprConst *)r)->Ico.U16);
				break;
			case Iop_CmpLT32U:
				res = IRExpr_Const_U1(
					((IRExprConst *)l)->Ico.U32 <
					((IRExprConst *)r)->Ico.U32);
				break;
			case Iop_CmpLT32S:
				res = IRExpr_Const_U1(
					(int)((IRExprConst *)l)->Ico.U32 <
					(int)((IRExprConst *)r)->Ico.U32);
				break;
			case Iop_CmpEQ8:
				res = IRExpr_Const_U1(
					((IRExprConst *)l)->Ico.U8 ==
					((IRExprConst *)r)->Ico.U8);
				break;
			case Iop_CmpEQ16:
				res = IRExpr_Const_U1(
					((IRExprConst *)l)->Ico.U16 ==
					((IRExprConst *)r)->Ico.U16);
				break;
			case Iop_CmpEQ64:
				res = IRExpr_Const_U1(
					((IRExprConst *)l)->Ico.U64 ==
					((IRExprConst *)r)->Ico.U64);
				break;
			case Iop_Sar32:
				res = IRExpr_Const_U32(
					(int)((IRExprConst *)l)->Ico.U32 >>
					((IRExprConst *)r)->Ico.U8);
				break;
			case Iop_Sar64:
				res = IRExpr_Const_U64(
					(long)((IRExprConst *)l)->Ico.U64 >>
					((IRExprConst *)r)->Ico.U8);
				break;
			case Iop_Shr32:
				res = IRExpr_Const_U32(
					((IRExprConst *)l)->Ico.U32 >>
					((IRExprConst *)r)->Ico.U8);
				break;
			case Iop_Shr64:
				res = IRExpr_Const_U64(
					((IRExprConst *)l)->Ico.U64 >>
					((IRExprConst *)r)->Ico.U8);
				break;
			case Iop_Shl64:
				res = IRExpr_Const_U64(
					((IRExprConst *)l)->Ico.U64 <<
					((IRExprConst *)r)->Ico.U8);
				break;
			case Iop_CmpLT8U:
				res = IRExpr_Const_U1(
					((IRExprConst *)l)->Ico.U8 <
					((IRExprConst *)r)->Ico.U8);
				break;
			case Iop_CmpLT8S: {
				char a = ((IRExprConst *)l)->Ico.U8;
				char b = ((IRExprConst *)r)->Ico.U8;
				res = IRExpr_Const_U1(a < b);
				break;
			}
			case Iop_32HLto64:
				res = IRExpr_Const_U64(
					((unsigned long)((IRExprConst *)l)->Ico.U32 << 32) |
					((IRExprConst *)r)->Ico.U32);
				break;

			case Iop_64HLto128:
				res = IRExpr_Const_U128(
					((IRExprConst *)l)->Ico.U64,
					((IRExprConst *)r)->Ico.U64);
				break;

			default:
				warning("cannot constant fold binop %d\n", e->op);
				printf("Cannot constant fold binop %d (", e->op);
				ppIROp(e->op, stdout);
				printf(")\n");
				break;
			}
		}
		break;
	}

	case Iex_Mux0X: {
		IRExprMux0X *e = (IRExprMux0X *)src;
		e->cond = optimiseIRExpr(e->cond, opt, done_something);
		e->expr0 = rewriteBoolean(e->cond, false, e->expr0, done_something);
		e->expr0 = optimiseIRExpr(e->expr0, opt, done_something);
		e->exprX = rewriteBoolean(e->cond, true, e->exprX, done_something);
		e->exprX = optimiseIRExpr(e->exprX, opt, done_something);
		if (e->cond->tag == Iex_Const) {
			if (((IRExprConst *)e->cond)->Ico.U1)
				res = e->exprX;
			else
				res = e->expr0;
			break;
		}

		if (_sortIRExprs(e->exprX, e->expr0) == equal_to) {
			res = e->exprX;
			break;
		}

		if (e->type() == Ity_I1) {
			/* If we're working at boolean type
			   then the whole thing turns into a
			   sequence of boolean operations. */
			res = IRExpr_Binop(
				Iop_Or1,
				IRExpr_Binop(
					Iop_And1,
					IRExpr_Unop(
						Iop_Not1,
						e->cond),
					e->expr0),
				IRExpr_Binop(
					Iop_And1,
					e->cond,
					e->exprX));
			break;
		}

		if (e->expr0->tag == Iex_Mux0X &&
		    e->exprX->tag == Iex_Mux0X) {
			IRExprMux0X *e0 = (IRExprMux0X *)e->expr0;
			IRExprMux0X *eX = (IRExprMux0X *)e->exprX;
			if (physicallyEqual(e0->expr0, eX->expr0) &&
			    physicallyEqual(e0->exprX, eX->exprX)) {
				/* Rewrite Mux0X(a, Mux0X(b, x, y), Mux0X(c, x, y))
				   to Mux0X( (!a && !b) || (a && !c), x, y) */
				res = IRExpr_Mux0X(
					IRExpr_Binop(
						Iop_Or1,
						IRExpr_Binop(
							Iop_And1,
							IRExpr_Unop(
								Iop_Not1,
								e->cond),
							IRExpr_Unop(
								Iop_Not1,
								e0->cond)),
						IRExpr_Binop(
							Iop_And1,
							e->cond,
							IRExpr_Unop(
								Iop_Not1,
								eX->cond))),
					e0->expr0,
					e0->exprX);
			}
		}

		break;
	}

	case Iex_GetI: {
		IRExprGetI *g = (IRExprGetI *)src;
		IRExpr *ix = optimiseIRExpr(g->ix, opt, done_something);
		if (ix != g->ix)
			res = new IRExprGetI(g, ix);
		break;
	}

	case Iex_Load: {
		IRExprLoad *l = (IRExprLoad *)src;
		l->addr = optimiseIRExpr(l->addr, opt, done_something);
		break;
	}

	case Iex_Qop: {
		IRExprQop *q = (IRExprQop *)src;
		q->arg1 = optimiseIRExpr(q->arg1, opt, done_something);
		q->arg2 = optimiseIRExpr(q->arg2, opt, done_something);
		q->arg3 = optimiseIRExpr(q->arg3, opt, done_something);
		q->arg4 = optimiseIRExpr(q->arg4, opt, done_something);
		break;
	}

	case Iex_Triop: {
		IRExprTriop *t = (IRExprTriop *)src;
		t->arg1 = optimiseIRExpr(t->arg1, opt, done_something);
		t->arg2 = optimiseIRExpr(t->arg2, opt, done_something);
		t->arg3 = optimiseIRExpr(t->arg3, opt, done_something);
		break;
	}

	case Iex_EntryPoint:
	case Iex_ControlFlow:
	case Iex_Get:
	case Iex_Const:
	case Iex_HappensBefore:
	case Iex_FreeVariable:
		break;
	}

	if (res != src) {
		progress = true;
		src = res;
	}
	if (progress) {
		*done_something = true;
		goto top;
	}

	res->optimisationsApplied |= opt.asUnsigned();
	return res;
}

IRExpr *
simplifyIRExpr(IRExpr *a, const IRExprOptimisations &opt)
{
	bool progress;
	return optimiseIRExprFP(a, opt, &progress);
}

IRExpr *
expr_eq(IRExpr *a, IRExpr *b)
{
	assert(a->type() == b->type());
	switch (a->type()) {
	case Ity_I1:
		return IRExpr_Binop(Iop_CmpEQ1, a, b);
	case Ity_I8:
		return IRExpr_Binop(Iop_CmpEQ8, a, b);
	case Ity_I16:
		return IRExpr_Binop(Iop_CmpEQ16, a, b);
	case Ity_I32:
		return IRExpr_Binop(Iop_CmpEQ32, a, b);
	case Ity_I64:
		return IRExpr_Binop(Iop_CmpEQ64, a, b);
	case Ity_I128:
		return IRExpr_Binop(Iop_CmpEQI128, a, b);
	case Ity_INVALID:
		break;
	}
	abort();
}

QueryCache<IRExpr, IRExpr, bool> definitelyEqualCache("Definitely equal");
QueryCache<IRExpr, IRExpr, bool> definitelyNotEqualCache("Definitely not equal");
bool
definitelyEqual(IRExpr *a, IRExpr *b, const IRExprOptimisations &opt)
{
	if (a == b)
		return true;
	assert(a->type() == b->type());
	/* If one expression is a constant and the other one isn't
	   then we're basically stuffed here and there's no point in
	   going through the rest of the machinery. */
	if ((a->tag == Iex_Const) != (b->tag == Iex_Const))
		return false;
	if (a->tag == Iex_Const) {
		/* Special fast path for comparing two constants. */
		IRExprConst *ac = (IRExprConst *)a;
		IRExprConst *bc = (IRExprConst *)b;
		return physicallyEqual(ac, bc);
	}
	int idx = definitelyEqualCache.hash(a, b);
	bool res;
	if (definitelyEqualCache.query(a, b, idx, &res))
		return res;
	IRExpr *r = simplifyIRExpr(expr_eq(a, b), opt);
	res = (r->tag == Iex_Const && ((IRExprConst *)r)->Ico.U1);
	if (!TIMEOUT)
		definitelyEqualCache.set(a, b, idx, res);
	return res;
}
bool
definitelyNotEqual(IRExpr *a, IRExpr *b, const IRExprOptimisations &opt)
{
	if (a == b)
		return false;
	assert(a->type() == b->type());
	int idx = definitelyNotEqualCache.hash(a, b);
	bool res;
	if (definitelyNotEqualCache.query(a, b, idx, &res))
		return res;
	IRExpr *r = simplifyIRExpr(expr_eq(a, b), opt);
	res = (r->tag == Iex_Const && !((IRExprConst *)r)->Ico.U1);
	if (!TIMEOUT)
		definitelyNotEqualCache.set(a, b, idx, res);
	return res;
}

#define mk_exprbdd(name)						\
	static bool							\
	name(exprbdd *a, exprbdd *b, const IRExprOptimisations &opt,	\
	     std::set<std::pair<exprbdd *, exprbdd *> > &memo)		\
	{								\
		if (a->isLeaf && b->isLeaf)				\
			return name(a->leaf(), b->leaf(), opt);		\
		if (!memo.insert(std::pair<exprbdd *, exprbdd *>(a, b)).second)	\
			return true;					\
		if (a->isLeaf)						\
			return name(a, b->internal().trueBranch,  opt, memo) &&	\
				name(a, b->internal().falseBranch, opt, memo); \
		if (b->isLeaf)						\
			return name(a->internal().trueBranch,  b, opt, memo) &&	\
				name(a->internal().falseBranch, b, opt, memo); \
		if (a->internal().rank < b->internal().rank)		\
			return name(a->internal().trueBranch,  b, opt, memo) &&	\
				name(a->internal().falseBranch, b, opt, memo); \
		if (a->internal().rank == b->internal().rank)		\
			return name(a->internal().trueBranch,  b->internal().trueBranch,  opt, memo) &&	\
				name(a->internal().falseBranch, b->internal().falseBranch, opt, memo); \
		return name(a, b->internal().trueBranch,  opt, memo) &&	\
			name(a, b->internal().falseBranch, opt, memo);	\
	}								\
	bool								\
	name(exprbdd *a, exprbdd *b, const IRExprOptimisations &opt)	\
	{								\
		std::set<std::pair<exprbdd *, exprbdd *> > memo;	\
		return name(a, b, opt, memo);				\
	}
mk_exprbdd(definitelyEqual)
mk_exprbdd(definitelyNotEqual)
#undef mk_exprbdd

bool
isBadAddress(exprbdd *e)
{
	if (e->isLeaf)
		return e->leaf()->tag == Iex_Const &&
			(long)((IRExprConst *)e->leaf())->Ico.U64 < 4096;
	else
		return isBadAddress(e->internal().trueBranch) &&
			isBadAddress(e->internal().falseBranch);
}

template <typename treeT, typename scopeT> static treeT *
simplifyBDD(scopeT *scope, bbdd::scope *bscope, treeT *bdd, const IRExprOptimisations &opt,
	    bool *done_something, std::map<treeT *, treeT *> &memo)
{
	if (TIMEOUT)
		return bdd;
	if (bdd->isLeaf)
		return bdd;
	typedef typename std::pair<treeT *, treeT *> treePairT;
	auto it_did_insert = memo.insert(treePairT(bdd, (treeT *)NULL));
	if (!it_did_insert.second)
		return it_did_insert.first->second;
	treeT *res;

	IRExpr *cond = optimiseIRExprFP(bdd->internal().condition, opt, done_something);
	assert(cond->type() == Ity_I1);
	if (cond->tag == Iex_Const) {
		if (((IRExprConst *)cond)->Ico.U1)
			res = simplifyBDD(scope, bscope, bdd->internal().trueBranch, opt, done_something, memo);
		else
			res = simplifyBDD(scope, bscope, bdd->internal().falseBranch, opt, done_something, memo);
	} else {
		treeT *t = simplifyBDD(scope, bscope, bdd->internal().trueBranch, opt, done_something, memo);
		treeT *f = simplifyBDD(scope, bscope, bdd->internal().falseBranch, opt, done_something, memo);
		if (cond == bdd->internal().condition && t == bdd->internal().trueBranch && f == bdd->internal().falseBranch)
			res = bdd;
		else
			res = treeT::ifelse(
				scope,
				bbdd::var(bscope, cond),
				t,
				f);
	}
	it_did_insert.first->second = res;
	return res;
}
/* Hideous hack: the normal template is actually *incorrect* at
   exprbdds, so supply an explicit instantiation which does the right
   thing.  Ulch. */
template <> exprbdd *
simplifyBDD(exprbdd::scope *scope, bbdd::scope *bscope, exprbdd *bdd, const IRExprOptimisations &opt,
	    bool *done_something, std::map<exprbdd *, exprbdd *> &memo)
{
	if (TIMEOUT)
		return bdd;
	auto it_did_insert = memo.insert(std::pair<exprbdd *, exprbdd *>(bdd, (exprbdd *)NULL));
	if (!it_did_insert.second)
		return it_did_insert.first->second;
	exprbdd *res;

        if (bdd->isLeaf) {
		IRExpr *r = optimiseIRExprFP(bdd->leaf(), opt, done_something);
		if (r == bdd->leaf())
			res = bdd;
		else
			res = exprbdd::var(scope, bscope, r);
	} else {
		IRExpr *cond = optimiseIRExprFP(bdd->internal().condition, opt, done_something);
		assert(cond->type() == Ity_I1);
		if (cond->tag == Iex_Const) {
			if (((IRExprConst *)cond)->Ico.U1)
				res = simplifyBDD(scope, bscope, bdd->internal().trueBranch, opt, done_something, memo);
			else
				res = simplifyBDD(scope, bscope, bdd->internal().falseBranch, opt, done_something, memo);
		} else {
			exprbdd *t = simplifyBDD(scope, bscope, bdd->internal().trueBranch, opt, done_something, memo);
			exprbdd *f = simplifyBDD(scope, bscope, bdd->internal().falseBranch, opt, done_something, memo);
			if (cond == bdd->internal().condition && t == bdd->internal().trueBranch && f == bdd->internal().falseBranch)
				res = bdd;
			else
				res = exprbdd::ifelse(
					scope,
					bbdd::var(bscope, cond),
					t,
					f);
		}
	}
	it_did_insert.first->second = res;
	return res;
}

template <typename treeT, typename scopeT> static treeT *
simplifyBDD(scopeT *scope, bbdd::scope *bscope, treeT *bdd, const IRExprOptimisations &opt,
	    bool *done_something)
{
	std::map<treeT *, treeT *> memo;
	return simplifyBDD(scope, bscope, bdd, opt, done_something, memo);
}

template bbdd   *simplifyBDD(bbdd::scope *,   bbdd::scope *, bbdd *,   const IRExprOptimisations &, bool *);
template smrbdd *simplifyBDD(smrbdd::scope *, bbdd::scope *, smrbdd *, const IRExprOptimisations &, bool *);
template exprbdd *simplifyBDD(exprbdd::scope *, bbdd::scope *, exprbdd *, const IRExprOptimisations &, bool *);
