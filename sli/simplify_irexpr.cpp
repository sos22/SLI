#include <time.h>

#include "sli.h"
#include "state_machine.hpp"

#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"
#include "query_cache.hpp"

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
		(op == Iop_Xor1) ||
		(op == Iop_CmpEQ1);
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
	hdr(Phi)
		return threadAndRegister::partialEq(a->reg, b->reg) &&
		        a->generations == b->generations &&
		        a->ty == b->ty;
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
	case AMD64G_CC_OP_SUBW:
		zf = IRExpr_Binop(Iop_CmpEQ64, dep1, dep2);
		cf = IRExpr_Binop(
			Iop_CmpLT64U,
			dep1,
			dep2);
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
#define do_logic(type)						\
		zf = IRExpr_Binop(				\
			Iop_CmpEQ ## type ,			\
			IRExpr_Unop(Iop_64to ## type, dep1),	\
			IRExpr_Const(IRConst_U ## type (0)));	\
		sf = IRExpr_Binop(				\
			Iop_CmpLT ## type ## S,			\
			IRExpr_Unop(Iop_64to ## type, dep1),	\
			IRExpr_Const(IRConst_U ## type (0)));	\
		of = IRExpr_Const(IRConst_U1(0));		\
		break;
	case AMD64G_CC_OP_LOGICB:
		do_logic(8);
	case AMD64G_CC_OP_LOGICW:
		do_logic(16);
	case AMD64G_CC_OP_LOGICL:
		do_logic(32);
#undef do_logic
	case AMD64G_CC_OP_LOGICQ:
		zf = IRExpr_Binop(				
			Iop_CmpEQ64,			
			dep1,					
			IRExpr_Const(IRConst_U64(0)));	
		sf = IRExpr_Binop(				
			Iop_CmpLT64S,			
			dep1,					
			IRExpr_Const(IRConst_U64(0)));	
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
_sortIRConsts(IRConst *a, IRConst *b)
{
	if (a->tag < b->tag)
		return less_than;
	if (a->tag > b->tag)
		return greater_than;
	switch (a->tag) {
#define do_type(t)							\
		case Ico_ ## t :					\
			return _sortIntegers(a->Ico. t, b->Ico. t)
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

/* Simple sort function: constants go at the front, and then
   everything goes afterwards.  We arrange that identical expressions
   are always sorted together.  Returns true if @a should be before
   @b. */
static sort_ordering
_sortIRExprs(IRExpr *_a, IRExpr *_b)
{
	if (_a == _b)
		return equal_to;
	if (_a->tag == Iex_Const && _b->tag == Iex_Const) {
		IRExprConst *a = (IRExprConst *)_a;
		IRExprConst *b = (IRExprConst *)_b;
		return _sortIRConsts(a->con, b->con);
	}
	if (_a->tag == Iex_Const)
		return less_than;
	if (_b->tag == Iex_Const)
		return greater_than;
	if (_a->tag < _b->tag)
		return less_than;
	if (_a->tag > _b->tag)
		return greater_than;

	sort_ordering s;

	switch (_a->tag) {
#define hdr1(t)								\
		case Iex_ ## t:	{					\
			IRExpr ## t *a = (IRExpr ## t *)_a,		\
				*b = (IRExpr ## t *)_b;
	hdr1(Get)
#define hdr(t) } hdr1(t)
		if (threadAndRegister::fullCompare()(a->reg, b->reg))
			return less_than;
		else if (threadAndRegister::fullCompare()(b->reg, a->reg))
			return greater_than;
		else
			return equal_to;
	hdr(GetI)
		return _sortIRExprs(a->ix, b->ix);
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
		if ((s = _sortIRExprs(a->arg1, b->arg1)) != equal_to)
			return s;
		else
			return _sortIRExprs(a->arg2, b->arg2);
	hdr(Unop)
		if (a->op < b->op)
			return less_than;
		if (a->op > b->op)
			return greater_than;
		return _sortIRExprs(a->arg, b->arg);
	hdr(Load)
		return _sortIRExprs(a->addr, b->addr);
	hdr(Const)
		return _sortIRConsts(a->con, b->con);
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
	hdr(FreeVariable)
		return _sortIntegers(a->key, b->key);
	hdr(ClientCall)
		if (a->callSite < b->callSite)
			return less_than;
		else if (a->callSite > b->callSite)
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
	hdr(ClientCallFailed)
		return _sortIRExprs(a->target,
				   b->target);
	hdr(HappensBefore)
		if ((s = _sortIntegers(a->before, b->before)) != equal_to)
			return s;
	        return _sortIntegers(a->after, b->after);

	hdr(Phi)
		if (threadAndRegister::partialCompare()(a->reg, b->reg))
			return less_than;
		if (threadAndRegister::partialCompare()(b->reg, a->reg))
			return greater_than;
	        if ((s = _sortIntegers(a->ty, b->ty)) != equal_to)
			return s;
		for (unsigned x = 0; x < a->generations.size() && x < b->generations.size(); x++) {
			if ((s = _sortIntegers(a->generations[x], b->generations[x])) != equal_to)
				return equal_to;
		}
		return _sortIntegers(a->generations.size(),
				     b->generations.size());
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
#ifndef NDEBUG
	e->sanity_check();
#endif
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
#ifndef NDEBUG
	e->sanity_check();
#endif
	return e;
}

template <bool ordering(IRExpr *, IRExpr *)> static void
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

template <bool ordering(IRExpr *, IRExpr *)> static void
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
_cnf_disjunction_sort(IRExpr *a, IRExpr *b)
{
	/* The disjunction order is essentially the same as the normal
	   sortIRExprs order, except that we strip off leading
	   Iop_Not1 operations, so that A and ~A always sort together,
	   and then do a little bit extra so that ~A is always after
	   A. */
	bool inv_a = false;
	bool inv_b = false;
	while (a->tag == Iex_Unop) {
		IRExprUnop *ua = (IRExprUnop *)a;
		if (ua->op != Iop_Not1)
			break;
		inv_a = true;
		a = ua->arg;
	}
	while (b->tag == Iex_Unop) {
		IRExprUnop *ub = (IRExprUnop *)b;
		if (ub->op != Iop_Not1)
			break;
		inv_b = true;
		b = ub->arg;
	}
	sort_ordering order = _sortIRExprs(a, b);
	if (order == equal_to) {
		return _sortIntegers(inv_a, inv_b);
	} else {
		return order;
	}
}

static sort_ordering
_cnf_conjunction_sort(IRExpr *a, IRExpr *b)
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
	IRExprAssociative *ae, *be;
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
sortIRExprs(IRExpr *a, IRExpr *b)
{
	return _sortIRExprs(a, b) == less_than;
}
bool
cnf_disjunction_sort(IRExpr *a, IRExpr *b)
{
	return _cnf_disjunction_sort(a, b) == less_than;
}
bool
cnf_conjunction_sort(IRExpr *a, IRExpr *b)
{
	return _cnf_conjunction_sort(a, b) == less_than;
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
	else
		_sortAssociativeArguments<sortIRExprs>(ae, done_something);
}

/* CNF subsetting relationship.  Essentially, does @a imply @b.  We
 * only care about the case where @a and @b are CNF disjunctions
 * here. */
static bool
isCnfSubset(IRExpr *a, IRExpr *b)
{
	IRExprAssociative *a_disjunct, *b_disjunct;
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
optimiseAssuming(IRExpr *iex, IRExpr *assumption, bool *done_something)
{
	bool invertAssumption;
	invertAssumption = false;
	if (assumption->tag == Iex_Unop) {
		IRExprUnop *u = (IRExprUnop *)assumption;
		if (u->op == Iop_Not1) {
			assumption = u->arg;
			invertAssumption = true;
		}
	}

	if (_sortIRExprs(iex, assumption) == equal_to) {
		*done_something = true;
		return IRExpr_Const(IRConst_U1(invertAssumption ? 0 : 1));
	}
	if (iex->tag == Iex_Unop) {
		IRExprUnop *u = (IRExprUnop *)iex;
		if (u->op == Iop_Not1 &&
		    _sortIRExprs(u->arg, assumption) == equal_to) {
			*done_something = true;
			return IRExpr_Const(IRConst_U1(invertAssumption ? 1 : 0));
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
				return IRExpr_Const(IRConst_U1(1));
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
					return IRExpr_Const(IRConst_U1(1));
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

/* Down-cast @expr so that it is of type @desiredType. */
IRExpr *
coerceTypes(IRType desiredType, IRExpr *expr)
{
	IRType origType = expr->type();
	assert(desiredType <= origType);
	switch (origType) {
	case Ity_I64:
		switch (desiredType) {
		case Ity_I8:
			return IRExpr_Unop(Iop_64to8, expr);
		case Ity_I16:
			return IRExpr_Unop(Iop_64to16, expr);
		case Ity_I32:
			return IRExpr_Unop(Iop_64to32, expr);
		default:
			break;
		}
		break;
	case Ity_I32:
		switch (desiredType) {
		case Ity_I8:
			return IRExpr_Unop(Iop_32to8, expr);
		case Ity_I16:
			return IRExpr_Unop(Iop_32to16, expr);
		default:
			break;
		}
		break;
	case Ity_I16:
		switch (desiredType) {
		case Ity_I8:
			return IRExpr_Unop(Iop_16to8, expr);
		default:
			break;
		}
		break;
	case Ity_I8:
		switch (desiredType) {
		case Ity_I1:
			return IRExpr_Unop(Iop_8to1, expr);
		default:
			break;
		}
		break;
	case Ity_F64:
		switch (desiredType) {
		case Ity_I64:
			return IRExpr_Unop(Iop_ReinterpF64asI64, expr);
		default:
			break;
		}
		break;
	case Ity_V128:
		switch (desiredType) {
		case Ity_F64:
			return IRExpr_Unop(Iop_ReinterpI64asF64,
					   IRExpr_Unop(Iop_V128to64, expr));
		default:
			break;
		}
	default:
		break;
	}
	if (desiredType != origType)
		abort();
	return expr;
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
			if (operationCommutes(e->op))
				sortAssociativeArguments(e, done_something);

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
#define do_sized_op(name, sz, op)					\
						case Iop_ ## name ## sz: \
							res = IRExpr_Const(IRConst_U ## sz \
									   (l->Ico.U ## sz op r->Ico.U ## sz));	\
							break
#define do_op(name, op)							   \
						do_sized_op(name, 8, op);  \
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
							res = IRExpr_Const(IRConst_U1(l->Ico.U1 & r->Ico.U1));
							break;
						case Iop_Or1:
							res = IRExpr_Const(IRConst_U1(l->Ico.U1 | r->Ico.U1));
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
						*done_something = true;
						purgeAssocArgument(e, it1 + 1);
					} else {
						it1++;
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

			/* x || ~x -> 1.  We know by the ordering that
			   if any such pairs are present then they'll
			   be adjacent and x will be before ~x, which
			   is handy. */
			if (e->op == Iop_Or1) {
				__set_profiling(optimise_assoc_x_or_not_x);
				for (int i = 0; i < e->nr_arguments - 1; i++) {
					if (e->contents[i+1]->tag == Iex_Unop &&
					    ((IRExprUnop *)e->contents[i+1])->op == Iop_Not1 &&
					    _sortIRExprs(((IRExprUnop *)e->contents[i+1])->arg,
							 e->contents[i]) == equal_to)
						return IRExpr_Const(IRConst_U1(1));
				}
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
							*done_something = true;
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
											     done_something);
					}
				}
			}

			if (e->op == Iop_Or1) {
				for (int idx1 = 0; idx1 < e->nr_arguments - 1; idx1++)
					for (int idx2 = idx1 + 1; idx2 < e->nr_arguments; idx2++)
						e->contents[idx2] = rewriteBoolean(e->contents[idx1],
										   false,
										   e->contents[idx2],
										   done_something);
			}

			if (e->op == Iop_And1) {
				for (int idx1 = 0; idx1 < e->nr_arguments - 1; idx1++)
					for (int idx2 = idx1 + 1; idx2 < e->nr_arguments; idx2++)
						e->contents[idx2] = rewriteBoolean(e->contents[idx1],
										   true,
										   e->contents[idx2],
										   done_something);
			}

			/* x + -x -> 0, for any plus-like operator, so remove
			 * both x and -x from the list. */
			/* Also do x & ~x -> 0, x ^ x -> 0, while we're here. */
			{
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
								*done_something = true;
								IRConst *result;
								switch (e->op) {
								case Iop_And8:
								case Iop_Xor8:
								case Iop_Add8:
									result = IRConst_U8(0);
									break;
								case Iop_And16:
								case Iop_Xor16:
								case Iop_Add16:
									result = IRConst_U16(0);
									break;
								case Iop_And32:
								case Iop_Xor32:
								case Iop_Add32:
									result = IRConst_U32(0);
									break;
								case Iop_And64:
								case Iop_Xor64:
								case Iop_Add64:
									result = IRConst_U64(0);
									break;
								case Iop_And1:
									result = IRConst_U1(0);
									break;
								default:
									abort();
								}
								if (and_like) {
									/* x & ~x -> 0 and eliminates the entire expression. */
									return IRExpr_Const(result);
								}

								/* Careful: do the largest index first so that the
								   other index remains valid. */
								if (it1 < it2) {
									purgeAssocArgument(e, it2);
									e->contents[it1] = IRExpr_Const(result);
								} else {
									purgeAssocArgument(e, it1);
									e->contents[it2] = IRExpr_Const(result);
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

			if (e->arg->tag == Iex_Unop) {
				IRExprUnop *argu = (IRExprUnop *)e->arg;
				if (inverseUnops(e->op, argu->op))
					return argu->arg;
				IROp ss;
				if (shortCircuitableUnops(e->op, argu->op, &ss))
					return optimiseIRExprFP(IRExpr_Unop(ss, argu->arg),
								opt,
								done_something);
			}

			if (e->arg->tag == Iex_Get) {
				IRExprGet *argg = (IRExprGet *)e->arg;
				if (e->op == Iop_64to32)
					return IRExpr_Get(argg->reg, Ity_I32);
				if (e->op == Iop_64to16 || e->op == Iop_32to16)
					return IRExpr_Get(argg->reg, Ity_I16);
				if (e->op == Iop_64to8 || e->op == Iop_32to8 || e->op == Iop_16to8)
					return IRExpr_Get(argg->reg, Ity_I8);
			}

			if (e->arg->tag == Iex_Load) {
				IRExprLoad *argl = (IRExprLoad *)e->arg;
				if (e->op == Iop_64to32)
					return IRExpr_Load(Ity_I32, argl->addr, argl->rip);
			}

			if (e->arg->tag == Iex_Associative) {
				IRExprAssociative *arga = (IRExprAssociative *)e->arg;
				if (e->op == Iop_Not1 &&
				    (arga->op == Iop_And1 || arga->op == Iop_Or1)) {
					/* Convert ~(x & y) to ~x | ~y */
					IRExprAssociative *a =
						(IRExprAssociative *)IRExpr_Associative(arga);
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
				if ((arga->op == Iop_Or8 || arga->op == Iop_Or16 || arga->op == Iop_Or32 || arga->op == Iop_Or64 ||
				     arga->op == Iop_And8 || arga->op == Iop_And16 || arga->op == Iop_And32 || arga->op == Iop_And64 ||
				     arga->op == Iop_Xor8 || arga->op == Iop_Xor16 || arga->op == Iop_Xor32 || arga->op == Iop_Xor64 ||
				     arga->op == Iop_Add8 || arga->op == Iop_Add16 || arga->op == Iop_Add32 || arga->op == Iop_Add64) &&
				    (e->op == Iop_64to32 || e->op == Iop_64to16 || e->op == Iop_64to8 ||
				                            e->op == Iop_32to16 || e->op == Iop_32to8 ||
				                                                   e->op == Iop_16to8)) {
					/* Push downcasts through and/or operations. */
					IRExprAssociative *a =
						(IRExprAssociative *)IRExpr_Associative(arga);
					for (int i = 0; i < a->nr_arguments; i++)
						a->contents[i] =
							optimiseIRExprFP(
								IRExpr_Unop(
									e->op,
									a->contents[i]),
								opt,
								done_something);
					IROp base_op = Iop_INVALID;
#define do_op(name)							\
					if (arga->op >= Iop_ ## name ## 8 \
					    && arga->op <= Iop_ ## name ## 64) \
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
					default:
						break;
					}
					assert(op != Iop_INVALID);
					a->op = op;
					return a;
				}
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
				case Iop_8Uto16:
					return IRExpr_Const(IRConst_U16(c->Ico.U8));
				case Iop_8Uto32:
					return IRExpr_Const(IRConst_U32(c->Ico.U8));
				case Iop_8Uto64:
					return IRExpr_Const(IRConst_U64(c->Ico.U8));
				case Iop_16Uto32:
					return IRExpr_Const(IRConst_U32(c->Ico.U16));
				case Iop_16Uto64:
					return IRExpr_Const(IRConst_U64(c->Ico.U16));
				case Iop_32Uto64:
					return IRExpr_Const(IRConst_U64(c->Ico.U32));
				case Iop_32Sto64:
					return IRExpr_Const(IRConst_U64((int)c->Ico.U32));
				case Iop_1Uto8:
					return IRExpr_Const(IRConst_U8(c->Ico.U1));
				case Iop_64to32:
					return IRExpr_Const(IRConst_U32(c->Ico.U64));
				case Iop_64to16:
					return IRExpr_Const(IRConst_U16(c->Ico.U64));
				case Iop_64to8:
					return IRExpr_Const(IRConst_U8(c->Ico.U64));
				case Iop_64to1:
					return IRExpr_Const(IRConst_U1(c->Ico.U64 & 1));
				case Iop_32to16:
					return IRExpr_Const(IRConst_U16(c->Ico.U32));
				case Iop_32to8:
					return IRExpr_Const(IRConst_U8(c->Ico.U32));
				case Iop_32to1:
					return IRExpr_Const(IRConst_U1(c->Ico.U32 & 1));
				case Iop_16to8:
					return IRExpr_Const(IRConst_U8(c->Ico.U16));
					/* VEX has no 16to1 operation, for some reason. */
				case Iop_8to1:
					return IRExpr_Const(IRConst_U1(c->Ico.U8 & 1));
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

			/* 0 << x -> 0, and x << 0 -> x */
			if (((e->op >= Iop_Shl8 && e->op <= Iop_Shl64) ||
			     (e->op >= Iop_Shr8 && e->op <= Iop_Shr64) ||
			     (e->op >= Iop_Sar8 && e->op <= Iop_Sar64)) &&
			    ((r->tag == Iex_Const && ((IRExprConst *)r)->con->Ico.U8 == 0) ||
			     (l->tag == Iex_Const && ((IRExprConst *)l)->con->Ico.U64 == 0))) {
				*done_something = true;
				return l;
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
				*done_something = true;
				return IRExpr_Const(IRConst_U1(1));
			}

			/* We simplify == expressions with sums on the left
			   and right by trying to move all of the constants to
			   the left and all of the non-constants to the
			   right. */
			if (e->op == Iop_CmpEQ64) {
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

				/* Special case: const:64 == {b}to64(X)
				   can be optimised a bit by
				   converting the constant to type b
				   and then removing the conversion.
				   In some cases, the conversion will
				   show that there is now way for it
				   to be true, which simplifies things
				   a bit further. */
				if (l->tag == Iex_Const &&
				    r->tag == Iex_Unop) {
					IRExprConst *lc = (IRExprConst *)l;
					IRExprUnop *ru = (IRExprUnop *)r;
					assert(lc->con->tag == Ico_U64);
					/* Only consider the cases b =
					 * 1U and b = 32U */
					if (ru->op == Iop_1Uto64) {
						if (lc->con->Ico.U64 & 0xfffffffffffffffeul) {
							return IRExpr_Const(IRConst_U1(0));
						} else {
							e->op = Iop_CmpEQ1;
							e->arg1 = IRExpr_Const(IRConst_U1(lc->con->Ico.U64));
							e->arg2 = ru->arg;
							*done_something = true;
							return e;
						}
					}
					if (ru->op == Iop_32Uto64) {
						if (lc->con->Ico.U64 & 0xffffffff00000000ul) {
							return IRExpr_Const(IRConst_U1(0));
						} else {
							e->op = Iop_CmpEQ32;
							e->arg1 = IRExpr_Const(IRConst_U32(lc->con->Ico.U64));
							e->arg2 = ru->arg;
							*done_something = true;
							return e;
						}
					}

					/* Another special case: if
					   you have k = -(foo), where
					   k is a constant, it's
					   better to convert that to
					   -k = foo */
					if (ru->op == Iop_Neg64) {
						e->arg1 = IRExpr_Const(IRConst_U64(-lc->con->Ico.U64));
						e->arg2 = ru->arg;
						*done_something = true;
						return e;
					}
				}

			}

			/* 0 == x -> !x if we're at the type U1. 1 == x is just x. */
			if (e->op == Iop_CmpEQ1 &&
			    l->tag == Iex_Const) {
				if ( ((IRExprConst *)l)->con->Ico.U1 )
					return r;
				else
					return IRExpr_Unop(Iop_Not1, r);
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
				*done_something = true;
				if (lc->con->Ico.U1)
					return ru->arg;
				else
					return IRExpr_Unop(Iop_Not1, ru->arg);
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
			if (opt.assumePrivateStack() &&
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
				case Iop_Shr32:
					*done_something = true;
					return IRExpr_Const(
						IRConst_U32(
							((IRExprConst *)l)->con->Ico.U32 >>
							((IRExprConst *)r)->con->Ico.U8));
				case Iop_Shr64:
					*done_something = true;
					return IRExpr_Const(
						IRConst_U64(
							((IRExprConst *)l)->con->Ico.U64 >>
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

		IRExpr *rewriteBoolean(IRExpr *expr, bool val, IRExpr *inp, bool *done_something) {
			struct : public IRExprTransformer {
				IRExpr *from;
				bool to;
				IRExpr *_to;
				bool *done_something;
				IRExpr *rewriteFrom;
				IRExpr *rewriteTo;
				IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
					if (physicallyEqual(e, from)) {
						if (!_to)
							_to = IRExpr_Const(IRConst_U1(to));
						*done_something = true;
						return _to;
					}
					if (rewriteFrom && physicallyEqual(e, rewriteFrom)) {
						*done_something = true;
						return rewriteTo;
					}
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
			doit.done_something = done_something;
			doit.rewriteFrom = NULL;
			doit.rewriteTo = NULL;
			if (val && expr->tag == Iex_Binop) {
				IRExprBinop *ieb = (IRExprBinop *)expr;
				if (ieb->op >= Iop_CmpEQ8 &&
				    ieb->op <= Iop_CmpEQ64) {
					/* CmpEQ is always sorted so
					   that the thing on the left
					   is before the thing on the
					   right in the expression
					   sort order.  That tends to
					   mean that the thing on the
					   left is simpler than the
					   thing on the right, so
					   rewriting from right to
					   left is generally
					   worthwhile. */
					doit.rewriteFrom = ieb->arg2;
					doit.rewriteTo = ieb->arg1;
				}
			}
			return doit.doit(inp);
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

			if (_sortIRExprs(e->exprX, e->expr0) == equal_to) {
				*done_something = true;
				return e->exprX;
			}

			if (e->type() == Ity_I1) {
				/* If we're working at boolean type
				   then the whole thing turns into a
				   sequence of boolean operations. */
				*done_something = true;
				return IRExpr_Binop(
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
			}

			if (e->exprX->tag == Iex_Associative &&
			    e->expr0->tag == Iex_Associative &&
			    ((IRExprAssociative *)e->exprX)->op ==
			    ((IRExprAssociative *)e->expr0)->op) {
				IRExprAssociative *eX = (IRExprAssociative *)e->exprX;
				IRExprAssociative *e0 = (IRExprAssociative *)e->expr0;
				IROp op = eX->op;
				if ((op >= Iop_Add8 && op <= Iop_Add64) ||
				    (op >= Iop_And8 && op <= Iop_And64) ||
				    (op >= Iop_Or8 && op <= Iop_Or64)) {
					/* Factorise the expression.  If we
					   have Mux0X(a, b + c, b + d),
					   we can turn that into
					   b + Mux0X(a, c, d). */
					/* We take advantage of the
					   fact that the operators are
					   all commutative and that
					   they're therefore
					   sorted. */
					int idx_x = 0;
					int idx_0 = 0;
					int nr_dupes = 0;
					while (idx_x < eX->nr_arguments &&
					       idx_0 < e0->nr_arguments) {
						sort_ordering s = _sortIRExprs(eX->contents[idx_x],
									       e0->contents[idx_0]);
						if (s == less_than) {
							idx_x++;
						} else if (s == greater_than) {
							idx_0++;
						} else {
							nr_dupes++;
							idx_x++;
							idx_0++;
						}
					}
					if (nr_dupes != 0) {
						*done_something = true;
						IRExprAssociative *newRoot =
							IRExpr_Associative(nr_dupes + 1,
									   op);
						IRExprAssociative *newX =
							IRExpr_Associative(
								eX->nr_arguments - nr_dupes,
								eX->op);
						IRExprAssociative *new0 =
							IRExpr_Associative(
								e0->nr_arguments - nr_dupes,
								e0->op);
						int idx_out;
						int idx_x_out;
						int idx_0_out;

						idx_x = 0;
						idx_0 = 0;
						idx_x_out = 0;
						idx_0_out = 0;
						idx_out = 0;
						while (idx_x < eX->nr_arguments &&
						       idx_0 < e0->nr_arguments) {
							sort_ordering s = _sortIRExprs(eX->contents[idx_x],
										       e0->contents[idx_0]);
							if (s == less_than) {
								newX->contents[idx_x_out] =
									eX->contents[idx_x];
								idx_x++;
								idx_x_out++;
							} else if (s == greater_than) {
								new0->contents[idx_0_out] =
									e0->contents[idx_0];
								idx_0++;
								idx_0_out++;
							} else {
								newRoot->contents[idx_out] =
									e0->contents[idx_0];
								idx_0++;
								idx_x++;
								idx_out++;
							}
						}
						while (idx_x < eX->nr_arguments) {
							newX->contents[idx_x_out] =
								eX->contents[idx_x];
							idx_x++;
							idx_x_out++;
						}
						while (idx_0 < e0->nr_arguments) {
							new0->contents[idx_0_out] =
								e0->contents[idx_0];
							idx_0++;
							idx_0_out++;
						}
						assert(idx_0 == e0->nr_arguments);
						assert(idx_x == eX->nr_arguments);
						assert(idx_0_out == e0->nr_arguments - nr_dupes);
						assert(idx_x_out == eX->nr_arguments - nr_dupes);
						assert(idx_out == nr_dupes);
						newRoot->contents[idx_out] =
							IRExpr_Mux0X(
								e->cond,
								new0,
								newX);
						newRoot->nr_arguments = idx_out + 1;
						newX->nr_arguments = idx_x_out;
						new0->nr_arguments = idx_0_out;
						return newRoot;
					}
				}
			}


			if (e->expr0->tag == Iex_Mux0X &&
			    e->exprX->tag == Iex_Mux0X) {
				IRExprMux0X *e0 = (IRExprMux0X *)e->expr0;
				IRExprMux0X *eX = (IRExprMux0X *)e->exprX;
				if (physicallyEqual(e0->expr0, eX->expr0) &&
				    physicallyEqual(e0->exprX, eX->exprX)) {
					/* Rewrite Mux0X(a, Mux0X(b, x, y), Mux0X(c, x, y))
					   to Mux0X( (!a && !b) || (a && !c), x, y) */
					*done_something = true;
					return IRExpr_Mux0X(
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

			return res;
		}

		IRExpr *transformIex(IRExprPhi *e) {
			hdr(Phi);
			if (e->generations.size() == 1)
				return IRExpr_Get(e->reg.setGen(e->generations[0]),
						  e->ty);
			return res;
		}
#undef hdr

	public:
		_(const AllowableOptimisations &_opt,
		  bool *_done_something)
			: opt(_opt), done_something(_done_something)
		{}
	} t(opt, done_something);
	return t.doit(src, done_something);
}

IRExpr *
simplifyIRExpr(IRExpr *a, const AllowableOptimisations &opt)
{
	bool progress;
	return optimiseIRExprFP(a, opt, &progress);
}

static IRExpr *
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
	case Ity_F32:
		return IRExpr_Binop(Iop_CmpEQF32, a, b);
	case Ity_F64:
		return IRExpr_Binop(Iop_CmpEQF64, a, b);
	case Ity_V128:
		return IRExpr_Binop(Iop_CmpEQV128, a, b);
	default:
		abort();
	}
}

QueryCache<IRExpr, IRExpr, bool> definitelyEqualCache("Definitely equal");
QueryCache<IRExpr, IRExpr, bool> definitelyNotEqualCache("Definitely not equal");
bool
definitelyEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt)
{
	assert(a->type() == b->type());
	int idx = definitelyEqualCache.hash(a, b);
	bool res;
	if (definitelyEqualCache.query(a, b, idx, &res)) {
		assert(a != b || res == true);
		return res;
	}
	IRExpr *r = simplifyIRExpr(expr_eq(a, b), opt);
	res = (r->tag == Iex_Const && ((IRExprConst *)r)->con->Ico.U1);
	if (!TIMEOUT) {
#warning This assertion could turn into a simple optimisation
		assert(a != b || res == true);
		definitelyEqualCache.set(a, b, idx, res);
	}
	return res;
}
bool
definitelyNotEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt)
{
	if (a == b)
		return false;
	assert(a->type() == b->type());
	int idx = definitelyNotEqualCache.hash(a, b);
	bool res;
	if (definitelyNotEqualCache.query(a, b, idx, &res))
		return res;
	IRExpr *r = simplifyIRExpr(expr_eq(a, b), opt);
	res = (r->tag == Iex_Const && !((IRExprConst *)r)->con->Ico.U1);
	if (!TIMEOUT)
		definitelyNotEqualCache.set(a, b, idx, res);
	return res;
}

bool
isBadAddress(IRExpr *e, const AllowableOptimisations &opt, Oracle *oracle)
{
	return e->tag == Iex_Const &&
		(long)((IRExprConst *)e)->con->Ico.U64 < 4096;
}

bool
definitelyUnevaluatable(IRExpr *e, const AllowableOptimisations &opt, Oracle *oracle)
{
	if (TIMEOUT)
		return false;
	class _ : public IRExprTransformer {
	public:
		bool res;
		const AllowableOptimisations &opt;
		Oracle *oracle;

		IRExpr *transformIex(IRExprLoad *e) {
			if (isBadAddress(e->addr, opt, oracle))
				res = true;
			return IRExprTransformer::transformIex(e);
		}
		_(const AllowableOptimisations &_opt,
		  Oracle *_oracle)
			: res(false), opt(_opt), oracle(_oracle)
		{}
	} t(opt, oracle);
	t.doit(e);
	return t.res;
}

