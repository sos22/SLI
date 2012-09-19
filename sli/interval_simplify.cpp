/* Simplify expressions using integer interval arithmetic. */
#include "sli.h"
#include "sat_checker.hpp"

#ifndef NDEBUG
static bool debug_interval_arith = false;
static bool debug_interval_conv = false;
#else
#define debug_interval_arith false
#define debug_interval_conv false
#endif

namespace _interval_simplify {

/* A space is a subset of an integer type.  It's represented as a set
   of contiguous intervals of the type, closed on both ends.  e.g. we
   might, for instance, want to represent 5,6,7,8,11,12,13, which
   would look like [5,8]+[11,13].
*/
class space : public Named {
	typedef std::pair<unsigned long, unsigned long> interval;
	std::vector<interval> intervals;
	unsigned long type_max;
	char *mkName() const {
		std::vector<const char *> fragments;
		for (auto it = intervals.begin(); it != intervals.end(); it++)
			fragments.push_back(vex_asprintf("[%lx,%lx]", it->first, it->second));
		return flattenStringFragmentsMalloc(fragments,
						    ", ",
						    "{",
						    "}");
	}
public:
	IRExpr *asIRExpr(IRExpr *key);
	space operator!() const;
	space operator&&(const space &o) const;
	space operator||(const space &o) const;
	void sanity_check() const {
		assert(type_max);
		assert(!((type_max + 1) & (type_max)));
		for (unsigned x = 0; x < intervals.size(); x++) {
			assert(intervals[x].first <= intervals[x].second);
			assert(intervals[x].second <= type_max);
			if (x != 0)
				assert(intervals[x].first > intervals[x-1].second + 1);
		}
	}
	space(const std::vector<interval> &_intervals, unsigned long _type_max)
		: intervals(_intervals), type_max(_type_max)
	{
		sanity_check();
	}
	space(unsigned long low, unsigned long high, unsigned long _type_max)
		: type_max(_type_max)
	{
		intervals.push_back(interval(low, high));
		sanity_check();
	}
	space()
		: type_max(0)
	{}
	static space empty(unsigned long _type_max)
	{
		std::vector<interval> v;
		return space(v, _type_max);
	}
};

IRExpr *
space::asIRExpr(IRExpr *key)
{
	IRType ty;
	switch (type_max) {
	case 0xff:
		ty = Ity_I8;
		break;
	case 0xffff:
		ty = Ity_I16;
		break;
	case 0xffffffff:
		ty = Ity_I32;
		break;
	case 0xfffffffffffffffful:
		ty = Ity_I64;
		break;
	default:
		abort();
	}
	struct {
		IRType ty;
		unsigned long type_max;
		IRExpr *cnst(unsigned long v) {
			IRConst *c;
			switch (ty) {
			case Ity_I8:
				c = IRConst_U8(v);
				break;
			case Ity_I16:
				c = IRConst_U16(v);
				break;
			case Ity_I32:
				c = IRConst_U32(v);
				break;
			case Ity_I64:
				c = IRConst_U64(v);
				break;
			default:
				abort();
			}
			return IRExpr_Const(c);
		}
		IROp op() const {
			switch (ty) {
			case Ity_I8: return Iop_CmpLT8U;
			case Ity_I16: return Iop_CmpLT16U;
			case Ity_I32: return Iop_CmpLT32U;
			case Ity_I64: return Iop_CmpLT64U;
			default:
				abort();
			}
		}
		IROp eqOp() const {
			switch (ty) {
			case Ity_I8: return Iop_CmpEQ8;
			case Ity_I16: return Iop_CmpEQ16;
			case Ity_I32: return Iop_CmpEQ32;
			case Ity_I64: return Iop_CmpEQ64;
			default:
				abort();
			}
		}
		IRExpr *operator()(IRExpr *a, unsigned long v) {
			if (v == 0)
				return IRExpr_Const(
					IRConst_U1(0));
			else if (v == 1)
				return IRExpr_Binop(
					eqOp(),
					a,
					cnst(0));
			else if (v == type_max)
				return IRExpr_Unop(
					Iop_Not1,
					IRExpr_Binop(
						eqOp(),
						a,
						cnst(type_max)));
			else
				return IRExpr_Binop(op(), a, cnst(v));
		}
		IRExpr *operator()(unsigned long v, IRExpr *a) {
			if (v == type_max)
				return IRExpr_Const(
					IRConst_U1(0));
			else if (v == type_max - 1)
				return IRExpr_Binop(
					eqOp(),
					a,
					cnst(type_max));
			else if (v == 0)
				return IRExpr_Unop(
					Iop_Not1,
					IRExpr_Binop(
						eqOp(),
						a,
						cnst(0)));
			else
				return IRExpr_Binop(op(), cnst(v), a);
		}
	} lt = {ty, type_max};

	IRExprAssociative *res = IRExpr_Associative(intervals.size(), Iop_Or1);
	for (unsigned x = 0; x < intervals.size(); x++) {
		IRExpr *arg;
		if (intervals[x].first == intervals[x].second)
			arg = IRExpr_Binop(
				lt.eqOp(),
				lt.cnst(intervals[x].first),
				key);
		else if (intervals[x].first == 0 && intervals[x].second == type_max)
			arg = IRExpr_Const(IRConst_U1(1));
		else if (intervals[x].first == 0)
			arg = lt(key, intervals[x].second + 1);
		else if (intervals[x].second == type_max)
			arg = lt(intervals[x].first - 1, key);
		else
			arg = IRExpr_Binop(
				Iop_And1,
				lt(intervals[x].first - 1, key),
				lt(key, intervals[x].second + 1));
		res->contents[x] = arg;
	}
	res->nr_arguments = intervals.size();
	return res;
}

space
space::operator!() const
{
	std::vector<std::pair<unsigned long, unsigned long> > newIntervals;
	if (intervals.size() == 0) {
		newIntervals.push_back(interval(0, type_max));
		return space(newIntervals, type_max);
	}
	if (intervals[0].first != 0)
		newIntervals.push_back(interval(0, intervals[0].first - 1));
	for (unsigned x = 0; x < intervals.size() - 1; x++)
		newIntervals.push_back(interval(intervals[x].second + 1, intervals[x+1].first-1));
	if (intervals.back().second != type_max)
		newIntervals.push_back(interval(intervals.back().second + 1, type_max));
	space res = space(newIntervals, type_max);
	if (debug_interval_arith)
		printf("Intervals: !%s -> %s\n", name(), res.name());
	return res;
}

space
space::operator&&(const space &o) const
{
	assert(type_max == o.type_max);
	if (intervals.empty())
		return *this;
	if (o.intervals.empty())
		return o;
	return !(!*this || !o);
}

space
space::operator||(const space &o) const
{
	assert(type_max == o.type_max);
	if (intervals.empty())
		return o;
	if (o.intervals.empty())
		return *this;
	std::vector<interval> newIntervals;
	auto it1 = intervals.begin();
	auto it2 = o.intervals.begin();
	if (it1->first < it2->first) {
		newIntervals.push_back(*it1);
		it1++;
	} else {
		newIntervals.push_back(*it2);
		it2++;
	}
	while (it1 != intervals.end() || it2 != o.intervals.end()) {
		interval int_to_add;
		if (it1 != intervals.end() &&
		    (it2 == o.intervals.end() || it1->first < it2->first)) {
			int_to_add = *it1;
			it1++;
		} else {
			int_to_add = *it2;
			it2++;
		}
		assert(int_to_add.first >= newIntervals.back().first);
		if (int_to_add.first > newIntervals.back().second + 1) {
			/* Disjoint with existing range -> add a new interval. */
			newIntervals.push_back(int_to_add);
		} else if (int_to_add.first <= newIntervals.back().second + 1 &&
			   int_to_add.second > newIntervals.back().second) {
			/* Extends last existing range */
			newIntervals.back().second = int_to_add.second;
		} else {
			/* Subsumed by existing last range, discard */
		}
	}
	space res = space(newIntervals, type_max);
	if (debug_interval_arith)
		printf("Intervals: %s || %s -> %s\n", name(), o.name(), res.name());
	return res;
}

/* A spaces records the space which we've derived for each
   variable. */
class spaces : public Named {
	std::map<IRExpr *, space> content;
	char *mkName() const {
		std::vector<const char *> fragments;
		for (auto it = content.begin(); it != content.end(); it++)
			fragments.push_back(vex_asprintf("%s = %s",
							 nameIRExpr(it->first),
							 it->second.name()));
		return flattenStringFragmentsMalloc(fragments,
						    "; ",
						    "[",
						    "]");
	}
public:
	IRExpr *asIRExpr();
	bool empty() const { return content.empty(); }
	spaces operator!() {
		spaces n;
		for (auto it = content.begin(); it != content.end(); it++)
			n.content.insert(std::pair<IRExpr *, space>(it->first, !it->second));
		return n;
	}
	void operator &=(const spaces &sp) {
		for (auto it = sp.content.begin(); it != sp.content.end(); it++) {
			auto it2 = content.find(it->first);
			if (it2 == content.end())
				content.insert(*it);
			else
				it2->second = it->second && it2->second;
		}
	}

	spaces(IRExpr *key, const space &sp)
	{
		content.insert(std::pair<IRExpr *, space>(key, sp));
	}
	spaces()
	{}
};

IRExpr *
spaces::asIRExpr()
{
	assert(!content.empty());
	if (content.size() == 1)
		return content.begin()->second.asIRExpr(content.begin()->first);
	IRExprAssociative *res = IRExpr_Associative(content.size(), Iop_And1);
	res->nr_arguments = 0;
	for (auto it = content.begin(); it != content.end(); it++)
		res->contents[res->nr_arguments++] = it->second.asIRExpr(it->first);
	return res;
}

class intervalified : public Named {
	char *mkName() const {
		return my_asprintf("%s &&& %s", sp.name(), nameIRExpr(rest));
	}
public:
	spaces sp;
	IRExpr *rest;
	
	IRExpr *asIRExpr();

	intervalified operator!() {
		if (!rest)
			return intervalified(!sp);
		else
			return intervalified(IRExpr_Unop(Iop_Not1, asIRExpr()));
	}
	void operator &=(const intervalified &o) {
		sp &= o.sp;
		if (o.rest) {
			if (rest)
				rest = IRExpr_Binop(
					Iop_And1,
					rest,
					o.rest);
			else
				rest = o.rest;
		}
	}
	explicit intervalified(IRExpr *a)
		: rest(a)
	{}
	explicit intervalified(const spaces &_sp)
		: sp(_sp), rest(NULL)
	{}
	explicit intervalified(const spaces &_sp, IRExpr *_rest)
		: sp(_sp), rest(_rest)
	{}
};

static void
unpack_const(IRConst *cnst, unsigned long *type_max, unsigned long *val)
{
	switch (cnst->tag) {
	case Ico_U8:
		*val = cnst->Ico.U8;
		*type_max = 0xff;
		break;
	case Ico_U16:
		*val = cnst->Ico.U16;
		*type_max = 0xffff;
		break;
	case Ico_U32:
		*val = cnst->Ico.U32;
		*type_max = 0xffffffff;
		break;
	case Ico_U64:
		*val = cnst->Ico.U64;
		*type_max = 0xfffffffffffffffful;
		break;
	default:
		abort();
	}
}

static intervalified
interval_eq(IRConst *cnst, IRExpr *what)
{
	unsigned long cnsti;
	unsigned long type_max;
	unpack_const(cnst, &type_max, &cnsti);
	return intervalified(
		spaces(what, space(cnsti, cnsti, type_max)));
}

static intervalified
interval_ltu(IRExpr *arg1, IRExpr *arg2)
{
	space finalSpace;
	IRExpr *key;

	assert(arg1->tag == Iex_Const || arg2->tag == Iex_Const);
	assert(!(arg1->tag == Iex_Const && arg2->tag == Iex_Const));
	if (arg1->tag == Iex_Const) {
		unsigned long type_max;
		unsigned long k1;
		unsigned long k2;
		unpack_const( ((IRExprConst *)arg1)->con, &type_max, &k2);
		if (arg2->tag == Iex_Associative &&
		    ((IRExprAssociative *)arg2)->op >= Iop_Add8 &&
		    ((IRExprAssociative *)arg2)->op <= Iop_Add64 &&
		    ((IRExprAssociative *)arg2)->nr_arguments == 2 &&
		    ((IRExprAssociative *)arg2)->contents[0]->tag == Iex_Const) {
			IRExprAssociative *iea = (IRExprAssociative *)arg2;
			unsigned long t;
			unpack_const( ((IRExprConst *)iea->contents[0])->con, &t, &k1);
			assert(t == type_max);
			key = iea->contents[1];
		} else {
			k1 = 0;
			key = arg2;
		}

		assert(k1 <= type_max);
		assert(k2 <= type_max);
		/* Need to encode k2 < (x + k1), being careful of
		 * overflow. */
		if (k2 == type_max)
			finalSpace = space::empty(type_max);
		else if (k2 + 1 >= k1)
			finalSpace = space(k2 - k1 + 1, type_max - k1, type_max);
		else
			finalSpace =
				space(0, type_max - k1, type_max) ||
				space(type_max + 2 - k1 + k2, type_max, type_max);
	} else {
		assert(arg2->tag == Iex_Const);

		unsigned long type_max;
		unsigned long k2;
		unsigned long k1;
		unpack_const( ((IRExprConst *)arg2)->con, &type_max, &k2);
		if (arg1->tag == Iex_Associative &&
		    ((IRExprAssociative *)arg1)->op >= Iop_Add8 &&
		    ((IRExprAssociative *)arg1)->op <= Iop_Add64 &&
		    ((IRExprAssociative *)arg1)->nr_arguments == 2 &&
		    ((IRExprAssociative *)arg1)->contents[0]->tag == Iex_Const) {
			IRExprAssociative *iea = (IRExprAssociative *)arg1;
			unsigned long t;
			unpack_const( ((IRExprConst *)iea->contents[0])->con, &t, &k1);
			assert(t == type_max);
			key = iea->contents[1];
		} else {
			k1 = 0;
			key = arg1;
		}

		assert(k1 <= type_max);
		assert(k2 <= type_max);
		/* Now we need to encode (x + k1) < k2. */
		if (k2 == 0)
			finalSpace = space::empty(type_max);
		else if (k1 == 0)
			finalSpace = space(0, k2 - 1, type_max);
		else if (k1 < k2)
			finalSpace =
				space(0, k2 - k1 - 1, type_max) ||
				space(type_max + 1 - k1, type_max, type_max);
		else /* k1 >= k2, k2 != 0, k1 != 0 */
			finalSpace =
				space(type_max + 1 - k1,
				      type_max + k2 - k1,
				      type_max);
	}
	return intervalified(spaces(key, finalSpace));
}

static intervalified
intervalify(IRExpr *what)
{
	switch (what->tag) {
	case Iex_Const:
	case Iex_Get:
	case Iex_GetI:
	case Iex_Qop:
	case Iex_Triop:
	case Iex_HappensBefore:
	case Iex_FreeVariable:
		return intervalified(what);
	case Iex_Binop: {
		IRExprBinop *ieb = (IRExprBinop *)what;
		if (ieb->arg1->tag != Iex_Const && ieb->arg2->tag != Iex_Const)
			return intervalified(what);
		switch (ieb->op) {
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			assert(ieb->arg1->tag == Iex_Const);
			if (ieb->arg2->tag == Iex_Const)
				return intervalified(what);
			return interval_eq(((IRExprConst *)ieb->arg1)->con, ieb->arg2);
		case Iop_CmpLT8U:
		case Iop_CmpLT16U:
		case Iop_CmpLT32U:
		case Iop_CmpLT64U:
			return interval_ltu(ieb->arg1, ieb->arg2);
		case Iop_CmpLT8S:
		case Iop_CmpLT16S:
		case Iop_CmpLT32S:
		case Iop_CmpLT64S:
			abort();
		default:
			return intervalified(what);
		}
	}
	case Iex_Unop: {
		IRExprUnop *ieu = (IRExprUnop *)what;
		switch (ieu->op) {
		case Iop_Not1:
			return !intervalify(ieu->arg);
		default:
			return intervalified(what);
		}
	}
	case Iex_Associative: {
		IRExprAssociative *iea = (IRExprAssociative *)what;
		switch (iea->op) {
		case Iop_And1: {
			intervalified acc(intervalify(iea->contents[0]));
			for (int i = 1; i < iea->nr_arguments; i++)
				acc &= intervalify(iea->contents[i]);
			return acc;
		}
		case Iop_Or1:
			abort();
		default:
			return intervalified(what);
		}
	}
	}
	abort();
}

IRExpr *
intervalified::asIRExpr()
{
	if (sp.empty()) {
		if (rest)
			return rest;
		else
			return IRExpr_Const(IRConst_U1(1));
	} else {
		if (rest)
			return IRExpr_Binop(
				Iop_And1,
				sp.asIRExpr(),
				rest);
		else
			return sp.asIRExpr();
	}
}

static IRExpr *
interval_simplify(IRExpr *what)
{
	intervalified i(intervalify(what));
	if (debug_interval_conv)
		printf("intervalify(%s) -> %s\n", nameIRExpr(what), i.name());
	IRExpr *res = i.asIRExpr();
	if (debug_interval_conv)
		printf("%s asIRExpr() -> %s\n", i.name(), nameIRExpr(res));
	return res;
}

/* End of namespace */
};

IRExpr *
interval_simplify(IRExpr *what)
{
	return _interval_simplify::interval_simplify(what);
}
