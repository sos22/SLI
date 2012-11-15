#include "sli.h"
#include "bdd.hpp"
#include "simplify_irexpr.hpp"

bbdd *
bbdd::var(scope *scope, IRExpr *a)
{
	assert(a->type() == Ity_I1);
	if (a->tag == Iex_Associative) {
		IRExprAssociative *iex = (IRExprAssociative *)a;
		assert(iex->op == Iop_And1 || iex->op == Iop_Or1);
		bbdd *res = bbdd::var(scope, iex->contents[0]);
		for (int i = 1; i < iex->nr_arguments; i++) {
			bbdd *r = bbdd::var(scope, iex->contents[i]);
			if (iex->op == Iop_And1)
				res = bbdd::And(scope, res, r);
			else
				res = bbdd::Or(scope, res, r);
		}
		return res;
	}
	if (a->tag == Iex_Unop &&
	    ((IRExprUnop *)a)->op == Iop_Not1)
		return bbdd::invert(scope, bbdd::var(scope, ((IRExprUnop *)a)->arg));
	return scope->makeInternal(a,
				   scope->cnst(true),
				   scope->cnst(false));
}

template <typename constT, typename subtreeT> template <typename scopeT, typename zipInternalT>
subtreeT *
const_bdd<constT, subtreeT>::zip(scopeT *scope,
				 zipInternalT where,
				 std::map<zipInternalT, subtreeT *> &memo)
{
	if (where.isLeaf())
		return where.leafzip();

	auto it_did_insert = memo.insert(
		std::pair<zipInternalT, subtreeT *>(where, (subtreeT *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		assert(it->second);
		return it->second;
	}

	IRExpr *bestCond = where.bestCond(scope->ordering);
	subtreeT *trueSucc = zip(scope, where.trueSucc(scope->ordering, bestCond), memo);
	subtreeT *falseSucc = zip(scope, where.falseSucc(scope->ordering, bestCond), memo);
	it->second = where.mkNode(scope, bestCond, trueSucc, falseSucc);
	return it->second;
}


class binary_zip_internal {
public:
	bool isAnd;
	bbdd *first;
	bbdd *second;
	IRExpr *bestCond(bdd_ordering *ordering) const {
		assert(!(first->isLeaf && second->isLeaf));
		if (first->isLeaf) {
			return second->content.condition;
		} else if (second->isLeaf) {
			return first->content.condition;
		} else if (ordering->before(first->content.condition,
					    second->content.condition)) {
			return first->content.condition;
		} else {
			return second->content.condition;
		}
	}
	binary_zip_internal trueSucc(bdd_ordering *ordering, IRExpr *cond) const {
		return binary_zip_internal(
			isAnd,
			first->isLeaf  || !ordering->equal(first->content.condition, cond)  ? first  : first->content.trueBranch,
			second->isLeaf || !ordering->equal(second->content.condition, cond) ? second : second->content.trueBranch);
	}
	binary_zip_internal falseSucc(bdd_ordering *ordering, IRExpr *cond) const {
		return binary_zip_internal(
			isAnd,
			first->isLeaf  || !ordering->equal(first->content.condition, cond)  ? first  : first->content.falseBranch,
			second->isLeaf || !ordering->equal(second->content.condition, cond) ? second : second->content.falseBranch);
	}
	binary_zip_internal(bool _isAnd, bbdd *_first, bbdd *_second)
		: isAnd(_isAnd), first(_first), second(_second)
	{}
	bool isLeaf() const {
		if (first == second)
			return true;
		return first->isLeaf || second->isLeaf;
	}
	bbdd *leafzip() const {
		assert(isLeaf());
		if (first == second)
			return first;
		if (first->isLeaf) {
			if (first->content.leaf) {
				if (isAnd)
					return second;
				else
					return first;
			} else {
				if (isAnd)
					return first;
				else
					return second;
			}
		} else if (second->isLeaf) {
			if (second->content.leaf) {
				if (isAnd)
					return first;
				else
					return second;
			} else {
				if (isAnd)
					return second;
				else
					return first;
			}
		} else {
			abort();
		}

	}
	bbdd *mkNode(bbdd::scope *scope,
		     IRExpr *a,
		     bbdd *t,
		     bbdd *f)
	{
		return scope->makeInternal(a, t, f);
	}
	bool operator<(const binary_zip_internal &o) const {
		if (first < o.first)
			return true;
		if (first > o.first)
			return false;
		return second < o.second;
	}
};
bbdd *
bbdd::And(scope *scope, bbdd *a, bbdd *b)
{
	return zip(scope, binary_zip_internal(true, a, b));
}
bbdd *
bbdd::Or(scope *scope, bbdd *a, bbdd *b)
{
	return zip(scope, binary_zip_internal(false, a, b));
}

template <typename subtreeT> class assume_zip_internal {
public:
	subtreeT *thing;
	bbdd *assumption;
	assume_zip_internal(subtreeT *_thing, bbdd *_assumption)
		: thing(_thing), assumption(_assumption)
	{}
	IRExpr *bestCond(bdd_ordering *ordering) const {
		assert(!(thing->isLeaf && assumption->isLeaf));
		if (thing->isLeaf) {
			return assumption->content.condition;
		} else if (assumption->isLeaf) {
			return thing->content.condition;
		} else if (ordering->before(thing->content.condition,
					    assumption->content.condition)) {
			return thing->content.condition;
		} else {
			return assumption->content.condition;
		}
	}
	assume_zip_internal trueSucc(bdd_ordering *ordering, IRExpr *cond) const {
		return assume_zip_internal(
			thing->isLeaf  || !ordering->equal(thing->content.condition, cond)  ? thing  : thing->content.trueBranch,
			assumption->isLeaf || !ordering->equal(assumption->content.condition, cond) ? assumption : assumption->content.trueBranch);
	}
	assume_zip_internal falseSucc(bdd_ordering *ordering, IRExpr *cond) const {
		return assume_zip_internal(
			thing->isLeaf  || !ordering->equal(thing->content.condition, cond)  ? thing  : thing->content.falseBranch,
			assumption->isLeaf || !ordering->equal(assumption->content.condition, cond) ? assumption : assumption->content.falseBranch);
	}
	bool isLeaf() const {
		return assumption->isLeaf || thing->isLeaf;
	}
	subtreeT *leafzip() const {
		if (assumption->isLeaf) {
			if (assumption->content.leaf)
				return thing;
			else
				return NULL;
		} else {
			assert(thing->isLeaf);
			return thing;
		}
	}
	subtreeT *mkNode(bdd_scope<subtreeT> *scope, IRExpr *cond, subtreeT *t, subtreeT *f) const
	{
		if (!t)
			return f;
		if (!f)
			return t;
		return scope->makeInternal(cond, t, f);
	}
	bool operator<(const assume_zip_internal &o) const {
		if (thing < o.thing)
			return true;
		if (thing > o.thing)
			return false;
		return assumption < o.assumption;
	}
};
template <typename constT, typename subtreeT> subtreeT *
const_bdd<constT, subtreeT>::assume(scope *scope, subtreeT *thing, bbdd *assumption)
{
	return zip(scope, assume_zip_internal<subtreeT>(thing, assumption));
}

bbdd *
bbdd::invert(scope *scope, bbdd *a)
{
	if (a->isLeaf)
		return scope->cnst(!a->content.leaf);
	else
		return scope->makeInternal(
			a->content.condition,
			bbdd::invert(scope, a->content.trueBranch),
			bbdd::invert(scope, a->content.falseBranch));
}

long
bdd_ordering::rankVariable(const IRExpr *a)
{
	auto it_did_insert = variableRankings.insert(std::pair<const IRExpr *, long>(a, nextRanking));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		bool dupe = false;
		for (auto it2 = variableRankings.begin();
		     !dupe && it2 != variableRankings.end();
		     it2++) {
			if (a != it2->first && physicallyEqual(a, it2->first)) {
				it->second = it2->second;
				dupe = true;
			}
		}
		if (!dupe)
			nextRanking++;
	}
	return it->second;
}

void
bdd_ordering::runGc(HeapVisitor &hv)
{
	std::map<const IRExpr *, long> newRankings;
	for (auto it = variableRankings.begin();
	     it != variableRankings.end();
	     it++) {
		const IRExpr *a = hv.visited(it->first);
		if (a)
			newRankings[a] = it->second;
	}
	variableRankings = newRankings;
}

#define INTBDD_DONT_CARE ((intbdd *)1)
class from_enabling_internal {
public:
	bool failed;
	intbdd::enablingTableT table;
	from_enabling_internal(const intbdd::enablingTableT &_table)
		: table(_table)
	{}
	from_enabling_internal(bool _failed)
		: failed(_failed)
	{}
	bool isLeaf() const {
		return failed || table.size() <= 1;
	}
	intbdd *leafzip() const {
		if (failed)
			return NULL;
		else if (table.size() == 0)
			return INTBDD_DONT_CARE;
		else
			return table.begin()->second;
	}
	IRExpr *bestCond(bdd_ordering *ordering) const {
		IRExpr *bestCond = NULL;
		for (auto it = table.begin(); it != table.end(); it++) {
			if (!it->first->isLeaf &&
			    (!bestCond ||
			     ordering->before(it->first->content.condition, bestCond)))
				bestCond = it->first->content.condition;
			if (!it->second->isLeaf &&
			    (!bestCond ||
			     ordering->before(it->second->content.condition, bestCond)))
				bestCond = it->second->content.condition;
		}
		assert(bestCond != NULL);
		return bestCond;
	}
	from_enabling_internal trueSucc(bdd_ordering *ordering,
					IRExpr *cond)
	{
		from_enabling_internal res(false);
		for (auto it = table.begin(); it != table.end(); it++) {
			bbdd *newGuard = it->first;
			intbdd *newRes = it->second;
			if (!newGuard->isLeaf &&
			    ordering->equal(newGuard->content.condition, cond))
				newGuard = newGuard->content.trueBranch;
			if (newGuard->isLeaf && !newGuard->content.leaf)
				continue;
			if (!newRes->isLeaf &&
			    ordering->equal(newRes->content.condition, cond))
				newRes = newRes->content.trueBranch;
			auto it2_did_insert = res.table.insert(std::pair<bbdd *, intbdd *>(newGuard, newRes));
			if (it2_did_insert.first->second != newRes)
				return from_enabling_internal(true);
		}
		return res;
	}
	from_enabling_internal falseSucc(bdd_ordering *ordering,
					 IRExpr *cond)
	{
		from_enabling_internal res(false);
		for (auto it = table.begin(); it != table.end(); it++) {
			bbdd *newGuard = it->first;
			intbdd *newRes = it->second;
			if (!newGuard->isLeaf &&
			    ordering->equal(newGuard->content.condition, cond))
				newGuard = newGuard->content.falseBranch;
			if (newGuard->isLeaf && !newGuard->content.leaf)
				continue;
			if (!newRes->isLeaf &&
			    ordering->equal(newRes->content.condition, cond))
				newRes = newRes->content.falseBranch;
			auto it2_did_insert = res.table.insert(std::pair<bbdd *, intbdd *>(newGuard, newRes));
			if (it2_did_insert.first->second != newRes)
				return from_enabling_internal(true);
		}
		return res;
	}
	intbdd *mkNode(intbdd::scope *scope, IRExpr *a, intbdd *t, intbdd *f)
	{
		if (t == NULL || f == NULL)
			return NULL;
		if (t == INTBDD_DONT_CARE)
			return f;
		if (f == INTBDD_DONT_CARE)
			return t;
		return scope->makeInternal(a, t, f);
	}
	bool operator<(const from_enabling_internal &o) const {
		return table < o.table;
	}
};

intbdd *
intbdd::from_enabling(scope *scope, const enablingTableT &inp)
{
	intbdd *res = zip(scope, from_enabling_internal(inp));
	if (res == INTBDD_DONT_CARE)
		return scope->cnst(0);
	else
		return res;
}
#undef INTBDD_DONT_CARE

template <typename leafT, typename subtreeT> void
_bdd<leafT, subtreeT>::prettyPrint(FILE *f)
{
	int nextLabel = 0;
	std::map<_bdd *, int> labels;

	/* First, assign labels to anything which occurs multiple
	 * times. */
	{
		std::set<_bdd *> seen;
		std::vector<_bdd *> pending;
		pending.push_back(this);
		while (!pending.empty()) {
			auto l = pending.back();
			assert(l);
			pending.pop_back();
			if (labels.count(l))
				continue;
			if (seen.count(l)) {
				/* Need a label */
				labels[l] = nextLabel;
				nextLabel++;
			}
			seen.insert(l);
			if (!l->isLeaf) {
				assert(l->content.trueBranch);
				assert(l->content.falseBranch);
				pending.push_back(l->content.trueBranch);
				pending.push_back(l->content.falseBranch);
			}
		}
	}

	int lsize = 1;
	int c = 1;
	while (c <= nextLabel) {
		c *= 10;
		lsize++;
	}

	/* Now print it */
	std::set<_bdd *> printed;
	std::vector<std::pair<int, _bdd *> > pending;
	pending.push_back(std::pair<int, _bdd *>(0, this));
	while (!pending.empty()) {
		int depth = pending.back().first;
		auto what = pending.back().second;
		pending.pop_back();

		if (labels.count(what) && !printed.count(what))
			fprintf(f, "[%*d]", lsize, labels[what]);
		else
			fprintf(f, "%*s", lsize + 2, "");
		fprintf(f, "%*s", depth, "");
		if (printed.count(what)) {
			assert(labels.count(what));
			fprintf(f, "[->%d]", labels[what]);
		} else {
			printed.insert(what);
			if (what->isLeaf) {
				fprintf(f, "Leaf: ");
				what->_prettyPrint(f, what->content.leaf);
			} else {
				fprintf(f, "Mux: ");
				ppIRExpr(what->content.condition, f);
				pending.push_back(std::pair<int, _bdd *>(depth + 1, what->content.falseBranch));
				pending.push_back(std::pair<int, _bdd *>(depth + 1, what->content.trueBranch));
			}
		}
		fprintf(f, "\n");
	}
}

template <typename t> t *
bdd_scope<t>::makeInternal(IRExpr *cond, t *a, t *b)
{
	assert(a);
	assert(b);
	if (a == b)
		return a;
	auto it_did_insert = intern.insert(
		std::pair<entry, t *>(
			entry(cond, a, b),
			(t *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = new t(cond, a, b);
	return it->second;
}

template void _bdd<int, intbdd>::prettyPrint(FILE *);
template void _bdd<bool, bbdd>::prettyPrint(FILE *);
template intbdd *const_bdd<int, intbdd>::assume(const_bdd_scope<intbdd> *, intbdd *, bbdd*);
template bbdd *const_bdd<bool, bbdd>::assume(const_bdd_scope<bbdd> *, bbdd *, bbdd*);
