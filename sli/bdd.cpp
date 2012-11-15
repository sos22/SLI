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

/* The zipper effectively inlines these so that they never actually
 * get called, but they still need to be here so that it has something
 * to key off. */
static bbdd *
_leafzip_and(bool, bool)
{
	abort();
}
static bbdd *
_leafzip_or(bool, bool)
{
	abort();
}
static bbdd *
_leafzip_assume(bool, bool)
{
	abort();
}

bbdd *
bbdd::zip(scope *scope,
	  zipInternalT where,
	  zipLeafT leafzip,
	  std::map<zipInternalT, bbdd *> &memo)
{
	if (where.first == where.second) {
		if (leafzip == _leafzip_and || leafzip == _leafzip_or)
			return where.first;
		if (leafzip == _leafzip_assume)
			return scope->cnst(true);
	}
	if (leafzip == _leafzip_and || leafzip == _leafzip_or || leafzip == _leafzip_assume) {
		if (where.second->isLeaf) {
			if (where.second->content.leaf) {
				if (leafzip == _leafzip_and || leafzip == _leafzip_assume)
					return where.first;
				else
					return scope->cnst(true);
			} else {
				if (leafzip == _leafzip_assume)
					return NULL;
				else if (leafzip == _leafzip_and)
					return scope->cnst(false);
				else
					return where.first;
			}
		}
		if (where.first->isLeaf) {
			if (where.first->content.leaf) {
				if (leafzip == _leafzip_and)
					return where.second;
				else
					return scope->cnst(true);
			} else {
				if (leafzip == _leafzip_and || leafzip == _leafzip_assume)
					return scope->cnst(false);
				else
					return where.second;
			}
		}
	}

	if (where.first->isLeaf && where.second->isLeaf)
		return leafzip(where.first->content.leaf, where.second->content.leaf);

	auto it_did_insert = memo.insert(
		std::pair<zipInternalT, bbdd *>(where, (bbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		assert(it->second);
		return it->second;
	}

	IRExpr *bestCond;
	if (where.first->isLeaf) {
		bestCond = where.second->content.condition;
	} else if (where.second->isLeaf) {
		bestCond = where.first->content.condition;
	} else if (scope->ordering->before(where.first->content.condition,
					   where.second->content.condition)) {
		bestCond = where.first->content.condition;
	} else {
		bestCond = where.second->content.condition;
	}

	zipInternalT trueSucc;
	zipInternalT falseSucc;
	if (!where.first->isLeaf && scope->ordering->equal(bestCond, where.first->content.condition)) {
		trueSucc.first = where.first->content.trueBranch;
		falseSucc.first = where.first->content.falseBranch;
	} else {
		trueSucc.first = where.first;
		falseSucc.first = where.first;
	}
	if (!where.second->isLeaf && scope->ordering->equal(bestCond, where.second->content.condition)) {
		trueSucc.second = where.second->content.trueBranch;
		falseSucc.second = where.second->content.falseBranch;
	} else {
		trueSucc.second = where.second;
		falseSucc.second = where.second;
	}
	it->second = scope->makeInternal(
		bestCond,
		zip(scope, trueSucc, leafzip, memo),
		zip(scope, falseSucc, leafzip, memo));
	return it->second;
}

bbdd *
bbdd::And(scope *scope, bbdd *a, bbdd *b)
{
	return zip(scope, zipInternalT(a, b), _leafzip_and);
}
bbdd *
bbdd::Or(scope *scope, bbdd *a, bbdd *b)
{
	return zip(scope, zipInternalT(a, b), _leafzip_or);
}
bbdd *
bbdd::assume(scope *scope, bbdd *thing, bbdd *assumption)
{
	return zip(scope, zipInternalT(thing, assumption), _leafzip_assume);
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

intbdd *
intbdd::from_enabling(scope *scope,
		      const enablingTableT &_inp,
		      std::map<enablingTableT, intbdd *> &memo)
{
	enablingTableT inp;
	for (auto it = _inp.begin();
	     it != _inp.end();
	     it++) {
		if (it->first->isLeaf &&
		    !it->first->content.leaf)
			continue;
		inp[it->first] = it->second;
	}
	
	if (inp.empty())
		return INTBDD_DONT_CARE;

	if (inp.size() == 1)
		return inp.begin()->second;

	auto it_did_insert = memo.insert(std::pair<enablingTableT, intbdd *>(inp, (intbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;

	IRExpr *bestCond = NULL;
	for (auto it = inp.begin(); it != inp.end(); it++) {
		if (!it->first->isLeaf &&
		    (!bestCond ||
		     scope->ordering->before(it->first->content.condition, bestCond)))
			bestCond = it->first->content.condition;
		if (!it->second->isLeaf &&
		    (!bestCond ||
		     scope->ordering->before(it->second->content.condition, bestCond)))
			bestCond = it->second->content.condition;
	}
	assert(bestCond != NULL);

	enablingTableT trueSucc;
	for (auto it = inp.begin(); it != inp.end(); it++) {
		bbdd *newGuard = it->first;
		intbdd *newRes = it->second;
		if (!newGuard->isLeaf &&
		    newGuard->content.condition == bestCond)
			newGuard = newGuard->content.trueBranch;
		if (!newRes->isLeaf &&
		    newRes->content.condition == bestCond)
			newRes = newRes->content.trueBranch;
		if (trueSucc.count(newGuard) && trueSucc[newGuard] != newRes) {
			return NULL;
		} else {
			trueSucc[newGuard] = newRes;
		}
	}
	intbdd *trueB = intbdd::from_enabling(scope, trueSucc, memo);
	if (trueB == NULL) {
		it->second = NULL;
	} else {
		enablingTableT falseSucc;
		for (auto it2 = inp.begin(); it2 != inp.end(); it2++) {
			bbdd *newGuard = it2->first;
			intbdd *newRes = it2->second;
			if (!newGuard->isLeaf &&
			    newGuard->content.condition == bestCond)
				newGuard = newGuard->content.falseBranch;
			if (!newRes->isLeaf &&
			    newRes->content.condition == bestCond)
				newRes = newRes->content.falseBranch;
			if (falseSucc.count(newGuard) && falseSucc[newGuard] != newRes) {
				return NULL;
			} else {
				falseSucc[newGuard] = newRes;
			}
		}
		intbdd *falseB = intbdd::from_enabling(scope, falseSucc, memo);
		if (falseB == NULL) {
			it->second = NULL;
		} else if (trueB == falseB || trueB == INTBDD_DONT_CARE) {
			it->second = falseB;
		} else if (falseB == INTBDD_DONT_CARE) {
			it->second = trueB;
		} else {
			it->second = scope->makeInternal(bestCond, trueB, falseB);
		}
	}

	return it->second;
}
intbdd *
intbdd::from_enabling(scope *scope, const enablingTableT &inp)
{
	std::map<enablingTableT, intbdd *> memo;
	intbdd *res = from_enabling(scope, inp, memo);
	if (res == INTBDD_DONT_CARE)
		return scope->cnst(0);
	else
		return res;
}
#undef INTBDD_DONT_CARE

intbdd *
intbdd::assume(scope *scope,
	       intbdd *a,
	       bbdd *b,
	       std::map<std::pair<intbdd *, bbdd *>, intbdd *> &memo)
{
	if (a->isLeaf)
		return a;
	if (b->isLeaf) {
		if (b->content.leaf)
			return a;
		else
			return NULL;
	}

	auto it_did_insert = memo.insert(
		std::pair<std::pair<intbdd *, bbdd *>, intbdd *>(
			std::pair<intbdd *, bbdd *>(a, b),
			(intbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;
	IRExpr *cond;
	if (scope->ordering->before(a->content.condition, b->content.condition))
		cond = a->content.condition;
	else
		cond = b->content.condition;
	intbdd *trueB;
	intbdd *falseB;
	if (cond == a->content.condition) {
		if (cond == b->content.condition) {
			trueB = intbdd::assume(scope,
					       a->content.trueBranch,
					       b->content.trueBranch,
					       memo);
			falseB = intbdd::assume(scope,
						a->content.falseBranch,
						b->content.falseBranch,
						memo);
		} else {
			trueB = intbdd::assume(scope,
					       a->content.trueBranch,
					       b,
					       memo);
			falseB = intbdd::assume(scope,
						a->content.falseBranch,
						b,
						memo);
		}
	} else {
		assert(cond == b->content.condition);
		trueB = intbdd::assume(scope,
				       a,
				       b->content.trueBranch,
				       memo);
		falseB = intbdd::assume(scope,
					a,
					b->content.falseBranch,
					memo);
	}
	if (!trueB || trueB == falseB)
		return falseB;
	if (!falseB)
		return trueB;
	intbdd *res = scope->makeInternal(cond, trueB, falseB);
	it->second = res;
	return res;
}
			

intbdd *
intbdd::assume(scope *scope,
	       intbdd *thing,
	       bbdd *assumption)
{
	std::map<std::pair<intbdd *, bbdd *>, intbdd *> memo;
	intbdd *res = assume(scope, thing, assumption, memo);
	if (res == NULL)
		return scope->cnst(0);
	else
		return res;
}

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
