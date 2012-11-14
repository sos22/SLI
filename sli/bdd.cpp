#include <queue>

#include "sli.h"
#include "bdd.hpp"

VexPtr<bbdd, &ir_heap>
bbdd::trueLeaf(new bbdd(true));
VexPtr<bbdd, &ir_heap>
bbdd::falseLeaf(new bbdd(false));

bbdd *
bbdd::var(bbdd_scope *scope, IRExpr *a)
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
				   cnst(true),
				   cnst(false));
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
bbdd::zip(bbdd_scope *scope,
	  bbdd *a,
	  bbdd *b,
	  bbdd *(*leafzip)(bool a, bool b),
	  std::map<std::pair<bbdd *, bbdd *>, bbdd *> &memo)
{
	if (a == b) {
		if (leafzip == _leafzip_and || leafzip == _leafzip_or)
			return a;
		if (leafzip == _leafzip_assume)
			return cnst(true);
	}
	if (leafzip == _leafzip_and || leafzip == _leafzip_or || leafzip == _leafzip_assume) {
		if (b->isLeaf) {
			if (b->content.leaf) {
				if (leafzip == _leafzip_and || leafzip == _leafzip_assume)
					return a;
				else
					return cnst(true);
			} else {
				if (leafzip == _leafzip_assume)
					return NULL;
				else if (leafzip == _leafzip_and)
					return cnst(false);
				else
					return a;
			}
		}
		if (a->isLeaf) {
			if (a->content.leaf) {
				if (leafzip == _leafzip_and)
					return b;
				else
					return cnst(true);
			} else {
				if (leafzip == _leafzip_and || leafzip == _leafzip_assume)
					return cnst(false);
				else
					return b;
			}
		}
	}

	if (a->isLeaf && b->isLeaf)
		return leafzip(a->content.leaf, b->content.leaf);

	auto it_did_insert = memo.insert(
		std::pair<std::pair<bbdd *, bbdd *>, bbdd *>(
			std::pair<bbdd *, bbdd *>(a, b), (bbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		assert(it->second);
		return it->second;
	}

	IRExpr *bestCond;
	if (a->isLeaf) {
		bestCond = b->content.condition;
	} else if (b->isLeaf) {
		bestCond = a->content.condition;
	} else if (scope->ordering->before(a->content.condition,
					   b->content.condition)) {
		bestCond = a->content.condition;
	} else {
		bestCond = b->content.condition;
	}

	bbdd *trueB;
	bbdd *falseB;
	if (bestCond == a->content.condition) {
		if (bestCond == b->content.condition) {
			trueB = bbdd::zip(scope,
					  a->content.trueBranch,
					  b->content.trueBranch,
					  leafzip,
					  memo);
			falseB = bbdd::zip(scope,
					   a->content.falseBranch,
					   b->content.falseBranch,
					   leafzip,
					   memo);
		} else {
			trueB = bbdd::zip(scope,
					  a->content.trueBranch,
					  b,
					  leafzip,
					  memo);
			falseB = bbdd::zip(scope,
					   a->content.falseBranch,
					   b,
					   leafzip,
					   memo);
		}
	} else {
		trueB = bbdd::zip(scope,
				  a,
				  b->content.trueBranch,
				  leafzip,
				  memo);
		falseB = bbdd::zip(scope,
				   a,
				   b->content.falseBranch,
				   leafzip,
				   memo);
	}

	if (trueB == falseB || !trueB) {
		it->second = falseB;
	} else if (!falseB) {
		it->second = trueB;
	} else {
		it->second = scope->makeInternal(bestCond, trueB, falseB);
	}
	return it->second;
}

bbdd *
bbdd::And(bbdd_scope *scope, bbdd *a, bbdd *b)
{
	return zip(scope, a, b, _leafzip_and);
}
bbdd *
bbdd::Or(bbdd_scope *scope, bbdd *a, bbdd *b)
{
	return zip(scope, a, b, _leafzip_or);
}
bbdd *
bbdd::assume(bbdd_scope *scope, bbdd *thing, bbdd *assumption)
{
	return zip(scope, thing, assumption, _leafzip_assume);
}

bbdd *
bbdd::invert(bbdd_scope *scope, bbdd *a)
{
	if (a->isLeaf)
		return bbdd::cnst(!a->content.leaf);
	else
		return scope->makeInternal(
			a->content.condition,
			bbdd::invert(scope, a->content.trueBranch),
			bbdd::invert(scope, a->content.falseBranch));
}

bdd_ordering::ordT
bdd_ordering::operator()(const IRExpr *a, const IRExpr *b)
{
	if (a < b)
		return lt;
	if (a == b)
		return eq;
	return gt;
}


intbdd *
intbdd_scope::cnst(int k)
{
	auto it_did_insert = content.insert(std::pair<int, intbdd *>(k, (intbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = new intbdd(k);
	return it->second;
}

#define INTBDD_DONT_CARE ((intbdd *)1)

intbdd *
intbdd::from_enabling(intbdd_scope *scope,
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
intbdd::from_enabling(intbdd_scope *scope, const enablingTableT &inp)
{
	std::map<enablingTableT, intbdd *> memo;
	intbdd *res = from_enabling(scope, inp, memo);
	if (res == INTBDD_DONT_CARE)
		return cnst(scope, 0);
	else
		return res;
}
#undef INTBDD_DONT_CARE

intbdd *
intbdd::assume(intbdd_scope *scope,
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
intbdd::assume(intbdd_scope *scope,
	       intbdd *thing,
	       bbdd *assumption)
{
	std::map<std::pair<intbdd *, bbdd *>, intbdd *> memo;
	intbdd *res = assume(scope, thing, assumption, memo);
	if (res == NULL)
		return cnst(scope, 0);
	else
		return res;
}

template <typename leafT, typename subtreeT> void
_bdd<leafT, subtreeT>::prettyPrint(FILE *f)
{
	int nextLabel = 0;
	std::map<thisT *, int> labels;

	/* First, assign labels to anything which occurs multiple
	 * times. */
	{
		std::set<thisT *> seen;
		std::vector<thisT *> pending;
		pending.push_back(this);
		while (!pending.empty()) {
			thisT *l = pending.back();
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
	std::set<thisT *> printed;
	std::vector<std::pair<int, thisT *> > pending;
	pending.push_back(std::pair<int, thisT *>(0, this));
	while (!pending.empty()) {
		int depth = pending.back().first;
		thisT *what = pending.back().second;
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
				pending.push_back(std::pair<int, thisT *>(depth + 1, what->content.falseBranch));
				pending.push_back(std::pair<int, thisT *>(depth + 1, what->content.trueBranch));
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
