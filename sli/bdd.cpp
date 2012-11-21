#include "sli.h"
#include "bdd.hpp"
#include "simplify_irexpr.hpp"

/* Convert @what so that it uses muxes wherever possible (i.e. no
   And1, Or1, or Not1 operators) and so that all muxes are at top
   level. */
static IRExpr *
muxify(IRExpr *what)
{
	switch (what->tag) {
	case Iex_Get:
		return what;
	case Iex_GetI:
		abort();
	case Iex_Qop: {
		IRExprQop *w = (IRExprQop *)what;
		IRExpr *a = muxify(w->arg1);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Qop(
					       w->op,
					       ((IRExprMux0X *)a)->expr0,
					       w->arg2,
					       w->arg3,
					       w->arg4)),
				muxify(IRExpr_Qop(
					       w->op,
					       ((IRExprMux0X *)a)->exprX,
					       w->arg2,
					       w->arg3,
					       w->arg4)));
		IRExpr *b = muxify(w->arg2);
		if (b->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)b)->cond,
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->expr0,
					       w->arg3,
					       w->arg4)),
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->exprX,
					       w->arg3,
					       w->arg4)));
		IRExpr *c = muxify(w->arg3);
		if (c->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)c)->cond,
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       b,
					       ((IRExprMux0X *)c)->expr0,
					       w->arg4)),
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       b,
					       ((IRExprMux0X *)c)->exprX,
					       w->arg4)));
		IRExpr *d = muxify(w->arg4);
		if (d->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)c)->cond,
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       b,
					       c,
					       ((IRExprMux0X *)d)->expr0)),
				muxify(IRExpr_Qop(
					       w->op,
					       a,
					       b,
					       c,
					       ((IRExprMux0X *)d)->exprX)));
		assert(a == w->arg1 && b == w->arg2 && c == w->arg3 && d == w->arg4);
		return what;
	}
	case Iex_Triop: {
		IRExprTriop *w = (IRExprTriop *)what;
		IRExpr *a = muxify(w->arg1);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Triop(
					       w->op,
					       ((IRExprMux0X *)a)->expr0,
					       w->arg2,
					       w->arg3)),
				muxify(IRExpr_Triop(
					       w->op,
					       ((IRExprMux0X *)a)->exprX,
					       w->arg2,
					       w->arg3)));
		IRExpr *b = muxify(w->arg2);
		if (b->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)b)->cond,
				muxify(IRExpr_Triop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->expr0,
					       w->arg3)),
				muxify(IRExpr_Triop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->exprX,
					       w->arg3)));
		IRExpr *c = muxify(w->arg3);
		if (c->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)c)->cond,
				muxify(IRExpr_Triop(
					       w->op,
					       a,
					       b,
					       ((IRExprMux0X *)c)->expr0)),
				muxify(IRExpr_Triop(
					       w->op,
					       a,
					       b,
					       ((IRExprMux0X *)c)->exprX)));
		if (a == w->arg1 && b == w->arg2 && c == w->arg3)
			return what;
		else
			return IRExpr_Triop(w->op, a, b, c);
	}
	case Iex_Binop: {
		IRExprBinop *w = (IRExprBinop *)what;
		IRExpr *a = muxify(w->arg1);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Binop(
					       w->op,
					       ((IRExprMux0X *)a)->expr0,
					       w->arg2)),
				muxify(IRExpr_Binop(
					       w->op,
					       ((IRExprMux0X *)a)->exprX,
					       w->arg2)));
		IRExpr *b = muxify(w->arg2);
		if (b->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)b)->cond,
				muxify(IRExpr_Binop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->expr0)),
				muxify(IRExpr_Binop(
					       w->op,
					       a,
					       ((IRExprMux0X *)b)->exprX)));
		assert(a == w->arg1 && b == w->arg2);
		return what;
	}
	case Iex_Unop: {
		IRExprUnop *w = (IRExprUnop *)what;
		IRExpr *a = muxify(w->arg);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Unop(
					       w->op,
					       ((IRExprMux0X *)a)->expr0)),
				muxify(IRExpr_Unop(
					       w->op,
					       ((IRExprMux0X *)a)->exprX)));
		if (w->op == Iop_Not1)
			return IRExpr_Mux0X(
				a,
				IRExpr_Const_U1(true),
				IRExpr_Const_U1(false));
		assert(a == w->arg);
		return w;
	}
	case Iex_Const:
		return what;
	case Iex_Mux0X: {
		IRExprMux0X *m = (IRExprMux0X *)what;
		IRExpr *cond = muxify(m->cond);
		IRExpr *expr0 = muxify(m->expr0);
		IRExpr *exprX = muxify(m->exprX);
		if (cond == m->cond && expr0 == m->expr0 && exprX == m->exprX)
			return what;
		else
			return IRExpr_Mux0X(cond, expr0, exprX);
	}
	case Iex_CCall: {
		IRExprCCall *cee = (IRExprCCall *)what;
		IRExpr *a;
		int i;
		for (i = 0; cee->args[i]; i++) {
			a = muxify(cee->args[i]);
			if (a->tag == Iex_Mux0X)
				break;
			assert(a == cee->args[i]);
		}
		if (!cee->args[i])
			return what;
		int nr_args;
		for (nr_args = i; cee->args[nr_args]; nr_args++)
			;
		IRExpr **newArgs0 = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_args + 1);
		memcpy(newArgs0, cee->args, sizeof(cee->args[0]) * (nr_args + 1));
		newArgs0[i] = ((IRExprMux0X *)a)->expr0;
		IRExpr **newArgsX = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_args + 1);
		memcpy(newArgsX, cee->args, sizeof(cee->args[0]) * (nr_args + 1));
		newArgsX[i] = ((IRExprMux0X *)a)->exprX;
		return muxify(
			IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				IRExpr_CCall(cee->cee, cee->retty, newArgs0),
				IRExpr_CCall(cee->cee, cee->retty, newArgsX)));
	}
	case Iex_Associative: {
		IRExprAssociative *iea = (IRExprAssociative *)what;
		if (iea->op == Iop_And1) {
			IRExpr *acc = IRExpr_Const_U1(true);
			IRExpr *fls = IRExpr_Const_U1(false);
			for (int i = 0; i < iea->nr_arguments; i++)
				acc = IRExpr_Mux0X(
					muxify(iea->contents[i]),
					fls,
					acc);
			return acc;
		} else if (iea->op == Iop_Or1) {
			IRExpr *acc = IRExpr_Const_U1(false);
			IRExpr *tru = IRExpr_Const_U1(true);
			for (int i = 0; i < iea->nr_arguments; i++)
				acc = IRExpr_Mux0X(
					muxify(iea->contents[i]),
					acc,
					tru);
			return acc;
		}

		IRExpr *a;
		int i;
		for (i = 0; i < iea->nr_arguments; i++) {
			a = muxify(iea->contents[i]);
			if (a->tag == Iex_Mux0X)
				break;
			assert(a == iea->contents[i]);
		}
		if (i == iea->nr_arguments)
			return what;
		IRExpr **newArgs0 = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, iea->nr_arguments);
		memcpy(newArgs0, iea->contents, sizeof(iea->contents[0]) * iea->nr_arguments);
		newArgs0[i] = ((IRExprMux0X *)a)->expr0;
		IRExpr **newArgsX = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, iea->nr_arguments);
		memcpy(newArgsX, iea->contents, sizeof(iea->contents[0]) * iea->nr_arguments);
		newArgsX[i] = ((IRExprMux0X *)a)->exprX;
		IRExprAssociative *exp0 = new IRExprAssociative();
		exp0->op = iea->op;
		exp0->nr_arguments = iea->nr_arguments;
		exp0->nr_arguments_allocated = iea->nr_arguments;
		exp0->contents = newArgs0;
		IRExprAssociative *expX = new IRExprAssociative();
		expX->op = iea->op;
		expX->nr_arguments = iea->nr_arguments;
		expX->nr_arguments_allocated = iea->nr_arguments;
		expX->contents = newArgsX;
		return muxify(
			IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				exp0,
				expX));
	}
		
	case Iex_Load: {
		IRExprLoad *l = (IRExprLoad *)what;
		IRExpr *a = muxify(l->addr);
		if (a->tag == Iex_Mux0X)
			return IRExpr_Mux0X(
				((IRExprMux0X *)a)->cond,
				muxify(IRExpr_Load(
					       l->ty,
					       ((IRExprMux0X *)a)->expr0)),
				muxify(IRExpr_Load(
					       l->ty,
					       ((IRExprMux0X *)a)->exprX)));
		assert(a == l->addr);
		return what;
	}
	case Iex_HappensBefore:
		return what;
	case Iex_FreeVariable:
		return what;
	case Iex_EntryPoint:
		return what;
	case Iex_ControlFlow:
		return what;
	}
	abort();
}

bbdd *
bbdd::_var(scope *scope, IRExpr *a)
{
	if (a->tag == Iex_Mux0X)
		return ifelse(
			scope,
			_var(scope, ((IRExprMux0X *)a)->cond),
			_var(scope, ((IRExprMux0X *)a)->exprX),
			_var(scope, ((IRExprMux0X *)a)->expr0));
	else
		return scope->makeInternal(a,
					   scope->cnst(true),
					   scope->cnst(false));
}
bbdd *
bbdd::var(scope *scope, IRExpr *a)
{
	return _var(scope, muxify(a));
}

template <typename constT, typename subtreeT> template <typename scopeT, typename zipInternalT>
subtreeT *
_bdd<constT, subtreeT>::zip(scopeT *scope,
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
template <typename constT, typename subtreeT> template <typename scopeT> subtreeT *
_bdd<constT, subtreeT>::assume(scopeT *scope, subtreeT *thing, bbdd *assumption)
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
			nextRanking--;
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

#define INTBDD_DONT_CARE ((subtreeT *)0x1)
template <typename subtreeT, typename scopeT>
class from_enabling_internal {
public:
	bool failed;
	typename subtreeT::enablingTableT table;
	from_enabling_internal(const typename subtreeT::enablingTableT &_table)
		: failed(false), table(_table)
	{}
	from_enabling_internal(bool _failed)
		: failed(_failed)
	{}
	bool isLeaf() const {
		return failed || table.size() <= 1;
	}
	subtreeT *leafzip() const {
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
			subtreeT *newRes = it->second;
			if (!newGuard->isLeaf &&
			    ordering->equal(newGuard->content.condition, cond))
				newGuard = newGuard->content.trueBranch;
			if (newGuard->isLeaf && !newGuard->content.leaf)
				continue;
			if (!newRes->isLeaf &&
			    ordering->equal(newRes->content.condition, cond))
				newRes = newRes->content.trueBranch;
			auto it2_did_insert = res.table.insert(std::pair<bbdd *, subtreeT *>(newGuard, newRes));
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
			subtreeT *newRes = it->second;
			if (!newGuard->isLeaf &&
			    ordering->equal(newGuard->content.condition, cond))
				newGuard = newGuard->content.falseBranch;
			if (newGuard->isLeaf && !newGuard->content.leaf)
				continue;
			if (!newRes->isLeaf &&
			    ordering->equal(newRes->content.condition, cond))
				newRes = newRes->content.falseBranch;
			auto it2_did_insert = res.table.insert(std::pair<bbdd *, subtreeT *>(newGuard, newRes));
			if (it2_did_insert.first->second != newRes)
				return from_enabling_internal(true);
		}
		return res;
	}
	subtreeT *mkNode(scopeT *scope, IRExpr *a, subtreeT *t, subtreeT *f)
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

template <typename constT, typename subtreeT> template <typename scopeT>
subtreeT *
_bdd<constT, subtreeT>::from_enabling(scopeT *scope, const enablingTableT &inp, subtreeT *defaultValue)
{
	subtreeT *res = zip(scope, from_enabling_internal<subtreeT, scopeT>(inp));
	if (res == INTBDD_DONT_CARE)
		return defaultValue;
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

template <typename leafT, typename subtreeT> template <typename scopeT,
						       subtreeT *(*parseLeaf)(scopeT *, const char *, const char **)> subtreeT *
_bdd<leafT, subtreeT>::_parse(scopeT *scope,
			      const char *str,
			      const char **suffix,
			      std::map<int, subtreeT *> &labels)
{
	int label = -1;
	/* Discard whitespace */
	parseThisChar(' ', str, &str);

	/* Deal with references to elsewhere in the tree. */
	if (parseThisString("[->", str, &str)) {
		if (!parseDecimalInt(&label, str, &str) ||
		    !parseThisString("]\n", str, suffix) ||
		    !labels.count(label))
			return NULL;
		return labels[label];
	}

	/* Does it have a label? */
	if (parseThisChar('[', str, &str)) {
		/* Yes */
		parseThisChar(' ', str, &str);
		if (!parseDecimalInt(&label, str, &str) ||
		    !parseThisChar(']', str, &str) ||
		    labels.count(label))
			return NULL;
		parseThisChar(' ', str, &str);
	}
	subtreeT *res;
	if (parseThisString("Leaf: ", str, &str)) {
		res = parseLeaf(scope, str, &str);
		if (!res || !parseThisChar('\n', str, suffix))
			return NULL;
	} else if (parseThisString("Mux: ", str, &str)) {
		IRExpr *a;
		if (!parseIRExpr(&a, str, &str))
			return NULL;
		subtreeT *t = _parse<scopeT, parseLeaf>(scope, str, &str, labels);
		if (!t)
			return NULL;
		subtreeT *f = _parse<scopeT, parseLeaf>(scope, str, suffix, labels);
		if (!f)
			return NULL;
		res = scope->makeInternal(a, t, f);
	} else {
		return NULL;
	}
	if (label != -1)
		labels[label] = res;
	return res;
}

template <typename leafT, typename subtreeT> template <typename scopeT,
						       subtreeT *(*parseLeaf)(scopeT *scope, const char *, const char **)> bool
_bdd<leafT, subtreeT>::_parse(scopeT *scope, subtreeT **root, const char *str, const char **suffix)
{
	std::map<int, subtreeT *> labels;
	subtreeT *res = _parse<scopeT, parseLeaf>(scope, str, suffix, labels);
	if (res) {
		*root = res;
		return true;
	} else {
		return false;
	}
}

template <typename t> t *
bdd_scope<t>::makeInternal(IRExpr *cond, t *a, t *b)
{
	assert(a);
	assert(b);
	assert(a->isLeaf || ordering->before(cond, a->content.condition));
	assert(b->isLeaf || ordering->before(cond, b->content.condition));
	if (a == b)
		return a;
	if (cond->tag == Iex_Const) {
		if ( ((IRExprConst *)cond)->Ico.U1 )
			return a;
		else
			return b;
	}

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

template <typename constT, typename subtreeT> template <IRExpr *mkConst(constT)> IRExpr *
const_bdd<constT, subtreeT>::to_irexpr(subtreeT *what, std::map<subtreeT *, IRExpr *> &memo)
{
	auto it_did_insert = memo.insert(std::pair<subtreeT *, IRExpr *>(what, (IRExpr *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (what->isLeaf) {
			it->second = mkConst(what->content.leaf);
		} else {
			it->second = IRExpr_Mux0X(
				what->content.condition,
				to_irexpr<mkConst>(what->content.falseBranch, memo),
				to_irexpr<mkConst>(what->content.trueBranch, memo));
		}
	} else {
		assert(it->second != NULL);
	}
	return it->second;
}

template <typename constT, typename subtreeT> template <IRExpr *mkConst(constT)> IRExpr *
const_bdd<constT, subtreeT>::to_irexpr(subtreeT *what)
{
	std::map<subtreeT *, IRExpr *> memo;
	return to_irexpr<mkConst>(what, memo);
}

template <typename constT, typename subtreeT> template <typename scopeT> const std::map<constT, bbdd *> &
_bdd<constT, subtreeT>::to_selectors(scopeT *scope,
				     subtreeT *what,
				     std::map<subtreeT *, std::map<constT, bbdd *> > &memo)
{
	auto it_did_insert = memo.insert(std::pair<subtreeT *, std::map<constT, bbdd *> >(what, std::map<constT, bbdd *>()));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		std::map<constT, bbdd *> &res(it->second);
		assert(res.empty());
		if (what->isLeaf) {
			res[what->content.leaf] = scope->cnst(true);
		} else {
			const std::map<constT, bbdd *> &trueB(to_selectors(scope, what->content.trueBranch, memo));
			const std::map<constT, bbdd *> &falseB(to_selectors(scope, what->content.falseBranch, memo));
			auto true_it = trueB.begin();
			auto false_it = falseB.begin();
			bbdd *const_false = scope->cnst(false);
			while (true_it != trueB.end() || false_it != falseB.end()) {
				if (true_it != trueB.end() &&
				    (false_it == falseB.end() || true_it->first < false_it->first)) {
					res[true_it->first] =
						scope->makeInternal(what->content.condition,
								    true_it->second,
								    const_false);
					true_it++;
				} else if (false_it != falseB.end() &&
					   (true_it == trueB.end() || false_it->first < true_it->first)) {
					res[false_it->first] =
						scope->makeInternal(what->content.condition,
								    const_false,
								    false_it->second);
					false_it++;
				} else {
					/* (true_it != trueB.end() || false_it != falseB.end()) &&
					   !(true_it != trueB.end() &&
					    (false_it == falseB.end() || true_it->first < false_it->first)) &&
					   !(false_it != falseB.end() &&
					    (true_it == trueB.end() || false_it->first < true_it->first))
					   =>
					   (true_it != trueB.end() || false_it != falseB.end()) &&
					   (true_it == trueB.end() ||
					    (false_it != falseB.end() && !(true_it->first < false_it->first))) &&
					   (false_it == falseB.end() ||
					    (true_it != trueB.end() && !(false_it->first < true_it->first)))
					   =>
					   (!finished(t) || !finished(f)) &&
					   (finished(t) || (!finished(f) && t >= f)) &&
					   (finished(f) || (!finished(t) && f >= t))
					   =>
					   (!finished(t) &&
					     (finished(t) || (!finished(f) && t >= f)) &&
					     (finished(f) || (!finished(t) && f >= t))) ||
					   (!finished(f) &&
					     (finished(t) || (!finished(f) && t >= f)) &&
					     (finished(f) || (!finished(t) && f >= t)))
					   =>
					   (!finished(t) &&
					     (!finished(f) && t >= f) &&
					     (finished(f) || f >= t)) ||
					   (!finished(f) &&
					     (finished(t) || t >= f) &&
					     (!finished(t) && f >= t))
					   =>
					   (!finished(t) &&
					    !finished(f) &&
					    t >= f &&
					    f >= t) ||
					   (!finished(f) &&
					    t >= f &&
					    !finished(t) &&
					    f >= t)
					   => !finished(t) && !finished(f) && t == f
					*/
					res[false_it->first] =
						scope->makeInternal(what->content.condition,
								    true_it->second,
								    false_it->second);
					true_it++;
					false_it++;
				}
			}
		}
	}
	return it->second;
}

template <typename constT, typename subtreeT> template <typename scopeT> std::map<constT, bbdd *>
_bdd<constT, subtreeT>::to_selectors(scopeT *scope, subtreeT *what)
{
	std::map<subtreeT *, std::map<constT, bbdd *> > memo;
	return to_selectors(scope, what, memo);
}

template <typename subtreeT, typename scopeT> class ifelse_zip_internal {
	bbdd *cond;
	subtreeT *ifTrue;
	subtreeT *ifFalse;
public:
	ifelse_zip_internal(bbdd *_cond, subtreeT *_ifTrue, subtreeT *_ifFalse)
		: cond(_cond), ifTrue(_ifTrue), ifFalse(_ifFalse)
	{}
	bool isLeaf() const {
		return cond->isLeaf || (ifTrue == ifFalse);
	}
	subtreeT *leafzip() const {
		if (cond->isLeaf) {
			if (cond->content.leaf)
				return ifTrue;
			else
				return ifFalse;
		}
		if (ifTrue == ifFalse)
			return ifTrue;
		abort();
	}
	IRExpr *bestCond(bdd_ordering *ordering) const {
		assert(!cond->isLeaf);
		IRExpr *best = cond->content.condition;
		if (!ifTrue->isLeaf && ordering->before(ifTrue->content.condition, best))
			best = ifTrue->content.condition;
		if (!ifFalse->isLeaf && ordering->before(ifFalse->content.condition, best))
			best = ifFalse->content.condition;
		return best;
	}
	ifelse_zip_internal trueSucc(bdd_ordering *ordering, IRExpr *on) const {
		return ifelse_zip_internal(
			ordering->trueBranch(cond, on),
			ordering->trueBranch(ifTrue, on),
			ordering->trueBranch(ifFalse, on));
	}
	ifelse_zip_internal falseSucc(bdd_ordering *ordering, IRExpr *on) const {
		return ifelse_zip_internal(
			ordering->falseBranch(cond, on),
			ordering->falseBranch(ifTrue, on),
			ordering->falseBranch(ifFalse, on));
	}
	subtreeT *mkNode(scopeT *scope, IRExpr *cond, subtreeT *trueB, subtreeT *falseB) const {
		return scope->makeInternal(cond, trueB, falseB);
	}
	bool operator<(const ifelse_zip_internal &o) const {
		if (cond < o.cond)
			return true;
		if (cond > o.cond)
			return false;
		if (ifTrue < o.ifTrue)
			return true;
		if (ifTrue > o.ifTrue)
			return false;
		return ifFalse < o.ifFalse;
	}
};

template <typename constT, typename subtreeT> template <typename scopeT> subtreeT *
_bdd<constT, subtreeT>::ifelse(scopeT *scope,
				    bbdd *cond,
				    subtreeT *ifTrue,
				    subtreeT *ifFalse)
{
	return zip(scope, ifelse_zip_internal<subtreeT, scopeT>(cond, ifTrue, ifFalse));
}

void
bdd_ordering::prettyPrint(FILE *f) const
{
	fprintf(f, "Variable rankings:\n");
	for (auto it = variableRankings.begin();
	     it != variableRankings.end();
	     it++) {
		fprintf(f, "\t");
		ppIRExpr(it->first, f);
		fprintf(f, "\t -> \t%ld\n", it->second);
	}
}

bool
bdd_ordering::parse(const char *buf, const char **end)
{
	if (!parseThisString("Variable rankings:\n", buf, &buf))
		return false;
	variableRankings.clear();
	while (1) {
		IRExpr *key;
		long rank;
		if (!parseIRExpr(&key, buf, &buf) ||
		    !parseThisString("\t->\t", buf, &buf) ||
		    !parseDecimalLong(&rank, buf, &buf) ||
		    !parseThisChar('\n', buf, &buf))
			break;
		variableRankings[key] = rank;
	}
	*end = buf;
	return true;
}

void
exprbdd::sanity_check(bdd_ordering *ordering) const
{
	std::set<const IRExpr *> terminals;
	std::set<const exprbdd *> visited;
	std::vector<const exprbdd *> q;
	q.push_back(this);
	IRType ty = Ity_INVALID;
	while (!q.empty()) {
		const exprbdd *e = q.back();
		q.pop_back();
		if (!visited.insert(e).second)
			continue;
		if (e->isLeaf) {
			assert(e->content.leaf->tag != Iex_Mux0X);
			if (ty == Ity_INVALID)
				ty = e->content.leaf->type();
			else
				assert(ty == e->content.leaf->type());
			assert(ty != Ity_I1 || e->content.leaf->tag == Iex_Const);
		} else {
			assert(e->content.condition->tag != Iex_Mux0X);
			q.push_back(e->content.trueBranch);
			q.push_back(e->content.falseBranch);
		}
	}
	parentT::sanity_check(ordering);
}

exprbdd *
exprbdd::_var(exprbdd::scope *scope, bbdd::scope *bscope, IRExpr *what)
{
	if (what->tag == Iex_Mux0X)
		return ifelse(
			scope,
			bbdd::var(bscope, ((IRExprMux0X *)what)->cond),
			_var(scope, bscope, ((IRExprMux0X *)what)->exprX),
			_var(scope, bscope, ((IRExprMux0X *)what)->expr0));
	else if (what->type() == Ity_I1)
		return ifelse(
			scope,
			bbdd::var(bscope, what),
			scope->cnst(IRExpr_Const_U1(true)),
			scope->cnst(IRExpr_Const_U1(false)));
	else
		return scope->cnst(what);
}

exprbdd *
exprbdd::var(exprbdd::scope *scope, bbdd::scope *bscope, IRExpr *what)
{
	return _var(scope, bscope, muxify(what));
}

IRExpr *
exprbdd::to_irexpr(exprbdd *what, std::map<exprbdd *, IRExpr *> &memo)
{
	if (what->isLeaf)
		return what->content.leaf;
	auto it_did_insert = memo.insert(std::pair<exprbdd *, IRExpr *>(what, (IRExpr *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = IRExpr_Mux0X(
			what->content.condition,
			to_irexpr(what->content.falseBranch, memo),
			to_irexpr(what->content.trueBranch, memo));
       return it->second;
}

IRExpr *
exprbdd::to_irexpr(exprbdd *what)
{
	std::map<exprbdd *, IRExpr *> memo;
	return to_irexpr(what, memo);
}

exprbdd *
exprbdd::parseLeaf(scope *scope, const char *str, const char **suffix)
{
	IRExpr *a;
	if (parseThisChar('<', str, &str) &&
	    parseIRExpr(&a, str, &str) &&
	    parseThisChar('>', str, suffix))
		return scope->cnst(a);
	else
		return NULL;
}

exprbdd *
exprbdd_scope::cnst(IRExpr *what)
{
	auto it_did_insert = leaves.insert(std::pair<IRExpr *, exprbdd *>(what, (exprbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = new exprbdd(what);
	return it->second;
}

void
exprbdd_scope::runGc(HeapVisitor &hv)
{
	std::map<IRExpr *, exprbdd *> newLeaves;
	for (auto it = leaves.begin(); it != leaves.end(); it++) {
		exprbdd *b = hv.visited(it->second);
		newLeaves[it->first] = b;
	}
	leaves = newLeaves;
}

template void _bdd<bool, bbdd>::prettyPrint(FILE *);
template bbdd *_bdd<bool, bbdd>::assume(const_bdd_scope<bbdd> *, bbdd *, bbdd*);
template IRExpr *const_bdd<bool, bbdd>::to_irexpr<bbdd::mkConst>(bbdd *);
template std::map<bool, bbdd *> _bdd<bool, bbdd>::to_selectors(const_bdd_scope<bbdd> *, bbdd *);
template bbdd *_bdd<bool, bbdd>::ifelse(const_bdd_scope<bbdd> *, bbdd *, bbdd *, bbdd *);

template void _bdd<int, intbdd>::prettyPrint(FILE *);
template bool _bdd<bool, bbdd>::_parse<const_bdd_scope<bbdd>, bbdd::parseBool>(const_bdd_scope<bbdd>*, bbdd **, const char *, const char **);
template intbdd *_bdd<int, intbdd>::assume(const_bdd_scope<intbdd> *, intbdd *, bbdd*);
template intbdd *_bdd<int, intbdd>::from_enabling(const_bdd_scope<intbdd> *, const enablingTableT &, intbdd *);

template void _bdd<StateMachineRes, smrbdd>::prettyPrint(FILE *);
template bool _bdd<StateMachineRes, smrbdd>::_parse<const_bdd_scope<smrbdd>, smrbdd::parseLeaf>(const_bdd_scope<smrbdd>*, smrbdd **, const char *, const char **);
template smrbdd *_bdd<StateMachineRes, smrbdd>::assume(const_bdd_scope<smrbdd> *, smrbdd *, bbdd*);
template smrbdd *_bdd<StateMachineRes, smrbdd>::ifelse(const_bdd_scope<smrbdd> *, bbdd *, smrbdd *, smrbdd *);
template std::map<StateMachineRes, bbdd *> _bdd<StateMachineRes, smrbdd>::to_selectors(const_bdd_scope<bbdd> *, smrbdd *);
template smrbdd *_bdd<StateMachineRes, smrbdd>::from_enabling(const_bdd_scope<smrbdd> *, const enablingTableT &, smrbdd *);

template void _bdd<IRExpr *, exprbdd>::prettyPrint(FILE *);
template bool _bdd<IRExpr *, exprbdd>::_parse<exprbdd_scope, exprbdd::parseLeaf>(exprbdd_scope *, exprbdd **, const char *, const char **);
template exprbdd *_bdd<IRExpr *, exprbdd>::assume(exprbdd_scope *, exprbdd *, bbdd*);
template std::map<IRExpr *, bbdd *> _bdd<IRExpr *, exprbdd>::to_selectors(const_bdd_scope<bbdd> *, exprbdd *);
template exprbdd *_bdd<IRExpr *, exprbdd>::from_enabling(exprbdd_scope *, const enablingTableT &, exprbdd *);
