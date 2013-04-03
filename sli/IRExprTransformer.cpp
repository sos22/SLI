#include "sli.h"

#include "offline_analysis.hpp"

IRExpr *
IRExprTransformer::transformIRExpr(IRExpr *e)
{
	if (TIMEOUT)
		return e;
	if (aborted)
		return e;
	IRExpr *oldCurrent = _currentIRExpr;
	_currentIRExpr = e;
	IRExpr *res = NULL;
	switch (e->tag) {
#define do_case(n)						\
		case Iex_ ## n:					\
			res = transformIex((IRExpr ## n *)e);	\
			break
		do_case(Get);
		do_case(GetI);
		do_case(Qop);
		do_case(Triop);
		do_case(Binop);
		do_case(Unop);
		do_case(Load);
		do_case(Const);
		do_case(CCall);
		do_case(Mux0X);
		do_case(Associative);
		do_case(HappensBefore);
		do_case(FreeVariable);
		do_case(EntryPoint);
		do_case(ControlFlow);
#undef do_case
	}
	assert(res != NULL);
	_currentIRExpr = oldCurrent;
	return res;
}

IRExpr *
IRExprTransformer::transformIex(IRExprCCall *e)
{
	IRExpr **newArgs;
	int nr_args;
	int x;
	bool t = false;

	for (nr_args = 0; e->args[nr_args]; nr_args++)
		;
	newArgs = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_args + 1);
	for (x = 0; x < nr_args; x++) {
		newArgs[x] = transformIRExpr(e->args[x]);
		t |= newArgs[x] != e->args[x];
	}
	newArgs[nr_args] = NULL;
	if (!t)
		return e;
	else
		return IRExpr_CCall(e->cee,
				    e->retty,
				    newArgs);
}

IRExpr *
IRExprTransformer::transformIex(IRExprAssociative *e)
{
	bool t = false;
	int x = 0;
	IRExpr *newArgs[e->nr_arguments];
	while (x < e->nr_arguments) {
		newArgs[x] = transformIRExpr(e->contents[x]);
		t |= newArgs[x] != e->contents[x];
		x++;
	}
	if (t)
		return IRExpr_Associative_Copy(e->op, e->nr_arguments, newArgs);
	else
		return e;
}

bbdd *
IRExprTransformer::transform_bbdd(bbdd::scope *scope, bbdd *what, std::map<bbdd *, bbdd *> &memo)
{
	if (what->isLeaf())
		return what;
	auto it_did_insert = memo.insert(std::pair<bbdd *, bbdd *>(what, (bbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	bbdd *&res(it->second);
	if (did_insert) {
		IRExpr *e = doit(what->internal().condition);
		bbdd *t = transform_bbdd(scope, what->internal().trueBranch, memo);
		bbdd *f = transform_bbdd(scope, what->internal().falseBranch, memo);
		if (e == what->internal().condition &&
		    t == what->internal().trueBranch &&
		    f == what->internal().falseBranch) {
			res = what;
		} else if (e == what->internal().condition) {
			res = scope->node(what->internal().condition,
					  what->internal().rank,
					  t,
					  f);
		} else {
			res = bbdd::ifelse(
				scope,
				bbdd::var(scope, e, bdd_ordering::rank_hint::Near(what)),
				t,
				f);
		}
	}
	return res;
}

smrbdd *
IRExprTransformer::transform_smrbdd(bbdd::scope *bscope, smrbdd::scope *scope, smrbdd *what, std::map<smrbdd *, smrbdd *> &memo)
{
	if (what->isLeaf())
		return what;
	auto it_did_insert = memo.insert(std::pair<smrbdd *, smrbdd *>(what, (smrbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	smrbdd *&res(it->second);
	if (did_insert) {
		IRExpr *e = doit(what->internal().condition);
		smrbdd *t = transform_smrbdd(bscope, scope, what->internal().trueBranch, memo);
		smrbdd *f = transform_smrbdd(bscope, scope, what->internal().falseBranch, memo);
		if (e == what->internal().condition &&
		    t == what->internal().trueBranch &&
		    f == what->internal().falseBranch) {
			res = what;
		} else if (e == what->internal().condition) {
			res = scope->node(what->internal().condition,
					  what->internal().rank,
					  t,
					  f);
		} else {
			res = smrbdd::ifelse(
				scope,
				bbdd::var(bscope, e, bdd_ordering::rank_hint::Near(what)),
				t,
				f);
		}
	}
	return res;
}

exprbdd *
IRExprTransformer::transform_exprbdd(bbdd::scope *bscope, exprbdd::scope *scope, exprbdd *what,
				     std::map<exprbdd *, exprbdd *> &memo)
{
	auto it_did_insert = memo.insert(std::pair<exprbdd *, exprbdd *>(what, what));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	exprbdd *&res(it->second);
	if (did_insert) {
		if (what->isLeaf()) {
			IRExpr *newLeaf = doit(what->leaf());
			if (what->leaf() != newLeaf)
				res = exprbdd::var(scope, bscope, newLeaf, bdd_ordering::rank_hint::End());
		} else {
			IRExpr *e = doit(what->internal().condition);
			exprbdd *t = transform_exprbdd(bscope, scope, what->internal().trueBranch, memo);
			exprbdd *f = transform_exprbdd(bscope, scope, what->internal().falseBranch, memo);
			if (e != what->internal().condition ||
			    t != what->internal().trueBranch ||
			    f != what->internal().falseBranch) {
				if (e == what->internal().condition) {
					res = scope->node(
						what->internal().condition,
						what->internal().rank,
						t,
						f);
				} else {
					res = exprbdd::ifelse(
						scope,
						bbdd::var(bscope, e, bdd_ordering::rank_hint::Near(what)),
						t,
						f);
				}
			}
		}
	}
	return res;
}
