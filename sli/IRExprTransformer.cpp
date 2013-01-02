#include "sli.h"

#include "offline_analysis.hpp"

IRExpr *
IRExprTransformer::transformIRExpr(IRExpr *e, bool *done_something)
{
	if (TIMEOUT)
		return e;
	if (aborted)
		return NULL;
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
	/* res == e shouldn't really happen, but it's just about
	   possible that expression internment could make it happen in
	   otherwise correct code, so handle it correctly. */
	if (res && res != e) {
		*done_something = true;
	} else {
		res = e;
	}
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
	for (x = 0; x < nr_args; x++)
		newArgs[x] = transformIRExpr(e->args[x], &t);
	newArgs[nr_args] = NULL;
	if (!t)
		return NULL;
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
	IRExpr *newE;
	while (x < e->nr_arguments) {
		newE = transformIRExpr(e->contents[x], &t);
		if (t)
			break;
		x++;
	}
	if (!t)
		return NULL;
	IRExprAssociative *r = (IRExprAssociative *)IRExpr_Associative(e);
	r->contents[x] = newE;
	x++;
	while (x < e->nr_arguments) {
		r->contents[x] = transformIRExpr(e->contents[x], &t);
		x++;
	}
	return r;
}

bbdd *
IRExprTransformer::transform_bbdd(bbdd::scope *scope, bbdd *what, bool *done_something,
				  std::map<bbdd *, bbdd *> &memo)
{
	if (what->isLeaf)
		return what;
	auto it_did_insert = memo.insert(std::pair<bbdd *, bbdd *>(what, (bbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	bbdd *&res(it->second);
	if (did_insert) {
		bool b = false;
		IRExpr *e = doit(what->internal().condition, &b);
		bbdd *t = transform_bbdd(scope, what->internal().trueBranch, &b, memo);
		bbdd *f = transform_bbdd(scope, what->internal().falseBranch, &b, memo);
		if (!b) {
			res = what;
		} else {
			*done_something = true;
			res = bbdd::ifelse(
				scope,
				bbdd::var(scope, e),
				t,
				f);
		}
	}
	return res;
}

smrbdd *
IRExprTransformer::transform_smrbdd(bbdd::scope *bscope, smrbdd::scope *scope, smrbdd *what, bool *done_something,
				    std::map<smrbdd *, smrbdd *> &memo)
{
	if (what->isLeaf)
		return what;
	auto it_did_insert = memo.insert(std::pair<smrbdd *, smrbdd *>(what, (smrbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	smrbdd *&res(it->second);
	if (did_insert) {
		bool b = false;
		IRExpr *e = doit(what->internal().condition, &b);
		smrbdd *t = transform_smrbdd(bscope, scope, what->internal().trueBranch, &b, memo);
		smrbdd *f = transform_smrbdd(bscope, scope, what->internal().falseBranch, &b, memo);
		if (!b) {
			res = what;
		} else {
			*done_something = true;
			res = smrbdd::ifelse(
				scope,
				bbdd::var(bscope, e),
				t,
				f);
		}
	}
	return res;
}

exprbdd *
IRExprTransformer::transform_exprbdd(bbdd::scope *bscope, exprbdd::scope *scope, exprbdd *what,
				     bool *done_something, std::map<exprbdd *, exprbdd *> &memo)
{
	auto it_did_insert = memo.insert(std::pair<exprbdd *, exprbdd *>(what, what));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	exprbdd *&res(it->second);
	if (did_insert) {
		if (what->isLeaf) {
			IRExpr *newLeaf = doit(what->leaf(), done_something);
			if (what->leaf() != newLeaf)
				res = exprbdd::var(scope, bscope, newLeaf);
		} else {
			bool b = false;
			IRExpr *e = doit(what->internal().condition, &b);
			exprbdd *t = transform_exprbdd(bscope, scope, what->internal().trueBranch, &b, memo);
			exprbdd *f = transform_exprbdd(bscope, scope, what->internal().falseBranch, &b, memo);
			if (b)
				*done_something = true;
			if (e != what->internal().condition ||
			    t != what->internal().trueBranch ||
			    f != what->internal().falseBranch) {
				*done_something = true;
				res = exprbdd::ifelse(
					scope,
					bbdd::var(bscope, e),
					t,
					f);
			}
		}
	}
	return res;
}
