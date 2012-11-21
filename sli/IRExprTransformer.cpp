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
IRExprTransformer::transform_bbdd(bbdd::scope *scope, bbdd *what, bool *done_something)
{
	if (what->isLeaf)
		return what;
	bool b = false;
	IRExpr *e = doit(what->content.condition, &b);
	bbdd *t = transform_bbdd(scope, what->content.trueBranch, &b);
	bbdd *f = transform_bbdd(scope, what->content.falseBranch, &b);
	if (!b)
		return what;
	*done_something = true;
	return bbdd::ifelse(
		scope,
		bbdd::var(scope, e),
		t,
		f);
}

smrbdd *
IRExprTransformer::transform_smrbdd(bbdd::scope *bscope, smrbdd::scope *scope, smrbdd *what, bool *done_something)
{
	if (what->isLeaf)
		return what;
	bool b = false;
	IRExpr *e = doit(what->content.condition, &b);
	smrbdd *t = transform_smrbdd(bscope, scope, what->content.trueBranch, &b);
	smrbdd *f = transform_smrbdd(bscope, scope, what->content.falseBranch, &b);
	if (!b)
		return what;
	*done_something = true;
	return smrbdd::ifelse(
		scope,
		bbdd::var(bscope, e),
		t,
		f);
}

exprbdd *
IRExprTransformer::transform_exprbdd(bbdd::scope *bscope, exprbdd::scope *scope, exprbdd *what, bool *done_something)
{
	if (what->isLeaf) {
		IRExpr *newLeaf = doit(what->content.leaf, done_something);
		if (what->content.leaf == newLeaf)
			return what;
		return exprbdd::var(scope, bscope, newLeaf);
	}
	bool b = false;
	IRExpr *e = doit(what->content.condition, &b);
	exprbdd *t = transform_exprbdd(bscope, scope, what->content.trueBranch, &b);
	exprbdd *f = transform_exprbdd(bscope, scope, what->content.falseBranch, &b);
	if (!b)
		return what;
	*done_something = true;
	return exprbdd::ifelse(
		scope,
		bbdd::var(bscope, e),
		t,
		f);
}
