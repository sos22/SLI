#include "sli.h"

#include "offline_analysis.hpp"

IRExpr *
IRExprTransformer::transformIRExpr(IRExpr *e, bool *done_something)
{
	if (TIMEOUT)
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
		do_case(FreeVariable);
		do_case(ClientCall);
		do_case(ClientCallFailed);
		do_case(HappensBefore);
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
IRExprTransformer::transformIex(IRExprClientCall *e)
{
	IRExpr **newArgs;
	int nr_args;
	int x;
	bool t = false;

	for (nr_args = 0; e->args[nr_args]; nr_args++)
		;
	newArgs = alloc_irexpr_array(nr_args + 1);
	for (x = 0; x < nr_args; x++)
		newArgs[x] = transformIRExpr(e->args[x], &t);
	newArgs[nr_args] = NULL;
	if (!t)
		return NULL;
	else
		return IRExpr_ClientCall(e->calledRip, e->callSite, newArgs);
}

IRExpr *
IRExprTransformer::transformIex(IRExprAssociative *e)
{
	bool t = false;
	IRExprAssociative *r = (IRExprAssociative *)IRExpr_Associative(e);
	for (int x = 0; x < e->nr_arguments; x++)
		r->contents[x] = transformIRExpr(e->contents[x], &t);
	if (!t)
		return NULL;
	else
		return r;
}
