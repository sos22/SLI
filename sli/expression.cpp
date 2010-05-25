#include "sli.h"

template<> abstract_interpret_value
load_ait(abstract_interpret_value val, abstract_interpret_value addr, ReplayTimestamp when)
{
	abstract_interpret_value res;
	res.v = val.v;
	res.origin = LoadExpression::get(when, val.origin, addr.origin);
	return res;
}

template<> unsigned long
load_ait(unsigned long x, unsigned long addr, ReplayTimestamp when)
{
	return x;
}

VexAllocTypeWrapper<ConstExpression, visit_object<ConstExpression>, destruct_object<ConstExpression> > ConstExpression::allocator;
VexAllocTypeWrapper<ImportExpression, visit_object<ImportExpression>, destruct_object<ImportExpression> > ImportExpression::allocator;
VexAllocTypeWrapper<LoadExpression> LoadExpression::allocator;

Expression *ternarycondition::get(Expression *cond, Expression *t, Expression *f)
{
	unsigned long cv;
	if (cond->isConstant(&cv)) {
		if (cv)
			return t;
		else
			return f;
	}
	ternarycondition *work = new (allocator.alloc()) ternarycondition();
	work->cond = cond;
	work->t = t;
	work->f = f;
	return work;
}

#define mk_op_allocator(op)						\
	VexAllocTypeWrapper<op, visit_object<op>, destruct_object<op> > op::allocator

#define mk_binop(nme, op, associates)					\
	mk_op_allocator(nme);						\
	Expression *nme::get(Expression *l, Expression *r)		\
	{								\
	        unsigned long lc, rc;				        \
		if (l->isConstant(&lc) && r->isConstant(&rc))		\
			return ConstExpression::get(lc op rc);		\
		if (nme *ll = dynamic_cast<nme *>(l))			\
			return nme::get(ll->l, nme::get(ll->r, r));	\
		nme *work = new (allocator.alloc()) nme();		\
		work->l = l;						\
		work->r = r;						\
		return work;						\
	}

#define mk_unop(nme, op)						\
	mk_op_allocator(nme);						\
	Expression *nme::get(Expression *l)				\
	{								\
	        unsigned long lc;				        \
		if (l->isConstant(&lc))					\
			return ConstExpression::get(op lc);		\
		nme *work = new (allocator.alloc()) nme();		\
		work->l = l;						\
		return work;						\
	}

Expression *subtract::get(Expression *l, Expression *r)
{
	return plus::get(l, unaryminus::get(r));
}

mk_binop(lshift, <<, false);
mk_binop(rshift, >>, false);
mk_binop(bitwiseand, &, true);
mk_binop(bitwiseor, |, true);
mk_binop(bitwisexor, ^, true);
mk_binop(plus, +, true);
mk_binop(times, *, false);
mk_binop(divide, /, false);
mk_binop(modulo, %, false);
mk_binop(greaterthanequals, >=, false);
mk_binop(greaterthan, >, false);
mk_binop(lessthanequals, <=, false);
mk_binop(lessthan, <, false);
mk_binop(equals, ==, false);
mk_binop(notequals, !=, false);
mk_binop(logicalor, ||, true);
mk_binop(logicaland, &&, true);

mk_unop(logicalnot, !);
mk_unop(bitwisenot, ~);
mk_unop(unaryminus, -);

mk_op_allocator(ternarycondition);
