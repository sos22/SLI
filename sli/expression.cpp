#include "sli.h"

VexAllocTypeWrapper<ConstExpression, visit_object<ConstExpression>, destruct_object<ConstExpression> > ConstExpression::allocator;
VexAllocTypeWrapper<ImportExpression, visit_object<ImportExpression>, destruct_object<ImportExpression> > ImportExpression::allocator;

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

#define mk_binop(nme, op)						\
	mk_op_allocator(nme);						\
	Expression *nme::get(Expression *l, Expression *r)		\
	{								\
	        unsigned long lc, rc;				        \
		if (l->isConstant(&lc) && r->isConstant(&rc))		\
			return ConstExpression::get(lc op rc);		\
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

mk_binop(lshift, <<);
mk_binop(rshift, >>);
mk_binop(bitwiseand, &);
mk_binop(bitwiseor, |);
mk_binop(bitwisexor, ^);
mk_binop(plus, +);
mk_binop(subtract, -);
mk_binop(times, *);
mk_binop(divide, /);
mk_binop(modulo, %);
mk_binop(greaterthanequals, >=);
mk_binop(greaterthan, >);
mk_binop(lessthanequals, <=);
mk_binop(lessthan, <);
mk_binop(equals, ==);
mk_binop(notequals, !=);
mk_binop(logicalor, ||);
mk_binop(logicaland, &&);

mk_unop(logicalnot, !);
mk_unop(bitwisenot, ~);

mk_op_allocator(ternarycondition);
