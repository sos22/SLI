#include "sli.h"

Expression *Expression::heads[Expression::nr_heads];
unsigned Expression::tot_outstanding;
unsigned Expression::chain_lengths[Expression::nr_heads];
unsigned Expression::nr_interned;

static unsigned calls_to_intern;
static unsigned intern_hits;
static unsigned long nr_intern_steps;

Expression *Expression::intern(Expression *e)
{
	calls_to_intern++;
	e->hashval = e->_hash();
	unsigned h = e->hashval % nr_heads;
	Expression *cursor;
	tot_outstanding++;
	for (cursor = heads[h]; cursor && !cursor->isEqual(e); cursor = cursor->next)
		nr_intern_steps++;
	if (cursor) {
		intern_hits++;
		if (cursor != heads[h]) {
			*cursor->pprev = cursor->next;
			if (cursor->next)
				cursor->next->pprev = cursor->pprev;
			if (heads[h])
				heads[h]->pprev = &cursor->next;
			cursor->pprev = &heads[h];
			cursor->next = heads[h];
		}
		e->pprev = NULL;
		e->next = NULL;
		return cursor;
	}
	e->next = heads[h];
	e->pprev = &heads[h];
	if (heads[h])
		heads[h]->pprev = &e->next;
	heads[h] = e;
	chain_lengths[h]++;
	nr_interned++;
	return e;
}

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
	return intern(work);
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
		return intern(work);					\
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
		return intern(work);					\
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
