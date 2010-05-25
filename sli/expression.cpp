#include "sli.h"

Expression *Expression::heads[Expression::nr_heads];
unsigned Expression::tot_outstanding;
unsigned Expression::chain_lengths[Expression::nr_heads];
unsigned long Expression::eq_calls[Expression::nr_heads];
unsigned Expression::nr_interned;

static unsigned calls_to_intern;
static unsigned intern_hits;
static unsigned long nr_intern_steps;

void Expression::dump_eq_calls_table()
{
	FILE *f;
	f = fopen("eqcalls.inf", "w");
	for (unsigned x = 0; x < nr_heads; x++)
		fprintf(f, "%d\t%ld\n", x, eq_calls[x]);
	fclose(f);
}

Expression *Expression::intern(Expression *e)
{
	calls_to_intern++;
	e->hashval = e->_hash();
	unsigned h = e->hashval % nr_heads;
	Expression *cursor;
	tot_outstanding++;
	for (cursor = heads[h]; cursor && !cursor->isEqual(e); cursor = cursor->next) {
		nr_intern_steps++;
		eq_calls[h]++;
	}
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
                if (associates) {					\
			if (nme *ll = dynamic_cast<nme *>(l))		\
				return nme::get(ll->l, nme::get(ll->r, r)); \
		}							\
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

mk_binop(bitwisexor, ^, true);
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

mk_op_allocator(plus);							
Expression *plus::get(Expression *l, Expression *r)			
{									
	unsigned long lc, rc;						
	bool lIsConstant = l->isConstant(&lc);
	bool rIsConstant = r->isConstant(&rc);
	if (lIsConstant) {
		if (lc == 0)
			return r;
		if (rIsConstant)
			return ConstExpression::get(lc + rc);			
	} else if (rIsConstant && rc == 0)
		return l;

	/* We rewrite (a & Y) + (b & Z) to (a & Y) | (b & Z) whenever
	   possible, which is pretty much when Y and Z don't
	   intersect. */
	{
		bitwiseand *land = dynamic_cast<bitwiseand *>(l);
		bitwiseand *rand = dynamic_cast<bitwiseand *>(r);
		if (land && rand) {
			Expression *c = bitwiseand::get(land->r, rand->r);
			unsigned long cc;
			if (c->isConstant(&cc) && cc == 0)
				return bitwiseor::get(land, rand);
		}
	}
	
	if (plus *ll = dynamic_cast<plus *>(l))				
		return plus::get(ll->l, plus::get(ll->r, r));		
	plus *work = new (allocator.alloc()) plus();			
	work->l = l;							
	work->r = r;							
	return intern(work);						
}

/* C's normal semantics for shifts by negative amounts and by amounts
   greater than the width of the type are broken.  Use sane
   alternatives. */
static unsigned long sane_lshift(unsigned long r, long cntr);
static unsigned long
sane_rshift(unsigned long r, long cntr)
{
	if (cntr < 0)
		return sane_lshift(r, -cntr);
	else if (cntr >= 64)
		return 0;
	else
		return r >> cntr;
}
static unsigned long
sane_lshift(unsigned long r, long cntr)
{
	if (cntr < 0)
		return sane_rshift(r, -cntr);
	else if (cntr >= 64)
		return 0;
	else
		return r << cntr;
}

mk_op_allocator(lshift);
Expression *lshift::get(Expression *l, Expression *r)			
{									
	unsigned long lc, rc;	
	bool rIsConstant;

	rIsConstant = r->isConstant(&rc);
	if (l->isConstant(&lc)) {
		if (lc == 0)
			return l;
		if (rIsConstant)
			return ConstExpression::get(sane_lshift(lc, rc));
	} else if (rIsConstant && rc == 0)
		return l;

	/* We rewrite ((x >> A) & B) << C into
	   (x >> (A - C)) & (B << C) if A, B, and C
	   are all constants. */
	if (rIsConstant) {
		bitwiseand *land = dynamic_cast<bitwiseand *>(l);
		rshift *lrshift;
		Expression *x;
		unsigned long A, B, C = rc;
		if (land) {
			lrshift = dynamic_cast<rshift *>(land->l);
			x = lrshift->l;
			if (lrshift &&
			    lrshift->r->isConstant(&A) &&
			    land->r->isConstant(&B)) {
				return bitwiseand::get(
					rshift::get(x, ConstExpression::get(A - C)),
					ConstExpression::get(sane_lshift(B, C)));
			}
		}
	}
	lshift *work = new (allocator.alloc()) lshift();			
	work->l = l;							
	work->r = r;							
	return intern(work);						
}

mk_op_allocator(rshift);
Expression *rshift::get(Expression *l, Expression *r)			
{									
	unsigned long lc, rc;	
	bool rIsConstant;

	rIsConstant = r->isConstant(&rc);
	if (l->isConstant(&lc)) {
		if (lc == 0)
			return l;
		if (rIsConstant)
			return ConstExpression::get(sane_rshift(lc, rc));
	} else if (rIsConstant && rc == 0)
		return l;
	rshift *work = new (allocator.alloc()) rshift();			
	work->l = l;							
	work->r = r;							
	return intern(work);						
}

mk_op_allocator(bitwiseor);
Expression *bitwiseor::get(Expression *l, Expression *r)			
{									
	unsigned long lc, rc;						
	bool lIsConstant = l->isConstant(&lc);
	bool rIsConstant = r->isConstant(&rc);
	if (lIsConstant) {
		if (lc == 0)
			return r;
		if (rIsConstant)
			return ConstExpression::get(lc | rc);
	} else if (rIsConstant && rc == 0)
		return l;

	/* Rewrite (x & Y) | (x & Z) to x & (Y | Z) */
	{
		bitwiseand *land = dynamic_cast<bitwiseand *>(l);
		bitwiseand *rand = dynamic_cast<bitwiseand *>(r);
		if (land && rand && land->l == rand->l)
			return bitwiseand::get(land->l,
					       bitwiseor::get(land->r,
							      rand->r));
	}
	
	if (bitwiseor *ll = dynamic_cast<bitwiseor *>(l))
		return bitwiseor::get(ll->l, bitwiseor::get(ll->r, r));		
	bitwiseor *work = new (allocator.alloc()) bitwiseor();
	work->l = l;							
	work->r = r;							
	return intern(work);						
}

mk_op_allocator(bitwiseand);
Expression *bitwiseand::get(Expression *l, Expression *r)			
{									
	unsigned long lc, rc;						
	bool lIsConstant = l->isConstant(&lc);
	bool rIsConstant = r->isConstant(&rc);
	if (lIsConstant) {
		if (lc == 0)
			return l;
		if (lc == 0xfffffffffffffffful)
			return r;
		if (rIsConstant)
			return ConstExpression::get(lc & rc);
	} else if (rIsConstant) {
		if (rc == 0)
			return r;
		if (rc == 0xfffffffffffffffful)
			return l;
	}

	if (bitwiseand *ll = dynamic_cast<bitwiseand *>(l))
		return bitwiseand::get(ll->l, bitwiseand::get(ll->r, r));		
	bitwiseand *work = new (allocator.alloc()) bitwiseand();
	work->l = l;
	work->r = r;
	return intern(work);						
}
