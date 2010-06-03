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
		cursor->pull_to_front();
		LibVEX_free(e);
		return cursor;
	}
	e->add_to_hash();
	chain_lengths[h]++;
	nr_interned++;
	return e;
}

template<> abstract_interpret_value
load_ait(abstract_interpret_value val, abstract_interpret_value addr, EventTimestamp when,
	 EventTimestamp store, abstract_interpret_value storeAddr)
{
	abstract_interpret_value res;
	res.v = val.v;
	res.origin = LoadExpression::get(when, val.origin, addr.origin, storeAddr.origin, store);
	return res;
}

template<> unsigned long
load_ait(unsigned long x, unsigned long addr, EventTimestamp when, EventTimestamp store,
	 unsigned long storeAddr)
{
	return x;
}

VexAllocTypeWrapper<ConstExpression> ConstExpression::allocator;
VexAllocTypeWrapper<ImportExpression> ImportExpression::allocator;
VexAllocTypeWrapper<LoadExpression> LoadExpression::allocator;

#define mk_op_allocator(op)						\
	VexAllocTypeWrapper<op> op::allocator

#define mk_binop(nme, op, associates, logical)				\
	mk_op_allocator(nme);						\
	bool nme::isLogical() const { return logical; }			\
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
        bool nme::isLogical() const { return false; }			\
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

mk_binop(times, *, false, false);
mk_binop(divide, /, false, false);
mk_binop(modulo, %, false, false);
mk_binop(greaterthanequals, >=, false, true);
mk_binop(greaterthan, >, false, true);
mk_binop(lessthanequals, <=, false, true);
mk_binop(lessthan, <, false, true);
mk_binop(notequals, !=, false, true);

mk_unop(bitwisenot, ~);
mk_unop(unaryminus, -);

Expression *logicalor::get(Expression *l, Expression *r)
{
	return bitsaturate::get(bitwiseor::get(l, r));
}

Expression *logicaland::get(Expression *l, Expression *r)
{
	return bitsaturate::get(bitwiseand::get(l, r));
}

Expression *logicalnot::get(Expression *l)
{
	return bitsaturate::get(bitwisenot::get(bitsaturate::get(l)));
}

mk_op_allocator(bitsaturate);
bool bitsaturate::isLogical() const { return true; }
Expression *bitsaturate::get(Expression *arg)
{
	unsigned long c;
	if (arg->isConstant(&c)) {
		if (c == 0 || c == 1)
			return arg;
		else
			return ConstExpression::get(1);
	}
	if (arg->isLogical())
		return arg;
	bitsaturate *work = new (allocator.alloc()) bitsaturate;
	work->l = arg;
	return work;
}

mk_op_allocator(ternarycondition);
bool ternarycondition::isLogical() const
{
	return t->isLogical() && f->isLogical();
}
Expression *ternarycondition::get(Expression *cond, Expression *t, Expression *f)
{
	unsigned long cv;
	if (t == f)
		return t;
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

mk_op_allocator(plus);							
bool plus::isLogical() const { return false; }
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
bool lshift::isLogical() const { return false; }
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
bool rshift::isLogical() const { return false; }
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
bool bitwiseor::isLogical() const { return l->isLogical() && r->isLogical(); }
Expression *bitwiseor::get(Expression *l, Expression *r)			
{									
	unsigned long lc, rc;						
	bool lIsConstant = l->isConstant(&lc);
	bool rIsConstant = r->isConstant(&rc);
	if (lIsConstant) {
		if (lc == 0)
			return r;
		if (lc == 0xfffffffffffffffful)
			return l;
		if (r->isLogical() && (lc & 1))
			return l;
		if (rIsConstant)
			return ConstExpression::get(lc | rc);
	} else if (rIsConstant) {
		if (rc == 0)
			return l;
		if (rc == 0xfffffffffffffffful)
			return r;
		if (l->isLogical() && (rc & 1))
			return r;
	}

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

mk_op_allocator(bitwisexor);
bool bitwisexor::isLogical() const { return l->isLogical() && r->isLogical(); }
Expression *bitwisexor::get(Expression *l, Expression *r)			
{									
	unsigned long lc, rc;						
	bool lIsConstant = l->isConstant(&lc);
	bool rIsConstant = r->isConstant(&rc);
	if (lIsConstant) {
		if (lc == 0)
			return r;
		if (rIsConstant)
			return ConstExpression::get(lc ^ rc);
	} else if (rIsConstant && rc == 0)
		return l;

	if (bitwiseor *ll = dynamic_cast<bitwiseor *>(l))
		return bitwisexor::get(ll->l, bitwisexor::get(ll->r, r));		
	bitwisexor *work = new (allocator.alloc()) bitwisexor();
	work->l = l;							
	work->r = r;							
	return intern(work);						
}

mk_op_allocator(bitwiseand);
bool bitwiseand::isLogical() const { return l->isLogical() && r->isLogical(); }
Expression *bitwiseand::get(Expression *l, Expression *r)			
{									
	unsigned long lc, rc;						
	bool lIsConstant = l->isConstant(&lc);
	bool rIsConstant = r->isConstant(&rc);
	if (lIsConstant) {
		if (lc == 0)
			return l;
		if (lc == 1 && r->isLogical())
			return r;
		if (lc == 0xfffffffffffffffful)
			return r;
		if (rIsConstant)
			return ConstExpression::get(lc & rc);
	} else if (rIsConstant) {
		if (rc == 0)
			return r;
		if (rc == 1 && l->isLogical())
			return l;
		if (rc == 0xfffffffffffffffful)
			return l;
	}

	if (bitwiseand *ll = dynamic_cast<bitwiseand *>(l)) {
		/* Rewrite (x & A) & A to just x & A */
		if (ll->r == r)
			return l;

		/* Otherwise, rewrite (x & y) & z to x & (y & z) */
		return bitwiseand::get(ll->l, bitwiseand::get(ll->r, r));		
	}
	bitwiseand *work = new (allocator.alloc()) bitwiseand();
	work->l = l;
	work->r = r;
	return intern(work);						
}


VexAllocType ImportOrigin::allocator = { -1, ImportOrigin::visit,
					 ImportOrigin::destruct,
					 "ImportOrigin" };

void *ImportOrigin::operator new(size_t s)
{
	return LibVEX_Alloc_Sized(&allocator, s);
}

ImportOriginSymbolicFailure *ImportOriginSymbolicFailure::w;
ImportOrigin *ImportOriginSymbolicFailure::get()
{
	if (!w)
		w = new ImportOriginSymbolicFailure();
	return w;
}

ImportOriginInitialValue *ImportOriginInitialValue::w;
ImportOrigin *ImportOriginInitialValue::get()
{
	if (!w)
		w = new ImportOriginInitialValue();
	return w;
}

ImportOriginLogfile *ImportOriginLogfile::w;
ImportOrigin *ImportOriginLogfile::get()
{
	if (!w)
		w = new ImportOriginLogfile();
	return w;
}

mk_op_allocator(equals);							
bool equals::isLogical() const { return true; }			
Expression *equals::get(Expression *l, Expression *r)		
{									
	unsigned long lc, rc;
	if (r->isConstant(&rc)) {
		if (l->isConstant(&lc))
			return ConstExpression::get(lc == rc);

		/* Rewrite X ? a : b == a to just X if a and b are
		   non-equal constants. */
		ternarycondition *tc = dynamic_cast<ternarycondition *>(l);
		if (tc) {
			unsigned long tc_true_const, tc_false_const;
			if (tc->t->isConstant(&tc_true_const) &&
			    tc->f->isConstant(&tc_false_const)) {
				if (tc_true_const == rc)
					return bitsaturate::get(tc->cond);
				else
					return logicalnot::get(tc->cond);
			}
		}
	}

	equals *work = new (allocator.alloc()) equals();
	work->l = l;							
	work->r = r;							
	return intern(work);						
}

