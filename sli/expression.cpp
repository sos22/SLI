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

void Expression::dump_chain_length_table()
{
	FILE *f;
	f = fopen("chains.inf", "w");
	for (unsigned x = 0; x < nr_heads; x++)
		fprintf(f, "%d\t%d\n", x, chain_lengths[x]);
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
		e->release(e);
		return cursor;
	}
	e->add_to_hash();
	nr_interned++;
	return e;
}

#if 0
static unsigned long interesting_addresses[] = {
	0x26f4030,                                                                                                       
	0x26f4160,                                                                                                       
	0x26f49f0,                                                                                                       
	0x26f4a18,                                                                                                       
	0x26f4d28,                                                                                                       
	0x26f4d38,                                                                                                       
	0x26f4d40,                                                                                                       
	0x2ef5160,                                                                                                       
	0x2ef59f0,                                                                                                       
	0x2ef5a18,                                                                                                       
	0x2ef5d28,                                                                                                       
	0x2ef5d38,                                                                                                       
	0x34a1e20,                                                                                                       
	0x34a2d50,                                                                                                       
	0x350c010,                                                                                                       
	0x350c0c8,                                                                                                       
	0x350c170,                                                                                                       
	0x3555bf8,                                                                                                       
	0x3555ca0,                                                                                                       
	0x3556000,                                                                                                       
	0x3556008,                                                                                                       
	0x3567b08,                                                                                                       
	0x3567b28,                                                                                                       
	0x3567b2c,                                                                                                       
	0x3567b38,                                                                                                       
	0x3567b48,                                                                                                       
	0x3583070,                                                                                                       
	0x3583110,                                                                                                       
	0x3668bc0,                                                                                                       
	0x3675140,                                                                                                       
	0x36794c8,                                                                                                       
	0x3679570,                                                                                                       
	0x374c3a8,                                                                                                       
	0x374c3cc,                                                                                                       
	0x3780ff8,                                                                                                       
	0x37810a0,                                                                                                       
	0x399de28,                                                                                                       
	0x3ad3ce8,                                                                                                       
	0x3cb9318,                                                                                                       
	0x3cb93c0,                                                                                                       
	0x3dac278,                                                                                                       
	0x3f1d4a8,                                                                                                       
	0x3f1d550,                                                                                                       
	0x41f1178,                                                                                                       
	0x4268e88,                                                                                                       
	0x4268f30,                                                                                                       
	0x426e2e0,                                                                                                       
	0x42acbf8,                                                                                                       
	0x42c2a50,                                                                                                       
	0x42c5128,                                                                                                       
	0x42c51d0,                                                                                                       
	0x42fe738,                                                                                                       
	0x42fe7e0,                                                                                                       
	0x4358990,                                                                                                       
	0x436c268,                                                                                                       
	0x436c278,                                                                                                       
	0x437c648,                                                                                                       
	0x437edd8,                                                                                                       
	0x437ee80,                                                                                                       
	0x43815e8,                                                                                                       
	0x4381690,                                                                                                       
	0x43c32e8,                                                                                                       
	0x43ca018,                                                                                                       
	0x43cdf48,                                                                                                       
	0x44d3588,                                                                                                       
	0x44d3630,                                                                                                       
	0x4513ce8,                                                                                                       
	0x4530078,                                                                                                       
	0x4530120,                                                                                                       
	0x4530c78,                                                                                                       
	0x4540228,                                                                                                       
	0x4551248,                                                                                                       
	0x4551258,                                                                                                       
	0x4551808,                                                                                                       
	0x4551858,                                                                                                       
	0x4551900,                                                                                                       
	0x4551b68,                                                                                                       
	0x4551bc0,                                                                                                       
	0x4551d58,                                                                                                       
	0x4551df0,                                                                                                       
	0x4551e58,                                                                                                       
	0x4551e68,                                                                                                       
	0x4551f18,                                                                                                       
	0x4551f28,                                                                                                       
	0x4552138,                                                                                                       
	0x4552188,                                                                                                       
	0x4552230,                                                                                                       
	0x456e9e0,                                                                                                       
	0x456ebd8,                                                                                                       
	0x456ebe8,                                                                                                       
	0x456ec28,                                                                                                       
	0x456ecd0,                                                                                                       
	0x456eda8,                                                                                                       
	0x456edb8,                                                                                                       
	0x456f1a0,                                                                                                       
	0x4582928,                                                                                                       
	0x459b8b8,                                                                                                       
	0x45a0e08,                                                                                                       
	0x45bf628,                                                                                                       
	0x45bf6d0,                                                                                                       
	0x45de118,                                                                                                       
	0x45e5aa8,                                                                                                       
	0x46074b8,                                                                                                       
	0x4607508,                                                                                                       
	0x46075b0,                                                                                                       
	0x4607608,                                                                                                       
	0x4607618,                                                                                                       
	0x4607658,                                                                                                       
	0x4607700,                                                                                                       
	0x4641718,                                                                                                       
	0x46a44e8,                                                                                                       
	0x46a4590,                                                                                                       
	0x46a4818,                                                                                                       
	0x46a8fb8,                                                                                                       
	0x46a92b8,                                                                                                       
	0x46a9308,                                                                                                       
	0x46a9388,                                                                                                       
	0x46a93b0,                                                                                                       
	0x46a93d8,                                                                                                       
	0x46a93e8,                                                                                                       
	0x46a9428,                                                                                                       
	0x46a94d0,                                                                                                       
	0x46a95a0,                                                                                                       
	0x46a9778,                                                                                                       
	0x46dab70,                                                                                                       
	0x46db1b8,                                                                                                       
	0x46db208,
	0x46db2b0,
	0x46db2d8,
	0x46db2e8,
	0x46db328,
	0x46db3d0,
	0x46db4a0,
	0x46dc608,
	0x47178a8,
	0x47178f8,
	0x47179a0,
	0x47179c8,
	0x47179d8,
	0x4717a18,
	0x4717ac0,
	0x4717b40,
	0x4718ad8,
	0x4718b80,
	0x471d4f8,
	0x471d568,
	0x471d610,
	0x5715160,
	0x5715a18,
	0x5715d28,
	0x5715d38,
	0x5715d40,
	0x7faa316fe160,
	0x7faa316fed28,
	0x7faa3275c160,
	0x7faa3275cd28,
	0x7faa34000020,
	0x7faa34000098,
	0x7faa34044980,
	0x7faa39fea160,
	0x7faa39feaa18,
	0x7faa39fead28,
	0x7faa39fead38,
	0x7faa39fead40,
	0x7faa3a7521b0,
	0x7faa44fbe9c0,
	0x7faa44fbe9c8,
	0x7faa44fbea00,
	0x7faa44fbea04,
	0x7faa44fbea18,
	0x7faa44fbea48,
	0x7faa44fbea60,
	0x7faa44fbea78,
	0x7faa44fbea88,
	0x7faa4a029728,
	0x7faa4a029738,
	0x7faa4a02c030,
	0x7faa4a02c034,
	0x7faa4a02c040,
	0x7faa4b166218,
	0x7faa4b16a290,
	0x7faa4b16a310,
	0x7faa4b38b508
};
#else
static unsigned long interesting_addresses[] = {
	0x456e9e0
};
#endif

static bool
address_is_interesting(ThreadId tid, unsigned long addr)
{
	if (tid._tid() != 9)
		return false;

	for (unsigned x = 0; x < sizeof(interesting_addresses) / sizeof(interesting_addresses[0]); x++)
		if (addr == interesting_addresses[x])
			return true;
	return false;
}

template<> abstract_interpret_value
load_ait(abstract_interpret_value val, abstract_interpret_value addr, EventTimestamp when,
	 EventTimestamp store, abstract_interpret_value storeAddr, unsigned size)
{
	abstract_interpret_value res;
	res.v = val.v;
	if (address_is_interesting(when.tid, addr.v))
		res.origin = LoadExpression::get(when, val.origin, addr.origin, storeAddr.origin, store,
						 size, addr.v);
	else
		res.origin = val.origin;
	return res;
}

template<> unsigned long
load_ait(unsigned long x, unsigned long addr, EventTimestamp when, EventTimestamp store,
	 unsigned long storeAddr, unsigned size)
{
	return x;
}

#define binop_float_rip(nme)						\
	do {								\
		ExpressionRip *lrip = dynamic_cast<ExpressionRip *>(l);	\
		ExpressionRip *rrip = dynamic_cast<ExpressionRip *>(r);	\
		if (lrip && rrip && lrip->history->isEqual(rrip->history)) \
			return ExpressionRip::get(lrip->tid,		\
						  lrip->history,	\
						  nme::get(lrip->cond,	\
							   rrip->cond), \
						  lrip->model_execution, \
						  lrip->model_exec_start); \
		if (rrip && lIsConstant)				\
			return ExpressionRip::get(rrip->tid,		\
						  rrip->history,	\
						  nme::get(l,		\
							   rrip->cond), \
						  rrip->model_execution, \
						  rrip->model_exec_start); \
		if (lrip && rIsConstant)				\
			return ExpressionRip::get(lrip->tid,		\
						  lrip->history,	\
						  nme::get(r,		\
							   lrip->cond), \
						  lrip->model_execution, \
						  lrip->model_exec_start); \
		if (onlyif *loif = dynamic_cast<onlyif*>(l))		\
			return onlyif::get(loif->l,			\
					   nme::get(loif->r, r));	\
		if (onlyif *roif = dynamic_cast<onlyif*>(r))		\
			return onlyif::get(roif->l,			\
					   nme::get(l, roif->r));	\
	} while (0)

#define mk_binop(nme, op, associates, logical)				\
	bool nme::isLogical() const { return logical; }			\
	Expression *nme::get(Expression *l, Expression *r)		\
	{								\
	        unsigned long lc, rc;				        \
		bool lIsConstant = l->isConstant(&lc);			\
		bool rIsConstant = r->isConstant(&rc);			\
		if (lIsConstant && rIsConstant)				\
			return ConstExpression::get(lc op rc);		\
                if (associates) {					\
			if (nme *ll = dynamic_cast<nme *>(l))		\
				return nme::get(ll->l, nme::get(ll->r, r)); \
		}							\
		binop_float_rip(nme);					\
		nme *work = new nme();					\
		work->l = l;						\
		work->r = r;						\
		return intern(work);					\
	}

#define unop_float_rip(nme)						\
	do {								\
		if (ExpressionRip *re =					\
		    dynamic_cast<ExpressionRip *>(l)) {			\
			return ExpressionRip::get(re->tid, re->history,	\
						  nme::get(re->cond),	\
						  re->model_execution,	\
						  re->model_exec_start); \
		}							\
		if (onlyif *oif = dynamic_cast<onlyif*>(l))		\
			return onlyif::get(oif->l,			\
					   nme::get(oif->r));		\
	} while (0)

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

bool unaryminus::isLogical() const { return false; }
Expression *unaryminus::get(Expression *l)
{
	unsigned long lc;
	if (l->isConstant(&lc))
		return ConstExpression::get(-lc);
	if (plus *p = dynamic_cast<plus *>(l)) {
		return plus::get(unaryminus::get(p->l),
				 unaryminus::get(p->r));
	}
	unop_float_rip(unaryminus);
	unaryminus *work = new unaryminus();
	work->l = l;
	return intern(work);
}

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
	return bitwiseand::get(bitwisenot::get(bitsaturate::get(l)),
			       ConstExpression::get(1));
}

bool bitsaturate::isLogical() const { return true; }
Expression *bitsaturate::get(Expression *l)
{
	unsigned long c;
	if (l->isConstant(&c)) {
		if (c == 0 || c == 1)
			return l;
		else
			return ConstExpression::get(1);
	}
	if (l->isLogical())
		return l;
	unop_float_rip(bitsaturate);
	bitsaturate *work = new bitsaturate();
	work->l = l;
	return intern(work);
}

bool bitwisenot::isLogical() const { return false; }
Expression *bitwisenot::get(Expression *l)
{
	unsigned long c;
	if (l->isConstant(&c)) {
		return ConstExpression::get(~c);
	}
	if (bitwisenot *bn = dynamic_cast<bitwisenot *>(l))
		return bn->l;
	unop_float_rip(bitwisenot);
	bitwisenot *work = new bitwisenot();
	work->l = l;
	return intern(work);
}

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
	unsigned long tv;
	unsigned long fv;
	if (t->isConstant(&tv) && f->isConstant(&fv) &&
	    tv == 1 && fv == 0)
		return bitsaturate::get(cond);
	ternarycondition *work = new ternarycondition();
	work->cond = cond;
	work->t = t;
	work->f = f;
	return intern(work);
}

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
	} else if (rIsConstant) {
		if (rc == 0)
			return l;
		/* Prefer constants on the left where possible. */
		Expression *t = l;
		l = r;
		r = t;
	}

	binop_float_rip(plus);

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

	/* Rewrite x + (c + y) to c + (x + y) whenever c is a constant */
	{
		plus *rplus = dynamic_cast<plus *>(r);
		unsigned long c;
		if (rplus && rplus->l->isConstant(&c)) {
			if (lIsConstant)
				/* Rewrite c + (c' + y) to (c + c') +
				 * y whenever c and c' are constant */
				return plus::get(plus::get(l, rplus->l),
						 rplus->r);
			else
				return plus::get(rplus->l,
						 plus::get(l, rplus->r));
		}
	}
	/* And (c + y) + x */
	{
		plus *lplus = dynamic_cast<plus *>(l);
		unsigned long c;
		if (lplus && lplus->l->isConstant(&c))
			return plus::get(lplus->l,
					 plus::get(r, lplus->r));
	}

	/* Rewrite -x + x to just 0 */
	{
		unaryminus *lminus = dynamic_cast<unaryminus *>(l);
		if (lminus && lminus->l == r)
			return ConstExpression::get(0);
	}

	/* Likewise x + -x to just 0 */
	{
		unaryminus *rminus = dynamic_cast<unaryminus *>(r);
		if (rminus && rminus->l == r)
			return ConstExpression::get(0);
	}

	if (plus *ll = dynamic_cast<plus *>(l))				
		return plus::get(ll->l, plus::get(ll->r, r));		
	plus *work = new plus();			
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
static long
sane_rshift_arith(long r, long cntr)
{
	if (cntr < 0)
		return sane_lshift(r, -cntr);
	else if (cntr >= 64) {
		if (r < 0)
			return -1;
		else
			return 0;
	} else
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

bool lshift::isLogical() const { return false; }
Expression *lshift::get(Expression *l, Expression *r)			
{									
	unsigned long lc, rc;	
	bool rIsConstant;
	bool lIsConstant;
	rIsConstant = r->isConstant(&rc);
	lIsConstant = l->isConstant(&lc);

	if (lIsConstant) {
		if (lc == 0)
			return l;
		if (rIsConstant)
			return ConstExpression::get(sane_lshift(lc, rc));
	} else if (rIsConstant && rc == 0)
		return l;

	binop_float_rip(lshift);

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
			if (lrshift &&
			    lrshift->r->isConstant(&A) &&
			    land->r->isConstant(&B)) {
				x = lrshift->l;
				return bitwiseand::get(
					rshift::get(x, ConstExpression::get(A - C)),
					ConstExpression::get(sane_lshift(B, C)));
			}
		}
	}
	lshift *work = new lshift();			
	work->l = l;							
	work->r = r;							
	return intern(work);						
}

bool rshift::isLogical() const { return false; }
Expression *rshift::get(Expression *l, Expression *r)			
{									
	unsigned long lc, rc;	
	bool rIsConstant;
	bool lIsConstant;

	rIsConstant = r->isConstant(&rc);
	lIsConstant = l->isConstant(&lc);
	if (lIsConstant) {
		if (lc == 0)
			return l;
		if (rIsConstant)
			return ConstExpression::get(sane_rshift(lc, rc));
	} else if (rIsConstant && rc == 0)
		return l;
	binop_float_rip(rshift);
	rshift *work = new rshift();			
	work->l = l;							
	work->r = r;							
	return intern(work);						
}

bool rshiftarith::isLogical() const { return false; }
Expression *rshiftarith::get(Expression *l, Expression *r)			
{									
	unsigned long lc, rc;	
	bool rIsConstant;
	bool lIsConstant;

	rIsConstant = r->isConstant(&rc);
	lIsConstant = l->isConstant(&lc);
	if (lIsConstant) {
		if (lc == 0)
			return l;
		if (rIsConstant)
			return ConstExpression::get(sane_rshift_arith(lc, rc));
	} else if (rIsConstant && rc == 0)
		return l;
	binop_float_rip(rshiftarith);
	rshiftarith *work = new rshiftarith();
	work->l = l;
	work->r = r;							
	return intern(work);						
}

bool bitwiseor::isLogical() const { return l->isLogical() && r->isLogical(); }
Expression *bitwiseor::get(Expression *l, Expression *r)			
{
	if (l == r)
		return l;
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

	binop_float_rip(bitwiseor);

	/* Rewrite (x & Y) | (x & Z) to x & (Y | Z) */
	{
		bitwiseand *land = dynamic_cast<bitwiseand *>(l);
		bitwiseand *rand = dynamic_cast<bitwiseand *>(r);
		if (land && rand) {
			if (land->l == rand->l)
				return bitwiseand::get(land->l,
						       bitwiseor::get(land->r,
								      rand->r));
			if (land->r == rand->r)
				return bitwiseand::get(bitwiseor::get(land->l,
								      land->l),
						       land->r);
		}
	}
	
	if (bitwiseor *ll = dynamic_cast<bitwiseor *>(l))
		return bitwiseor::get(ll->l, bitwiseor::get(ll->r, r));		
	bitwiseor *work = new bitwiseor();
	work->l = l;							
	work->r = r;							
	return intern(work);						
}

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

	binop_float_rip(bitwisexor);

	bitwisexor *work = new bitwisexor();
	work->l = l;							
	work->r = r;							
	return intern(work);						
}

bool bitwiseand::isLogical() const { return l->isLogical() || r->isLogical(); }
Expression *bitwiseand::get(Expression *l, Expression *r)			
{
	if (l == r)
		return l;
	unsigned long lc, rc;						
	bool lIsConstant = l->isConstant(&lc);
	bool rIsConstant = r->isConstant(&rc);
	unsigned long mask = 0xfffffffffffffffful;
	if (lIsConstant) {
		r = r->restrictToMask(lc);
		if (LoadExpression *le =
		    dynamic_cast<LoadExpression *>(r)) {
			switch (le->size) {
			case 1:
				mask = 0xff;
				break;
			case 2:
				mask = 0xffff;
				break;
			case 4:
				mask = 0xffffffff;
			}
		}
		if ((lc & mask) == 0)
			return ConstExpression::get(0);
		if (r->isLogical()) {
			if (lc & 1)
				return r;
			else
				return ConstExpression::get(0);
		}
		if ((lc & mask) == (0xfffffffffffffffful & mask))
			return r;
		if (rIsConstant)
			return ConstExpression::get(lc & rc);
	} else if (rIsConstant) {
		l = l->restrictToMask(rc);
		if (LoadExpression *le =
		    dynamic_cast<LoadExpression *>(l)) {
			switch (le->size) {
			case 1:
				mask = 0xff;
				break;
			case 2:
				mask = 0xffff;
				break;
			case 4:
				mask = 0xffffffff;
			}
		}
		if ((rc & mask) == 0)
			return ConstExpression::get(0);
		if (l->isLogical()) {
			if (rc & 1)
				return l;
			else
				return ConstExpression::get(0);
		}
		if ((rc & mask) == (0xfffffffffffffffful & mask))
			return l;
	}

	binop_float_rip(bitwiseand);

	if (dynamic_cast<bitwisenot *>(r)) {
		/* Rewrite x & ~y to ~y & x */
		Expression *t = l;
		l = r;
		r = t;
	}

	if (bitwisenot *ll = dynamic_cast<bitwisenot *>(l)) {
		/* Rewrite ~(x & y) & z to just ~x & (y & z) */
		if (bitwiseand *lll = dynamic_cast<bitwiseand *>(ll->l)) {
			return bitwiseand::get(bitwisenot::get(lll->l),
					       bitwiseand::get(lll->r, r));
		}
		/* Rewrite ~(x == y) & 1 to x != y */
		if (rIsConstant && rc == 1) {
			if (equals *eq = dynamic_cast<equals *>(ll->l))
				return notequals::get(eq->l, eq->r);
		}
		/* And ~(x != y) & 1 to x == y */
		if (rIsConstant && rc == 1) {
			if (notequals *eq = dynamic_cast<notequals *>(ll->l))
				return equals::get(eq->l, eq->r);
		}
	}
	if (bitwiseand *ll = dynamic_cast<bitwiseand *>(l)) {
		/* Rewrite (x & A) & A to just x & A */
		if (ll->r == r)
			return l;
		/* Rewrite (A & x) & A to just A & x */
		if (ll->l == r)
			return l;
		/* Otherwise, rewrite (x & y) & z to x & (y & z) */
		return bitwiseand::get(ll->l, bitwiseand::get(ll->r, r));		
	}

	if (bitwiseand *rr = dynamic_cast<bitwiseand *>(r)) {
		/* Rewrite A & (x & A) to just x & A */
		if (rr->r == l)
			return r;
		/* Rewrite A & (A & x) to just A & x */
		if (rr->l == l)
			return r;
	}

	/* rewrite (~y + (x & y)) & y to just (x & y) */
	if (plus *lp = dynamic_cast<plus *>(l)) {
		if (bitwiseand *lr = dynamic_cast<bitwiseand *>(lp->r)) {
			if (lr->r == r) {
				Expression *complement_r = bitwisenot::get(r);
				if (complement_r == lp->l)
					return lr;
			}
		}
	}
	bitwiseand *work = new bitwiseand();
	work->l = l;
	work->r = r;
	return intern(work);						
}


bool equals::isLogical() const { return true; }			
Expression *equals::get(Expression *l, Expression *r)		
{									
	unsigned long lc, rc;
	bool lIsConstant = l->isConstant(&lc);
	bool rIsConstant = r->isConstant(&rc);
	if (lIsConstant && !rIsConstant) {
		/* Prefer X == c to c == X, where c is a constant and
		 * X isn't. */
		Expression *t = l;
		l = r;
		r = t;
	}

	if (rIsConstant) {
		if (lIsConstant)
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

		/* Rewrite (c + X) == c', where c and c' constants, to
		 * X == c' - c */
		plus *lplus = dynamic_cast<plus *>(l);
		if (lplus) {
			unsigned long c;
			if (lplus->l->isConstant(&c))
				return equals::get(lplus->r,
						   ConstExpression::get(rc - c));
		}
	}

	binop_float_rip(equals);

	equals *work = new equals();
	work->l = l;							
	work->r = r;							
	return intern(work);						
}

bool onlyif::isLogical() const { return r->isLogical(); }
Expression *onlyif::get(Expression *l, Expression *r)
{
	unsigned long lc;
	if (l->isConstant(&lc)) {
		if (lc)
			return r;
		else
			return BottomExpression::get();
	}
	onlyif *work= new onlyif();
	work->l = l;
	work->r = r;
	return intern(work);
}

BottomExpression *BottomExpression::bottom;

Expression *
alias::restrictToMask(unsigned long x)
{
	return get(l->restrictToMask(x));
}

Expression *
onlyif::restrictToMask(unsigned long x)
{
	return get(l, r->restrictToMask(x));
}

#define RESTRICT_LOGICAL(name)				\
	Expression *					\
	name::restrictToMask(unsigned long x)		\
	{						\
		if (!(x & 1))				\
			return ConstExpression::get(0);	\
		else					\
			return this;			\
	}
RESTRICT_LOGICAL(equals)
RESTRICT_LOGICAL(notequals)
RESTRICT_LOGICAL(lessthan)
RESTRICT_LOGICAL(lessthanequals)
RESTRICT_LOGICAL(greaterthan)
RESTRICT_LOGICAL(greaterthanequals)

#define RESTRICT_BITWISE(name)						\
	Expression *							\
	name::restrictToMask(unsigned long x)				\
	{								\
		return get(l->restrictToMask(x), r->restrictToMask(x));	\
	}
RESTRICT_BITWISE(bitwisexor)
RESTRICT_BITWISE(bitwiseor)
RESTRICT_BITWISE(bitwiseand)
RESTRICT_BITWISE(plus)

#define RESTRICT_TRIVIAL(name)			\
	Expression *				\
	name::restrictToMask(unsigned long)	\
	{					\
		return this;			\
	}
RESTRICT_TRIVIAL(rshiftarith)
RESTRICT_TRIVIAL(rshift)
RESTRICT_TRIVIAL(lshift)
RESTRICT_TRIVIAL(modulo)
RESTRICT_TRIVIAL(divide)
RESTRICT_TRIVIAL(times)
RESTRICT_TRIVIAL(bitwisenot)
RESTRICT_TRIVIAL(bitsaturate)
RESTRICT_TRIVIAL(unaryminus)

#define TRIV_EXPR_MAPPER(c)			\
	Expression *				\
	ExpressionMapper::map(c *e)		\
	{					\
		return idmap(e);		\
	}					\

TRIV_EXPR_MAPPER(BottomExpression)
TRIV_EXPR_MAPPER(ConstExpression)
TRIV_EXPR_MAPPER(ExpressionHappensBefore)

Expression *
ExpressionMapper::map(ExpressionLastStore *els)
{
	return idmap(ExpressionLastStore::get(els->load, els->store,
					      els->vaddr->map(*this),
					      els->concrete_vaddr));
}

Expression *
ExpressionMapper::map(LoadExpression *le)
{
	return idmap(LoadExpression::get(le->when,
					 le->val->map(*this),
					 le->addr->map(*this),
					 le->storeAddr->map(*this),
					 le->store,
					 le->size,
					 le->concrete_addr));
}

Expression *
ExpressionMapper::map(BinaryExpression *be)
{
	return idmap(be->semiDupe(be->l->map(*this),
				  be->r->map(*this)));
}

Expression *
ExpressionMapper::map(UnaryExpression *ue)
{
	return idmap(ue->semiDupe(ue->l->map(*this)));
}

Expression *
ExpressionMapper::map(ternarycondition *tc)
{
	return idmap(ternarycondition::get(tc->cond->map(*this),
					   tc->t->map(*this),
					   tc->f->map(*this)));
}

Expression *
ExpressionMapper::map(ExpressionRip *er)
{
	return idmap(ExpressionRip::get(er->tid,
					er->history ? er->history->map(*this) : NULL,
					er->cond->map(*this),
					er->model_execution,
					er->model_exec_start));
}

Expression *
ExpressionMapper::map(ExpressionBadPointer *ebp)
{
	return idmap(ExpressionBadPointer::get(ebp->when,
					       ebp->addr->map(*this)));
}

Expression *
ExpressionMapper::idmap(Expression *e)
{
	return e;
}

const Relevance Relevance::irrelevant(10000);
const Relevance Relevance::perfect(0);

bool alias::isLogical() const { return l->isLogical(); }
Expression *alias::get(Expression *l)
{
	unsigned long lc;
	if (l->isConstant(&lc))
		return ConstExpression::get(lc);
	alias *work = new alias();
	work->l = l;
	return intern(work);
}
Relevance alias::relevance(const EventTimestamp &ev,
			   Relevance lowThresh,
			   Relevance highThresh)
{
	return l->relevance(ev, lowThresh + 1000000, highThresh) - 1000000;
}
Expression *alias::refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
			  VexPtr<LogReader<abstract_interpret_value> > &lf,
			  LogReaderPtr ptr,
			  bool *progress,
			  VexPtr<gc_map<ThreadId, unsigned long> >&validity,
			  EventTimestamp ev,
			  GarbageCollectionToken)
{
	*progress = true;
	return l;
}

void
History::calcLastAccessed()
{
	const gc_map<ThreadId, unsigned long> *p;
	const gc_map<ThreadId, unsigned long> *c;
	if (parent)
		p = parent->lastAccessMap();
	else
		p = NULL;
	if (condition)
		c = condition->lastAccessMap();
	else
		c = NULL;
	gc_map<ThreadId, unsigned long> *t;
	if (!p && !c) {
		t = new gc_map<ThreadId, unsigned long>();
	} else if (!p) {
		t = new gc_map<ThreadId, unsigned long>(*c);
	} else if (!c) {
		t = new gc_map<ThreadId, unsigned long>(*p);
	} else {
		t = new gc_map<ThreadId, unsigned long>(*c);
		Expression::mergeAccessMaps(t, p);
	}

	lastAccessed = t;
}

void
Expression::mergeAccessMaps(gc_map<ThreadId, unsigned long> *out,
			    const gc_map<ThreadId, unsigned long> *_in)
{
	gc_map<ThreadId, unsigned long> *in =
		const_cast<gc_map<ThreadId, unsigned long> *>(_in);
	for (gc_map<ThreadId, unsigned long>::iterator it = in->begin();
	     it != in->end();
	     it++) {
		if ( (*out)[it.key()] < it.value() )
			(*out)[it.key()] = it.value();
	}
}

void
fixup_expression_table(void)
{
	for (unsigned x = 0; x < Expression::nr_heads; x++)
		if (Expression::heads[x])
			Expression::heads[x]->pprev = &Expression::heads[x];
}

