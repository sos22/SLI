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
	 EventTimestamp store, abstract_interpret_value storeAddr, unsigned size)
{
	abstract_interpret_value res;
	res.v = val.v;
	res.origin = LoadExpression::get(when, val.origin, addr.origin, storeAddr.origin, store,
					 size);
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

#define mk_unop(nme, op)						\
        bool nme::isLogical() const { return false; }			\
	Expression *nme::get(Expression *l)				\
	{								\
	        unsigned long lc;				        \
		if (l->isConstant(&lc))					\
			return ConstExpression::get(op lc);		\
		unop_float_rip(nme);					\
		nme *work = new nme();					\
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
	} else if (rIsConstant && rc == 0)
		return l;

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
		if (land && rand && land->l == rand->l)
			return bitwiseand::get(land->l,
					       bitwiseor::get(land->r,
							      rand->r));
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

	if (bitwiseor *ll = dynamic_cast<bitwiseor *>(l))
		return bitwisexor::get(ll->l, bitwisexor::get(ll->r, r));		
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
		if (lc == 1 && r->isLogical())
			return r;
		if ((lc & mask) == (0xfffffffffffffffful & mask))
			return r;
		if (rIsConstant)
			return ConstExpression::get(lc & rc);
	} else if (rIsConstant) {
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
		if (rc == 1 && l->isLogical())
			return l;
		if ((rc & mask) == (0xfffffffffffffffful & mask))
			return l;
	}

	binop_float_rip(bitwiseand);

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

	bitwiseand *work = new bitwiseand();
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

bool equals::isLogical() const { return true; }			
Expression *equals::get(Expression *l, Expression *r)		
{									
	unsigned long lc, rc;
	bool lIsConstant = l->isConstant(&lc);
	bool rIsConstant = r->isConstant(&rc);
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

#define TRIV_EXPR_MAPPER(c)			\
	Expression *				\
	ExpressionMapper::map(c *e)		\
	{					\
		return idmap(e);		\
	}					\

TRIV_EXPR_MAPPER(BottomExpression)
TRIV_EXPR_MAPPER(ConstExpression)
TRIV_EXPR_MAPPER(ImportExpression)
TRIV_EXPR_MAPPER(ExpressionHappensBefore)

Expression *
ExpressionMapper::map(ExpressionLastStore *els)
{
	return idmap(ExpressionLastStore::get(els->load, els->store,
					      els->vaddr->map(*this)));
}

Expression *
ExpressionMapper::map(LoadExpression *le)
{
	return idmap(LoadExpression::get(le->when,
					 le->val->map(*this),
					 le->addr->map(*this),
					 le->storeAddr->map(*this),
					 le->store,
					 le->size));
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
	return l->relevance(ev, lowThresh + 100, highThresh) - 100;
}
Expression *alias::refine(const MachineState<abstract_interpret_value> *ms,
			  LogReader<abstract_interpret_value> *lf,
			  LogReaderPtr ptr,
			  bool *progress,
			  const std::map<ThreadId, unsigned long> &validity,
			  EventTimestamp ev)
{
	*progress = true;
	return l;
}
