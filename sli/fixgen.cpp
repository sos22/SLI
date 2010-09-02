#include <list>
#include <set>
#include <algorithm>

#include "sli.h"

class CollectTimestampsVisitor : public ExpressionVisitor {
public:
	gc_map<ThreadId, std::vector<EventTimestamp> > *timestamps;
	CollectTimestampsVisitor() : timestamps(new gc_map<ThreadId, std::vector<EventTimestamp> >()) {}
	void addTimestamp(EventTimestamp ts);
	void visit(Expression *e);
};

void
CollectTimestampsVisitor::addTimestamp(EventTimestamp ts)
{
	(*timestamps)[ts.tid].push_back(ts);
}

void
CollectTimestampsVisitor::visit(Expression *e)
{
	if (ExpressionHappensBefore *hb = dynamic_cast<ExpressionHappensBefore *>(e)) {
		addTimestamp(hb->before);
		addTimestamp(hb->after);
	}
}

template <typename t, typename s> s&
rindex(t &vect, unsigned idx)
{
	class t::reverse_iterator it;
	for (it = vect.rbegin();
	     it != vect.rend() && idx != 0;
	     (it++, idx--))
		;
	assert(it != vect.rend());
	return *it;
}

class RemoveEventsMapper : public ExpressionMapper {
	History *removeNullConditionsHist(History *hs)
	{
		if (!hs)
			return NULL;
		if (!hs->condition || dynamic_cast<ConstExpression *>(hs->condition))
			return removeNullConditionsHist(hs->parent);
		return new History(hs->condition,
				   hs->last_valid_idx,
				   hs->when,
				   hs->rips,
				   removeNullConditionsHist(hs->parent));
	}
public:
	const std::set<EventTimestamp> &allowed;
	RemoveEventsMapper(const std::set<EventTimestamp> &_allowed)
		: allowed(_allowed)
	{
	}
	bool allow(EventTimestamp ts)
	{
		return allowed.count(ts) != 0;
	}
	Expression *map(ExpressionLastStore *els)
	{
		if (!allow(els->load) || !allow(els->store))
			return NULL;
		Expression *va;
		va = els->vaddr->map(*this);
		if (!va)
			return NULL;
		else
			return ExpressionLastStore::get(els->load, els->store, va);
	}
	Expression *map(ExpressionHappensBefore *ehb)
	{
		if (allow(ehb->before) && allow(ehb->after))
			return ehb;
		else
			return NULL;
	}
	Expression *map(LoadExpression *le)
	{
		Expression *val = le->val->map(*this);
		if (!val)
			return NULL;
		if (!allow(le->when) || !allow(le->store))
			return val;
		Expression *addr = le->addr->map(*this);
		Expression *sa = le->storeAddr->map(*this);
		if (!addr || !sa)
			return val;
		return LoadExpression::get(le->when, val, addr, sa,
					   le->store, le->size);
	}
	Expression *map(BinaryExpression *be)
	{
		if (onlyif *oif = dynamic_cast<onlyif *>(be)) {
			Expression *e = ternarycondition::get(oif->l,
							      oif->r,
							      logicalnot::get(oif->r));
			return e->map(*this);
		}

		Expression *l = be->l->map(*this);
		Expression *r = be->r->map(*this);
		if (l && r)
			return be->semiDupe(l, r);
		else if (!l && !r)
			return NULL;

		Expression *a = NULL;
		if (l)
			a = l;
		if (r)
			a = r;
		assert(a != NULL);
		if (dynamic_cast<bitwiseand *>(be) ||
		    dynamic_cast<bitwiseand *>(be))
			return a;
		else
			return NULL;
	}
	Expression *map(UnaryExpression *ue)
	{
		if (dynamic_cast<alias *>(ue)) {
			return ue->concretise();
		} else {
			Expression *l = ue->l->map(*this);
			if (l)
				return ue->semiDupe(l);
			else
				return NULL;
		}
	}
	Expression *map(ternarycondition *tc)
	{
		Expression *c = tc->cond->map(*this),
			*t, *f;
		if (!c)
			return NULL;
		t = tc->t->map(*this);
		f = tc->f->map(*this);
		if (!t)
			return f;
		if (!f)
			return t;
		return logicalor::get(logicaland::get(c, t),
				      logicaland::get(logicalnot::get(c), f))->map(*this);
	}
	Expression *map(ExpressionRip *er)
	{
		Expression *a = ExpressionMapper::map(er);
		ExpressionRip *a2 = dynamic_cast<ExpressionRip *>(a);
		assert(a2);
		Expression *cond = a2->cond;
		if (!cond)
			cond = ConstExpression::get(1);
		History *h = removeNullConditionsHist(a2->history);
		if (h)
			return ExpressionRip::get(a2->tid,
						  removeNullConditionsHist(a2->history),
						  cond,
						  a2->model_execution,
						  a2->model_exec_start);
		else
			return cond;
	}
	Expression *map(ExpressionBadPointer *ebp)
	{
		if (!allow(ebp->when))
			return NULL;
		Expression *e = ebp->addr->map(*this);
		if (e)
			return ExpressionBadPointer::get(ebp->when, e);
		else
			return NULL;
	}
};

Expression *
bitwiseand::_CNF()
{
	return bitwiseand::get(l->CNF(), r->CNF());
}

Expression *
bitwiseor::_CNF()
{
	if (bitwiseand *bal = dynamic_cast<bitwiseand *>(l)) {
		return bitwiseand::get(
			bitwiseor::get(bal->l, r)->CNF(),
			bitwiseor::get(bal->r, r)->CNF());
	} else if (bitwiseand *bar = dynamic_cast<bitwiseand *>(r)) {
		return bitwiseand::get(
			bitwiseor::get(l, bar->l)->CNF(),
			bitwiseor::get(l, bar->r)->CNF());
	} else {
		Expression *lc = l->CNF();
		Expression *rc = r->CNF();
		if (lc == l && rc == r)
			return this;
		else
			return bitwiseor::get(lc, rc)->CNF();
	}
}

Expression *
bitsaturate::_CNF()
{
	return bitsaturate::get(l->CNF());
}

Expression *
bitwisenot::_CNF()
{
	if (bitwiseand *ba = dynamic_cast<bitwiseand *>(l))
		return bitwiseor::get(bitwisenot::get(ba->l),
				      bitwisenot::get(ba->r))->CNF();
	else if (bitwiseor *bo = dynamic_cast<bitwiseor *>(l))
		return bitwiseand::get(bitwisenot::get(bo->l)->CNF(),
				       bitwisenot::get(bo->r)->CNF());
	else
		return this;
}

class SimpleRewrite : public ExpressionMapper {
public:
	Expression *from;
	Expression *to;
	SimpleRewrite(Expression *_from,
		      Expression *_to)
		: from(_from), to(_to)
	{
	}
	Expression *idmap(Expression *x)
	{
		if (x == from)
			return to;
		else
			return x;
	}
	Expression *map(ExpressionHappensBefore *ehb)
	{
		if (ExpressionHappensBefore *assume =
		    dynamic_cast<ExpressionHappensBefore *>(from)) {
			/* We're trying to simplify t1:idx1 < t2:idx2
			   given t3:idx3 < t4:idx4.  We want to move
			   idx1 as early as possible and idx2 as
			   late as possible, so we consider two
			   cases:

			   t4 == t1 && idx4 < idx1 -> t3:idx3 < t2:idx2
			   t2 == t3 && idx2 < idx3 -> t1:idx1 < t4:idx4

			   We can't, unfortunately, just introduce the
			   transitive edges, but we can handle the
			   special case that it's a backwards self
			   edge.
			*/
			if (assume->after.tid == ehb->before.tid &&
			    assume->before.tid == ehb->after.tid &&
			    assume->after.idx <= ehb->before.idx &&
			    ehb->after.idx <= assume->before.idx)
				return ConstExpression::get(0);

			/* We can rewrite ehb into just true if it's
			   implied by the assumption.  That's the case
			   if t1 == t3, t2 == t4, idx1 <= idx3, and
			   idx2 >= idx4. */
			if (ehb->before.tid == assume->before.tid &&
			    ehb->before.idx <= assume->before.idx &&
			    ehb->after.tid == assume->after.tid &&
			    ehb->after.idx >= assume->after.idx)
				return ConstExpression::get(1);
		}
		return ExpressionMapper::map(ehb);
	}
};


static Expression *
simplifyAssuming(Expression *what, Expression *assumption)
{
	unsigned long cass;
	if (assumption->isConstant(&cass)) {
		if (cass == 0)
			return assumption;
		else
			return what;
	}
	SimpleRewrite rw(assumption, ConstExpression::get(1));
	return what->map(rw);
}

static Expression *
simplifyLogic(Expression *e)
{
	if (bitwiseand *ba = dynamic_cast<bitwiseand *>(e)) {
		if (ConstExpression *e = dynamic_cast<ConstExpression *>(ba->l)) {
			if (e->v & 1)
				return simplifyLogic(ba->r);
			else
				return ba->l;
		}
		if (ConstExpression *e = dynamic_cast<ConstExpression *>(ba->r)) {
			if (e->v & 1)
				return simplifyLogic(ba->l);
			else
				return ba->r;
		}
		Expression *l = simplifyLogic(ba->l);
		Expression *r = simplifyLogic(simplifyAssuming(simplifyLogic(ba->r), l));
		return bitwiseand::get(l, r);
	}
	if (bitwiseor *ba = dynamic_cast<bitwiseor *>(e)) {
		if (ConstExpression *e = dynamic_cast<ConstExpression *>(ba->l)) {
			if (e->v & 1)
				return ba->l;
			else
				return simplifyLogic(ba->r);
		}
		if (ConstExpression *e = dynamic_cast<ConstExpression *>(ba->r)) {
			if (e->v & 1)
				return ba->r;
			else
				return simplifyLogic(ba->l);
		}
		Expression *l = simplifyLogic(ba->l);
		Expression *r = simplifyLogic(simplifyAssuming(simplifyLogic(ba->r),
							       simplifyLogic(logicalnot::get(l))));
		return bitwiseor::get(l, r);
	}
	if (bitwisenot *bn = dynamic_cast<bitwisenot *>(e)) {
		if (ExpressionHappensBefore *ehb = dynamic_cast<ExpressionHappensBefore *>(bn->l))
			return ExpressionHappensBefore::get(ehb->after, ehb->before);
	}
	if (ConstExpression *ce = dynamic_cast<ConstExpression *>(e))
		return ConstExpression::get(ce->v & 1);
	return e;
}

class AssumptionSet {
public:
	std::set<Expression *> content;
	AssumptionSet() : content() {}
	void assertTrue(Expression *e);
	bool contradiction() const;
	void dump() const;
};
void
AssumptionSet::assertTrue(Expression *e)
{
	unsigned long c;
	if (e->isConstant(&c)) {
		if (c) {
			/* Introducing a constant true assumption ->
			 * nothing to do */
			return;
		} else {
			/* Contradiction! */
			content.clear();
			content.insert(ConstExpression::get(0));
			return;
		}
	}

	if (bitwiseand *ba = dynamic_cast<bitwiseand *>(e)) {
		assertTrue(ba->l);
		assertTrue(ba->r);
		return;
	}

	/* At this point, content has been ``logically'' rewritten to
	   include the new assumption.  Go and see if there are any
	   nice simplifications available as a result before doing the
	   actual concrete rewrite. */

	/* Use the new assumption to reduce our existing
	 * assumptions. */
	for (std::set<Expression *>::iterator it = content.begin();
	     it != content.end();
	     it++) {
		if (*it == e)
			return;
		Expression *newIt = simplifyAssuming(*it, e);
		if (newIt != *it) {
			content.erase(it);
			assertTrue(newIt);
			assertTrue(e);
			return;
		}
	}

	/* Now use the existing assumptions to reduce the new one. */
	Expression *newE = e;
	for (std::set<Expression *>::iterator it = content.begin();
	     it != content.end();
	     it++) {
		newE = simplifyAssuming(newE, *it);
	}

	if (e == newE)
		content.insert(e);
	else
		assertTrue(newE);
}
bool
AssumptionSet::contradiction() const
{
	return content.count(ConstExpression::get(0)) != 0;
}
void
AssumptionSet::dump() const
{
	for (std::set<Expression *>::const_iterator it = content.begin();
	     it != content.end();
	     it++) {
		printf("%s\n", (*it)->name());
	}
}

class CSCandidate {
public:
	EventTimestamp tid1start;
	EventTimestamp tid1end;
	EventTimestamp tid2start;
	EventTimestamp tid2end;

	CSCandidate() {}
	CSCandidate(EventTimestamp _tid1start,
		    EventTimestamp _tid1end,
		    EventTimestamp _tid2start,
		    EventTimestamp _tid2end)
		: tid1start(_tid1start),
		  tid1end(_tid1end),
		  tid2start(_tid2start),
		  tid2end(_tid2end)
	{
	}
};

static bool operator<(const CSCandidate &a,
		      const CSCandidate &b)
{
#define F(x)					\
	if (a. x < b. x)			\
		return true;			\
	else if (a. x > b. x)			\
		return false
	F(tid1start);
	F(tid1end);
	F(tid2start);
	F(tid2end);
#undef F
	return false;
}

static void generateCSCandidates(Expression *e, std::set<CSCandidate> *output,
				 const AssumptionSet &assumptions);
static void
generateCSCandidates(ExpressionHappensBefore *ehb,
		     std::set<CSCandidate> *output,
		     const AssumptionSet &assumptions)
{
	CSCandidate work;

	for (std::set<Expression *>::iterator it = assumptions.content.begin();
	     it != assumptions.content.end();
	     it++) {
		ExpressionHappensBefore *assumption = dynamic_cast<ExpressionHappensBefore *>(*it);
		if (!assumption)
			continue;

		/* We have four memory accesses, and we want to know
		   if we can build any critical sections out of them.
		   Try every possible combination. */
		EventTimestamp W, X, Y, Z;
		W = ehb->before;
		X = ehb->after;
		Y = assumption->before;
		Z = assumption->after;
		if (W.tid == X.tid && Y.tid == Z.tid) {
			work.tid1start = min<EventTimestamp>(W, X);
			work.tid1end = max<EventTimestamp>(W, X);
			work.tid2start = min<EventTimestamp>(Y, Z);
			work.tid2end = max<EventTimestamp>(Y, Z);
		} else if (W.tid == Y.tid && X.tid == Z.tid) {
			work.tid1start = min<EventTimestamp>(W, Y);
			work.tid1end = max<EventTimestamp>(W, Y);
			work.tid2start = min<EventTimestamp>(X, Z);
			work.tid2end = max<EventTimestamp>(X, Z);
		} else if (W.tid == Z.tid && X.tid == Y.tid) {
			work.tid1start = min<EventTimestamp>(W, Z);
			work.tid1end = max<EventTimestamp>(W, Z);
			work.tid2start = min<EventTimestamp>(X, Y);
			work.tid2end = max<EventTimestamp>(X, Y);
		} else
			continue;

		assert(work.tid1start.tid == work.tid1end.tid);
		assert(work.tid2start.tid == work.tid2end.tid);

		if (work.tid1start.tid == work.tid2start.tid)
			continue;

		/* Critical section is syntactically valid.  Check
		 * that it actually works. */

		AssumptionSet aset(assumptions);
		/* This is the thing which is imposed by the critical
		 * section. */
		aset.assertTrue(
			logicalor::get(
				ExpressionHappensBefore::get(
					work.tid2end,
					work.tid1start),
				ExpressionHappensBefore::get(
					work.tid1end,
					work.tid2start)));
		/* The combination of the mutex constraint, the
		   assumption, and the crash predictor should lead to
		   a contradiction. */
		aset.assertTrue(ehb);
		if (aset.contradiction())
			output->insert(work);
	}
}

/* Walk back down the history, simultaneously generating critical
   sections which could prevent the history from happening and
   building up an assumption set which will hold if it does happen. */
static void
generateCSCandidates(History *h, std::set<CSCandidate> *output, AssumptionSet *assumptions)
{
	if (!h)
		return;
	generateCSCandidates(h->parent, output, assumptions);
	Expression *c = simplifyLogic(h->condition->CNF());
	generateCSCandidates(c, output, *assumptions);
	assumptions->assertTrue(c);
}

static void
generateCSCandidates(Expression *e, std::set<CSCandidate> *output, const AssumptionSet &assumptions)
{
	if (ExpressionHappensBefore *ehb = dynamic_cast<ExpressionHappensBefore *>(e)) {
		generateCSCandidates(ehb, output, assumptions);
	} else if (bitwiseand *ba = dynamic_cast<bitwiseand *>(e)) {
		generateCSCandidates(ba->l, output, assumptions);
		AssumptionSet newAssumes(assumptions);
		newAssumes.assertTrue(ba->l);
		generateCSCandidates(ba->r, output, newAssumes);
	} else if (bitwiseor *bo = dynamic_cast<bitwiseor *>(e)) {
		std::set<CSCandidate> l, r;
		generateCSCandidates(bo->l, &l, assumptions);
		AssumptionSet newAssumes(assumptions);
		newAssumes.assertTrue(logicalnot::get(bo->l));
		generateCSCandidates(bo->r, &r, newAssumes);
		for (std::set<CSCandidate>::iterator it = l.begin();
		     it != l.end();
		     it++) 
			if (r.count(*it))
				output->insert(*it);
	} else if (ExpressionRip *er = dynamic_cast<ExpressionRip *>(e)) {
		AssumptionSet newAssumptions(assumptions);
		generateCSCandidates(er->history, output, &newAssumptions);
		generateCSCandidates(simplifyLogic(er->cond->CNF()), output, newAssumptions);
	}
}

static void
considerReducedExpression(Expression *expr,
			  std::set<EventTimestamp> &avail_timestamps,
			  std::set<CSCandidate> *output)
{
	RemoveEventsMapper mapper(avail_timestamps);
	Expression *simplified = expr->map(mapper);
	if (!simplified) {
		printf("Simplification -> nothing at all?\n");
		return;
	}
	simplified = simplifyLogic(simplified->CNF());

	/* We now suspect that if @simplified is true then we'll crash
	   in the observed way.  Find ways of making it not be
	   true. */
	AssumptionSet assumptions;
	generateCSCandidates(simplified, output, assumptions);
}

/* Phase 2: For two selected threads, enumerate every set of accesses
   such that there are at more two accesses from each thread. */
static void
enumReducedExpressions(Expression *expr,
		       const std::vector<EventTimestamp> *t1,
		       const std::vector<EventTimestamp> *t2,
		       std::set<CSCandidate> *output)
{
	if (t2->size() < t1->size()) {
		const std::vector<EventTimestamp> *temp = t2;
		t2 = t1;
		t1 = temp;
	}

	for (int t1endidx = t1->size() - 1;
	     t1endidx >= 0;
	     t1endidx--) {
		for (int t2endidx = t2->size() - 1;
		     t2endidx >= 0;
		     t2endidx--) {
			for (int t1startidx = t1endidx;
			     t1startidx >= 0;
			     t1startidx--) {
				for (int t2startidx = t2endidx;
				     t2startidx >= 0;
				     t2startidx--) {
					std::set<EventTimestamp> s;
					s.insert((*t1)[t1startidx]);
					s.insert((*t1)[t1endidx]);
					s.insert((*t2)[t2startidx]);
					s.insert((*t2)[t2endidx]);
					considerReducedExpression(expr, s, output);
				}
			}
		}
	}
}

/* Phase 1: Enumerate every possible combination of pairs of
 * threads. */
static void
enumReducedExpressions(Expression *expr,
		       const std::set<ThreadId> &avail_threads,
		       const gc_map<ThreadId, std::vector<EventTimestamp> > &timestamps,
		       std::set<CSCandidate> *output)
{
	for (std::set<ThreadId>::const_iterator outer = avail_threads.begin();
	     outer != avail_threads.end();
	     outer++) {
		std::set<ThreadId>::const_iterator inner(outer);
		inner++;
		while (inner != avail_threads.end()) {
			enumReducedExpressions(expr,
					       &timestamps[*outer],
					       &timestamps[*inner],
					       output);
			inner++;
		}
	}
}

static void
generateCSCandidates(Expression *expr, std::set<CSCandidate> *output)
{
	/* First phase is to produce a simplified version of the
	   expression, most importantly by reducing the number of
	   memory accesses which we have to think about.  We start by
	   just using the last two accesses in every thread, and then
	   work back from there if that doesn't work. */

	Expression *noAliasExpr = expr->concretise();

	CollectTimestampsVisitor v;
	noAliasExpr->visit(v);

	std::set<ThreadId> avail_threads;
	for (gc_map<ThreadId, std::vector<EventTimestamp> >::iterator it = v.timestamps->begin();
	     it != v.timestamps->end();
	     it++) {
		std::sort(it.value().begin(), it.value().end());
		std::vector<EventTimestamp>::iterator vit = std::unique(it.value().begin(), it.value().end());
		it.value().resize(vit - it.value().begin());
		avail_threads.insert(it.key());
	}
	enumReducedExpressions(noAliasExpr, avail_threads, *v.timestamps, output);
}

/* Refinement believes that if we could make @expr false then we'd
   avoid the crash.  Investigate ways of doing so. */
void
considerPotentialFixes(Expression *expr)
{
	printf("Consider fixing from %s\n", expr->name());

	std::set<CSCandidate> candidates;
	generateCSCandidates(expr, &candidates);
	for (std::set<CSCandidate>::iterator it = candidates.begin();
	     it != candidates.end();
	     it++) {
		printf("Candidate: %d:%lx@%lx->%lx@%lx;%d:%lx@%lx->%lx@%lx\n",
		       it->tid1start.tid._tid(), it->tid1start.idx, it->tid1start.rip,
		       it->tid1end.idx, it->tid1end.rip,
		       it->tid2start.tid._tid(), it->tid2start.idx, it->tid2start.rip,
		       it->tid2end.idx, it->tid2end.rip);
	}
}
