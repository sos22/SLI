#include <list>
#include <set>

#include "sli.h"

class CollectTimestampsVisitor : public ExpressionVisitor {
public:
	std::map<ThreadId, std::list<EventTimestamp> > timestamps;
	void addTimestamp(EventTimestamp ts);
	void visit(Expression *e);
};

void
CollectTimestampsVisitor::addTimestamp(EventTimestamp ts)
{
	timestamps[ts.tid].push_back(ts);
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
		if (!allow(le->when) || !allow(le->store))
			return NULL;
		Expression *val = le->val->map(*this);
		Expression *addr = le->addr->map(*this);
		Expression *sa = le->storeAddr->map(*this);
		if (!val || !addr || !sa)
			return NULL;
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
		else if (l)
			return l;
		else if (r)
			return r;
		else
			return NULL;
	}
	Expression *map(UnaryExpression *ue)
	{
		Expression *l = ue->l->map(*this);
		if (l)
			return ue->semiDupe(l);
		else
			return NULL;
	}
	Expression *map(ternarycondition *tc)
	{
		Expression *c = tc->cond->map(*this),
			*t = tc->t->map(*this),
			*f = tc->f->map(*this);
		if (!t)
			return f;
		if (!f)
			return t;
		if (!c)
			return NULL;
		return ternarycondition::get(c, t, f);
	}
	Expression *map(ExpressionRip *er)
	{
		Expression *a = ExpressionMapper::map(er);
		ExpressionRip *a2 = dynamic_cast<ExpressionRip *>(a);
		assert(a2);
		if (!a2->cond)
			return NULL;
		else
			return ExpressionRip::get(a2->tid,
						  removeNullConditionsHist(a2->history),
						  a2->cond,
						  a2->model_execution,
						  a2->model_exec_start);
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

static Expression *
convertToCNF(Expression *e)
{
	if (bitwiseand *ba = dynamic_cast<bitwiseand *>(e)) {
		return bitwiseand::get(convertToCNF(ba->l),
				       convertToCNF(ba->r));
	} else if (bitwiseor *bo = dynamic_cast<bitwiseor *>(e)) {
		if (bitwiseand *bal = dynamic_cast<bitwiseand *>(bo->l)) {
			return convertToCNF(
				bitwiseand::get(
					bitwiseor::get(bal->l, bo->r),
					bitwiseor::get(bal->r, bo->r)));
		} else if (bitwiseand *bar = dynamic_cast<bitwiseand *>(bo->r)) {
			return convertToCNF(
				bitwiseand::get(
					bitwiseor::get(bo->l, bar->l),
					bitwiseor::get(bo->l, bar->r)));
		} else {
			Expression *lc = convertToCNF(bo->l);
			Expression *rc = convertToCNF(bo->l);
			if (lc == rc)
				return e;
			else
				return convertToCNF(bitwiseor::get(lc, rc));
		}
	} else if (bitwisenot *bn = dynamic_cast<bitwisenot *>(e)) {
		if (bitwiseand *ba = dynamic_cast<bitwiseand *>(bn->l))
			return convertToCNF(bitwiseor::get(bitwisenot::get(ba->l),
							   bitwisenot::get(ba->r)));
		else if (bitwiseor *bo = dynamic_cast<bitwiseor *>(bn->l))
			return convertToCNF(bitwiseand::get(bitwisenot::get(bo->l),
							    bitwisenot::get(bo->r)));
		else
			return e;
	} else {
		return e;
	}
}

static Expression *
simplifyLogic(Expression *e)
{
	if (bitwiseand *ba = dynamic_cast<bitwiseand *>(e)) {
		if (ConstExpression *e = dynamic_cast<ConstExpression *>(ba->l)) {
			if (e->v)
				return simplifyLogic(ba->r);
			else
				return ba->l;
		}
		if (ConstExpression *e = dynamic_cast<ConstExpression *>(ba->r)) {
			if (e->v)
				return simplifyLogic(ba->l);
			else
				return ba->r;
		}
		return bitwiseand::get(simplifyLogic(ba->l),
				       simplifyLogic(ba->r));
	}
	if (bitwiseor *ba = dynamic_cast<bitwiseor *>(e)) {
		if (ConstExpression *e = dynamic_cast<ConstExpression *>(ba->l)) {
			if (e->v)
				return ba->l;
			else
				return simplifyLogic(ba->r);
		}
		if (ConstExpression *e = dynamic_cast<ConstExpression *>(ba->r)) {
			if (e->v)
				return ba->r;
			else
				return simplifyLogic(ba->l);
		}
		return bitwiseor::get(simplifyLogic(ba->l),
				      simplifyLogic(ba->r));
	}
	if (bitwisenot *bn = dynamic_cast<bitwisenot *>(e)) {
		if (ExpressionHappensBefore *ehb = dynamic_cast<ExpressionHappensBefore *>(bn->l))
			return ExpressionHappensBefore::get(ehb->after, ehb->before);
	}
	return e;
}

class CSCandidate {
public:
	ThreadId tid1;
	unsigned long tid1start;
	unsigned long tid1end;
	ThreadId tid2;
	unsigned long tid2start;
	unsigned long tid2end;

	CSCandidate() {}
	CSCandidate(ThreadId _tid1,
		    unsigned long _t1start,
		    unsigned long _t1end,
		    ThreadId _tid2,
		    unsigned long _t2start,
		    unsigned long _t2end)
		: tid1(_tid1),
		  tid1start(_t1start),
		  tid1end(_t1end),
		  tid2(_tid2),
		  tid2start(_t2start),
		  tid2end(_t2end)
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
	F(tid1);
	F(tid1start);
	F(tid1end);
	F(tid2);
	F(tid2start);
	F(tid2end);
#undef F
	return false;
}

static void
generateCSCandidates(ExpressionHappensBefore *ehb,
		     std::set<CSCandidate> *output,
		     const std::set<Expression *> &assumptions)
{
	CSCandidate work;

	for (std::set<Expression *>::iterator it = assumptions.begin();
	     it != assumptions.end();
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
			work.tid1 = W.tid;
			work.tid1start = min<unsigned long>(W.idx,X.idx);
			work.tid1end = max<unsigned long>(W.idx,X.idx);
			work.tid2 = Y.tid;
			work.tid2start = min<unsigned long>(Y.idx, Z.idx);
			work.tid2end = max<unsigned long>(Y.idx, Z.idx);
		} else if (W.tid == Y.tid && X.tid == Z.tid) {
			work.tid1 = W.tid;
			work.tid1start = min<unsigned long>(W.idx,Y.idx);
			work.tid1end = max<unsigned long>(W.idx,Y.idx);
			work.tid2 = Y.tid;
			work.tid2start = min<unsigned long>(X.idx, Z.idx);
			work.tid2end = max<unsigned long>(X.idx, Z.idx);
		} else if (W.tid == Z.tid && X.tid == Y.tid) {
			work.tid1 = W.tid;
			work.tid1start = min<unsigned long>(W.idx,Z.idx);
			work.tid1end = max<unsigned long>(W.idx,Z.idx);
			work.tid2 = Y.tid;
			work.tid2start = min<unsigned long>(X.idx, Y.idx);
			work.tid2end = max<unsigned long>(X.idx, Y.idx);
		} else
			continue;

		if (work.tid1 == work.tid2)
			continue;

		output->insert(work);
	}
}

static void
generateCSCandidates(Expression *e, std::set<CSCandidate> *output, const std::set<Expression *> &assumptions)
{
	if (ExpressionHappensBefore *ehb = dynamic_cast<ExpressionHappensBefore *>(e)) {
		generateCSCandidates(ehb, output, assumptions);
	} else if (bitwiseand *ba = dynamic_cast<bitwiseand *>(e)) {
		generateCSCandidates(ba->l, output, assumptions);
		generateCSCandidates(ba->r, output, assumptions);
	} else if (bitwiseor *bo = dynamic_cast<bitwiseor *>(e)) {
		std::set<CSCandidate> l, r;
		generateCSCandidates(bo->l, &l, assumptions);
		generateCSCandidates(bo->r, &r, assumptions);
		for (std::set<CSCandidate>::iterator it = l.begin();
		     it != l.end();
		     it++) 
			if (r.count(*it))
				output->insert(*it);
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

	CollectTimestampsVisitor v;
	expr->visit(v);

	std::set<EventTimestamp> avail_timestamps;
	for (std::map<ThreadId, std::list<EventTimestamp> >::iterator it = v.timestamps.begin();
	     it != v.timestamps.end();
	     it++) {
		it->second.sort();
		it->second.unique();
		if (it->second.size() > 0)
			avail_timestamps.insert(rindex<std::list<EventTimestamp>, EventTimestamp>(it->second, 0));
		if (it->second.size() > 1)
			avail_timestamps.insert(rindex<std::list<EventTimestamp>, EventTimestamp>(it->second, 1));
	}

	/* Now remove all bits of the expression which mention a
	   timestamp other than the one which we're interested in. */
	RemoveEventsMapper mapper(avail_timestamps);
	Expression *simplified = expr->map(mapper);
	printf("Simplified expression %s\n", simplified->name());

	/* We now strip the outer layers of rip expression, turning
	   them into assumptions which will be available during
	   critical section derivation. */
	std::set<Expression *> assumptions;
	while (ExpressionRip *er = dynamic_cast<ExpressionRip *>(simplified)) {
		for (History *h = er->history; h; h = h->parent) {
			Expression *e = simplifyLogic(convertToCNF(h->condition));
			printf("Assumption %s\n", e->name());
			assumptions.insert(e);
		}
		simplified = er->cond;
	}

	simplified = simplifyLogic(convertToCNF(simplified));
	printf("Stripped simplified: %s\n", simplified->name());

	/* We now suspect that if all the assumptions are satisfied
	   and @simplified is true then we'll crash in the observed
	   way. */
	generateCSCandidates(simplified, output, assumptions);
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
		printf("Candidate: %d:%lx->%lx;%d:%lx->%lx\n",
		       it->tid1._tid(), it->tid1start, it->tid1end,
		       it->tid2._tid(), it->tid2start, it->tid2end);
	}
}
