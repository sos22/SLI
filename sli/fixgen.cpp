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
		if (!hs->condition)
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

/* Refinement believes that if we could make @expr false then we'd
   avoid the crash.  Investigate ways of doing so. */
void
considerPotentialFixes(Expression *expr)
{
	printf("Consider fixing from %s\n", expr->name());

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

	printf("Consider timestamps:\n");
	for (std::set<EventTimestamp>::iterator it = avail_timestamps.begin();
	     it != avail_timestamps.end();
	     it++)
		printf("\t%d:%lx\n", it->tid._tid(), it->idx);

	/* Now remove all bits of the expression which mention a
	   timestamp other than the one which we're interested in. */
	RemoveEventsMapper mapper(avail_timestamps);
	Expression *simplified = expr->map(mapper);
	printf("Simplified expression %s\n", simplified->name());
}
