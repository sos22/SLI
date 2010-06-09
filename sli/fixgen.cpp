#include <list>

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

	std::list<EventTimestamp> avail_timestamps;
	for (std::map<ThreadId, std::list<EventTimestamp> >::iterator it = v.timestamps.begin();
	     it != v.timestamps.end();
	     it++) {
		it->second.sort();
		it->second.unique();
		if (it->second.size() > 0)
			avail_timestamps.push_back(rindex<std::list<EventTimestamp>, EventTimestamp>(it->second, 0));
		if (it->second.size() > 1)
			avail_timestamps.push_back(rindex<std::list<EventTimestamp>, EventTimestamp>(it->second, 1));
	}

	printf("Consider timestamps:\n");
	for (std::list<EventTimestamp>::iterator it = avail_timestamps.begin();
	     it != avail_timestamps.end();
	     it++)
		printf("\t%d:%lx\n", it->tid._tid(), it->idx);
}
