#include <map>
#include <vector>

#include "sli.h"
#include "simplify_ordering.hpp"
#include "state_machine.hpp"

bool operator<(const IRExpr::HappensBefore &a, const IRExpr::HappensBefore &b)
{
	if (a.before < b.before)
		return true;
	else if (a.before > b.before)
		return false;
	else
		return a.after < b.after;
}

class canonMemAccessT : public std::map<ThreadRip, unsigned> {
public:
	unsigned next_idx;
	canonMemAccessT()
		: std::map<ThreadRip, unsigned>(),
		  next_idx(0)
	{}
	void addEvent(ThreadRip evt)
	{
		if (!count(evt))
			(*this)[evt] = next_idx++;
	}
	void addEdge(IRExpr::HappensBefore hb)
	{
		addEvent(hb.before);
		addEvent(hb.after);
	}
	void addEdges(const std::set<IRExpr::HappensBefore> &e)
	{
		for (std::set<IRExpr::HappensBefore>::const_iterator it = e.begin();
		     it != e.end();
		     it++)
			addEdge(*it);
	}

	ThreadRip inverse_lookup(unsigned x) const {
		for (const_iterator it = begin();
		     it != end();
		     it++)
			if (it->second == x)
				return it->first;
		abort();
	}
	void print(FILE *f) const
	{
		for (const_iterator it = begin();
		     it != end();
		     it++) {
			fprintf(f, "%d:%lx\t\t%d\n", it->first.thread, it->first.rip, it->second);
		}
	}
};

class denseRelationshipT : public std::vector<std::vector<bool> > {
public:
	denseRelationshipT(unsigned size)
		: std::vector<std::vector<bool> >()
	{
		resize(size);
		for (unsigned x = 0; x < size; x++) {
			(*this)[x].resize(size);
		}
	}
	bool related(unsigned a, unsigned b) const {
		return (*this)[a][b];
	}
	void set_related(unsigned a, unsigned b) {
		(*this)[a][b] = true;
	}
	void clear_related(unsigned a, unsigned b) {
		(*this)[a][b] = false;
	}
	void transitiveClosure();
	bool cyclic() const; /* Only valid after taking transitive
			      * closure */

	denseRelationshipT operator~() const {
		denseRelationshipT res(size());
		for (unsigned x = 0; x < size(); x++)
			for (unsigned y = 0; y < size(); y++)
				res[x][y] = !(*this)[x][y];
		return res;
	}
	void operator &=(const denseRelationshipT &o) {
		assert(o.size() == size());
		for (unsigned x = 0; x < size(); x++)
			for (unsigned y = 0; y < size(); y++)
				if (!o.related(x, y))
					clear_related(x, y);
	}
	void operator |=(const denseRelationshipT &o) {
		assert(o.size() == size());
		for (unsigned x = 0; x < size(); x++)
			for (unsigned y = 0; y < size(); y++)
				if (o.related(x, y))
					set_related(x, y);
	}
	void print(FILE *) const;
};

void
denseRelationshipT::transitiveClosure(void)
{
	/* Not the most efficient algorithm possible, but this isn't a
	   hot path, so do something easy. */
	bool progress;
	do {
		progress = false;
		for (unsigned x = 0; x < size(); x++) {
			for (unsigned y = 0; y < size(); y++) {
				if (!related(x, y))
					continue;
				for (unsigned z = 0; z < size(); z++) {
					if (related(y, z) && !related(x, z)) {
						set_related(x, z);
						progress = true;
					}
				}
			}
		}
	} while (progress);
}

bool
denseRelationshipT::cyclic() const
{
	for (unsigned x = 0; x < size(); x++)
		for (unsigned y = 0; y < size(); y++)
			if (related(x, y) && related(y, x))
				return true;
	return false;
}

void
denseRelationshipT::print(FILE *f) const
{
	for (unsigned x = 0; x < size(); x++) {
		for (unsigned y = 0; y < size(); y++)
			if (related(x, y))
				fputc('1', f);
			else
				fputc('0', f);
		fputc('\n', f);
	}
}

/* Simplify @relations so that it contains a minimal set of
   happens-before relationships which, when combined with
   @assumptions, is equivalent to the original set. */
bool
simplifyOrdering(std::set<IRExpr::HappensBefore> &relations,
		 const std::set<IRExpr::HappensBefore> &_assumptions)
{
	/* Start by building a mapping from relevant events to
	 * indexes. */
	canonMemAccessT canonMap;
	canonMap.addEdges(relations);
	canonMap.addEdges(_assumptions);

	/* Now build the complete relationship matrix. */
	denseRelationshipT relationship(canonMap.next_idx);
	for (std::set<IRExpr::HappensBefore>::const_iterator it = relations.begin();
	     it != relations.end();
	     it++) {
		relationship.set_related(canonMap[it->before],
					 canonMap[it->after]);
	}
	denseRelationshipT assumptions(canonMap.next_idx);
	for (std::set<IRExpr::HappensBefore>::const_iterator it = _assumptions.begin();
	     it != _assumptions.end();
	     it++) {
		assumptions.set_related(canonMap[it->before],
					canonMap[it->after]);
	}
	relationship |= assumptions;

	/* Take transitive closure. */
	relationship.transitiveClosure();
	/* A cycle is a contradiction, because this is supposed to be
	   a non-reflexive relationship. */
	if (relationship.cyclic()) {
		printf("Cyclic!\n");
		return false;
	}

	/* We now use a modified Floyd-Warshall algorithm to find a
	   (usually) minimal relationship whose transitive closure
	   when union'ed with @assumption is @relationship.  The basic
	   approach is to consider indexes up to N of @relationship,
	   and ensure that that sub-relationship contains no redundant
	   transitive links, and slowly increase N from 0 to the size
	   of the relationship. */
	for (unsigned N = 0; N < relationship.size(); N++) {
		/* Loop invariant: there is no i such that a<-<i<-<b
		   and a<-<b, for i <= N, *unless* a<-<b is present
		   in @assumptions. */
		/* Because the loop invariant held on the previous
		 * iteration, we only need to consider the case where
		 * i == N. */
		for (unsigned a = 0; a < relationship.size(); a++) {
			if (a == N)
				continue;
			for (unsigned b = 0; b < relationship.size(); b++) {
				if (b == N ||
				    !relationship.related(a, b) ||
				    assumptions.related(a, b))
					continue;
				if (relationship.related(a, N) &&
				    relationship.related(N, b))
					relationship.clear_related(a, b);
			}
		}
	}

	/* Subtract out the things which are true because of the
	 * assumptions. */
	relationship &= ~assumptions;

#if 0
	canonMap.print(stdout);
	relationship.print(stdout);
#endif

	/* @relationship should now be a minimal relationship which
	   induces the original relationship under the assumptions in
	   @assumptions.  Translate back. */
	std::set<IRExpr::HappensBefore> out;
	for (unsigned x = 0; x < relationship.size(); x++) {
		for (unsigned y = 0; y < relationship.size(); y++) {
			if (relationship.related(x, y)) {
				IRExpr::HappensBefore hb;
				hb.before = canonMap.inverse_lookup(x);
				hb.after = canonMap.inverse_lookup(y);
				out.insert(hb);
			}
		}
	}

	relations = out;

	return true;
}

static void extractImplicitOrder(StateMachineState *sm,
				 std::vector<ThreadRip> &eventsSoFar,
				 std::set<IRExpr::HappensBefore> &out);
static void
extractImplicitOrder(StateMachineEdge *sme,
		     std::vector<ThreadRip> &eventsSoFar,
		     std::set<IRExpr::HappensBefore> &out)
{
	if (sme->sideEffects.size() == 0) {
		extractImplicitOrder(sme->target, eventsSoFar, out);
		return;
	}

	unsigned startSize = eventsSoFar.size();
	eventsSoFar.reserve(startSize + sme->sideEffects.size());
	for (unsigned x = 0; x < sme->sideEffects.size(); x++) {
		StateMachineSideEffectMemoryAccess *smsema =
			dynamic_cast<StateMachineSideEffectMemoryAccess *>(sme->sideEffects[x]);
		if (!smsema)
			continue;

		for (unsigned y = 0; y < eventsSoFar.size(); y++) {
			IRExpr::HappensBefore hb;
			hb.before = eventsSoFar[y];
			hb.after = smsema->rip;
			out.insert(hb);
		}

		eventsSoFar.push_back(smsema->rip);
	}
	extractImplicitOrder(sme->target, eventsSoFar, out);
	eventsSoFar.resize(startSize);
}

static void
extractImplicitOrder(StateMachineState *sm,
		     std::vector<ThreadRip> &eventsSoFar,
		     std::set<IRExpr::HappensBefore> &out)
{
	if (dynamic_cast<const StateMachineTerminal *>(sm))
		return;
	if (StateMachineProxy *smp =
	    dynamic_cast<StateMachineProxy *>(sm)) {
		extractImplicitOrder(smp->target, eventsSoFar, out);
		return;
	}
	StateMachineBifurcate *smb =
		dynamic_cast<StateMachineBifurcate *>(sm);
	assert(smb);
	extractImplicitOrder(smb->trueTarget, eventsSoFar, out);
	extractImplicitOrder(smb->falseTarget, eventsSoFar, out);
}

/* Walk the state machine and extract all of the happens-before
   relationships which are implied by its internal structure. */
void
extractImplicitOrder(StateMachine *sm, std::set<IRExpr::HappensBefore> &out)
{
	std::vector<ThreadRip> eventsSoFar;
	extractImplicitOrder(sm->root, eventsSoFar, out);
}