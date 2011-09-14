#include <map>
#include <queue>

#include "sli.h"
#include "offline_analysis.hpp"

namespace _cycle_break {
#if 0
}
#endif

/* A thing which says, for every edge, which edges that edge can reach
 * by control flow.  Slight oddity: we start by only considering paths
 * of length 0, and slowly increase the path length.  That means that
 * we can guarantee to always find the shortest cycles first.  Note
 * that we don't consider that an edgee can reach itself as a length-0
 * path, so the length 0 map is always empty; that's fine, and in fact
 * as desired. */

class reachabilityMap {
public:
	std::map<StateMachineEdge *,
		 std::set<StateMachineEdge *> > content;
	std::vector<StateMachineEdge *> edges;

	void initialise(StateMachine *s) {
		if (!dynamic_cast<StateMachineProxy *>(s->root))
			s->root = new StateMachineProxy(s->origin, s->root);
		std::set<StateMachineEdge *> allEdges;
		findAllEdges(s, allEdges);
		for (auto it = allEdges.begin(); it != allEdges.end(); it++) {
			StateMachineEdge *e = *it;
			std::set<StateMachineEdge *> &contentE(content[e]);
			contentE.clear();
			StateMachineState *s = e->target;
			assert(s);
			if (s->target0())
				contentE.insert(s->target0());
			if (s->target1())
				contentE.insert(s->target1());
		}

		buildEdgeList(s);
	}

	struct extendPathsRes {
		bool finished;
		bool haveCycle;
	};

	void buildEdgeList(StateMachine *);
	extendPathsRes extendPaths();
	void breakCycle();
};

/* We can't use a normal traversal for this, because we care about the
   order in which we discover edges (which must be breadth-first). */
void
reachabilityMap::buildEdgeList(StateMachine *s)
{
	std::queue<StateMachineEdge *> q;

	/* This is just @edges as a set rather than a vector, but
	   that's handy, because we need a fast membership test. */
	std::set<StateMachineEdge *> visited;

	/* Start clean */
	edges.clear();

	assert(dynamic_cast<StateMachineProxy *>(s->root));
	q.push(((StateMachineProxy *)s->root)->target);
	while (!q.empty()) {
		StateMachineEdge *e = q.front();
		q.pop();
		if (visited.count(e))
			continue;
		visited.insert(e);

		edges.push_back(e);
		StateMachineState *s = e->target;
		assert(s);

		if (s->target0())
			q.push(s->target0());
		if (s->target1())
			q.push(s->target1());
	}
}

reachabilityMap::extendPathsRes
reachabilityMap::extendPaths(void)
{
	bool progress;
	bool haveCycle;

	std::map<StateMachineEdge *, std::set<StateMachineEdge *> > newContent(content);
	progress = false;
	haveCycle = false;
	for (auto it = newContent.begin(); it != newContent.end(); it++) {
		StateMachineEdge *e = it->first;
		std::set<StateMachineEdge *> &reachableByUs(it->second);

		struct {
			void operator()(reachabilityMap *_this,
					std::set<StateMachineEdge *> &reachableByUs,
					StateMachineEdge *src,
					StateMachineEdge *dest,
					bool &haveCycle,
					bool &progress) {
				std::set<StateMachineEdge *> &reachableByDest(_this->content[dest]);
				for (auto it2 = reachableByDest.begin();
				     it2 != reachableByDest.end();
				     it2++) {
					if (*it2 == src)
						haveCycle = true;
					if (!reachableByUs.count(*it2))
						progress = true;
					reachableByUs.insert(*it2);
				}
			}
		} doEdge;
		assert(e->target);
		StateMachineState *s = e->target;
		if (s->target0())
			doEdge(this, reachableByUs, e, s->target0(), haveCycle,
			       progress);
		if (s->target1())
			doEdge(this, reachableByUs, e, s->target1(), haveCycle,
			       progress);
	}

	content = newContent;

	extendPathsRes res;

	res.haveCycle = haveCycle;
	res.finished = !progress;

	return res;
}

void
reachabilityMap::breakCycle(void)
{
	for (auto it = edges.rbegin(); it != edges.rend(); it++) {
		StateMachineEdge *e = *it;
		if (content[e].count(e)) {
			/* This edge can reach itself, and is
			   therefore part of a cycle.  Furthermore, we
			   know that it's in some sense the last thing
			   in the cycle because we process edges in
			   reverse-breadth-first order (i.e. with
			   those furthest from the root considered
			   first).  It is therefore a good choice for
			   a cycle breaking edge. */
			e->target = StateMachineUnreached::get();

			/* Only want to break one cycle on each
			   iteration, as otherwise the various maps
			   will be wrong. */
			return;
		}
	}

	/* We should only be called if there are cycles to break. */
	abort();
}

static void
breakCycles(StateMachine *inp)
{
	reachabilityMap reach;

	reach.initialise(inp);
	while (1) {
		auto r = reach.extendPaths();
		if (r.finished)
			break;
		if (!r.haveCycle)
			continue;

		reach.breakCycle();

		/* We've modified the graph; start again. */
		reach.initialise(inp);
	}
}

/* End of namespace */
}

void
breakCycles(StateMachine *inp)
{
	_cycle_break::breakCycles(inp);
}
