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
	std::map<StateMachineState *,
		 std::set<StateMachineState *> > content;
	std::vector<StateMachineState *> edges;

	struct extendPathsRes {
		bool finished;
		bool haveCycle;
	};

	extendPathsRes initialise(StateMachine *s) {
		extendPathsRes res;
		res.finished = false;
		res.haveCycle = false;
		std::set<StateMachineState *> allStates;
		findAllStates(s, allStates);
		content.clear();
		for (auto it = allStates.begin(); it != allStates.end(); it++) {
			StateMachineState *e = *it;
			std::set<StateMachineState *> &contentE(content[e]);
			contentE.clear();
			e->targets(contentE);
			if (contentE.count(e))
				res.haveCycle = true;
		}

		buildEdgeList(s);

		return res;
	}

	void buildEdgeList(StateMachine *);
	extendPathsRes extendPaths();
	void breakCycle();
};

/* We can't use a normal traversal for this, because we care about the
   order in which we discover edges (which must be breadth-first). */
void
reachabilityMap::buildEdgeList(StateMachine *s)
{
	std::queue<StateMachineState *> q;

	/* This is just @edges as a set rather than a vector, but
	   that's handy, because we need a fast membership test. */
	std::set<StateMachineState *> visited;

	/* Start clean */
	edges.clear();

	q.push(s->root);
	while (!q.empty()) {
		StateMachineState *e = q.front();
		q.pop();
		if (visited.count(e))
			continue;
		visited.insert(e);

		edges.push_back(e);

		e->targets(q);
	}
}

reachabilityMap::extendPathsRes
reachabilityMap::extendPaths(void)
{
	bool progress;
	bool haveCycle;

	std::map<StateMachineState *, std::set<StateMachineState *> > newContent(content);
	progress = false;
	haveCycle = false;
	for (auto it = newContent.begin(); it != newContent.end(); it++) {
		StateMachineState *e = it->first;
		std::set<StateMachineState *> &reachableByUs(it->second);

		struct {
			void operator()(reachabilityMap *_this,
					std::set<StateMachineState *> &reachableByUs,
					StateMachineState *src,
					StateMachineState *dest,
					bool &haveCycle,
					bool &progress) {
				std::set<StateMachineState *> &reachableByDest(_this->content[dest]);
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
		std::vector<StateMachineState *> edges;
		e->targets(edges);
		for (auto it = edges.begin(); it != edges.end(); it++)
			doEdge(this, reachableByUs, e, *it, haveCycle,
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
		StateMachineState *e = *it;
		if (content[e].count(e)) {
			/* This edge can reach itself, and is
			   therefore part of a cycle.  Furthermore, we
			   know that it's in some sense the last thing
			   in the cycle because we process edges in
			   reverse-breadth-first order (i.e. with
			   those furthest from the root considered
			   first).  It is therefore a good choice for
			   a cycle breaking edge. */
			switch (e->type) {
			case StateMachineState::Bifurcate: {
				StateMachineBifurcate *smb = (StateMachineBifurcate *)e;
				smb->trueTarget =
					smb->falseTarget =
					StateMachineUnreached::get();
				break;
			}
			case StateMachineState::SideEffecting: {
				((StateMachineSideEffecting *)e)->target =
					StateMachineUnreached::get();
				break;
			}
			case StateMachineState::Unreached:
			case StateMachineState::Crash:
			case StateMachineState::NoCrash:
			case StateMachineState::Stub:
				/* These can't be part of a cycle, as
				   they have no outgoing edges. */
				abort();
			}

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

	while (1) {
		reachabilityMap::extendPathsRes r = reach.initialise(inp);
		if (TIMEOUT)
			return;
		while (!r.finished && !r.haveCycle)
			r = reach.extendPaths();
		if (r.finished)
			break;

		reach.breakCycle();
	}
}

/* End of namespace */
}

void
breakCycles(StateMachine *inp)
{
	_cycle_break::breakCycles(inp);
}
