#include "sli.h"
#include "enforce_crash.hpp"

expressionStashMapT::expressionStashMapT(const SummaryId &summary,
					 std::set<const IRExpr *> &neededExpressions,
					 ThreadAbstracter &abs,
					 crashEnforcementRoots &roots)
{
	for (auto it = neededExpressions.begin();
	     it != neededExpressions.end();
	     it++) {
		auto e = *it;
		if (e->tag == Iex_Get) {
			auto ieg = (const IRExprGet *)e;
			for (auto it2 = roots.begin(ConcreteThread(summary, ieg->reg.tid())); !it2.finished(); it2.advance()) {
				(*this)[it2.threadCfgLabel()].insert(ieg);
			}
		} else if (e->tag == Iex_HappensBefore) {
			/* These don't really get stashed in any useful sense */
		} else if (e->tag == Iex_EntryPoint) {
			/* These are always stashed at every entry
			 * point node of the relevant thread. */
			auto ep = (const IRExprEntryPoint *)e;
			ConcreteThread ct(summary, ep->thread);
			for (auto it = roots.begin(ct); !it.finished(); it.advance()) {
				(*this)[it.threadCfgLabel()].insert(ep);
			}
		} else if (e->tag == Iex_ControlFlow) {
			/* These are always stashed at the first
			 * nominated node. */
			auto ep = (const IRExprControlFlow *)e;
			for (auto it = abs.begin(ConcreteThread(summary, ep->thread), ep->cfg1); !it.finished(); it.advance())
				(*this)[it.get()].insert(ep);
		} else {
			abort();
		}
	}
}
