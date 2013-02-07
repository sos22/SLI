#include "sli.h"
#include "enforce_crash.hpp"

expressionStashMapT::expressionStashMapT(const SummaryId &summary,
					 std::set<input_expression> &neededExpressions,
					 ThreadAbstracter &abs,
					 crashEnforcementRoots &roots)
{
	for (auto it = neededExpressions.begin();
	     it != neededExpressions.end();
	     it++) {
		auto e = *it;
		if (e.unwrap()->tag == Iex_Get) {
			auto ieg = (const IRExprGet *)e.unwrap();
			for (auto it2 = roots.begin(ConcreteThread(summary, ieg->reg.tid())); !it2.finished(); it2.advance()) {
				(*this)[it2.threadCfgLabel()].insert(e);
			}
		} else if (e.unwrap()->tag == Iex_HappensBefore) {
			/* These don't really get stashed in any useful sense */
		} else if (e.unwrap()->tag == Iex_EntryPoint) {
			/* These are always stashed at every entry
			 * point node of the relevant thread. */
			auto ep = (const IRExprEntryPoint *)e.unwrap();
			ConcreteThread ct(summary, ep->thread);
			for (auto it = roots.begin(ct); !it.finished(); it.advance()) {
				(*this)[it.threadCfgLabel()].insert(e);
			}
		} else if (e.unwrap()->tag == Iex_ControlFlow) {
			/* These are always stashed at the first
			 * nominated node. */
			auto ep = (const IRExprControlFlow *)e.unwrap();
			for (auto it = abs.begin(ConcreteThread(summary, ep->thread), ep->cfg1); !it.finished(); it.advance())
				(*this)[it.get()].insert(e);
		} else {
			abort();
		}
	}
}
