#include "sli.h"
#include "enforce_crash.hpp"

expressionStashMapT::expressionStashMapT(const SummaryId &summary,
					 const std::set<input_expression> &neededExpressions,
					 ThreadAbstracter &abs,
					 crashEnforcementRoots &roots)
{
	for (auto it = neededExpressions.begin();
	     it != neededExpressions.end();
	     it++) {
		switch (it->tag) {
		case input_expression::inp_register:
			for (auto it2 = roots.begin(ConcreteThread(summary, it->thread));
			     !it2.finished();
			     it2.advance()) {
				(*this)[it2.threadCfgLabel()].insert(*it);
			}
			break;
		case input_expression::inp_happens_before: 
			/* These don't really get stashed in any useful sense */
			break;
		case input_expression::inp_entry_point:
			/* These are always stashed at every entry
			 * point node of the relevant thread. */
			for (auto it2 = roots.begin(ConcreteThread(summary, it->thread));
			     !it2.finished();
			     it2.advance()) {
				(*this)[it2.threadCfgLabel()].insert(*it);
			}
			break;
		case input_expression::inp_control_flow:
			/* These are always stashed at the first
			 * nominated node. */
			for (auto it2 = abs.begin(ConcreteThread(summary, it->thread), it->label1);
			     !it2.finished();
			     it2.advance()) {
				(*this)[it2.get()].insert(*it);
			}
			break;
		}
	}
}
