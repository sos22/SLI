#include "sli.h"
#include "enforce_crash.hpp"

expressionStashMapT::expressionStashMapT(std::set<IRExpr *> &neededExpressions,
					 ThreadAbstracter &abs,
					 StateMachine *probeMachine,
					 StateMachine *storeMachine,
					 crashEnforcementRoots &roots,
					 const MaiMap &mai)
{
	/* XXX keep this in sync with buildCED */
	std::set<IRExprGet *> neededTemporaries;
	for (auto it = neededExpressions.begin();
	     it != neededExpressions.end();
	     it++) {
		IRExpr *e = *it;
		if (e->tag == Iex_Get) {
			IRExprGet *ieg = (IRExprGet *)e;
			if (ieg->reg.isReg()) {
				for (auto it2 = roots.begin(ieg->reg.tid()); !it2.finished(); it2.advance())
					(*this)[it2.get()].insert(ieg);
			} else {
				neededTemporaries.insert(ieg);
			}
		} else if (e->tag == Iex_HappensBefore) {
			/* These don't really get stashed in any useful sense */
		} else {
			abort();
		}
	}
	if (!neededTemporaries.empty()) {
		std::set<StateMachineSideEffectLoad *> loads;
		enumSideEffects(probeMachine, loads);
		enumSideEffects(storeMachine, loads);
		for (auto it = neededTemporaries.begin();
		     it != neededTemporaries.end();
		     it++) {
			StateMachineSideEffectLoad *l = NULL;
			for (auto it2 = loads.begin(); it2 != loads.end(); it2++) {
				if ( (*it2)->target == (*it)->reg ) {
					assert(!l);
					l = *it2;
				}
			}
			assert(l);
			for (auto it2 = abs.begin(mai, l->rip); !it2.finished(); it2.advance())
				(*this)[it2.get()].insert(*it);
		}
	}
}
