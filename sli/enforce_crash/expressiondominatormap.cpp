#include "sli.h"
#include "enforce_crash.hpp"

expressionDominatorMapT::expressionDominatorMapT(DNF_Conjunction &c,
						 expressionStashMapT &stash,
						 instructionDominatorMapT &idom,
						 predecessorMapT &pred,
						 happensAfterMapT &happensBefore)
{
	/* First, figure out where the various expressions could in
	   principle be evaluated. */
	expressionDominatorMapT evalable;
	for (instructionDominatorMapT::iterator it = idom.begin();
	     it != idom.end();
	     it++) {
		evalable[it->first].clear();
		std::set<IRExpr *> availExprs;
		for (auto it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			Instruction<ThreadCfgLabel> *dominating = *it2;
			std::set<IRExpr *> stashed(stash[dominating->rip]);
			for (auto it = stashed.begin();
			     it != stashed.end();
			     it++)
				availExprs.insert(*it);
		}
		for (unsigned x = 0; x < c.size(); x++)
			if (evaluatable(c[x].second, availExprs))
				evalable[it->first].insert(c[x]);
	}

	/* Just find all of the things which are evaluatable at X but
	   not at some of X's predecessors, for any instruction X.  I'm
	   not entirely convinced that that's *precisely* what we're
	   after, but it's a pretty reasonable approximation. */
	for (auto it = evalable.begin();
	     it != evalable.end();
	     it++) {
		auto i = it->first;
		std::set<std::pair<bool, IRExpr *> > &theoreticallyEvaluatable(evalable[i]);
		std::set<std::pair<bool, IRExpr *> > &actuallyEvalHere((*this)[i]);
		std::set<Instruction<ThreadCfgLabel> *> &predecessors(pred[i]);
		std::set<Instruction<ThreadCfgLabel> *> *orderingPredecessors = NULL;

		if (happensBefore.happensBefore.count(i))
			orderingPredecessors = &happensBefore.happensBefore[i];
		for (std::set<std::pair<bool, IRExpr *> >::iterator it2 = theoreticallyEvaluatable.begin();
		     it2 != theoreticallyEvaluatable.end();
		     it2++) {
			bool takeIt = false;
			for (auto it3 = predecessors.begin();
			     !takeIt && it3 != predecessors.end();
			     it3++) {
				auto *predecessor = *it3;
				if (!evalable[predecessor].count(*it2))
					takeIt = true;
			}
			if (predecessors.empty())
				takeIt = true;
			/* If it's evaluatable at *any* happens-before
			   predecessor then we don't want to take it,
			   because happens-before edges are always
			   satisfied and it's therefore certain that
			   it will have already been evaluated. */
			if (takeIt && orderingPredecessors) {
				for (auto it3 = orderingPredecessors->begin();
				     takeIt && it3 != orderingPredecessors->end();
				     it3++) {
					if (evalable[*it3].count(*it2))
						takeIt = false;
				}
			}
			if (takeIt) {
				printf("Eval ");
				ppIRExpr(it2->second, stdout);
				printf(" at %s\n", i->rip.name());
				actuallyEvalHere.insert(*it2);
			}
		}
	}
}

happensAfterMapT::happensAfterMapT(DNF_Conjunction &c, ThreadAbstracter &abs, CrashCfg &cfg, const MaiMap &mai)
{
	for (unsigned x = 0; x < c.size(); x++) {
		if (c[x].second->tag == Iex_HappensBefore) {
			IRExprHappensBefore *e = (IRExprHappensBefore *)c[x].second;
			for (auto before_it = abs.begin(mai, e->before, cfg); !before_it.finished(); before_it.advance()) {
				Instruction<ThreadCfgLabel> *const before = before_it.get();
				if (!before)
					continue;
				for (auto after_it = abs.begin(mai, e->after, cfg); !after_it.finished(); after_it.advance()) {
					auto after = after_it.get();
					if (!after)
						continue;
					if (c[x].first) {
						happensAfter[after].insert(before);
						happensBefore[before].insert(after);
					} else {
						happensAfter[before].insert(after);
						happensBefore[after].insert(before);
					}
				}
			}
		}
	}
}

void
expressionDominatorMapT::prettyPrint(FILE *f) const
{
	for (auto it = begin(); it != end(); it++) {
		fprintf(f, "%s -> {", it->first->label.name());
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			if (it2->first)
				fprintf(f, "!");
			ppIRExpr(it2->second, f);
		}
		fprintf(f, "}\n");
	}
}
