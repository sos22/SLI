#include "sli.h"
#include "enforce_crash.hpp"

expressionDominatorMapT::expressionDominatorMapT(DNF_Conjunction &c,
						 CFG<ThreadRip> *cfg,
						 const std::set<ThreadRip> &neededRips)
{
	happensAfterMapT happensBefore(c, cfg);
	predecessorMapT pred(cfg);

	/* Figure out where the various instructions become
	 * available. */
	instructionDominatorMapT idom(cfg, pred, happensBefore, neededRips);
	this->idom = idom;

	/* First, figure out where the various expressions could in
	   principle be evaluated. */
	std::map<Instruction<ThreadRip> *, std::set<std::pair<bool, IRExpr *> > > evalable;
	for (instructionDominatorMapT::iterator it = idom.begin();
	     it != idom.end();
	     it++) {
		evalable[it->first].clear();
		for (unsigned x = 0; x < c.size(); x++) {
			std::set<unsigned> availThreads;
			for (std::set<Instruction<ThreadRip> *>::iterator it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++)
				availThreads.insert((*it2)->rip.thread);
			if (evaluatable(c[x].second, it->second, availThreads, cfg))
				evalable[it->first].insert(c[x]);
		}
	}


	/* Just find all of the things which are evaluatable at X but
	   not at some of X's predecessors, for any instruction X.  I'm
	   not entirely convinced that that's *precisely* what we're
	   after, but it's a pretty reasonable approximation. */
	for (std::map<Instruction<ThreadRip> *, std::set<std::pair<bool, IRExpr *> > >::iterator it = evalable.begin();
	     it != evalable.end();
	     it++) {
		Instruction<ThreadRip> *i = it->first;
		std::set<std::pair<bool, IRExpr *> > &theoreticallyEvaluatable(evalable[i]);
		std::set<std::pair<bool, IRExpr *> > &actuallyEvalHere((*this)[i]);
		std::set<Instruction<ThreadRip> *> &predecessors(pred[i]);
		std::set<Instruction<ThreadRip> *> *orderingPredecessors;

		if (happensBefore.happensBefore.count(i))
			orderingPredecessors = &happensBefore.happensBefore[i];
		for (std::set<std::pair<bool, IRExpr *> >::iterator it2 = theoreticallyEvaluatable.begin();
		     it2 != theoreticallyEvaluatable.end();
		     it2++) {
			bool takeIt = false;
			for (std::set<Instruction<ThreadRip> *>::iterator it3 = predecessors.begin();
			     !takeIt && it3 != predecessors.end();
			     it3++) {
				Instruction<ThreadRip> *predecessor = *it3;
				if (!evalable[predecessor].count(*it2))
					takeIt = true;
			}
			/* If it's evaluatable at *any* happens-before
			   predecessor then we don't want to take it,
			   because happens-before edges are always
			   satisfied and it's therefore certain that
			   it will have already been evaluated. */
			if (takeIt && orderingPredecessors) {
				for (std::set<Instruction<ThreadRip> *>::iterator it3 = orderingPredecessors->begin();
				     takeIt && it3 != orderingPredecessors->end();
				     it3++) {
					if (evalable[*it3].count(*it2))
						takeIt = false;
				}
			}
			if (takeIt) {
				printf("Eval ");
				ppIRExpr(it2->second, stdout);
				printf(" at %d:%lx\n", i->rip.thread, i->rip.rip);
				actuallyEvalHere.insert(*it2);
			}
		}
	}
}
