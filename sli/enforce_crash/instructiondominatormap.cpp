#include "sli.h"
#include "enforce_crash.hpp"

class cfgRootSetT : public std::set<Instruction<ThreadRip> *> {
public:
	cfgRootSetT(CFG<ThreadRip> *cfg, predecessorMapT &pred, happensAfterMapT &happensAfter);
};
cfgRootSetT::cfgRootSetT(CFG<ThreadRip> *cfg, predecessorMapT &pred, happensAfterMapT &happensBefore)
{
	std::set<Instruction<ThreadRip> *> toEmit;
	for (CFG<ThreadRip>::ripToInstrT::iterator it = cfg->ripToInstr->begin();
	     it != cfg->ripToInstr->end();
	     it++)
		toEmit.insert(it.value());
	while (!toEmit.empty()) {
		/* Find one with no predecessors and emit that */
		std::set<Instruction<ThreadRip> *>::iterator it;
		for (it = toEmit.begin(); it != toEmit.end(); it++) {
			assert(pred.count(*it));
			if (pred[*it].size() == 0)
				break;
		}
		if (it == toEmit.end()) {
			/* Every instruction is part of a cycle.
			   Arbitrarily declare that the first one is
			   the root and emit that. */
			it = toEmit.begin();
			assert(it != toEmit.end());
		}

		Instruction<ThreadRip> *next = *it;

		/* We're going to use *it as a root.  Purge it and
		   everything reachable from it from the toEmit
		   set. */
		std::vector<Instruction<ThreadRip> *> toPurge;
		std::set<Instruction<ThreadRip> *> donePurge;
		toPurge.push_back(*it);
		while (!toPurge.empty()) {
			Instruction<ThreadRip> *purge = toPurge.back();
			toPurge.pop_back();
			if (donePurge.count(purge))
				continue;
			/* The loop breaking heuristic, above, isn't
			   terribly clever, and can sometimes choose a
			   bad node in a way which leads to one root
			   being reachable from another.  Fortunately,
			   it's easy to fix by just purging the
			   pseudo-root here. */
			erase(purge);

			toEmit.erase(purge);
			if (toEmit.count(purge)) {
				if (purge->branchNextI)
					toPurge.push_back(purge->branchNextI);
				if (purge->defaultNextI)
					toPurge.push_back(purge->defaultNextI);
			}
			donePurge.insert(purge);
		}

		/* Emit the new root.  This has to happen after the
		   loop above so that it doesn't immediately get
		   purged again, and we have to stash it in a
		   temporary because the changes to toEmit in the loop
		   would invalidate the iterator. */
		insert(next);
	}
}

instructionDominatorMapT::instructionDominatorMapT(CFG<ThreadRip> *cfg,
						   predecessorMapT &predecessors,
						   happensAfterMapT &happensAfter,
						   const std::set<ThreadRip> &neededRips)
{
	std::set<Instruction<ThreadRip> *> neededInstructions;
	for (std::set<ThreadRip>::const_iterator it = neededRips.begin();
	     it != neededRips.end();
	     it++)
		neededInstructions.insert(cfg->ripToInstr->get(*it));

	/* Start by assuming that everything dominates everything */
	cfgRootSetT entryPoints(cfg, predecessors, happensAfter);
	std::set<Instruction<ThreadRip> *> needingRecompute;
	for (CFG<ThreadRip>::ripToInstrT::iterator it = cfg->ripToInstr->begin();
	     it != cfg->ripToInstr->end();
	     it++) {
		insert(std::pair<Instruction<ThreadRip> *, std::set<Instruction<ThreadRip> *> >(
			       it.value(),
			       neededInstructions));
		needingRecompute.insert(it.value());
	}

	/* Now iterate to a fixed point. */
	while (!needingRecompute.empty()) {
		Instruction<ThreadRip> *i;
		{
			std::set<Instruction<ThreadRip> *>::iterator it = needingRecompute.begin();
			i = *it;
			needingRecompute.erase(it);
		}

		std::set<Instruction<ThreadRip> *> &slot( (*this)[i] );

		/* new entry domination set is intersection of all of
		 * the predecessor's exit sets.  If there are no
		 * predecessor sets then the entry domination set is
		 * empty. */
		std::set<Instruction<ThreadRip> *> newDominators;
		std::set<Instruction<ThreadRip> *> &allPreds(predecessors[i]);
		if (!allPreds.empty()) {
			newDominators = slot;

			for (std::set<Instruction<ThreadRip> *>::iterator predIt = allPreds.begin();
			     predIt != allPreds.end();
			     predIt++) {
				Instruction<ThreadRip> *predecessor = *predIt;
				assert(count(predecessor));
				std::set<Instruction<ThreadRip> *> &pred_dominators((*this)[predecessor]);
				for (std::set<Instruction<ThreadRip> *>::iterator it2 = newDominators.begin();
				     it2 != newDominators.end();
					) {
					if (pred_dominators.count(*it2)) {
						it2++;
					} else {
						/* *it2 is dominated
						   by us, but not by
						   our predecessor.
						   That's a
						   contradiction.
						   Resolve it by
						   erasing *it2 from
						   our dominator
						   set. */
						newDominators.erase(it2++);
					}
				}
			}
		}

		/* Every instruction dominates itself. */
		if (neededInstructions.count(i))
			newDominators.insert(i);

		/* Anything dominated by something which is ordered
		   before us is also dominated by us.  Happens-before
		   edges are different to ordinary edges, because
		   happens-before edges are always satisfied, whereas
		   for ordinary control edges only one per instruction
		   will be satisfied. */
		std::set<Instruction<ThreadRip> *> &orderedBefore(happensAfter.happensBefore[i]);
		for (std::set<Instruction<ThreadRip> *>::iterator it = orderedBefore.begin();
		     it != orderedBefore.end();
		     it++) {
			std::set<Instruction<ThreadRip> *> &predecessor_dominates( (*this)[*it] );
			for (std::set<Instruction<ThreadRip> *>::iterator it2 = predecessor_dominates.begin();
			     it2 != predecessor_dominates.end();
			     it2++)
				newDominators.insert(*it2);
		}

		if (newDominators != slot) {
			slot = newDominators;
			if (i->branchNextI)
				needingRecompute.insert(i->branchNextI);
			if (i->defaultNextI)
				needingRecompute.insert(i->defaultNextI);
			if (happensAfter.happensAfter.count(i)) {
				std::set<Instruction<ThreadRip> *> &orderedAfter(happensAfter.happensAfter[i]);
				for (std::set<Instruction<ThreadRip> *>::iterator it = orderedAfter.begin();
				     it != orderedAfter.end();
				     it++)
					needingRecompute.insert(*it);
			}
		}
	}
}
