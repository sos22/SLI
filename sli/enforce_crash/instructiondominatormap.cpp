#include "sli.h"
#include "enforce_crash.hpp"

class cfgRootSetT : public std::set<Instruction<ThreadCfgLabel> *> {
public:
	cfgRootSetT(ThreadCfgDecode &cfg, predecessorMapT &pred);
};
cfgRootSetT::cfgRootSetT(ThreadCfgDecode &cfg, predecessorMapT &pred)
{
	std::set<Instruction<ThreadCfgLabel> *> toEmit;
	for (auto it = cfg.begin();
	     it != cfg.end();
	     it++)
		if (it.value())
			toEmit.insert(it.value());
	while (!toEmit.empty()) {
		/* Find one with no predecessors and emit that */
		auto it = toEmit.begin();
		for ( ; it != toEmit.end(); it++) {
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

		auto *next = *it;

		/* We're going to use *it as a root.  Purge it and
		   everything reachable from it from the toEmit
		   set. */
		std::vector<Instruction<ThreadCfgLabel> *> toPurge;
		std::set<Instruction<ThreadCfgLabel> *> donePurge;
		toPurge.push_back(*it);
		while (!toPurge.empty()) {
			auto purge = toPurge.back();
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
				for (auto it = purge->successors.begin();
				     it != purge->successors.end();
				     it++)
					if (it->instr)
						toPurge.push_back(it->instr);
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

instructionDominatorMapT::instructionDominatorMapT(ThreadCfgDecode &cfg,
						   predecessorMapT &predecessors,
						   happensAfterMapT &happensAfter,
						   const std::set<ThreadCfgLabel> &neededRips)
{
	std::set<Instruction<ThreadCfgLabel> *> neededInstructions;
	for (auto it = cfg.begin();
	     it != cfg.end();
	     it++) {
		assert(it.value());
		neededInstructions.insert(it.value());
	}

	/* Start by assuming that everything dominates everything */
	cfgRootSetT entryPoints(cfg, predecessors);
	std::set<Instruction<ThreadCfgLabel> *> needingRecompute;
	std::set<Instruction<ThreadCfgLabel> *> empty;
	for (auto it = cfg.begin();
	     it != cfg.end();
	     it++) {
		if (!it.value())
			continue;
		insert(std::pair<Instruction<ThreadCfgLabel> *, std::set<Instruction<ThreadCfgLabel> *> >(
			       it.value(),
			       empty));
		needingRecompute.insert(it.value());
	}

	/* Now iterate to a fixed point. */
	while (!needingRecompute.empty()) {
		Instruction<ThreadCfgLabel> *i;
		{
			auto it = needingRecompute.begin();
			i = *it;
			needingRecompute.erase(it);
		}

		assert(i);

		std::set<Instruction<ThreadCfgLabel> *> &slot( (*this)[i] );

		/* new entry domination set is intersection of all of
		 * the predecessors' exit sets.  If there are no
		 * predecessor sets then the entry domination set is
		 * empty. */
		std::set<Instruction<ThreadCfgLabel> *> newDominators;
		std::set<Instruction<ThreadCfgLabel> *> &allPreds(predecessors[i]);
		if (!allPreds.empty()) {
			auto predIt = allPreds.begin();
			assert(count(*predIt));
			newDominators = (*this)[*predIt];
			for (predIt++ ; predIt != allPreds.end(); predIt++) {
				auto predecessor = *predIt;
				assert(count(predecessor));
				std::set<Instruction<ThreadCfgLabel> *> &pred_dominators((*this)[predecessor]);
				for (auto it2 = newDominators.begin();
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
		std::set<Instruction<ThreadCfgLabel> *> &orderedBefore(happensAfter.happensBefore[i]);
		for (auto it = orderedBefore.begin();
		     it != orderedBefore.end();
		     it++) {
			std::set<Instruction<ThreadCfgLabel> *> &predecessor_dominates( (*this)[*it] );
			for (auto it2 = predecessor_dominates.begin();
			     it2 != predecessor_dominates.end();
			     it2++)
				newDominators.insert(*it2);
		}

		if (newDominators != slot) {
			slot = newDominators;
			for (auto it = i->successors.begin(); it != i->successors.end(); it++)
				if (it->instr)
					needingRecompute.insert(it->instr);
			if (happensAfter.happensAfter.count(i)) {
				std::set<Instruction<ThreadCfgLabel> *> &orderedAfter(happensAfter.happensAfter[i]);
				for (auto it = orderedAfter.begin();
				     it != orderedAfter.end();
				     it++) {
					if (*it)
						needingRecompute.insert(*it);
				}
			}
		}
	}

	/* Now filter things back down to the actually interesting
	 * instructions. */
	for (auto it = begin(); it != end(); ) {
		if (!neededRips.count(it->first->rip)) {
			erase(it++);
			continue;
		}
		for (auto it2 = it->second.begin(); it2 != it->second.end(); ) {
			if (!neededRips.count((*it2)->rip)) {
				it->second.erase(it2++);
			} else {
				it2++;
			}
		}
		it++;
	}
#if 0
	printf("Instruction dominator map:\n");
	print(stdout);
#endif
}
