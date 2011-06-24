/* Something which, given a thread and a snapshot of memory, tries to
   find some instruction which the thread is guaranteed to have
   executed recently (prior to the one which it's executing right now
   :)) */
#include <set>
#include <map>
#include <queue>

#include "sli.h"

struct representative_state {
	RegisterSet regs;
	std::vector<std::pair<unsigned long, unsigned long> > stores;
};

static void
handle_dirty_call(struct representative_state *rs,
		  IRDirty *details,
		  std::vector<expression_result> &temporaries,
		  AddressSpace *as)
{
	if (!strcmp(details->cee->name, "helper_load_64") ||
	    !strcmp(details->cee->name, "helper_load_32") ||
	    !strcmp(details->cee->name, "helper_load_16") ||
	    !strcmp(details->cee->name, "helper_load_8")) {
		unsigned long addr = eval_expression(&rs->regs, details->args[0], temporaries).lo;
		unsigned long res;
		bool have_res;
		have_res = false;
		for (unsigned idx = 0; !have_res && idx < rs->stores.size(); idx++) {
			if (addr == rs->stores[idx].first) {
				have_res = true;
				res = rs->stores[idx].second;
			}
		}
		if (!have_res) {
			try {
				if (!strcmp(details->cee->name, "helper_load_64"))
					res = as->fetch<unsigned long>(addr, NULL);
				else if (!strcmp(details->cee->name, "helper_load_32"))
					res = as->fetch<unsigned int>(addr, NULL);
				else if (!strcmp(details->cee->name, "helper_load_16"))
					res = as->fetch<unsigned short>(addr, NULL);
				else if (!strcmp(details->cee->name, "helper_load_8"))
					res = as->fetch<unsigned char>(addr, NULL);
				else
					abort();
			} catch (BadMemoryException &e) {
				/* Don't crash when teh guest
				 * dereferences a bad pointer. */
				res = 0;
			}
		}

		temporaries[details->tmp].lo = res;
	} else {
		abort();
	}
}

static unsigned long
return_address(RegisterSet &regs, AddressSpace *as, unsigned long &return_rsp)
{
	unsigned long rip = regs.rip();
	unsigned long rsp = regs.rsp();

	while (!as->isReadable(rip, 1)) {
		/* We assume that if the current RIP is un-executable
		   it means that we just called a bad function
		   pointer, in which case the return address is right
		   at the top of the stack and it's all very easy.
		   This gives the wrong answer if e.g. someone
		   accidentally unmaps their own text, or if they're
		   doing something clever at an assembly level (rather
		   than via the C compiler), but those are both pretty
		   rare. */
		rip = as->fetch<unsigned long>(rsp, NULL);
		rsp += 8;
	}

	/* Basic approach is to try to build a map from RIPs to
	 * ``representative states'', which show what the processor
	 * state might have been if we'd executed a particular
	 * instruction.  If we ever manage to generate such a state
	 * for a ret instruction then we're done. */
	std::set<unsigned long> visited;
	std::vector<representative_state> unexplored_instructions;
	representative_state s;
	s.regs = regs;
	s.regs.rsp() = rsp;
	s.regs.rip() = rip;
	unexplored_instructions.push_back(s);

	while (!unexplored_instructions.empty()) {
	escape:
		s = unexplored_instructions.back();
		unexplored_instructions.pop_back();
		if (visited.count(s.regs.rip()))
			continue;
		printf("Visiting %lx\n", s.regs.rip());
		IRSB *irsb;
		try {
			irsb = as->getIRSBForAddress(1, s.regs.rip());
		} catch (BadMemoryException &x) {
			/* Okay, that didn't work.  Guess we don't
			   want to go down here... */
			goto escape;
		}
		std::vector<expression_result> temporaries;
		temporaries.resize(irsb->tyenv->types_used);
		assert(irsb);
		for (int idx = 0; idx < irsb->stmts_used; idx++) {
			IRStmt *stmt = irsb->stmts[idx];
			switch (stmt->tag) {
			case Ist_NoOp:
				break;
			case Ist_IMark:
				if (visited.count(stmt->Ist.IMark.addr))
					goto escape;
				s.regs.rip() = stmt->Ist.IMark.addr;
				visited.insert(s.regs.rip());
				break;
			case Ist_AbiHint:
				break;
			case Ist_MBE:
				break;
			case Ist_WrTmp:
				temporaries[stmt->Ist.WrTmp.tmp] =
					eval_expression(&s.regs, stmt->Ist.WrTmp.data, temporaries);
				break;

			case Ist_Store: {
				assert(stmt->Ist.Store.end == Iend_LE);
				assert(stmt->Ist.Store.resSC == IRTemp_INVALID);
				struct expression_result data =
					eval_expression(&s.regs, stmt->Ist.Store.data, temporaries);
				struct expression_result addr =
					eval_expression(&s.regs, stmt->Ist.Store.addr, temporaries);
				s.stores.push_back(
					std::pair<unsigned long, unsigned long>(addr.lo,
										data.lo));
				break;
			}

			case Ist_CAS:
				abort();

			case Ist_Put:
				put_stmt(&s.regs,
					 stmt->Ist.Put.offset,
					 eval_expression(&s.regs, stmt->Ist.Put.data, temporaries),
					 typeOfIRExpr(irsb->tyenv, stmt->Ist.Put.data));
				break;
			case Ist_PutI: {
				struct expression_result idx = eval_expression(&s.regs, stmt->Ist.PutI.ix, temporaries);

				/* Crazy bloody encoding scheme */
				idx.lo =
					((idx.lo + stmt->Ist.PutI.bias) %
					 stmt->Ist.PutI.descr->nElems) *
					sizeofIRType(stmt->Ist.PutI.descr->elemTy) +
					stmt->Ist.PutI.descr->base;

				put_stmt(&s.regs,
					 idx.lo,
					 eval_expression(&s.regs, stmt->Ist.PutI.data, temporaries),
					 stmt->Ist.PutI.descr->elemTy);
				break;
			}
			case Ist_Dirty:
				handle_dirty_call(&s, stmt->Ist.Dirty.details, temporaries, as);
				break;

			case Ist_Exit: {
				/* Bit of a trick: we always assume
				   that the branch is untaken, and
				   push the taken variant to the stack
				   to deal with later. */
				unsigned long i = s.regs.rip();
				s.regs.rip() = stmt->Ist.Exit.dst->Ico.U64;
				unexplored_instructions.push_back(s);
				s.regs.rip() = i;
				break;
			}

			default:
				abort();
					  
			}
		}

		if (irsb->jumpkind == Ijk_Call) {
			/* Calls are special, and we assume that we
			 * just resume at the next instruction. */
			s.regs.rip() = extract_call_follower(irsb);
			s.regs.rsp() += 8;
		} else {
			s.regs.rip() = eval_expression(&s.regs, irsb->next, temporaries).lo;
			if (irsb->jumpkind == Ijk_Ret) {
				/* We're done */
				return_rsp = s.regs.rsp();
				return s.regs.rip();
			}
		}
		unexplored_instructions.push_back(s);
	}

	/* Failed. */
	abort();
}

static void
compensateForBadVCall(Thread *thr, AddressSpace *as)
{
	if (!as->isReadable(thr->regs.rip(), 1)) {
		thr->regs.rip() = as->fetch<unsigned long>(thr->regs.rsp(), NULL) - 2;
		thr->regs.rsp() += 8;
	}
}

/* Figure out where the first instruction in the current function
 * is. */
static unsigned long
findFunctionHead(RegisterSet *rs, AddressSpace *as)
{
	unsigned long ra;
	unsigned char h;
	unsigned long ign;

	/* First heuristic: figure out where this function is going to
	   return to, and then see if its right after a call
	   instruction. */
	ra = return_address(*rs, as, ign);

	/* Call is five bytes */
	h = as->fetch<unsigned char>(ra - 5, NULL);
	if (h == 0xe8) {
		/* That looks like a call. */
		int delta = as->fetch<int>(ra - 4, NULL);
		return ra + delta;
	}

	abort();
}

#define DBG_DOMINATORS(...) do {} while (0)
//#define DBG_DOMINATORS printf

/* Given the starting point of a function and the address of an
   instruction in that function, find all of the instructions which
   are guaranteed to be executed at least once on any path from the
   starting point to the target instruction.  We order them so that
   the dominators nearest to the target are reported first. */
void
findDominators(unsigned long functionHead,
	       const unsigned long rip,
	       AddressSpace *as,
	       std::vector<unsigned long> &out)
{
	std::vector<unsigned long> remainingToExplore;
	std::map<unsigned long, std::set<unsigned long> > successors;
	std::map<unsigned long, std::set<unsigned long> > predecessors;
	std::set<unsigned long> instrs;

	DBG_DOMINATORS("Exploring from %lx to find dominators of %lx\n", functionHead, rip);
	/* First: build the CFG, representing all of the successor
	   pointers as straight ulongs and not bothing about
	   predecessors. */
	remainingToExplore.push_back(functionHead);
	while (!remainingToExplore.empty()) {
		unsigned long rip = remainingToExplore.back();
		unsigned long r;
		remainingToExplore.pop_back();
		if (instrs.count(rip))
			continue;
		IRSB *irsb = as->getIRSBForAddress(1, rip);
		assert(irsb->stmts[0]->tag == Ist_IMark);
		assert(irsb->stmts[0]->Ist.IMark.addr == rip);
		for (int idx = 1; idx < irsb->stmts_used; idx++) {
			IRStmt *stmt = irsb->stmts[idx];
			switch (stmt->tag) {
			case Ist_IMark:
				successors[rip].insert(stmt->Ist.IMark.addr);
				predecessors[stmt->Ist.IMark.addr].insert(rip);
				instrs.insert(rip);
				rip = stmt->Ist.IMark.addr;
				if (instrs.count(rip))
					goto done_this_entry;
				break;
			case Ist_Exit:
				successors[rip].insert(stmt->Ist.Exit.dst->Ico.U64);
				predecessors[stmt->Ist.Exit.dst->Ico.U64].insert(rip);
				remainingToExplore.push_back(stmt->Ist.Exit.dst->Ico.U64);
				break;
			default:
				break;
			}
		}

		instrs.insert(rip);

		r = 0;
		if (irsb->jumpkind == Ijk_Call) {
			r = extract_call_follower(irsb);
		} else if (irsb->next->tag == Iex_Const) {
			r = irsb->next->Iex.Const.con->Ico.U64;
		}
		if (r) {
			successors[rip].insert(r);
			predecessors[r].insert(rip);
			remainingToExplore.push_back(r);
		}
	done_this_entry:
		;
	}

	/* Now iterate to build a dominator map.  We start by assuming
	   that every instruction dominates every other instruction
	   (except for the head, which only dominates itself), and
	   then iterate to eliminate any bad dominations.  The rule,
	   at this stage, is that node A dominates node B if either
	   A == B or every predecessor of B is itself dominated by A.
	   Later on we'll trim this down to include only direct dominators.
	*/

	/* Build initial optimistic map. */
	std::map<unsigned long, std::set<unsigned long> > dominators;
	for (std::set<unsigned long>::iterator it = instrs.begin();
	     it != instrs.end();
	     it++)
		dominators[*it] = instrs;
	dominators[functionHead].clear();
	dominators[functionHead].insert(functionHead);
	/* Iterate to fixed point */
	bool progress;
	progress = true;
	while (progress) {
		if (timed_out) {
			printf("%s timed out on line %d\n", __func__, __LINE__);
			return;
		}

		progress = false;
		for (std::set<unsigned long>::iterator it = instrs.begin();
		     it != instrs.end();
		     it++) {
			unsigned long rip = *it;
			/* Check that all of our current dominators
			 * are valid. */
			std::set<unsigned long> &dom(dominators[rip]);
			for (std::set<unsigned long>::iterator domit = dom.begin();
			     domit != dom.end();
				) {
				if (*domit == rip) {
					/* Instructions always
					 * dominate themselves. */
					domit++;
					continue;
				}
				/* Otherwise, must dominate all
				 * predecessors of rip. */
				bool should_be_dominator = true;
				for (std::set<unsigned long>::iterator pred_it =
					     predecessors[rip].begin();
				     should_be_dominator && pred_it != predecessors[rip].end();
				     pred_it++) {
					if (!dominators[*pred_it].count(*domit))
						should_be_dominator = false;
				}
				if (!should_be_dominator) {
					progress = true;
					dom.erase(domit++);
				} else {
					domit++;
				}
			}
		}
	}

	/* Dump the dominator map. */
	for (std::set<unsigned long>::iterator it = instrs.begin();
	     it != instrs.end();
	     it++) {
		DBG_DOMINATORS("Dominators of %lx:", *it);
		for (std::set<unsigned long>::iterator it2 = dominators[*it].begin();
		     it2 != dominators[*it].end();
		     it2++)
			DBG_DOMINATORS(" %lx", *it2);
		DBG_DOMINATORS("\n");
	}

	/* Now restrict ourselves to immediate dominators.  X is an
	   immediate dominator of Y if:

	   -- X is a dominator of Y, and
	   -- there exists no Z such that Z dominates Y and X dominates Z, and
	   -- X != Y.

	   In other words, if A dominates B and C, and B dominates
	   just C, then A immediately dominates just B and B
	   immediately dominates C.  The immediate dominator of the
	   function head is not defined.

	   The immediate dominator of a node is unique.  Suppose that
	   A had two immediate dominators, B and C.  B and C must both
	   dominate A, and so every path from the root to A must pass
	   through both of them.  What's more, they must pass through
	   in the same order i.e. either every path visits B and then
	   C, or every path visits C and then B (i.e. one dominates
	   the other).  Otherwise, we'd have a cycle, and could skip
	   one of B and C on our way to A by skipping the cycle, and
	   so that would contradict the assumption that B and C are
	   both dominators of A.

	   (The path which visits B and then C must go E=>B=>C=>A, and
	   the path which visits C then B must go E=>C=>B=>A, and so
	   there must be paths E=>B=>A and E=>C=>A.  E is the function
	   head and => is supposed to be the transitive closure of the
	   successor relationship.)
	*/
	/* This is effectively undoing the implicit transitive closure
	 * in the definition of dominators.  There's probably a
	 * version of the dominator algorithm whcih does it directly,
	 * but I couldn't think of one. */
	std::map<unsigned long, unsigned long> immediateDominators;
	for (std::set<unsigned long>::iterator it = instrs.begin();
	     it != instrs.end();
	     it++) {
		if (timed_out) {
			printf("%s timed out\n", __func__);
			return;
		}
		unsigned long rip = *it;
		if (rip == functionHead) /* immediate dominator of
					  * function head undefined */
			continue;
		std::set<unsigned long> &doms(dominators[rip]);
		bool found_one = false;
		DBG_DOMINATORS("Find immediate dominator of %lx...\n", rip);
		for (std::set<unsigned long>::iterator it2 = doms.begin();
		     it2 != doms.end();
		     it2++) {
			unsigned long dom = *it2;
			/* Is dom the immediate dominator of rip? */
			if (dom == rip)
				continue; /* can't be immediate dominator of yourself */
			bool over_dominated = false;
			/* We know that dom dominates rip; we need to
			   check if there's some other dom' which
			   dominates rip such that dom dominates dom'.
			   If so, dom cannot be the immediate
			   dominator. */
			for (std::set<unsigned long>::iterator it3 = doms.begin();
			     !over_dominated && it3 != doms.end();
			     it3++) {
				unsigned long dom_prime = *it3;
				if (dom_prime == dom || dom_prime == rip)
					continue;
				/* If dom_prime dominates dom then dom
				   must be eliminated from
				   consideration. */
				if (dominators[dom_prime].count(dom)) {
					DBG_DOMINATORS("Not %lx: dominates %lx\n", dom, dom_prime);
					over_dominated = true;
				}
			}
			if (!over_dominated) {
				/* This is the immediate dominator. */
				assert(!found_one);
				found_one = true;
				immediateDominators[rip] = dom;
				DBG_DOMINATORS("%lx is immediate dominator of %lx\n", dom, rip);
				/* Could break here, but I'd rather
				   keep going so that we can assert
				   that the immediate dominator is
				   unique. */
			}
		}
		/* immediate dominator is always defined, except for
		   the function head */
		assert(found_one);
	}

	/* Dump out the immediate dominators table. */
	for (std::set<unsigned long>::iterator it = instrs.begin();
	     it != instrs.end();
	     it++) {
		if (*it != functionHead)
			DBG_DOMINATORS("Immediate dominator of %lx = %lx\n", *it, immediateDominators[*it]);
	}

	/* Finally, walk the immediate dominator map to build the
	 * ordered dominator chain for the target instruction. */
	unsigned long r = rip;
	while (1) {
		out.push_back(r);
		if (!immediateDominators.count(r))
			break;
		r = immediateDominators[r];
	}

	/* And we're done. */
}

void
getDominators(Thread *thr, MachineState *ms, std::vector<unsigned long> &dominators, std::vector<unsigned long> &fheads)
{
	unsigned long head = findFunctionHead(&thr->regs, ms->addressSpace);
	fheads.push_back(head);
	compensateForBadVCall(thr, ms->addressSpace);
	findDominators(head, thr->regs.rip(), ms->addressSpace, dominators);

	RegisterSet rs = thr->regs;
	rs.rip() = return_address(rs, ms->addressSpace, rs.rsp()) - 5;
	try {
		head = findFunctionHead(&rs, ms->addressSpace);
		fheads.push_back(head);
		findDominators(head, rs.rip(), ms->addressSpace, dominators);
	} catch (BadMemoryException &e) {
		/* Just give up: if we can't find the caller's caller,
		 * we just won't bother backtracking that far. */
	}
}
