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
	if (!strcmp(details->cee->name, "helper_load_64")) {
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
		if (!have_res)
			res = as->fetch<unsigned long>(addr, NULL);
		temporaries[details->tmp].lo = res;
	} else {
		abort();
	}
}

static unsigned long
return_address(RegisterSet &regs, AddressSpace *as)
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
		IRSB *irsb;
		try {
			irsb = as->getIRSBForAddress(s.regs.rip());
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
				return s.regs.rip();
			}
		}
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

	/* First heuristic: figure out where this function is going to
	   return to, and then see if its right after a call
	   instruction. */
	ra = return_address(*rs, as);

	/* Call is five bytes */
	h = as->fetch<unsigned char>(ra - 5, NULL);
	if (h == 0xe8) {
		/* That looks like a call. */
		int delta = as->fetch<int>(ra - 4, NULL);
		return ra + delta;
	}

	abort();
}

/* Given the starting point of a function and the address of an
   instruction in that function, find all of the instructions which
   are guaranteed to be executed at least once on any path from the
   starting point to the target instruction.  We try to order them so
   that the dominators nearest to the target are reported first. */
/* Algorithm for finding dominators is a fairly standard Tarski-style
   iteration to fixed point: start out assuming that everything is a
   dominator, then flag any return instructions or unresolvable
   dynamic branches as not dominators, and fix up any resulting
   contradictions. */
struct fd_cfg_node : public GarbageCollected<fd_cfg_node> {
	unsigned long rip;
	union ptr_or_ulong {
		fd_cfg_node *ptr;
		unsigned long ulong;
		bool operator<(const ptr_or_ulong &x) const {
			return ulong < x.ulong;
		}
	};
	std::set<ptr_or_ulong> predecessors;
	std::set<ptr_or_ulong> successors;
	bool is_exit_node; /* Definitely not a dominator */
	bool is_dominator;
	bool already_output;

	/* These should never be live across a GC pass */
	void visit(HeapVisitor &hv) { abort(); }

	NAMED_CLASS
};
static void
findDominators(unsigned long functionHead,
	       unsigned long rip,
	       AddressSpace *as,
	       std::vector<unsigned long> &out)
{
	std::vector<unsigned long> remainingToExplore;
	std::map<unsigned long, fd_cfg_node *> cfg;

	/* First: build the CFG, representing all of the successor
	   pointers as straight ulongs and not bothing about
	   predecessors. */
	remainingToExplore.push_back(functionHead);
	while (!remainingToExplore.empty()) {
		unsigned long rip = remainingToExplore.back();
		remainingToExplore.pop_back();
		if (cfg.count(rip))
			continue;
		IRSB *irsb = as->getIRSBForAddress(rip);
		ppIRSB(irsb, stdout);
		fd_cfg_node *work = NULL;
		assert(irsb->stmts[0]->tag == Ist_IMark);
		assert(irsb->stmts[0]->Ist.IMark.addr == rip);
		for (int idx = 0; idx < irsb->stmts_used; idx++) {
			IRStmt *stmt = irsb->stmts[idx];
			switch (stmt->tag) {
			case Ist_IMark:
				rip = stmt->Ist.IMark.addr;
				if (work) {
					fd_cfg_node::ptr_or_ulong p;
					p.ulong = rip;
					work->successors.insert(p);
				}
				if (cfg.count(rip))
					goto done_this_entry;
				work = new fd_cfg_node();
				work->rip = rip;
				cfg[rip] = work;
				break;
			case Ist_Exit: {
				fd_cfg_node::ptr_or_ulong p;
				p.ulong = stmt->Ist.Exit.dst->Ico.U64;
				work->successors.insert(p);
				remainingToExplore.push_back(p.ulong);
				break;
			}
			default:
				break;
			}
		}

		if (irsb->jumpkind == Ijk_Call) {
			fd_cfg_node::ptr_or_ulong p;
			p.ulong = extract_call_follower(irsb);
			work->successors.insert(p);
			remainingToExplore.push_back(p.ulong);
		} else if (irsb->next->tag == Iex_Const) {
			fd_cfg_node::ptr_or_ulong p;
			p.ulong = irsb->next->Iex.Const.con->Ico.U64;
			work->successors.insert(p);
			remainingToExplore.push_back(p.ulong);
		} else {
			work->is_exit_node = true;
		}
	done_this_entry:
		;
	}

	/* Resolve successor pointers. */
	for (std::map<unsigned long, fd_cfg_node *>::iterator it = cfg.begin();
	     it != cfg.end();
	     it++) {
		for (std::set<fd_cfg_node::ptr_or_ulong>::iterator it2 =
			     it->second->successors.begin();
		     it2 != it->second->successors.end();
		     it2++) {
			fd_cfg_node *ptr = cfg[it2->ulong];
			assert(ptr != NULL);
			assert(ptr->rip == it2->ulong);
			((fd_cfg_node::ptr_or_ulong *)&*it2)->ptr = ptr;
		}
	}
	/* And now do predecessor ones */
	for (std::map<unsigned long, fd_cfg_node *>::iterator it = cfg.begin();
	     it != cfg.end();
	     it++) {
		for (std::set<fd_cfg_node::ptr_or_ulong>::iterator it2 =
			     it->second->successors.begin();
		     it2 != it->second->successors.end();
		     it2++) {
			fd_cfg_node *ptr = it2->ptr;
			fd_cfg_node::ptr_or_ulong p;
			p.ptr = it->second;
			ptr->predecessors.insert(p);
		}
	}

	/* Now do the Tarski thing to find dominators. */
	for (std::map<unsigned long, fd_cfg_node *>::iterator it = cfg.begin();
	     it != cfg.end();
	     it++) {
		assert(it->first == it->second->rip);
		if (it->second->is_exit_node)
			it->second->is_dominator = false;
		else
			it->second->is_dominator = true;
	}
	bool progress;
	do {
		progress = false;
		for (std::map<unsigned long, fd_cfg_node *>::iterator it = cfg.begin();
		     it != cfg.end();
		     it++) {
			fd_cfg_node *node = it->second;
			/* The target instruction is always considered
			   to be a dominator of itself. */
			if (node->rip == rip)
				continue;
			/* Never need to make any further changes once
			   we've flagged something as definitely not a
			   dominator. */
			if (!node->is_dominator)
				continue;
			/* Otherwise, flag as not-a-dominator if any
			   successor is not a dominator. */
			for (std::set<fd_cfg_node::ptr_or_ulong>::iterator it2 = node->successors.begin();
			     it2 != node->successors.end();
			     it2++) {
				if (!it2->ptr->is_dominator) {
					progress = true;
					node->is_dominator = false;
					break;
				}
			}
		}
	} while (progress);

	/* There are now no is_dominator=true nodes with
	   is_dominator=false nodes in their successor sets (except
	   for the target), which is what we want.  Now we do a
	   topological sort of the CFG graph into the output set,
	   using a breadth-first iteration starting from the target to
	   get a reasonable ordering. */
	std::queue<fd_cfg_node *> queue;
	queue.push(cfg[rip]);
	assert(queue.front());
	while (!queue.empty()) {
		fd_cfg_node *n = queue.front();
		assert(n);
		queue.pop();
		assert(n->is_dominator);
		if (n->already_output)
			continue;
		n->already_output = true;
		out.push_back(n->rip);
		for (std::set<fd_cfg_node::ptr_or_ulong>::iterator it = n->predecessors.begin();
		     it != n->predecessors.end();
		     it++) {
			assert(it->ptr);
			queue.push(it->ptr);
		}
	}

	/* And we're done. */
}

void
getDominators(Thread *thr, MachineState *ms, std::vector<unsigned long> &dominators)
{
	unsigned long head = findFunctionHead(&thr->regs, ms->addressSpace);
	compensateForBadVCall(thr, ms->addressSpace);
	findDominators(head, thr->regs.rip(), ms->addressSpace, dominators);
}
