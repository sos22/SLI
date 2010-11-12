/* Something which, given a thread and a snapshot of memory, tries to
   find some instruction which the thread is guaranteed to have
   executed recently (prior to the one which it's executing right now
   :)) */
#include <set>

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

		s.regs.rip() = eval_expression(&s.regs, irsb->next, temporaries).lo;
		if (irsb->jumpkind == Ijk_Ret) {
			/* We're done */
			return s.regs.rip();
		}
	}

	/* Failed. */
	abort();
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

int
main(int argc, char *argv[])
{
	init_sli();
	MachineState *ms = MachineState::readCoredump(argv[1]);
	Thread *thr = ms->findThread(ThreadId(1));

	printf("%lx\n", findFunctionHead(&thr->regs, ms->addressSpace));
	return 0;
}
