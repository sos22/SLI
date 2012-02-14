#include "sli.h"
#include "offline_analysis.hpp"
#include "libvex_prof.hpp"

/* A bunch of heuristics for figuring out why we crashed.  Returns
 * NULL on failure.  Pretty stupid. */
static StateMachineEdge *
_getProximalCause(MachineState *ms, unsigned long rip, Thread *thr, unsigned *idx)
{
	__set_profiling(getProximalCause);
	FreeVariableMap fv;

	IRSB *irsb;
	int x;
	int nr_marks;

	*idx = 9999999;
	if (rip == 0) {
		/* Probably caused by calling a bad function pointer.
		 * Look at the call site. */
		rip = ms->addressSpace->fetch<unsigned long>(thr->regs.rsp(), NULL) - 2;
		irsb = ms->addressSpace->getIRSBForAddress(thr->tid._tid(), rip);
		if (!irsb) {
			/* I guess that wasn't it.  Give up. */
			return NULL;
		}
		/* That should be a call instruction, in which case
		   we'll have a single mark, a jumpkind of Call, and a
		   next pointer of some expression. */
		if (irsb->jumpkind != Ijk_Call)
			return NULL;
		nr_marks = 0;
		for (x = 0; x < irsb->stmts_used; x++) {
			if (irsb->stmts[x]->tag == Ist_IMark)
				nr_marks++;
		}
		if (nr_marks != 1)
			return NULL;

		/* We now guess that we crashed because the function
		   pointer called turned out to be NULL. */
		*idx = irsb->stmts_used;
		return new StateMachineEdge(
			new StateMachineBifurcate(
				rip,
				IRExpr_Unop(
					Iop_BadPtr,
					irsb->next),
				StateMachineCrash::get(),
				StateMachineNoCrash::get()));
	}

	/* Next guess: it's caused by dereferencing a bad pointer.
	   Grab the crashing instruction and try emulating it.  If it
	   results in a crash, we can be pretty confident that we've
	   found the problem. */
	try {
		irsb = ms->addressSpace->getIRSBForAddress(thr->tid._tid(), rip);
	} catch (BadMemoryException &e) {
		return NULL;
	}

	thr->temporaries.setSize(irsb->tyenv->types_used);
	for (int x = 1 /* Skip the initial IMark */;
	     x < irsb->stmts_used;
	     x++) {
		IRStmt *stmt = irsb->stmts[x];
		ThreadEvent *evt;
		{
			ReplayEngineTimer ret;
			evt = interpretStatement(stmt,
						 thr,
						 NULL,
						 ms,
						 irsb,
						 ret);
		}
		if (evt == NULL)
			continue;
		if (evt == DUMMY_EVENT || evt == FINISHED_BLOCK) {
			/* Okay, so re-interpreting this instruction
			   didn't give us any clues as to why we're
			   crashing.  Give up. */
			break;
		}

		SignalEvent *se = dynamic_cast<SignalEvent *>(evt);
		if (se && se->signr == 11) {
			/* Program tripped over a segfault -> almost
			   certainly the cause of the crash.  It'll be
			   from either a load or a store, and we
			   special case the two cases here. */
			IRExpr *addr = NULL;
			if (stmt->tag == Ist_Dirty &&
			    (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
				     "helper_load_8") ||
			     !strcmp(((IRStmtDirty *)stmt)->details->cee->name,
				     "helper_load_16") ||
			     !strcmp(((IRStmtDirty *)stmt)->details->cee->name,
				     "helper_load_32") ||			     
			     !strcmp(((IRStmtDirty *)stmt)->details->cee->name,
				     "helper_load_64"))) {
				/* It's a load; the address loaded is
				   in the first argument. */
				addr = ((IRStmtDirty *)stmt)->details->args[0];
			} else if (stmt->tag == Ist_Store) {
				addr = ((IRStmtStore *)stmt)->addr;
			} else {
				/* Neither a load nor a store.  That
				   shouldn't be generating a segfault,
				   then. */
				abort();
			}
			assert(addr != NULL);
			*idx = x;
			return new StateMachineEdge(
				new StateMachineBifurcate(
					rip,
					IRExpr_Unop(
						Iop_BadPtr,
						addr),
					StateMachineCrash::get(),
					StateMachineNoCrash::get()));
		}
		fprintf(_logfile, "Generated event %s\n", evt->name());
	}

	fprintf(_logfile, "Hit end of block without any events -> no idea why we crashed.\n");
	return NULL;
}

static StateMachineEdge *
backtrackOneStatement(StateMachineEdge *sm, IRStmt *stmt, ThreadOracleRip site)
{
	switch (stmt->tag) {
	case Ist_NoOp:
	case Ist_IMark:
	case Ist_AbiHint:
		break;
	case Ist_Put:
		sm->prependSideEffect(
			new StateMachineSideEffectCopy(
				((IRStmtPut *)stmt)->target,
				((IRStmtPut *)stmt)->data));
		break;
	case Ist_PutI:
		/* We can't handle these correctly. */
		abort();
		return NULL;
	case Ist_Store:
		sm->prependSideEffect(
			new StateMachineSideEffectStore(
				((IRStmtStore *)stmt)->addr,
				((IRStmtStore *)stmt)->data,
				site));
		break;

	case Ist_Dirty:
		if (!strcmp(((IRStmtDirty *)stmt)->details->cee->name,
			    "helper_load_8") ||
		    !strcmp(((IRStmtDirty *)stmt)->details->cee->name,
			    "helper_load_16") ||
		    !strcmp(((IRStmtDirty *)stmt)->details->cee->name,
			    "helper_load_64") ||
		    !strcmp(((IRStmtDirty *)stmt)->details->cee->name,
			    "helper_load_32")) {
			StateMachineSideEffectLoad *smsel =
				new StateMachineSideEffectLoad(
					((IRStmtDirty *)stmt)->details->tmp,
					((IRStmtDirty *)stmt)->details->args[0],
					site);
			sm->prependSideEffect(smsel);
		}  else {
			abort();
		}
		break;

	case Ist_CAS:
		/* Can't backtrack across these */
		fprintf(_logfile, "Don't know how to backtrack across CAS statements?\n");
		sm = NULL;
		break;

	case Ist_MBE:
		break;
	case Ist_Exit:
		sm = new StateMachineEdge(
			new StateMachineBifurcate(
				site.rip.rip,
				((IRStmtExit *)stmt)->guard,
				new StateMachineEdge(
					new StateMachineStub(
						site.rip.rip,
						IRExpr_Const(((IRStmtExit *)stmt)->dst))),
				sm));
		break;
	}
	return sm;
}

StateMachineEdge *
getProximalCause(MachineState *ms, unsigned long rip, Thread *thr)
{
	unsigned idx;
	StateMachineEdge *sm = _getProximalCause(ms, rip, thr, &idx);
	if (!sm)
		return NULL;
	IRSB *irsb = ms->addressSpace->getIRSBForAddress(thr->tid._tid(), rip);
	while (idx != 0) {
		idx--;
		sm = backtrackOneStatement(sm, irsb->stmts[idx], ThreadOracleRip(thr->tid._tid(), rip));
		if (!sm)
			return NULL;
	}
	return sm;
}

