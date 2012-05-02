/* All the stuff for producing a proximal cause for a crash.
 * Generally pretty damn stupid. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "libvex_prof.hpp"

namespace ProximalCause {

static StateMachineEdge *
getProximalCause(MachineState *ms, const ThreadRip &rip, Thread *thr)
{
	IRSB *irsb;
	try {
		irsb = ms->addressSpace->getIRSBForAddress(rip);
	} catch (BadMemoryException &e) {
		/* If we can't decode the block then we assume the
		   problem was an instruction fetch fault, and produce
		   a proximal cause which says ``we always crash if we
		   get to this RIP''. */
		return new StateMachineEdge(StateMachineCrash::get());
	}

	/* Successfully decoded the block -> build a state machine
	   which does what we want of it.  This is a lot like a simple
	   compiler from VEX intercode to our state machine model. */
	StateMachineEdge *work = new StateMachineEdge(NULL);
	StateMachineEdge *res = work;

	class _ {
	public:
		const ThreadRip &rip;
		StateMachineEdge *&work;
		void operator()(IRExpr *condition, StateMachineState *target) {
			StateMachineEdge *newEdge = new StateMachineEdge(NULL);
			StateMachineBifurcate *smb = new StateMachineBifurcate(
				rip.rip,
				condition,
				new StateMachineEdge(target),
				newEdge);
			work->target = smb;
			work = newEdge;			
		}
		_(const ThreadRip &_rip, StateMachineEdge *&_work)
			: rip(_rip), work(_work)
		{}
	} conditionalBranch(rip, work);
	for (int idx = 1; /* Skip initial IMark */
	     idx < irsb->stmts_used;
	     idx++) {
		IRStmt *stmt = irsb->stmts[idx];
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			/* End of the instruction -> we're done */
			idx = irsb->stmts_used;
			break;
		case Ist_AbiHint:
			break;
		case Ist_Put: {
			IRStmtPut *isp = (IRStmtPut *)stmt;
			work->appendSideEffect(
				new StateMachineSideEffectCopy(
					isp->target,
					isp->data));
			break;
		}
		case Ist_PutI:
			/* These can't really be represented in the
			 * state machine model. */
			abort();
			break;
		case Ist_Store: {
			IRStmtStore *ist = (IRStmtStore *)stmt;
			conditionalBranch(IRExpr_Unop(Iop_BadPtr, ist->addr),
					  StateMachineCrash::get());
			work->appendSideEffect(
				new StateMachineSideEffectStore(
					ist->addr,
					ist->data,
					MemoryAccessIdentifier(rip, MemoryAccessIdentifier::static_generation)));
			break;
		}
		case Ist_CAS: {
			IRCAS *cas = ((IRStmtCAS *)stmt)->details;
			/* This is a bit tricky.  We take a

			   CAS *x : expd -> b

			   and we turn it into

			   if (BadPtr(x)) { crash }
			   else { t <- *x
			          if (t == expd) {
				      *x <- data;
				      old <- t
				      r
				  } else {
				      old <- t
				      r
				  }
                           }

			   where r is a freshly-allocated proxy state
			   which goes to a freshly-allocated edge, and
			   then we set the current work edge to that
			   freshly-allocated one. */
#warning This breaks the atomicity of the CAS
			/* Breaking the atomicity of the CAS like that
			   means that we'll sometimes report a crash
			   which can't happen, but we'll never miss a
			   crash which can. */
			conditionalBranch(IRExpr_Unop(Iop_BadPtr, cas->addr),
					  StateMachineCrash::get());
			IRTemp t = newIRTemp(irsb->tyenv);
			threadAndRegister tr = threadAndRegister::temp(rip.thread, t, 0);
			IRType ty = cas->expdLo->type();
			IRExpr *t_expr = IRExpr_Get(tr, ty);
			work->appendSideEffect(
				new StateMachineSideEffectLoad(
					tr,
					cas->addr,
					MemoryAccessIdentifier(rip, MemoryAccessIdentifier::static_generation),
					ty));
			StateMachineEdge *exitEdge = new StateMachineEdge(NULL);
			StateMachineProxy *r = new StateMachineProxy(rip.rip, exitEdge);
			exitEdge->appendSideEffect(
				new StateMachineSideEffectCopy(
					cas->oldLo,
					t_expr));
			StateMachineEdge *edgeIfEq = new StateMachineEdge(r);
			StateMachineEdge *edgeIfNEq = new StateMachineEdge(r);
			edgeIfEq->appendSideEffect(
				new StateMachineSideEffectStore(
					cas->addr,
					cas->dataLo,
					MemoryAccessIdentifier(rip, MemoryAccessIdentifier::static_generation)));
			IROp op;
			switch (ty) {
#define do_size(sz)						\
				case Ity_I ## sz :		\
					op = Iop_CmpEQ ## sz;	\
				break
				do_size(8);
				do_size(16);
				do_size(32);
				do_size(64);
#undef do_size
			default:
				abort();
			}
			StateMachineBifurcate *smb = new StateMachineBifurcate(
				rip.rip,
				IRExpr_Binop(op,
					     t_expr,
					     cas->expdLo),
				edgeIfEq,
				edgeIfNEq);
			work->target = smb;
			work = exitEdge;
			break;
		}
		case Ist_Dirty: {
			IRDirty *dirty = ((IRStmtDirty *)stmt)->details;
			IRType ity = Ity_INVALID;
			if (!strcmp(dirty->cee->name, "helper_load_8"))
				ity = Ity_I8;
			else if (!strcmp(dirty->cee->name, "helper_load_16"))
				ity = Ity_I16;
			else if (!strcmp(dirty->cee->name, "helper_load_32"))
				ity = Ity_I32;
			else if (!strcmp(dirty->cee->name, "helper_load_64"))
				ity = Ity_I64;
			else
				abort();
			assert(ity != Ity_INVALID);
			conditionalBranch(IRExpr_Unop(Iop_BadPtr, dirty->args[0]),
					  StateMachineCrash::get());
			work->appendSideEffect(
				new StateMachineSideEffectLoad(
					dirty->tmp,
					dirty->args[0],
					MemoryAccessIdentifier(rip, MemoryAccessIdentifier::static_generation),
					ity));
			break;
		}
		case Ist_MBE:
			break;
		case Ist_Exit: {
			/* If we exit the instruction then that's
			   considered to be a surviving run. */
			IRStmtExit *ise = (IRStmtExit *)stmt;
			conditionalBranch(ise->guard, StateMachineNoCrash::get());
			break;
		}
		}
	}

	/* If we get to the end of the block then we're considered to
	 * have survived. */
	work->target = StateMachineNoCrash::get();

	return res;
}

/* End of namespace */
}

StateMachineEdge *
getProximalCause(MachineState *ms, const ThreadRip &rip, Thread *thr)
{
	return ProximalCause::getProximalCause(ms, rip, thr);
}
