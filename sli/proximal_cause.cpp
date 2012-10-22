/* All the stuff for producing a proximal cause for a crash.
 * Generally pretty damn stupid. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "libvex_prof.hpp"
#include "alloc_mai.hpp"
#include "simplify_irexpr.hpp"
#include "allowable_optimisations.hpp"

namespace ProximalCause {

static StateMachineState *
getProximalCause(MachineState *ms,
		 Oracle *oracle,
		 const VexRip &rip,
		 MaiMap &mai,
		 const CFGNode *where,
		 int tid)
{
	IRSB *irsb;
	try {
		irsb = ms->addressSpace->getIRSBForAddress(ThreadRip(tid, rip), true);
	} catch (BadMemoryException &e) {
		/* If we can't decode the block then we assume the
		   problem was an instruction fetch fault, and produce
		   a proximal cause which says ``we always crash if we
		   get to this RIP''. */
		return StateMachineCrash::get();
	}

	/* Successfully decoded the block -> build a state machine
	   which does what we want of it.  This is a lot like a simple
	   compiler from VEX intercode to our state machine model. */
	StateMachineState *work;

	struct _ {
		const VexRip &rip;
		StateMachineState *&work;
		void operator()(IRExpr *condition, StateMachineState *target) {
			if (work != target)
				work = new StateMachineBifurcate(
					rip,
					condition,
					target,
					work);
		}
		_(const VexRip &_rip, StateMachineState *&_work)
			: rip(_rip), work(_work)
		{}
	} conditionalBranch(rip, work);
	struct _2 {
		const VexRip &rip;
		StateMachineState *&work;
		void operator()(StateMachineSideEffect *se) {
			if (work->type != StateMachineState::NoCrash)
				work = new StateMachineSideEffecting(
					rip,
					se,
					work);
		}
		_2(const VexRip &_rip, StateMachineState *&_work)
			: rip(_rip), work(_work)
		{}
	} prependSideEffect(rip, work);
	struct _3 {
		_ &conditionalBranch;
		AllowableOptimisations opt;
		StateMachineState *&work;
		void operator()(IRExpr *e) {
			e = IRExpr_Unop(Iop_BadPtr, e);
			e = simplifyIRExpr(e, opt);
			assert(e->type() == Ity_I1);
			if (e->tag == Iex_Const) {
				if ( ((IRExprConst *)e)->con->Ico.U1 )
					work = StateMachineCrash::get();
				return;
			}
			conditionalBranch(e, StateMachineCrash::get());
		}
		_3(_ &_conditionalBranch, const AllowableOptimisations &_opt,
		   StateMachineState *&_work)
			: conditionalBranch(_conditionalBranch),
			  opt(_opt), work(_work)
		{}
	} crashIfBadPtr(conditionalBranch,
			AllowableOptimisations::defaultOptimisations.setAddressSpace(ms->addressSpace),
			work);

	int idx;
	for (idx = 1; idx < irsb->stmts_used && irsb->stmts[idx]->tag != Ist_IMark; idx++)
		;
	work = StateMachineNoCrash::get();
	if (idx == irsb->stmts_used) {
		if (!irsb->next_is_const) {
			crashIfBadPtr(irsb->next_nonconst);
		} else if (oracle->isCrashingAddr(irsb->next_const.rip))
			work = StateMachineCrash::get();
	}

	idx--;
	while (idx >= 0) {
		IRStmt *stmt = irsb->stmts[idx];
		idx--;
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			break;
		case Ist_AbiHint:
			break;
		case Ist_Put: {
			IRStmtPut *isp = (IRStmtPut *)stmt;
			prependSideEffect(
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
			prependSideEffect(
				new StateMachineSideEffectStore(
					ist->addr,
					ist->data,
					mai(tid, where),
					MemoryTag::normal()));
			crashIfBadPtr(ist->addr);
			break;
		}
		case Ist_CAS: {
			IRCAS *cas = ((IRStmtCAS *)stmt)->details;
			/* This is a bit tricky.  We take a

			   CAS *x : expd -> b

			   and we turn it into

			   l1: if (BadPtr(x)) then <crash> else l2
			   l2: START_ATOMIC
			   l3: t <- *x then l4
			   l4: if (t == expd) then l5 else l6
			   l5: *x <- data
			   l6: END_ATOMIC
			   l7: old <- t
			*/
			IRTemp t = newIRTemp(irsb->tyenv);
			threadAndRegister tr = threadAndRegister::temp(tid, t, 0);
			IRType ty = cas->expdLo->type();
			IRExpr *t_expr = IRExpr_Get(tr, ty);
			StateMachineSideEffecting *l7 =
				new StateMachineSideEffecting(
					rip,
					new StateMachineSideEffectCopy(
						cas->oldLo,
						t_expr),
					work);
			StateMachineSideEffecting *l6 =
				new StateMachineSideEffecting(
					rip,
					StateMachineSideEffectEndAtomic::get(),
					l7);
			StateMachineSideEffecting *l5 =
				new StateMachineSideEffecting(
					rip,
					new StateMachineSideEffectCopy(
						cas->oldLo,
						t_expr),
					l6);
			StateMachineBifurcate *l4 =
				new StateMachineBifurcate(
					rip,
					expr_eq(t_expr, cas->expdLo),
					l5,
					l6);
			StateMachineSideEffecting *l3 =
				new StateMachineSideEffecting(
					rip,
					new StateMachineSideEffectLoad(
						tr,
						cas->addr,
						mai(tid, where),
						ty,
						MemoryTag::normal()),
					l4);
			StateMachineSideEffecting *l2 =
				new StateMachineSideEffecting(
					rip,
					StateMachineSideEffectStartAtomic::get(),
					l3);
			work = l2;
			crashIfBadPtr(cas->addr);
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
			else if (!strcmp(dirty->cee->name, "helper_load_128"))
				ity = Ity_I128;
			else
				abort();
			assert(ity != Ity_INVALID);
			prependSideEffect(
				new StateMachineSideEffectLoad(
					dirty->tmp,
					dirty->args[0],
					mai(tid, where),
					ity,
					MemoryTag::normal()));
			crashIfBadPtr(dirty->args[0]);
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
		case Ist_StartAtomic:
			break;
		case Ist_EndAtomic:
			break;
		}
	}

	return work;
}

/* End of namespace */
}

StateMachineState *
getProximalCause(MachineState *ms,
		 Oracle *oracle,
		 MaiMap &mai,
		 const CFGNode *where,
		 const VexRip &rip,
		 int tid)
{
	return ProximalCause::getProximalCause(ms, oracle, rip, mai, where, tid);
}
