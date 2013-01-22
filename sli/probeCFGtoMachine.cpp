/* This file is somewhat misnamed, because it also handles store CFGs. */
#include <sys/resource.h>

#include "sli.h"
#include "state_machine.hpp"
#include "cfgnode.hpp"
#include "oracle.hpp"
#include "alloc_mai.hpp"
#include "offline_analysis.hpp"
#include "smb_builder.hpp"
#include "maybe.hpp"
#include "visitor.hpp"

#include "libvex_guest_offsets.h"

#ifndef NDEBUG
static bool debug_assign_frame_ids = false;
static bool debug_rsp_canonicalisation = false;
#else
#define debug_assign_frame_ids false
#define debug_rsp_canonicalisation false
#endif

namespace _probeCFGsToMachine {

static IRExpr *
mkPendingFreeVar(IRType ty, const CFGNode *node, bool isUnique)
{
	return IRExpr_FreeVariable(mkPendingMai(node), ty, isUnique);
}

static void
ndChoiceState(SMScopes *scopes,
	      StateMachineState **slot,
	      const ThreadRip &vr,
	      CFGNode *node,
	      std::vector<reloc_t> &pendingRelocs,
	      std::vector<CFGNode *> &targets,
	      bool storeLike,
	      HashedSet<HashedPtr<CFGNode> > *usedExits)
{
	if (targets.empty()) {
		if (storeLike)
			*slot = new StateMachineTerminal(vr.rip, scopes->smrs.cnst(smr_crash));
		else
			*slot = new StateMachineTerminal(vr.rip, scopes->smrs.cnst(smr_survive));
	} else if (targets.size() == 1) {
		if (usedExits)
			usedExits->insert(targets[0]);
		assert(targets[0] != NULL);
		pendingRelocs.push_back(
			reloc_t(slot, targets[0]));
	} else {
		StateMachineSideEffecting *r =
			new StateMachineSideEffecting(
				vr.rip,
				new StateMachineSideEffectAssertFalse(
					bbdd::var(
						&scopes->bools,
						IRExpr_Unop(
							Iop_Not1,
							IRExprControlFlow::mk(
								vr.thread,
								node->label,
								targets[0]->label))),
					true),
				NULL);
		assert(targets[0] != NULL);
		pendingRelocs.push_back(
			reloc_t(&r->target, targets[0]));
		if (usedExits)
			usedExits->insert(targets[0]);
		StateMachineState *acc = r;
		for (unsigned x = 1; x < targets.size(); x++) {
			StateMachineBifurcate *b = 
				new StateMachineBifurcate(
					vr.rip,
					bbdd::var(
						&scopes->bools,
						IRExprControlFlow::mk(
							vr.thread,
							node->label,
							targets[x]->label)),
					NULL,
					acc);
			pendingRelocs.push_back(
				reloc_t(&b->trueTarget, targets[x]));
			assert(targets[x] != NULL);
			if (usedExits)
				usedExits->insert(targets[x]);
			acc = b;
		}
		*slot = acc;
	}
}

static StateMachineState *
entryState(SMScopes *scopes,
	   const VexRip &vr,
	   const std::vector<std::pair<CFGNode *, StateMachineState *> > &targets,
	   unsigned thread,
	   bool storeLike)
{
	if (targets.empty()) {
		if (storeLike)
			return new StateMachineTerminal(vr, scopes->smrs.cnst(smr_crash));
		else
			return new StateMachineTerminal(vr, scopes->smrs.cnst(smr_survive));
	} else if (targets.size() == 1) {
		return targets[0].second;
	} else {
		StateMachineSideEffecting *r =
			new StateMachineSideEffecting(
				targets[0].first->rip,
				new StateMachineSideEffectAssertFalse(
					bbdd::var(
						&scopes->bools,
						IRExpr_Unop(
							Iop_Not1,
							IRExprEntryPoint::mk(thread, targets[0].first->label))),
					true),
				targets[0].second);
		StateMachineState *acc = r;
		for (unsigned x = 1; x < targets.size(); x++) {
			StateMachineBifurcate *b = 
				new StateMachineBifurcate(
					targets[0].first->rip,
					bbdd::var(&scopes->bools, IRExprEntryPoint::mk(thread, targets[x].first->label)),
					targets[x].second,
					acc);
			acc = b;
		}
		return acc;
	}
}

static void
getTargets(CFGNode *node, const VexRip &vr, std::vector<CFGNode *> &targets)
{
	for (auto it = node->successors.begin(); it != node->successors.end(); it++)
		if (it->instr && it->instr->rip == vr)
			targets.push_back(it->instr);
}

static StateMachineState *
getLibraryStateMachine(SMScopes *scopes,
		       CFGNode *cfgnode,
		       unsigned tid,
		       std::vector<reloc_t> &pendingRelocs)
{
	threadAndRegister rax(threadAndRegister::reg(tid, OFFSET_amd64_RAX, 0));
	threadAndRegister arg1(threadAndRegister::reg(tid, OFFSET_amd64_RDI, 0));
	threadAndRegister arg2(threadAndRegister::reg(tid, OFFSET_amd64_RSI, 0));
	threadAndRegister arg3(threadAndRegister::reg(tid, OFFSET_amd64_RDX, 0));
	CFGNode *fallThrough = NULL;
	LibraryFunctionType lib = LibraryFunctionTemplate::none;
	for (auto it = cfgnode->successors.begin(); it != cfgnode->successors.end(); it++) {
		if (it->type == succ_default) {
			assert(!fallThrough);
			fallThrough = it->instr;
			lib = it->calledFunction;
		}
	}
	if (lib == LibraryFunctionTemplate::none)
		return NULL;
	assert(fallThrough);
	SMBPtr<SMBState> end(Proxy(fallThrough));
	SMBPtr<SMBState> acc(NULL);
	switch (lib) {
	case LibraryFunctionTemplate::__cxa_atexit: {
		acc = (!rax <<= smb_const64(0)) >> end;
		break;
	}
	case LibraryFunctionTemplate::bzero: {
		SMBPtr<SMBState> states[9];
		states[8] = end;
		for (int i = 7; i >= 0; i--)
			states[i] =
				(*(smb_reg(arg1, Ity_I64) + smb_const64((7 - i) * 8)) <<= smb_const64(0)) >>
				states[i+1];
		acc = end;
		for (int i = 0; i < 9; i++)
			acc = If(i == 8 ?
					smb_const64(i * 8) <= smb_reg(arg2, Ity_I64) :
				        smb_const64(i * 8) == smb_reg(arg2, Ity_I64),
				 states[8-i],
				 acc);
		break;
	}
	case LibraryFunctionTemplate::strlen: {
		int i;
		threadAndRegister tmp1(threadAndRegister::temp(tid, 0, 0));
		acc = (!rax <<= smb_const64(64)) >> end;
		for (i = 63; i >= 0; i--) {
			acc = Load(!tmp1,
				   *(smb_reg(arg1, Ity_I64) + smb_const64(i)),
				   Ity_I8) >>
				If(smb_reg(tmp1, Ity_I8) == smb_const8(0),
				   (!rax <<= smb_const64(i)) >> end,
				   acc);
		}
		break;
	}
	case LibraryFunctionTemplate::memcpy: {
		SMBPtr<SMBState> states[9];
		threadAndRegister tmp1(threadAndRegister::temp(tid, 0, 0));
		acc = states[8] = (!rax <<= smb_reg(arg1, Ity_I64)) >> end;
		for (int i = 7; i >= 0; i--)
			states[i] =
				Load(!tmp1,
				     *(smb_reg(arg2, Ity_I64) + smb_const64((7 - i) * 8)),
				     Ity_I64) >>
				((*(smb_reg(arg1, Ity_I64) + smb_const64((7 - i) * 8)) <<= smb_reg(tmp1, Ity_I64)) >>
				 states[i+1]);
		for (int i = 0; i < 9; i++)
			acc = If(i == 8 ?
					smb_const64(i * 8) <= smb_reg(arg3, Ity_I64) :
				        smb_const64(i * 8) == smb_reg(arg3, Ity_I64),
				 states[8-i],
				 acc);
		break;
	}
	case LibraryFunctionTemplate::memset: {
		SMBPtr<SMBExpression> arg2_byte =
			smb_reg(arg2, Ity_I64) & smb_const64(0xff);
		SMBPtr<SMBExpression> writeVal =
			arg2_byte                     |
			(arg2_byte << smb_const8(8))  |
			(arg2_byte << smb_const8(16)) |
			(arg2_byte << smb_const8(24)) |
			(arg2_byte << smb_const8(32)) |
			(arg2_byte << smb_const8(40)) |
			(arg2_byte << smb_const8(48)) |
			(arg2_byte << smb_const8(56));
		SMBPtr<SMBState> states[9];
		acc = states[8] = (!rax <<= smb_reg(arg1, Ity_I64)) >> end;
		for (int i = 7; i >= 0; i--)
			states[i] =
				(*(smb_reg(arg1, Ity_I64) + smb_const64((7 - i) * 8)) <<= writeVal) >>
				states[i+1];
		for (int i = 0; i < 9; i++)
			acc = If(i == 8 ?
					smb_const64(i * 8) <= smb_reg(arg3, Ity_I64) :
				        smb_const64(i * 8) == smb_reg(arg3, Ity_I64),
				 states[8-i],
				 acc);
		break;
	}
	case LibraryFunctionTemplate::malloc: {
		acc = (!rax <<= smb_expr(mkPendingFreeVar(Ity_I64, cfgnode, true))) >>
			(AssertFalse(smb_expr(IRExpr_Unop(Iop_BadPtr, IRExpr_Get(rax, Ity_I64)))) >> end);
		break;
	}
	case LibraryFunctionTemplate::_ZdlPv:
	case LibraryFunctionTemplate::free: {
		acc = If(smb_reg(arg1, Ity_I64) == smb_const64(0),
			 end,
			 Store(*smb_const64(CONFIG_LASTFREE_ADDR), smb_reg(arg1, Ity_I64), MemoryTag::last_free()) >> end);
		break;
	}
	case LibraryFunctionTemplate::pthread_mutex_lock: {
		threadAndRegister tmp1(threadAndRegister::temp(tid, 0, 0));
		acc = StartAtomic() >>
		      (Load(!tmp1,
			    *smb_reg(arg1, Ity_I64),
			    Ity_I8,
			    MemoryTag::mutex()) >>
		      (AssertFalse(smb_reg(tmp1, Ity_I8) != smb_const8(0)) >>
		      (Store(*smb_reg(arg1, Ity_I64), smb_const8(1), MemoryTag::mutex()) >>
		      (EndAtomic() >>
		      ((!rax <<= smb_const64(0)) >>
		      end)))));
		break;
	}
	case LibraryFunctionTemplate::pthread_mutex_unlock: {
		threadAndRegister tmp1(threadAndRegister::temp(tid, 0, 0));
		acc = StartAtomic() >>
		      (Load(!tmp1,
			    *smb_reg(arg1, Ity_I64),
			    Ity_I8,
			    MemoryTag::mutex()) >>
		      (AssertFalse(smb_reg(tmp1, Ity_I8) != smb_const8(1)) >>
		      (Store(*smb_reg(arg1, Ity_I64), smb_const8(0), MemoryTag::mutex()) >>
		      (EndAtomic() >>
		      ((!rax <<= smb_const64(0)) >>
		      end)))));
		break;
	}
	case LibraryFunctionTemplate::__stack_chk_fail:
	case LibraryFunctionTemplate::__assert_fail:
		return new StateMachineTerminal(cfgnode->rip, scopes->smrs.cnst(smr_unreached));
	case LibraryFunctionTemplate::time: {
		SMBPtr<SMBExpression> fv(smb_expr(mkPendingFreeVar(Ity_I64, cfgnode, false)));
		acc = (!rax <<= fv) >> end;
		If(smb_reg(arg1, Ity_I64) == smb_const64(0),
		   acc,
		   (*smb_reg(arg1, Ity_I64) <<= fv) >> acc);
		break;
	}
	case LibraryFunctionTemplate::getrusage: {
		acc = (!rax <<= smb_const64(0)) >> end;
		for (unsigned i = 0; i < sizeof(struct rusage) / 8; i++) {
			SMBPtr<SMBExpression> fv(smb_expr(mkPendingFreeVar(Ity_I64, cfgnode, false)));
			acc = (*(smb_reg(arg1, Ity_I64) + smb_const64(i * 8)) <<= fv) >>
				acc;
		}
		break;
	}
	case LibraryFunctionTemplate::sigwait: {
		acc = (*smb_reg(arg2, Ity_I64) <<= smb_const32(1)) >>
		      ((!rax <<= smb_const64(0)) >>
		      end);
		break;
	}
	case LibraryFunctionTemplate::__errno_location:
		acc = (!rax <<= smb_reg(threadAndRegister::reg(tid, offsetof(VexGuestAMD64State, errno_address), 0), Ity_I64)) >>
			end;
		break;
	case LibraryFunctionTemplate::pthread_getspecific:
		acc = Load(!rax,
			   *(smb_reg(arg1, Ity_I64) * smb_const64(8) +
			     smb_reg(threadAndRegister::reg(tid, offsetof(VexGuestAMD64State, pthread_specific_base), 0), Ity_I64)),
			   Ity_I64) >>
			end;
		break;
	case LibraryFunctionTemplate::pthread_setspecific:
		acc = (*(smb_reg(arg1, Ity_I64) * smb_const64(8) +
			 smb_reg(threadAndRegister::reg(tid, offsetof(VexGuestAMD64State, pthread_specific_base), 0), Ity_I64)) <<= smb_reg(arg2, Ity_I64)) >>
			end;
		break;
	case LibraryFunctionTemplate::none:
		abort();
	}
	if (!acc.content) {
		printf("Need to add support for library function %d (", (int)lib);
		LibraryFunctionTemplate::pp(lib, stdout);
		printf(")\n");
		abort();
	}
	SMBCompilerState state(cfgnode->rip, cfgnode, scopes);
	return acc.content->compile(pendingRelocs, state);
}

static void
canonicaliseRbp(SMScopes *scopes, StateMachineState *root, const VexRip &rip, Oracle *oracle)
{
	long delta;
	if (oracle->getRbpToRspDelta(rip, &delta)) {
		/* Rewrite any references to RBP to be references to
		   RSP-delta wherever possible. */
		struct : public StateMachineTransformer {
			long delta;
			IRExpr *canonedRbp;
			IRExpr *transformIex(IRExprGet *ieg) {
				if (ieg->ty == Ity_I64 &&
				    ieg->reg.isReg() &&
				    ieg->reg.asReg() == OFFSET_amd64_RBP) {
					if (!canonedRbp)
						canonedRbp =
							IRExpr_Binop(
								Iop_Add64,
								IRExpr_Const_U64(-delta),
								IRExpr_Get(
									threadAndRegister::reg(
										ieg->reg.tid(),
										OFFSET_amd64_RSP,
										0),
									Ity_I64));
					return canonedRbp;
				}
				return IRExprTransformer::transformIex(ieg);
			}
			bool rewriteNewStates() const { return false; }
		} doit;
		doit.delta = delta;
		doit.canonedRbp = NULL;

		/* Can't use normal state machine transformer because
		   some of the targets are still NULL pointers. */
		std::vector<StateMachineState *> pendingStates;
		pendingStates.push_back(root);
		while (!pendingStates.empty()) {
			StateMachineState *s = pendingStates.back();
			pendingStates.pop_back();
			if (!s)
				continue;
			s->targets(pendingStates);
			switch (s->type) {
			case StateMachineState::Bifurcate: {
				StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
				smb->set_condition(doit.transform_bbdd(&scopes->bools, smb->condition));
				break;
			}
			case StateMachineState::Terminal:
				break;
			case StateMachineState::SideEffecting: {
				StateMachineSideEffect *smse = s->getSideEffect();
				if (smse) {
					bool b;
					StateMachineSideEffect *new_smse =
						doit.transformSideEffect(scopes, smse, &b);
					if (new_smse)
						((StateMachineSideEffecting *)s)->sideEffect =
							new_smse;
				}
				break;
			}
			}
		}
	}
}

static StateMachineState *
cfgNodeToState(SMScopes *scopes,
	       Oracle *oracle,
	       unsigned tid,
	       CFGNode *target,
	       bool storeLike,
	       std::vector<reloc_t> &pendingRelocs)
{
	if (TIMEOUT)
		return NULL;

	ThreadRip tr(tid, target->rip);

	StateMachineState *root;
	root = getLibraryStateMachine(scopes, target, tid, pendingRelocs);
	if (root)
		return root;

	IRSB *irsb;
	try {
		irsb = oracle->ms->addressSpace->getIRSBForAddress(tr, true);
	} catch (BadMemoryException &e) {
		return new StateMachineTerminal(target->rip, scopes->smrs.cnst(smr_unreached));
	}
	HashedSet<HashedPtr<CFGNode> > usedExits;
	StateMachineState **cursor = &root;
	int i;
	for (i = 1; i < irsb->stmts_used && irsb->stmts[i]->tag != Ist_IMark; i++) {
		IRStmt *stmt = irsb->stmts[i];
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			abort();
			break;
		case Ist_AbiHint:
			break;
		case Ist_Put: {
			IRStmtPut *isp = (IRStmtPut *)stmt;
			StateMachineSideEffect *se =
				new StateMachineSideEffectCopy(
					isp->target,
					exprbdd::var(&scopes->exprs, &scopes->bools, isp->data));
			StateMachineSideEffecting *smse =
				new StateMachineSideEffecting(
					target->rip,
					se,
					NULL);
			*cursor = smse;
			cursor = &smse->target;
			break;
		}
		case Ist_PutI:
			/* These can't really be represented in the
			 * state machine model. */
			abort();
			break;
		case Ist_Store: {
			IRStmtStore *ist = (IRStmtStore *)stmt;
			bool isCall;
			isCall = false;
			int j;
			for (j = i + 1; j < irsb->stmts_used && irsb->stmts[j]->tag != Ist_IMark; j++)
				;
			if (j == irsb->stmts_used && irsb->jumpkind == Ijk_Call)
				isCall = true;
			if (!isCall) {
				/* Don't bother storing the return
				   address for function calls.  It'll
				   never get loaded (because we handle
				   all functions by inlining), and it's
				   sometimes a pain to optimise
				   out later. */
				StateMachineSideEffectStore *se =
					new StateMachineSideEffectStore(
						exprbdd::var(&scopes->exprs, &scopes->bools, ist->addr),
						exprbdd::var(&scopes->exprs, &scopes->bools, ist->data),
						mkPendingMai(target),
						MemoryTag::normal());
				StateMachineSideEffecting *smse =
					new StateMachineSideEffecting(
						target->rip,
						se,
						NULL);
				*cursor = smse;
				cursor = &smse->target;
			}
			break;
		}
		case Ist_CAS: {
			IRCAS *cas = ((IRStmtCAS *)stmt)->details;
			/* This is a bit tricky.  We take a

			   CAS *x : expd -> b

			   and we turn it into

			   l0: START_ATOMIC then l1
			   l1: t <- *x then l2
			   l2: if (t == expd) then l3 else l4
			   l3: *x <- data then l4
			   l4: END_ATOMIC then l5
			   l5: old <- t
			*/
			IRTemp t = newIRTemp(irsb->tyenv);
			threadAndRegister tempreg = threadAndRegister::temp(tid, t, 0);
			IRType ty = cas->expdLo->type();
			IRExpr *t_expr = IRExpr_Get(tempreg, ty);
			StateMachineSideEffecting *l5 =
				new StateMachineSideEffecting(
					target->rip,
					new StateMachineSideEffectCopy(
						cas->oldLo,
						exprbdd::var(&scopes->exprs, &scopes->bools, t_expr)),
					NULL);
			StateMachineSideEffecting *l4 =
				new StateMachineSideEffecting(
					target->rip,
					StateMachineSideEffectEndAtomic::get(),
					l5);
			StateMachineSideEffectStore *l3se =
				new StateMachineSideEffectStore(
					exprbdd::var(&scopes->exprs, &scopes->bools, cas->addr),
					exprbdd::var(&scopes->exprs, &scopes->bools, cas->dataLo),
					mkPendingMai(target),
					MemoryTag::normal());
			StateMachineState *l3 =
				new StateMachineSideEffecting(
					target->rip,
					l3se,
					l4);
			StateMachineState *l2 =
				new StateMachineBifurcate(
					target->rip,
					bbdd::var(&scopes->bools, expr_eq(t_expr, cas->expdLo)),
					l3,
					l4);
			StateMachineSideEffectLoad *l1se =
				new StateMachineSideEffectLoad(
					tempreg,
					exprbdd::var(&scopes->exprs, &scopes->bools, cas->addr),
					mkPendingMai(target),
					ty,
					MemoryTag::normal());
			StateMachineState *l1 =
				new StateMachineSideEffecting(
					target->rip,
					l1se,
					l2);
			StateMachineState *l0 =
				new StateMachineSideEffecting (
					target->rip,
					StateMachineSideEffectStartAtomic::get(),
					l1);
			*cursor = l0;
			cursor = &l5->target;
			break;
		}
		case Ist_Dirty: {
			IRDirty *dirty = ((IRStmtDirty *)stmt)->details;
			IRType ity = Ity_INVALID;
			StateMachineSideEffect *se;
			if (!strncmp(dirty->cee->name, "helper_load_", strlen("helper_load_"))) {
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
				auto sel = new StateMachineSideEffectLoad(
					dirty->tmp,
					exprbdd::var(&scopes->exprs, &scopes->bools, dirty->args[0]),
					mkPendingMai(target),
					ity,
					MemoryTag::normal());
				se = sel;
			} else if (!strcmp(dirty->cee->name, "amd64g_dirtyhelper_RDTSC")) {
				se = new StateMachineSideEffectCopy(
					dirty->tmp,
					exprbdd::var(&scopes->exprs, &scopes->bools, mkPendingFreeVar(Ity_I64, target, false)));
			} else {
				abort();
			}
			StateMachineSideEffecting *smse =
				new StateMachineSideEffecting(
					target->rip,
					se,
					NULL);
			*cursor = smse;
			cursor = &smse->target;
			break;
		}
		case Ist_MBE:
			break;
		case Ist_Exit: {
			IRStmtExit *stmt = (IRStmtExit *)irsb->stmts[i];
			std::vector<CFGNode *> targets;
			getTargets(target, stmt->dst.rip, targets);
			StateMachineBifurcate *smb;
			smb = new StateMachineBifurcate(
				target->rip,
				bbdd::var(&scopes->bools, stmt->guard),
				NULL,
				NULL);
			ndChoiceState(scopes, &smb->trueTarget, tr, target, pendingRelocs,
				      targets, storeLike, &usedExits);
			*cursor = smb;
			cursor = &smb->falseTarget;
			break;
		}
		case Ist_StartAtomic: {
			StateMachineSideEffecting *s =
				new StateMachineSideEffecting(
					target->rip,
					StateMachineSideEffectStartAtomic::get(),
					NULL);
			*cursor = s;
			cursor = &s->target;
			break;
		}
		case Ist_EndAtomic: {
			StateMachineSideEffecting *s =
				new StateMachineSideEffecting(
					target->rip,
					StateMachineSideEffectEndAtomic::get(),
					NULL);
			*cursor = s;
			cursor = &s->target;
			break;
		}
			
		}
	}

	if (root == NULL) {
		/* This can happen when you're looking at jmp
		   instructions, because they get encoded as empty
		   IRSBs by just setting the next field at the end.
		   Unfortunately, we need to have *something* to
		   return (can't return a relocation), so we need to
		   create a proxy state here. */
		StateMachineSideEffecting *smp =
			new StateMachineSideEffecting(
				target->rip,
				NULL,
				NULL);
		root = smp;
		cursor = &smp->target;
	}

	assert(*cursor == NULL);

	canonicaliseRbp(scopes, root, target->rip, oracle);

	std::vector<CFGNode *> targets;
	if (i == irsb->stmts_used) {
		if (irsb->jumpkind == Ijk_Call) {
			StateMachineSideEffecting *smp =
				new StateMachineSideEffecting(
					target->rip,
					new StateMachineSideEffectStartFunction(
						exprbdd::var(
							&scopes->exprs,
							&scopes->bools,
							IRExpr_Get(
								threadAndRegister::reg(
									tid,
									OFFSET_amd64_RSP,
									0),
								Ity_I64)),
						FrameId()),
					NULL);
			*cursor = smp;
			cursor = &smp->target;

			if (target->getDefault() &&
			    target->getDefault()->instr &&
			    target->getDefault()->instr->rip == extract_call_follower(irsb)) {
				/* Skip this call */
				targets.push_back(target->getDefault()->instr);
				smp = new StateMachineSideEffecting(
					target->rip,
					new StateMachineSideEffectEndFunction(
						exprbdd::var(
							&scopes->exprs,
							&scopes->bools,
							IRExpr_Binop(
								Iop_Add64,
								IRExpr_Get(
									threadAndRegister::reg(
										tid,
										OFFSET_amd64_RSP,
										0),
									Ity_I64),
								IRExpr_Const_U64(-8))),
						FrameId()),
					NULL);
				*cursor = smp;
				cursor = &smp->target;
				smp = new StateMachineSideEffecting(
					target->rip,
					new StateMachineSideEffectCopy(
						threadAndRegister::reg(
							tid,
							OFFSET_amd64_RSP,
							0),
						exprbdd::var(
							&scopes->exprs,
							&scopes->bools,
							IRExpr_Binop(
								Iop_Add64,
								IRExpr_Const_U64(8),
								IRExpr_Get(
									threadAndRegister::reg(
										tid,
										OFFSET_amd64_RSP,
										0),
									Ity_I64)))),
					NULL);
				*cursor = smp;
				cursor = &smp->target;
			}
		} else if (irsb->jumpkind == Ijk_Ret) {
			StateMachineSideEffecting *smp =
				new StateMachineSideEffecting(
					target->rip,
					new StateMachineSideEffectEndFunction(
						exprbdd::var(
							&scopes->exprs,
							&scopes->bools,
							IRExpr_Binop(
								Iop_Add64,
								IRExpr_Get(
									threadAndRegister::reg(
										tid,
										OFFSET_amd64_RSP,
										0),
									Ity_I64),
								IRExpr_Const_U64(-8))),
						FrameId()),
					NULL);
			*cursor = smp;
			cursor = &smp->target;
		}

		if (irsb->next_is_const) {
			getTargets(target, irsb->next_const.rip, targets);
		} else {
			for (auto it = target->successors.begin();
			     it != target->successors.end();
			     it++)
				if (it->instr &&
				    !usedExits.contains(it->instr))
					targets.push_back(it->instr);
		}
	} else {
		IRStmtIMark *mark = (IRStmtIMark *)irsb->stmts[i];
		getTargets(target, mark->addr.rip, targets);
	}
	ndChoiceState(scopes, cursor, tr, target, pendingRelocs, targets, storeLike, NULL);

	return root;
}

struct cfg_translator {
	virtual StateMachineState *operator()(SMScopes *scopes,
					      CFGNode *src,
					      Oracle *oracle,
					      unsigned tid,
					      std::vector<reloc_t> &pendingRelocations) = 0;
};

static StateMachineState *
performTranslation(SMScopes *scopes,
		   std::map<CFGNode *, StateMachineState *> &results,
		   CFGNode *rootCfg,
		   Oracle *oracle,
		   unsigned tid,
		   cfg_translator &node_translator)
{
	std::vector<reloc_t> pendingRelocations;
	StateMachineState *root = NULL;
	pendingRelocations.push_back(
		reloc_t(&root, rootCfg));
	while (!pendingRelocations.empty()) {
		reloc_t r(pendingRelocations.back());
		pendingRelocations.pop_back();
		assert(r.target);
		assert(r.ptr);
		assert(!*r.ptr);
		std::pair<CFGNode *, StateMachineState *> thingToInsert(r.target, (StateMachineState *)NULL);
		auto slot_and_inserted = results.insert(thingToInsert);
		auto slot = slot_and_inserted.first;
		auto inserted = slot_and_inserted.second;
		if (!inserted)
			assert(slot->second);
		else 
			slot->second = node_translator(scopes, r.target, oracle, tid, pendingRelocations);
		*r.ptr = slot->second;
	}
	return root;
}

struct RspCanonicalisationState : public Named {
	class eval_res : public Named {
		eval_res() {}
		char *mkName() const {
			switch (tag) {
			case eval_res_failed:
				return strdup("<failed>");
			case eval_res_delta:
				return my_asprintf("RSP+%ld", val);
			case eval_res_const:
				return my_asprintf("%ld", val);
			}
			abort();
		}
	public:
		enum {
			eval_res_failed, /* Can't say anything about value */
			eval_res_delta, /* Value is a fixed offset from initial RSP */
			eval_res_const /* Value is a constant */
		} tag;
		long val;
		static eval_res failed() {
			eval_res r;
			r.tag = eval_res_failed;
			return r;
		}
		static eval_res delta(long d) {
			eval_res r;
			r.tag = eval_res_delta;
			r.val = d;
			return r;
		}
		static eval_res cnst(long d) {
			eval_res r;
			r.tag = eval_res_const;
			r.val = d;
			return r;
		}

		void operator += (const eval_res &o) {
			switch (tag) {
			case eval_res_failed:
				break;
			case eval_res_delta:
				switch (o.tag) {
				case eval_res_failed:
				case eval_res_delta:
					tag = eval_res_failed;
					break;
				case eval_res_const:
					val += o.val;
					break;
				}
				break;
			case eval_res_const:
				switch (o.tag) {
				case eval_res_failed:
					tag = eval_res_failed;
					break;
				case eval_res_delta:
					tag = eval_res_delta;
					val += o.val;
					break;
				case eval_res_const:
					val += o.val;
					break;
				}
				break;
			}
			clearName();
		}

		eval_res operator - (const eval_res &o) const {
			switch (tag) {
			case eval_res_failed:
				return *this;
			case eval_res_delta:
				switch (o.tag) {
				case eval_res_failed:
					return o;
				case eval_res_delta: /* rsp + k - (rsp + k') -> k - k' */
					return cnst(val - o.val);
				case eval_res_const:
					return delta(val - o.val);
				}
				break;
			case eval_res_const:
				switch (o.tag) {
				case eval_res_failed:
					return o;
				case eval_res_delta: /* k - (rsp + k') -> unrepresentable */
					return failed();
				case eval_res_const:
					return cnst(val - o.val);
				}
				break;
			}
			abort();
		}
		eval_res operator - () const {
			switch (tag) {
			case eval_res_failed:
			case eval_res_delta:
				return failed();
			case eval_res_const:
				return cnst(-val);
			}
			abort();
		}
		eval_res operator + (const eval_res &o) const {
			switch (tag) {
			case eval_res_failed:
				return *this;
			case eval_res_delta:
				switch (o.tag) {
				case eval_res_failed:
					return o;
				case eval_res_delta: /* rsp + k + (rsp + k') -> unrepresentable */
					return failed();
				case eval_res_const:
					return delta(val + o.val);
				}
				break;
			case eval_res_const:
				switch (o.tag) {
				case eval_res_failed:
					return o;
				case eval_res_delta: /* k + (rsp + k') -> rsp + k + k' */
					return delta(val + o.val);
				case eval_res_const:
					return cnst(val + o.val);
				}
				break;
			}
			abort();
		}

		bool merge(const eval_res &o) {
			if (tag == eval_res_failed)
				return false;
			if (tag != o.tag || val != o.val) {
				tag = eval_res_failed;
				clearName();
				return true;
			}
			return false;
		}
	};

	char *mkName() const {
		std::vector<const char *> fragments;
		for (auto it = regs.begin(); it != regs.end(); it++)
			if (it->second.tag != eval_res::eval_res_failed)
				fragments.push_back(vex_asprintf("r%d=%s", it->first, it->second.name()));
		for (auto it = temps.begin(); it != temps.end(); it++)
			if (it->second.tag != eval_res::eval_res_failed)
				fragments.push_back(vex_asprintf("t%d=%s", it->first, it->second.name()));
		for (auto it = stackRsps.begin(); it != stackRsps.end(); it++)
			if (it->second.tag != eval_res::eval_res_failed)
				fragments.push_back(vex_asprintf("stack%ld=%s", it->first, it->second.name()));
		return flattenStringFragmentsMalloc(fragments, ", ", "{", "}");
	}

	std::map<unsigned, eval_res> regs;
	std::map<unsigned, eval_res> temps;
	/* When stack pointers have been pushed on the stack, this
	   tells you where they are and what the appropriate delta
	   is. */
	std::map<long, eval_res> stackRsps;

	bool merge(const RspCanonicalisationState &o) {
		bool res = false;
		for (auto it = regs.begin(); it != regs.end(); ) {
			auto it2 = o.regs.find(it->first);
			if (it2 == o.regs.end()) {
				regs.erase(it++);
				res = true;
			} else {
				res |= it->second.merge(it2->second);
				it++;
			}
		}
		for (auto it = temps.begin(); it != temps.end(); ) {
			auto it2 = o.temps.find(it->first);
			if (it2 == o.temps.end()) {
				temps.erase(it++);
				res = true;
			} else {
				res |= it->second.merge(it2->second);
				it++;
			}
		}
		for (auto it = stackRsps.begin(); it != stackRsps.end(); ) {
			auto it2 = o.stackRsps.find(it->first);
			if (it2 == o.stackRsps.end()) {
				stackRsps.erase(it++);
				res = true;
			} else {
				res |= it->second.merge(it2->second);
				it++;
			}
		}
		clearName();
		return res;
	}

	void set(const threadAndRegister &tr, const eval_res &val) {
		if (tr.isReg()) {
			auto it_did_insert = regs.insert(std::pair<unsigned, eval_res>(tr.asReg(), val));
			it_did_insert.first->second = val;
		} else {
			auto it_did_insert = temps.insert(std::pair<unsigned, eval_res>(tr.asTemp(), val));
			it_did_insert.first->second = val;
		}
		clearName();
	}

	eval_res eval(IRExpr *a) const {
		eval_res res(eval_res::failed());
		switch (a->tag) {
		case Iex_Associative: {
			IRExprAssociative *iea = (IRExprAssociative *)a;
			switch (iea->op) {
			case Iop_Add64:
				res = eval_res::cnst(0);
				for (int i = 0; i < iea->nr_arguments; i++)
					res += eval(iea->contents[i]);
				break;
			default:
				break;
			}
			break;
		}
		case Iex_Binop: {
			IRExprBinop *ieb = (IRExprBinop *)a;
			switch (ieb->op) {
			case Iop_Add64:
				res = eval(ieb->arg1) + eval(ieb->arg2);
				break;
			case Iop_Sub64:
				res = eval(ieb->arg1) - eval(ieb->arg2);
				break;
			default:
				break;
			}
			break;
		}
		case Iex_Const: {
			IRExprConst *iec = (IRExprConst *)a;
			if (iec->type() == Ity_I64)
				res = eval_res::cnst(iec->Ico.content.U64);
			break;
		}
		case Iex_Get: {
			IRExprGet *ieg = (IRExprGet *)a;
			if (ieg->reg.isReg()) {
				auto it = regs.find(ieg->reg.asReg());
				if (it == regs.end())
					return eval_res::failed();
				else
					return it->second;
			} else {
				assert(ieg->reg.isTemp());
				auto it = temps.find(ieg->reg.asTemp());
				if (it == temps.end())
					return eval_res::failed();
				else
					return it->second;
			}
			break;
		}
		case Iex_Unop: {
			IRExprUnop *ieu = (IRExprUnop *)a;
			switch (ieu->op) {
			case Iop_Neg64:
				res = -eval(ieu->arg);
				break;
			default:
				break;
			}
			break;
		}

		case Iex_Load: /* Not available yet */
			abort();
		default:
			break;
		}
		return res;
	}
	eval_res eval(exprbdd *expr) const {
		if (expr->isLeaf())
			return eval(expr->leaf());
		eval_res r1(eval(expr->internal().condition));
		if (r1.tag == eval_res::eval_res_const) {
			if (r1.val)
				return eval(expr->internal().trueBranch);
			else
				return eval(expr->internal().falseBranch);
		}
		eval_res rt(eval(expr->internal().trueBranch));
		eval_res rf(eval(expr->internal().falseBranch));
		rt.merge(rf);
		return rt;
	}
};

/* Find the delta between the start RSP and the RSP at the final crash
 * state.  Subtracting that out from RSP at the start tends to make it
 * much easier to merge machines which start in different places. */
static bool
getRspCanonicalisationDelta(SMScopes *scopes, StateMachineState *root, long *delta,
			    const CfgLabel &entryLabel)
{
	std::map<const StateMachineState *, int> stateLabels;
	if (debug_rsp_canonicalisation) {
		printf("Getting RSP canonicalisation delta for entry point %s\n",
		       entryLabel.name());
	}

	std::map<StateMachineState *, RspCanonicalisationState> res;
	{
		RspCanonicalisationState init;
		init.set(threadAndRegister::reg(-1, OFFSET_amd64_RSP, -1),
			 RspCanonicalisationState::eval_res::delta(0));
		res.insert(std::pair<StateMachineState *, RspCanonicalisationState>(root, init));
	}
	/* States X where we've updated res[X], but not res[X'] for X'
	 * successors of X. */
	std::queue<StateMachineState *> pending;
	pending.push(root);
	while (!pending.empty()) {
		StateMachineState *s = pending.front();
		pending.pop();
		auto it_s = res.find(s);
		assert(it_s != res.end());
		const RspCanonicalisationState &entryState(it_s->second);

		if (debug_rsp_canonicalisation)
			printf("Consider l%d, entry state %s\n",
			       stateLabels[s], entryState.name());

		RspCanonicalisationState exitState(entryState);
		StateMachineSideEffect *se = s->getSideEffect();
		if (se) {
			switch (se->type) {
			case StateMachineSideEffect::Copy: {
				StateMachineSideEffectCopy *sec = (StateMachineSideEffectCopy *)se;
				exitState.set(sec->target, entryState.eval(sec->value));
				break;
			}
			case StateMachineSideEffect::Load: {
				StateMachineSideEffectLoad *sel = (StateMachineSideEffectLoad *)se;
				RspCanonicalisationState::eval_res loadDelta = entryState.eval(sel->addr);
				RspCanonicalisationState::eval_res loadedDelta(RspCanonicalisationState::eval_res::failed());
				if (loadDelta.tag == RspCanonicalisationState::eval_res::eval_res_delta) {
					auto it = entryState.stackRsps.find(loadDelta.val);
					if (it != entryState.stackRsps.end())
						loadedDelta = it->second;
				}
				exitState.set(sel->target, loadedDelta);
				break;
			}
			case StateMachineSideEffect::Store: {
				StateMachineSideEffectStore *ses = (StateMachineSideEffectStore *)se;
				RspCanonicalisationState::eval_res addr = entryState.eval(ses->addr);
				if (addr.tag == RspCanonicalisationState::eval_res::eval_res_delta) {
					RspCanonicalisationState::eval_res data = entryState.eval(ses->data);
					auto it_did_insert = exitState.stackRsps.insert(std::pair<long, RspCanonicalisationState::eval_res>(addr.val, data));
					it_did_insert.first->second = data;
					exitState.clearName();
				}
				break;
			}

			case StateMachineSideEffect::EndFunction: {
				StateMachineSideEffectEndFunction *see = (StateMachineSideEffectEndFunction *)se;
				RspCanonicalisationState::eval_res rspDelta = entryState.eval(see->rsp);
				if (rspDelta.tag == RspCanonicalisationState::eval_res::eval_res_delta) {
					/* Clean up any frame pointers which might
					 * have been pushed by this function. */
					for (auto it = exitState.stackRsps.begin();
					     it != exitState.stackRsps.end();
						) {
						if (it->first < rspDelta.val)
							exitState.stackRsps.erase(it++);
						else
							it++;
					}
					exitState.clearName();
				} else {
					/* Leave the pointers on the
					   stack, since we have no way
					   of knowing which are still
					   live.  This shouldn't ever
					   make any actual difference,
					   beyond makign the analysis
					   a bit slower. */
				}
				break;
			}

			case StateMachineSideEffect::ImportRegister: {
				StateMachineSideEffectImportRegister *r = (StateMachineSideEffectImportRegister *)se;
				exitState.set(r->reg, RspCanonicalisationState::eval_res::failed());
				break;
			}

				/* Most side effects are irrelevant here. */
			case StateMachineSideEffect::Unreached:
			case StateMachineSideEffect::StartAtomic:
			case StateMachineSideEffect::EndAtomic:
			case StateMachineSideEffect::StackLayout:
			case StateMachineSideEffect::AssertFalse:
			case StateMachineSideEffect::StartFunction:
				break;

				/* Shouldn't have Phi states yet. */
			case StateMachineSideEffect::Phi:
				abort();
			}
		}

		if (debug_rsp_canonicalisation)
			printf("Exit state %s\n", exitState.name());

		std::vector<StateMachineState *> succ;
		s->targets(succ);
		for (auto it = succ.begin(); it != succ.end(); it++) {
			auto it2_did_insert = res.insert(std::pair<StateMachineState *, RspCanonicalisationState>(*it, exitState));
			auto it2 = it2_did_insert.first;
			auto did_insert = it2_did_insert.second;
			if (did_insert || it2->second.merge(exitState))
				pending.push(*it);
		}
	}

	if (debug_rsp_canonicalisation) {
		printf("Final table:\n");
		for (auto it = res.begin(); it != res.end(); it++)
			printf("l%d: %s\n", stateLabels[it->first], it->second.name());
	}
	/* So that's as much as we're going to get from that.
	   Hopefully, it'll be enough to assign a label to <crash>
	   state, in which case we have our answer. */
	auto it = res.begin();
	while (it != res.end()) {
		if ( it->first->type == StateMachineState::Terminal &&
		     ((StateMachineTerminal *)it->first)->res == scopes->smrs.cnst(smr_crash) &&
		     it->second.regs.count(OFFSET_amd64_RSP) )
			break;
		it++;
	}
	if (it == res.end()) {
		if (debug_rsp_canonicalisation)
			printf("No RSP delta for crash state\n");
		return false;
	}
	auto it2 = it->second.regs.find(OFFSET_amd64_RSP);
	assert(it2 != it->second.regs.end());
	if (debug_rsp_canonicalisation)
		printf("Crash RSP state %s\n", it2->second.name());
	if (it2->second.tag != RspCanonicalisationState::eval_res::eval_res_delta)
		return false;
	*delta = it2->second.val;
	return true;

}

static StateMachineState *
addEntrySideEffects(SMScopes *scopes, Oracle *oracle, unsigned tid, StateMachineState *final,
		    const std::vector<FrameId> &entryStack, const VexRip &vr,
		    const CfgLabel &entryLabel)
{
	StateMachineState *cursor = final;
	long delta;

	if (oracle->getRbpToRspDelta(vr, &delta)) {
		cursor = new StateMachineSideEffecting(
			vr,
			new StateMachineSideEffectCopy(
				threadAndRegister::reg(tid, OFFSET_amd64_RBP, 0),
				exprbdd::var(
					&scopes->exprs,
					&scopes->bools,
					IRExpr_Associative_V(
						Iop_Add64,
						IRExpr_Const_U64(-delta),
						IRExpr_Get(
							threadAndRegister::reg(tid, OFFSET_amd64_RSP, 0),
							Ity_I64),
						NULL))),
			cursor);
	}

	if (getRspCanonicalisationDelta(scopes, final, &delta, entryLabel)) {
		cursor = new StateMachineSideEffecting(
			vr,
			new StateMachineSideEffectCopy(
				threadAndRegister::reg(tid, OFFSET_amd64_RSP, 0),
				exprbdd::var(
					&scopes->exprs,
					&scopes->bools,
					IRExpr_Associative_V(
						Iop_Add64,
						IRExpr_Const_U64(-delta),
						IRExpr_Get(
							threadAndRegister::reg(tid, OFFSET_amd64_RSP, 0),
							Ity_I64),
						NULL))),
			cursor);
	} else {
		warning("Failed to get RSP canonicalisation delta\n");
	}

	std::set<FrameId> pointAtSelf;
	std::set<FrameId> pointedAtByOthers;

	/* We now need to figure out which stack frames each register
	 * might point to.  The oracle's static analysis can tell us
	 * which registers might point to the current function's
	 * frames, but not anything about the parent frames.  Suppose
	 * we have a call stack like this:
	 *
	 * func1, frame1
	 * func2, frame2
	 * func3, frame3 <--- you are here.
	 *
	 * Static analysis tells us whether frame3 is in registers.
	 * It can also tell us whether frame2 was in any registers or
	 * non-stack memory when func2 called func3.  If it was then
	 * we have to assume that it could have reached any registers
	 * by the time we get to the point of interest in func3.
	 *
	 * As a simplification, it happens that this is exactly what
	 * the static analysis phase does when it's deciding whether
	 * the return value of func3 might include a pointer to
	 * frame2, so all we need to do is look at the aliasing
	 * configuration for RAX at func3's return address and add
	 * frame2 to everything if it includes the stack. */
	PointerAliasingSet framesInRegisters(PointerAliasingSet::nothing);
	assert(vr.stack.size() >= entryStack.size());
	for (int x = 0; x < (int)entryStack.size() - 1; x++) {
		StaticRip rtrnRip(vr.stack[x]);
		Oracle::ThreadRegisterAliasingConfiguration rtrnConfig =
			oracle->getAliasingConfigurationForRip(rtrnRip);
		if (rtrnConfig.v[0].mightPointAtStack()) {
			framesInRegisters |= PointerAliasingSet::frame(entryStack[x]);
			pointAtSelf.insert(entryStack[x]);
			pointedAtByOthers.insert(entryStack[x]);
		}
	}
	{
		StaticRip currentRip(vr.stack.back());
		Oracle::ThreadRegisterAliasingConfiguration currentConfig =
			oracle->getAliasingConfigurationForRip(currentRip);
		if (currentConfig.stackInMemory)
			pointedAtByOthers.insert(entryStack.back());
		if (currentConfig.stackInStack)
			pointAtSelf.insert(entryStack.back());
	}


	/* RSP can be used to refer to any frame in this thread. */
	/* (realias uses more refined information than this, but this
	 * is good enough for all of the other analyses, and realias
	 * derives what it needs when it needs it) */
	PointerAliasingSet rspFrames(PointerAliasingSet::nothing);
	{
		std::set<StateMachineSideEffectStartFunction *> starts;
		std::set<StateMachineSideEffectEndFunction *> ends;
		enumSideEffects(cursor, starts);
		enumSideEffects(cursor, ends);
		for (auto it = starts.begin(); it != starts.end(); it++)
			rspFrames |= PointerAliasingSet::frame((*it)->frame);
		for (auto it = ends.begin(); it != ends.end(); it++)
			rspFrames |= PointerAliasingSet::frame((*it)->frame);
		for (auto it = entryStack.begin(); it != entryStack.end(); it++)
			rspFrames |= PointerAliasingSet::frame(*it);
	}

	/* Set up the initial stack layout */
	{
		std::vector<StateMachineSideEffectStackLayout::entry> stackAndEscape;
		for (auto it = entryStack.begin(); it != entryStack.end(); it++)
			stackAndEscape.push_back(
				StateMachineSideEffectStackLayout::entry(
					*it,
					pointAtSelf.count(*it),
					pointedAtByOthers.count(*it)));
		cursor = new StateMachineSideEffecting(
			vr,
			new StateMachineSideEffectStackLayout(
				stackAndEscape),
			cursor);
	}

	Oracle::ThreadRegisterAliasingConfiguration alias =
		oracle->getAliasingConfigurationForRip(vr);
	for (int i = 0; i < Oracle::NR_REGS; i++) {
		PointerAliasingSet v(alias.v[i]);
		if (i == 4) {
			v = rspFrames;
		} else {
			if (v.otherStackPointer) {
				v.otherStackPointer = false;
				v |= PointerAliasingSet::frame(entryStack.back());
			}
			v |= framesInRegisters;
		}
		cursor = new StateMachineSideEffecting(
			vr,
			new StateMachineSideEffectImportRegister(
				threadAndRegister::reg(tid, i * 8, 0),
				tid,
				i * 8,
				v),
			cursor);
	}
	return cursor;
}

typedef std::vector<FrameId> callStackT;

class StackEqConstraint : public std::pair<callStackT *, callStackT *> {
public:
	StackEqConstraint(callStackT *a, callStackT *b)
		: std::pair<callStackT *, callStackT *>(a, b)
	{}
};

class StackConstraint {
public:
	const char *name(const std::map<callStackT *, int> &labels) const {
		auto a = labels.find(afterExtension);
		auto b = labels.find(beforeExtension);
		assert(a != labels.end());
		assert(b != labels.end());
		return vex_asprintf("l%d = l%d:%p",
				    a->second,
				    b->second,
				    frame);
	}
	callStackT *beforeExtension;
	FrameId *frame;
	callStackT *afterExtension;
	StackConstraint(callStackT *_beforeExtension,
			FrameId *_frame,
			callStackT *_afterExtension)
		: beforeExtension(_beforeExtension),
		  frame(_frame),
		  afterExtension(_afterExtension)
	{
		assert(beforeExtension);
		assert(afterExtension);
		assert(frame);
	}
	bool operator<(const StackConstraint &o) const {
		if (beforeExtension < o.beforeExtension)
			return true;
		if (beforeExtension > o.beforeExtension)
			return false;
		if (frame < o.frame)
			return true;
		if (frame > o.frame)
			return false;
		if (afterExtension < o.afterExtension)
			return true;
		return false;
	}
#ifndef NDEBUG
	void assertSatisfied() const {
		assert(afterExtension->size() == beforeExtension->size() + 1);
		for (unsigned x = 0; x < beforeExtension->size(); x++)
			assert( (*afterExtension)[x] == (*beforeExtension)[x]);
		assert(afterExtension->back() == *frame);
	}
#endif
};

template <typename t> class UnionFind {
	mutable std::map<t, t> content;
public:
	class iterator {
		typename std::map<t, t>::const_iterator it;
		typename std::map<t, t>::const_iterator end_it;
	public:
		iterator(const typename std::map<t, t>::const_iterator &_it,
			 const typename std::map<t, t>::const_iterator &_end_it)
			: it(_it), end_it(_end_it)
		{}
		bool finished() const { return it == end_it; }
		void advance() { it++; }
		const t &element() const { return it->first; }
		const t &representative() const { return it->second; }
	};
	iterator begin() const {
		return iterator(content.begin(), content.end());
	}
	const t &get(const t &what) const {
		auto it = content.find(what);
		assert(it != content.end());
		if (it->first == it->second)
			return it->second;
		const t &o(get(it->second));
		content[what] = o;
		return o;
	}
	void merge(const t &a, const t &b) {
		t a2(get(a));
		t b2(get(b));
		content[a2] = b2;
	}
	void singleton(const t &what) {
		assert(!content.count(what));
		content[what] = what;
	}
};

static void
assignFrameIds(const std::set<StateMachineState *> &roots,
	       unsigned tid,
	       std::map<StateMachineState *, std::vector<FrameId> > &entryStacks)
{
	std::map<const StateMachineState *, int> stateLabels;
	std::map<callStackT *, int> stackLabels;
	if (debug_assign_frame_ids) {
		printf("Assigning frame IDs in:\n");
		std::set<const StateMachineState *> roots2; /* grr, constness */
		for (auto it = roots.begin(); it != roots.end(); it++)
			roots2.insert(*it);
		printStateMachine(roots2, stdout, stateLabels);
	}

	std::map<StateMachineState *, callStackT> stacks;
	std::set<StateMachineState *> allStates;
	for (auto it = roots.begin(); it != roots.end(); it++)
		enumStates(*it, &allStates);
	for (auto it = allStates.begin(); it != allStates.end(); it++)
		stacks[*it].resize(0, FrameId());

	if (debug_assign_frame_ids) {
		for (auto it = allStates.begin(); it != allStates.end(); it++)
			stackLabels[&stacks[*it]] = stateLabels[*it];
		printf("Constraints:\n");
	}

	/* Step one: walk over the set of states and convert them into
	   a set of constraints on the possible values of call
	   stacks. */
	std::set<StackEqConstraint> eq_constraints;
	std::set<StackConstraint> constraints;
	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		StateMachineState *s = *it;
		callStackT *entryState = &stacks[s];
		switch (s->type) {
		case StateMachineState::Terminal:
			if (debug_assign_frame_ids)
				printf("\tl%d: <terminal>\n",
				       stateLabels[s]);
			break;
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
			if (debug_assign_frame_ids)
				printf("\tl%d: l%d == l%d and l%d == l%d\n",
				       stateLabels[s],
				       stackLabels[entryState],
				       stackLabels[&stacks[smb->trueTarget]],
				       stackLabels[entryState],
				       stackLabels[&stacks[smb->falseTarget]]);
			eq_constraints.insert(
				StackEqConstraint
				(entryState, &stacks[smb->trueTarget]));
			eq_constraints.insert(
				StackEqConstraint
				(entryState, &stacks[smb->falseTarget]));
			break;
		}
		case StateMachineState::SideEffecting: {
			auto *smse = (StateMachineSideEffecting *)s;
			StateMachineSideEffect *se = smse->sideEffect;
			if (se && se->type == StateMachineSideEffect::StartFunction) {
				StackConstraint sc(
					entryState,
					(FrameId *)&((StateMachineSideEffectStartFunction *)se)->frame,
					&stacks[smse->target]);
				if (debug_assign_frame_ids)
					printf("\tl%d: %s\n",
					       stateLabels[s],
					       sc.name(stackLabels));
				constraints.insert(sc);
			} else if (se && se->type == StateMachineSideEffect::EndFunction) {
				StackConstraint sc(&stacks[smse->target],
						   (FrameId *)&((StateMachineSideEffectEndFunction *)se)->frame,
						  entryState);
				if (debug_assign_frame_ids)
					printf("\tl%d: %s\n",
					       stateLabels[s],
					       sc.name(stackLabels));
				constraints.insert(sc);
			} else {
				if (debug_assign_frame_ids)
					printf("\tl%d: l%d == l%d\n",
					       stateLabels[s],
					       stackLabels[entryState],
					       stackLabels[&stacks[smse->target]]);
				eq_constraints.insert(
					StackEqConstraint
					(entryState, &stacks[smse->target]));
			}
			break;
		}
		}
	}

	/* The <survive> and <crash> states are special, because they
	 * can have several different contexts.  Easy fix: just don't
	 * try to assign a stack to them at all. */
	std::set<callStackT *> specialStacks;
	for (auto it = stacks.begin(); it != stacks.end(); it++) {
		if ( it->first->type == StateMachineState::Terminal &&
		     ((StateMachineTerminal *)it->first)->res->isLeaf() )
			specialStacks.insert(&it->second);
	}
	for (auto it = eq_constraints.begin(); it != eq_constraints.end(); ) {
		if (specialStacks.count(it->first) ||
		    specialStacks.count(it->second))
			eq_constraints.erase(it++);
		else
			it++;
	}
	for (auto it = constraints.begin(); it != constraints.end(); ) {
		if (specialStacks.count(it->beforeExtension) ||
		    specialStacks.count(it->afterExtension))
			constraints.erase(it++);
		else
			it++;
	}

	/* Step two: Use the eq relationship to build up equivalence
	 * classes over stacks. */
	UnionFind<callStackT *> canonicalisationMap;
	for (auto it = stacks.begin(); it != stacks.end(); it++)
		canonicalisationMap.singleton(&it->second);
	for (auto it = eq_constraints.begin(); it != eq_constraints.end(); it++)
		canonicalisationMap.merge(it->first, it->second);

	if (debug_assign_frame_ids) {
		printf("Stack canonicalisation map:\n");
		for (auto it = canonicalisationMap.begin(); !it.finished(); it.advance())
			printf("\tl%d -> l%d\n", stackLabels[it.element()], stackLabels[it.representative()]);
	}

	std::set<callStackT *> canonStacks;
	for (auto it = canonicalisationMap.begin(); !it.finished(); it.advance())
		canonStacks.insert(it.representative());

	/* Step three: re-express the extend relationships in terms of
	   those equivalence classes. */
	std::set<StackConstraint> constraints2;
	for (auto it = constraints.begin(); it != constraints.end(); it++)
		constraints2.insert(
			StackConstraint(
				canonicalisationMap.get(it->beforeExtension),
				it->frame,
				canonicalisationMap.get(it->afterExtension)));
	constraints = constraints2;

	if (debug_assign_frame_ids) {
		printf("Canonicalised extension constraints:\n");
		for (auto it = constraints.begin(); it != constraints.end(); it++)
			printf("\t%s\n", it->name(stackLabels));
	}

	/* Step four: find the sizes of all of the call stacks.  Basic
	 * procedure is to start by assuming they're all empty and
	 * then extend until we no longer suffer underflows. */
	std::map<callStackT *, int> stackSizes;
	for (auto it = canonStacks.begin(); it != canonStacks.end(); it++)
		stackSizes[*it] = 0;
	bool progress = true;
	while (progress) {
		progress = false;
		for (auto it = constraints.begin(); it != constraints.end(); it++) {
			auto it_before = stackSizes.find(it->beforeExtension);
			auto it_after = stackSizes.find(it->afterExtension);
			if (it_before == stackSizes.end()) {
				if (it_after == stackSizes.end()) {
					continue;
				} else {
					int i = it_after->second - 1;
					if (i < 0) {
						i = 0;
						it_after->second = 1;
					}
					if (debug_assign_frame_ids)
						printf("Initialise l%d stack size to %d from l%d (after)\n",
						       stackLabels[it->beforeExtension],
						       i,
						       stackLabels[it->afterExtension]);
					stackSizes[it->beforeExtension] = i;
					progress = true;
				}
			} else {
				if (it_after == stackSizes.end()) {
					if (debug_assign_frame_ids)
						printf("Initialise l%d stack size to %d from l%d (before)\n",
						       stackLabels[it->afterExtension],
						       it_before->second + 1,
						       stackLabels[it->beforeExtension]);
					stackSizes[it->afterExtension] = it_before->second + 1;
					progress = true;
				} else {
					if (it_after->second != it_before->second + 1) {
						progress = true;
						if (it_after->second < it_before->second + 1) {
							if (debug_assign_frame_ids)
								printf("Update l%d stack size to %d from l%d (before)\n",
								       stackLabels[it->afterExtension],
								       it_before->second + 1,
								       stackLabels[it->beforeExtension]);
							it_after->second = it_before->second + 1;
						} else {
							if (debug_assign_frame_ids)
								printf("Update l%d stack size to %d from l%d (after)\n",
								       stackLabels[it->beforeExtension],
								       it_after->second - 1,
								       stackLabels[it->afterExtension]);
							it_before->second = it_after->second - 1;
						}
					}
				}
			}
		}
	}

	/* Allocate the stacks. */
	for (auto it = stackSizes.begin(); it != stackSizes.end(); it++)
		it->first->resize(it->second, FrameId());

	if (debug_assign_frame_ids) {
		printf("Stack sizes:\n");
		for (auto it = stackSizes.begin(); it != stackSizes.end(); it++)
			printf("\tl%d -> %d\n", stackLabels[it->first], it->second);
	}

	/* Step five: convert the constraints on stacks into
	 * constraints on frame IDs. */
	std::set<std::pair<FrameId *, FrameId *> > frame_eq_constraints;
	for (auto it = constraints.begin(); it != constraints.end(); it++) {
		if (debug_assign_frame_ids)
			printf("Frame constraint: %p == %p for %s\n",
			       &it->afterExtension->back(),
			       it->frame,
			       it->name(stackLabels));
		frame_eq_constraints.insert(
			std::pair<FrameId *, FrameId *>
			(&it->afterExtension->back(), it->frame));
		assert(it->afterExtension->size() ==
		       it->beforeExtension->size() + 1);
		for (unsigned x = 0; x < it->beforeExtension->size(); x++) {
			if (debug_assign_frame_ids)
				printf("Frame constraint2: %p == %p for %s\n",
				       &(*it->afterExtension)[x],
				       &(*it->beforeExtension)[x],
				       it->name(stackLabels));
			frame_eq_constraints.insert(
				std::pair<FrameId *, FrameId *>
				(&(*it->afterExtension)[x],
				 &(*it->beforeExtension)[x]));
		}
	}

	int nextFrameId = 1;

	/* Step six: solve those constraints to assign frame IDs to
	 * everything. */
	for (auto it = frame_eq_constraints.begin();
	     it != frame_eq_constraints.end();
	     it++) {
		if (*it->first != FrameId()) {
			assert(*it->second == *it->first);
			continue;
		}
		FrameId fid(nextFrameId, tid);
		if (debug_assign_frame_ids)
			printf("Assign %s to %p\n", fid.name(), it->first);
		std::queue<FrameId *> toAssign;
		toAssign.push(it->first);
		while (!toAssign.empty()) {
			FrameId *f = toAssign.front();
			toAssign.pop();
			if (*f == fid)
				continue;
			if (debug_assign_frame_ids)
				printf("\tPropagate to %p\n", f);
			assert(*f == FrameId());
			*f = fid;
			for (auto it2 = frame_eq_constraints.begin(); it2 != frame_eq_constraints.end(); it2++) {
				if (it2->first == f)
					toAssign.push(it2->second);
				if (it2->second == f)
					toAssign.push(it2->first);
			}
		}
		nextFrameId++;
	}

#ifndef NDEBUG
	/* Check that all constraints have actually been satisfied. */
	for (auto it = constraints.begin(); it != constraints.end(); it++)
		it->assertSatisfied();
#endif

	/* All frame IDs now assigned.  Extract the root stacks and
	 * return. */
	for (auto it = roots.begin(); it != roots.end(); it++) {
		callStackT *stack = &stacks[*it];
		stack = canonicalisationMap.get(stack);
		callStackT stack0 = *stack;

		/* Frame 0 is always on the top of the stack. */
		stack0.insert(stack0.begin(), FrameId(0, tid));

		entryStacks[*it] = stack0;
		
		if (debug_assign_frame_ids) {
			printf("Stack for l%d: {", stateLabels[*it]);
			for (auto it2 = stack0.begin(); it2 != stack0.end(); it2++) {
				if (it2 != stack0.begin())
					printf(", ");
				printf("%s", it2->name());
			}
			printf("}\n");
		}
	}

	if (debug_assign_frame_ids) {
		printf("Final assignment:\n");
		std::set<const StateMachineState *> roots2; /* grr, constness */
		for (auto it = roots.begin(); it != roots.end(); it++)
			roots2.insert(*it);
		printStateMachine(roots2, stdout, stateLabels);
	}
}

static visit_result
findUsedRegs__Get(std::set<threadAndRegister> *s, const IRExprGet *ieg)
{
	s->insert(ieg->reg);
	return visit_continue;
}
static void
findUsedRegs(exprbdd *expr, std::set<threadAndRegister> &tr)
{
	static struct irexpr_visitor<std::set<threadAndRegister> > visitor;
	visitor.Get = findUsedRegs__Get;
	visit_bdd(&tr, &visitor, visit_irexpr<std::set<threadAndRegister> >, expr);
}
static void
findUsedRegs(bbdd *expr, std::set<threadAndRegister> &tr)
{
	static struct irexpr_visitor<std::set<threadAndRegister> > visitor;
	visitor.Get = findUsedRegs__Get;
	visit_bdd(&tr, &visitor, expr);
}
static void
findUsedRegs(smrbdd *expr, std::set<threadAndRegister> &tr)
{
	static struct irexpr_visitor<std::set<threadAndRegister> > visitor;
	visitor.Get = findUsedRegs__Get;
	visit_bdd(&tr, &visitor, expr);
}

static StateMachineState *
importRegisters(StateMachineState *root)
{
	std::map<StateMachineState *, int> nrMissingPredecessors;
	std::set<StateMachineState *> visited;
	std::vector<StateMachineState *> q;
	q.push_back(root);
	while (!q.empty()) {
		StateMachineState *s = q.back();
		q.pop_back();
		if (!visited.insert(s).second)
			continue;
		std::vector<StateMachineState *> succ;
		s->targets(succ);
		for (auto it = succ.begin(); it != succ.end(); it++) {
			nrMissingPredecessors[*it]++;
			q.push_back(*it);
		}
	}
	visited.clear();

	std::set<threadAndRegister> needImport;

	q.push_back(root);
	std::map<StateMachineState *, std::set<threadAndRegister> > definedRegs;
	while (!TIMEOUT && !q.empty()) {
		StateMachineState *s = q.back();
		q.pop_back();
#ifndef NDEBUG
		assert(visited.insert(s).second);
#endif
		assert(nrMissingPredecessors[s] == 0);
		threadAndRegister tr(threadAndRegister::invalid());
		std::set<threadAndRegister> usedRegs;
		switch (s->type) {
		case StateMachineState::Bifurcate:
			findUsedRegs( ((StateMachineBifurcate *)s)->condition, usedRegs);
			break;
		case StateMachineState::Terminal:
			findUsedRegs( ((StateMachineTerminal *)s)->res, usedRegs);
			break;
		case StateMachineState::SideEffecting: {
			StateMachineSideEffecting *e = (StateMachineSideEffecting *)s;
			StateMachineSideEffect *se = e->sideEffect;
			if (se) {
				switch (se->type) {
				case StateMachineSideEffect::Load:
					findUsedRegs( ((StateMachineSideEffectLoad *)se)->addr, usedRegs );
					break;
				case StateMachineSideEffect::Store:
					findUsedRegs( ((StateMachineSideEffectStore *)se)->addr, usedRegs );
					findUsedRegs( ((StateMachineSideEffectStore *)se)->data, usedRegs );
					break;
				case StateMachineSideEffect::Copy:
					findUsedRegs( ((StateMachineSideEffectCopy *)se)->value, usedRegs );
					break;
				case StateMachineSideEffect::AssertFalse:
					findUsedRegs( ((StateMachineSideEffectAssertFalse *)se)->value, usedRegs );
					break;
				case StateMachineSideEffect::StartAtomic:
					break;
				case StateMachineSideEffect::EndAtomic:
					break;
				case StateMachineSideEffect::Phi: {
					StateMachineSideEffectPhi *p = (StateMachineSideEffectPhi *)s;
					for (auto it = p->generations.begin();
					     it != p->generations.end();
					     it++)
						findUsedRegs(it->val, usedRegs);
					break;
				}
				case StateMachineSideEffect::StartFunction:
					findUsedRegs( ((StateMachineSideEffectStartFunction *)se)->rsp, usedRegs );
					break;
				case StateMachineSideEffect::EndFunction:
					findUsedRegs( ((StateMachineSideEffectEndFunction *)se)->rsp, usedRegs );
					break;
				case StateMachineSideEffect::ImportRegister:
					break;
				case StateMachineSideEffect::StackLayout:
					break;
				case StateMachineSideEffect::Unreached:
					break;
				}
			}
			break;
		}
		}

		std::set<threadAndRegister> defined(definedRegs[s]);
		for (auto it = usedRegs.begin(); it != usedRegs.end(); it++) {
			if (!defined.count(*it))
				needImport.insert(*it);
		}
		if (s->getSideEffect() && s->getSideEffect()->definesRegister(tr))
			defined.insert(tr);
		std::vector<StateMachineState *> succ;
		s->targets(succ);
		for (auto it = succ.begin(); it != succ.end(); it++) {
			auto it2_did_insert = definedRegs.insert(
				(std::pair<StateMachineState *, std::set<threadAndRegister> >
				 (*it, defined)));
			auto it2 = it2_did_insert.first;
			auto did_insert = it2_did_insert.second;
			if (!did_insert) {
				for (auto it3 = it2->second.begin();
				     it3 != it2->second.end();
					) {
					if (defined.count(*it3))
						it3++;
					else
						it2->second.erase(it3++);
				}
			}
			nrMissingPredecessors[*it]--;
			if (nrMissingPredecessors[*it] == 0)
				q.push_back(*it);
			assert(nrMissingPredecessors[*it] >= 0);
		}
	}

	for (auto it = needImport.begin();
	     it != needImport.end();
	     it++) {
		assert(it->isReg());
		root = new StateMachineSideEffecting(
			root->dbg_origin,
			new StateMachineSideEffectImportRegister(
				*it,
				it->tid(),
				it->asReg(),
				PointerAliasingSet::anything),
			root);
	}

	return root;
}

static MemoryAccessIdentifier
assignMais(const MemoryAccessIdentifier &ident, int tid, MaiMap &mm)
{
	const CFGNode *node =
		(const CFGNode *)((unsigned long)(unsigned)ident.tid |
				  ((unsigned long)ident.id << 32));
	return mm(tid, node);
}
struct assignMaiTransformer : public IRExprTransformer {
	int tid;
	MaiMap &mm;
	IRExpr *transformIex(IRExprFreeVariable *fv) {
		return IRExpr_FreeVariable(assignMais(fv->id, tid, mm), fv->ty, fv->isUnique);
	}
	IRExpr *transformIex(IRExprHappensBefore *) {
		abort();
	}
	assignMaiTransformer(int _tid, MaiMap &_mm)
		: tid(_tid), mm(_mm)
	{}
};
static bbdd *
assignMais(SMScopes *scopes, bbdd *cond, int tid, MaiMap &mm)
{
	assignMaiTransformer doit(tid, mm);
	return doit.transform_bbdd(&scopes->bools, cond);
}
static smrbdd *
assignMais(SMScopes *scopes, smrbdd *cond, int tid, MaiMap &mm)
{
	assignMaiTransformer doit(tid, mm);
	return doit.transform_smrbdd(&scopes->bools, &scopes->smrs, cond);
}
static exprbdd *
assignMais(SMScopes *scopes, exprbdd *cond, int tid, MaiMap &mm)
{
	assignMaiTransformer doit(tid, mm);
	return doit.transform_exprbdd(&scopes->bools, &scopes->exprs, cond);
}
static StateMachineSideEffect *
assignMais(SMScopes *scopes, StateMachineSideEffect *se, int tid, MaiMap &mm)
{
	if (!se)
		return NULL;
	switch (se->type) {
	case StateMachineSideEffect::Load: {
		auto l = (StateMachineSideEffectLoad *)se;
		return new StateMachineSideEffectLoad(
			l->target,
			assignMais(scopes, l->addr, tid, mm),
			assignMais(l->rip, tid, mm),
			l->type, l->tag);
	}
	case StateMachineSideEffect::Store: {
		auto l = (StateMachineSideEffectStore *)se;
		return new StateMachineSideEffectStore(
			assignMais(scopes, l->addr, tid, mm),
			assignMais(scopes, l->data, tid, mm),
			assignMais(l->rip, tid, mm),
			l->tag);
	}
	case StateMachineSideEffect::Copy: {
		auto l = (StateMachineSideEffectCopy *)se;
		return new StateMachineSideEffectCopy(
			l,
			assignMais(scopes, l->value, tid, mm));
	}
	case StateMachineSideEffect::AssertFalse: {
		auto l = (StateMachineSideEffectAssertFalse *)se;
		return new StateMachineSideEffectAssertFalse(
			l,
			assignMais(scopes, l->value, tid, mm));
	}
	case StateMachineSideEffect::Unreached:
	case StateMachineSideEffect::StartAtomic:
	case StateMachineSideEffect::EndAtomic:
	case StateMachineSideEffect::ImportRegister:
	case StateMachineSideEffect::StackLayout:
		return se;
	case StateMachineSideEffect::Phi:
		abort();
	case StateMachineSideEffect::StartFunction: {
		auto l = (StateMachineSideEffectStartFunction *)se;
		return new StateMachineSideEffectStartFunction(
			l,
			assignMais(scopes, l->rsp, tid, mm));
	}
	case StateMachineSideEffect::EndFunction: {
		auto l = (StateMachineSideEffectEndFunction *)se;
		return new StateMachineSideEffectEndFunction(
			l,
			assignMais(scopes, l->rsp, tid, mm));
	}
	}
	abort();
}
static void
assignMais(SMScopes *scopes, StateMachineState *s, int tid, MaiMap &mm)
{
	switch (s->type) {
	case StateMachineState::Bifurcate: {
		auto smb = (StateMachineBifurcate *)s;
		smb->set_condition(assignMais(scopes, smb->condition, tid, mm));
		return;
	}
	case StateMachineState::Terminal: {
		auto smt = (StateMachineTerminal *)s;
		smt->set_res(assignMais(scopes, smt->res, tid, mm));
		return;
	}
	case StateMachineState::SideEffecting: {
		auto se = (StateMachineSideEffecting *)s;
		se->sideEffect = assignMais(scopes, se->sideEffect, tid, mm);
		return;
	}
	}
	abort();
}

/* Because the machine is acyclic, there is never simultaneously a
   path from A to B and from B to A.  That means that ``there is a
   path from A to B'' is a partial order.  We now derive that partial
   order and topologically sort it to find the numerical memory access
   identifiers for this thread.  The result is that if:

   a) A and B are in the same thread, and
   b) In this execution both A and B happen

   then A <-< B is just a numerical comparison on the memory access
   identifier ID component.

   Note that if sub-condition (b) does not hold then A <-< B is
   undefined, so we can just use the ID component test there as well.

   The result is that we can always immediately check which of two
   memory access identifies in a single thread happen first, without
   further reference to the machine structure. */
/* Optimisation: rather than explicitly building the partial order, we
   do the toplogical sort directly on the state machine by making sure
   that when we assign an MAI to A we have already assigned MAIs to
   all of the possible predecessors of A. */
static void
setMais(SMScopes *scopes, StateMachineState *root, int tid, MaiMap &mai)
{
	std::map<StateMachineState *, int> predecessors;
	std::set<StateMachineState *> states;
	enumStates(root, &states);
	predecessors[root] = 0;
	for (auto it = states.begin(); it != states.end(); it++) {
		StateMachineState *s = *it;
		std::vector<StateMachineState *> targ;
		s->targets(targ);
		for (auto it2 = targ.begin(); it2 != targ.end(); it2++)
			predecessors[*it2]++;
	}
	assert(predecessors[root] == 0);
	std::vector<StateMachineState *> pending;
	pending.push_back(root);
	while (!pending.empty()) {
		StateMachineState *s = pending.back();
		pending.pop_back();
		assert(predecessors[s] == 0);

		assignMais(scopes, s, tid, mai);
		std::vector<StateMachineState *> targ;
		s->targets(targ);
		for (auto it = targ.begin(); it != targ.end(); it++) {
			if (--predecessors[*it] == 0)
				pending.push_back(*it);
		}
	}
}

static StateMachine *
probeCFGsToMachine(SMScopes *scopes,
		   Oracle *oracle,
		   unsigned tid,
		   HashedSet<HashedPtr<CFGNode> > &roots,
		   HashedSet<HashedPtr<const CFGNode> > &proximalNodes,
		   MaiMap &mai)
{
	struct _ : public cfg_translator {
		HashedSet<HashedPtr<const CFGNode> > &proximalNodes;
		StateMachineState *operator()(SMScopes *scopes,
					      CFGNode *e,
					      Oracle *oracle,
					      unsigned tid,
					      std::vector<reloc_t> &pendingRelocations) {
			if (proximalNodes.contains(e)) {
				return getProximalCause(scopes,
							oracle->ms,
							oracle,
							e,
							e->rip,
							tid);
			} else {
				return cfgNodeToState(scopes, oracle, tid, e, false, pendingRelocations);
			}
		}
		_(HashedSet<HashedPtr<const CFGNode> > &_proximalNodes)
			: proximalNodes(_proximalNodes)
		{}
	} doOne(proximalNodes);

	assert(!roots.empty());

	std::map<CFGNode *, StateMachineState *> results;
	for (auto it = roots.begin(); !it.finished(); it.advance())
		performTranslation(scopes, results, *it, oracle, tid, doOne);

	if (TIMEOUT)
		return NULL;

	std::map<StateMachineState *, std::vector<FrameId> > entryStacks;
	{
		std::set<StateMachineState *> roots_this_sm1;
		for (auto it = roots.begin(); !it.finished(); it.advance())
			roots_this_sm1.insert(results[*it]);
		assignFrameIds(roots_this_sm1, tid, entryStacks);
	}
	std::vector<std::pair<CFGNode *, StateMachineState *> > roots_this_sm2;
	for (auto it = roots.begin(); !it.finished(); it.advance()) {
		CFGNode *cfgnode = *it;
		StateMachineState *root = results[*it];
		root = addEntrySideEffects(scopes, oracle, tid, root, entryStacks[root],
					   cfgnode->rip, cfgnode->label);
		roots_this_sm2.push_back(std::pair<CFGNode *, StateMachineState *>(cfgnode, root));
	}

	std::vector<std::pair<unsigned, const CFGNode *> > cfg_roots_this_sm;
	for (auto it = roots.begin(); !it.finished(); it.advance())
		cfg_roots_this_sm.push_back(std::pair<unsigned, const CFGNode *>(tid, *it));

	StateMachineState *root = entryState(scopes, VexRip(), roots_this_sm2, tid, false);
	root = importRegisters(root);
	if (TIMEOUT)
		return NULL;
	setMais(scopes, root, tid, mai);
	return new StateMachine(root, cfg_roots_this_sm);
}

static StateMachine *
storeCFGsToMachine(SMScopes *scopes,
		   Oracle *oracle,
		   unsigned tid,
		   CFGNode *root,
		   MaiMap &mai)
{
	struct _ : public cfg_translator {
		StateMachineState *operator()(SMScopes *scopes,
					      CFGNode *e,
					      Oracle *oracle,
					      unsigned tid,
					      std::vector<reloc_t> &pendingRelocations)
		{
			return cfgNodeToState(scopes, oracle, tid, e, true, pendingRelocations);
		}
	} doOne;
	std::map<CFGNode *, StateMachineState *> results;
	std::vector<std::pair<unsigned, const CFGNode *> > roots;
	roots.push_back(std::pair<unsigned, const CFGNode *>(tid, root));
	StateMachineState *s =
		performTranslation(
			scopes,
			results,
			root,
			oracle,
			tid,
			doOne);
	if (TIMEOUT)
		return NULL;
	std::set<StateMachineState *> sm_roots;
	sm_roots.insert(s);
	std::map<StateMachineState *, std::vector<FrameId> > entryStacks;
	assignFrameIds(sm_roots, tid, entryStacks);
	if (TIMEOUT)
		return NULL;
	setMais(scopes, s, tid, mai);
	s = addEntrySideEffects(
		scopes,
		oracle,
		tid,
		s,
		entryStacks[s],
		root->rip,
		root->label);
	return new StateMachine(
		importRegisters(s),
		roots);
}

/* End of namespace */
};

StateMachine *
probeCFGsToMachine(SMScopes *scopes,
		   Oracle *oracle,
		   unsigned tid,
		   HashedSet<HashedPtr<CFGNode> > &roots,
		   HashedSet<HashedPtr<const CFGNode> > &proximalNodes,
		   MaiMap &mai)
{
	return _probeCFGsToMachine::probeCFGsToMachine(scopes, oracle, tid, roots, proximalNodes, mai);
}

StateMachine *
storeCFGToMachine(SMScopes *scopes,
		  Oracle *oracle,
		  unsigned tid,
		  CFGNode *root,
		  MaiMap &mai)
{
	return _probeCFGsToMachine::storeCFGsToMachine(scopes, oracle, tid, root, mai);
}

MemoryAccessIdentifier
mkPendingMai(const CFGNode *node)
{
	MemoryAccessIdentifier where(MemoryAccessIdentifier::uninitialised());
	where.tid = (int)(unsigned long)node;
	where.id = (int)((unsigned long)node >> 32);
	return where;
}
