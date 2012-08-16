/* This file is somewhat misnamed, because it also handles store CFGs. */
#include "sli.h"
#include "state_machine.hpp"
#include "cfgnode.hpp"
#include "oracle.hpp"
#include "alloc_mai.hpp"
#include "offline_analysis.hpp"
#include "smb_builder.hpp"

#include "libvex_guest_offsets.h"

#ifndef NDEBUG
static bool debug_assign_frame_ids = false;
#else
#define debug_assign_frame_ids false
#endif

namespace _probeCFGsToMachine {

static void
ndChoiceState(StateMachineState **slot,
	      const ThreadRip &vr,
	      CFGNode *node,
	      std::vector<reloc_t> &pendingRelocs,
	      std::vector<CFGNode *> &targets,
	      MemoryAccessIdentifierAllocator &mai,
	      bool storeLike,
	      std::set<CFGNode *> *usedExits)
{
	if (targets.empty()) {
		if (storeLike)
			*slot = StateMachineCrash::get();
		else
			*slot = StateMachineNoCrash::get();
	} else if (targets.size() == 1) {
		if (usedExits)
			usedExits->insert(targets[0]);
		assert(targets[0] != NULL);
		pendingRelocs.push_back(
			reloc_t(slot, targets[0]));
	} else {
		IRExpr *fv = mai.freeVariable(Ity_I64, vr.thread, node->label, false);
		StateMachineSideEffecting *r =
			new StateMachineSideEffecting(
				vr.rip,
				new StateMachineSideEffectAssertFalse(
					IRExpr_Unop(
						Iop_Not1,
						IRExpr_Binop(
							Iop_CmpEQ64,
							fv,
							IRExpr_Const(
								IRConst_U64(0)))),
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
					IRExpr_Binop(
						Iop_CmpEQ64,
						fv,
						IRExpr_Const(IRConst_U64(x))),
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

static void
getTargets(CFGNode *node, const VexRip &vr, std::vector<CFGNode *> &targets)
{
	for (auto it = node->successors.begin(); it != node->successors.end(); it++)
		if (it->instr && it->instr->rip == vr)
			targets.push_back(it->instr);
}

static StateMachineState *
getLibraryStateMachine(CFGNode *cfgnode, unsigned tid,
		       std::vector<reloc_t> &pendingRelocs,
		       MemoryAccessIdentifierAllocator &mai)
{
	threadAndRegister rax(threadAndRegister::reg(tid, OFFSET_amd64_RAX, 0));
	threadAndRegister arg1(threadAndRegister::reg(tid, OFFSET_amd64_RDI, 0));
	threadAndRegister arg2(threadAndRegister::reg(tid, OFFSET_amd64_RSI, 0));
	threadAndRegister arg3(threadAndRegister::reg(tid, OFFSET_amd64_RDX, 0));
	CFGNode *fallThrough = NULL;
	LibraryFunctionType lib = LibraryFunctionTemplate::none;
	for (auto it = cfgnode->successors.begin(); it != cfgnode->successors.end(); it++) {
		if (it->type == CFGNode::successor_t::succ_default) {
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
		acc = (!rax <<= smb_expr(mai.freeVariable(Ity_I64, tid, cfgnode->label, true))) >>
			(AssertFalse(smb_expr(IRExpr_Unop(Iop_BadPtr, IRExpr_Get(rax, Ity_I64)))) >> end);
		break;
	}
	case LibraryFunctionTemplate::free: {
		acc = end;
		for (int i = 0; i < 8; i++) {
			SMBPtr<SMBExpression> fv(smb_expr(mai.freeVariable(Ity_I64, tid, cfgnode->label, false)));
			acc = (*(smb_reg(arg1, Ity_I64) + smb_const64(i * 8)) <<= fv) >>
				acc;
		}
		acc = If(smb_reg(arg1, Ity_I64) == smb_const64(0),
			 end,
			 acc);
		break;
	}
	case LibraryFunctionTemplate::pthread_mutex_lock: {
		threadAndRegister tmp1(threadAndRegister::temp(tid, 0, 0));
		acc = StartAtomic() >>
			(Load(!tmp1,
			      *smb_reg(arg1, Ity_I64),
			      Ity_I8) >>
			 (AssertFalse(smb_reg(tmp1, Ity_I8) != smb_const8(0)) >>
			  ((*smb_reg(arg1, Ity_I64) <<= smb_const8(1)) >>
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
			      Ity_I8) >>
			 (AssertFalse(smb_reg(tmp1, Ity_I8) != smb_const8(1)) >>
			  ((*smb_reg(arg1, Ity_I64) <<= smb_const8(0)) >>
			   (EndAtomic() >>
			    ((!rax <<= smb_const64(0)) >>
			     end)))));
		break;
	}
	case LibraryFunctionTemplate::__stack_chk_fail:
		return StateMachineUnreached::get();
	case LibraryFunctionTemplate::time: {
		SMBPtr<SMBExpression> fv(smb_expr(mai.freeVariable(Ity_I64, tid, cfgnode->label, false)));
		acc = (!rax <<= fv) >> end;
		If(smb_reg(arg1, Ity_I64) == smb_const64(0),
		   acc,
		   (*smb_reg(arg1, Ity_I64) <<= fv) >> acc);
		break;
	}
	case LibraryFunctionTemplate::none:
		abort();
	}
	if (!acc.content) {
		printf("Need to add support for library function %d (", (int)lib);
		LibraryFunctionTemplate::pp(lib, stdout);
		printf(")\n");
		abort();
	}
	return acc.content->compile(pendingRelocs, mai, cfgnode, tid);
}

static void
canonicaliseRbp(StateMachineState *root, const VexRip &rip, Oracle *oracle)
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
								IRExpr_Const(
									IRConst_U64(-delta)),
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
				smb->condition = doit.doit(smb->condition);
				break;
			}
			case StateMachineState::Crash:
			case StateMachineState::NoCrash:
			case StateMachineState::Unreached:
			case StateMachineState::Stub:
				break;
			case StateMachineState::SideEffecting: {
				StateMachineSideEffect *smse = s->getSideEffect();
				if (smse) {
					bool b;
					StateMachineSideEffect *new_smse =
						doit.transformSideEffect(smse, &b);
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
cfgNodeToState(Oracle *oracle,
	       unsigned tid,
	       CFGNode *target,
	       bool storeLike,
	       MemoryAccessIdentifierAllocator &mai,
	       std::vector<reloc_t> &pendingRelocs)
{
	if (TIMEOUT)
		return NULL;

	ThreadRip tr(tid, target->rip);

	StateMachineState *root;
	root = getLibraryStateMachine(target, tid, pendingRelocs, mai);
	if (root)
		return root;

	IRSB *irsb;
	try {
		irsb = oracle->ms->addressSpace->getIRSBForAddress(tr);
	} catch (BadMemoryException &e) {
		return StateMachineUnreached::get();
	}
	std::set<CFGNode *> usedExits;
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
					isp->data);
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
			StateMachineSideEffect *se =
				new StateMachineSideEffectStore(
					ist->addr,
					ist->data,
					mai(target->label, tid));
			StateMachineSideEffecting *smse =
				new StateMachineSideEffecting(
					target->rip,
					se,
					NULL);
			*cursor = smse;
			cursor = &smse->target;
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
						t_expr),
					NULL);
			StateMachineSideEffecting *l4 =
				new StateMachineSideEffecting(
					target->rip,
					StateMachineSideEffectEndAtomic::get(),
					l5);
			StateMachineState *l3 =
				new StateMachineSideEffecting(
					target->rip,
					new StateMachineSideEffectStore(
						cas->addr,
						cas->dataLo,
						mai(target->label, tid)),
					l4);
			StateMachineState *l2 =
				new StateMachineBifurcate(
					target->rip,
					expr_eq(t_expr, cas->expdLo),
					l3,
					l4);
			StateMachineState *l1 =
				new StateMachineSideEffecting(
					target->rip,
					new StateMachineSideEffectLoad(
						tempreg,
						cas->addr,
						mai(target->label, tid),
						ty),
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
				else
					abort();
				assert(ity != Ity_INVALID);
				se = new StateMachineSideEffectLoad(
					dirty->tmp,
					dirty->args[0],
					mai(target->label, tid),
					ity);
			} else if (!strcmp(dirty->cee->name, "amd64g_dirtyhelper_RDTSC")) {
				se = new StateMachineSideEffectCopy(
					dirty->tmp,
					mai.freeVariable(Ity_I64, tid, target->label, false));
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
				stmt->guard,
				NULL,
				NULL);
			ndChoiceState(&smb->trueTarget, tr, target, pendingRelocs,
				      targets, mai, storeLike, &usedExits);
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

	canonicaliseRbp(root, target->rip, oracle);

	std::vector<CFGNode *> targets;
	if (i == irsb->stmts_used) {
		if (irsb->jumpkind == Ijk_Call) {
			StateMachineSideEffecting *smp =
				new StateMachineSideEffecting(
					target->rip,
					new StateMachineSideEffectStartFunction(
						IRExpr_Get(
							threadAndRegister::reg(
								tid,
								OFFSET_amd64_RSP,
								0),
							Ity_I64),
						FrameId::invalid()),
					NULL);
			*cursor = smp;
			cursor = &smp->target;
			if (irsb->next_is_const &&
			    target->getDefault() &&
			    target->getDefault()->instr &&
			    target->getDefault()->instr->rip != irsb->next_const.rip) {
				targets.push_back(target->getDefault()->instr);
				smp = new StateMachineSideEffecting(
					target->rip,
					new StateMachineSideEffectEndFunction(
						IRExpr_Get(
							threadAndRegister::reg(
								tid,
								OFFSET_amd64_RSP,
								0),
							Ity_I64),
						FrameId::invalid()),
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
						IRExpr_Binop(
							Iop_Add64,
							IRExpr_Const(IRConst_U64(8)),
							IRExpr_Get(
								threadAndRegister::reg(
									tid,
									OFFSET_amd64_RSP,
									0),
								Ity_I64))),
					NULL);
				*cursor = smp;
				cursor = &smp->target;
			}
		} else if (irsb->jumpkind == Ijk_Ret) {
			StateMachineSideEffecting *smp =
				new StateMachineSideEffecting(
					target->rip,
					new StateMachineSideEffectEndFunction(
						IRExpr_Get(
							threadAndRegister::reg(
								tid,
								OFFSET_amd64_RSP,
								0),
							Ity_I64),
						FrameId::invalid()),
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
				    !usedExits.count(it->instr))
					targets.push_back(it->instr);
		}
	} else {
		IRStmtIMark *mark = (IRStmtIMark *)irsb->stmts[i];
		getTargets(target, mark->addr.rip, targets);
	}
	ndChoiceState(cursor, tr, target, pendingRelocs, targets, mai, storeLike, NULL);

	return root;
}

struct cfg_translator {
	virtual StateMachineState *operator()(CFGNode *src,
					      Oracle *oracle,
					      unsigned tid,
					      std::vector<reloc_t> &pendingRelocations) = 0;
};

static StateMachineState *
performTranslation(std::map<CFGNode *, StateMachineState *> &results,
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
			slot->second = node_translator(r.target, oracle, tid, pendingRelocations);
		*r.ptr = slot->second;
	}
	return root;
}

static StateMachineState *
addEntrySideEffects(Oracle *oracle, unsigned tid, StateMachineState *final, const std::vector<FrameId> &entryStack, const VexRip &vr)
{
	StateMachineState *cursor = final;
	long delta;

	cursor = new StateMachineSideEffecting(
		vr,
		new StateMachineSideEffectStackLayout(
			tid,
			entryStack),
		cursor);

	if (oracle->getRbpToRspDelta(vr, &delta)) {
		cursor = new StateMachineSideEffecting(
			vr,
			new StateMachineSideEffectCopy(
				threadAndRegister::reg(tid, OFFSET_amd64_RBP, 0),
				IRExpr_Associative(
					Iop_Add64,
					IRExpr_Get(
						threadAndRegister::reg(tid, OFFSET_amd64_RSP, 0),
						Ity_I64),
					IRExpr_Const(
						IRConst_U64(-delta)),
					NULL)),
			cursor);
	}

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
	 * it can also tell us whether frame2 was in any registers or
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
	for (int x = 0; x < (int)vr.stack.size() - 1; x++) {
		StaticRip rtrnRip(vr.stack[x]);
		Oracle::ThreadRegisterAliasingConfiguration rtrnConfig =
			oracle->getAliasingConfigurationForRip(rtrnRip);
		if (rtrnConfig.v[0].mightPointAtStack())
			framesInRegisters |= PointerAliasingSet::frame(entryStack[x]);
	}
	/* RSP be used to refer to any frame in this thread. */
	/* (realias uses refined information than this, but this is
	 * good enough for all of the other analyses, and realias
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

	Oracle::ThreadRegisterAliasingConfiguration alias =
		oracle->getAliasingConfigurationForRip(vr);
	cursor = new StateMachineSideEffecting(
		vr,
		new StateMachineSideEffectStackLeaked(
			alias.stackHasLeaked,
			tid),
		cursor);
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
			new StateMachineSideEffectPointerAliasing(
				threadAndRegister::reg(tid, i * 8, 0),
				v),
			cursor);
	}
	return cursor;
}

typedef std::vector<FrameId *> callStackT;

static StateMachineState *
assignFrameIds(StateMachineState *root,
	       unsigned tid,
	       std::vector<FrameId> &entryStack)
{
	/* Step one: figure out how many things are on the stack at
	 * the root state.  The idea here is to simulate every
	 * possible path through the machine and check for stack
	 * underflows.  If we get an underflow then we need more stuff
	 * in the initial stack. */
	int initialStackDepth;
	{
		int worst_underflow = 0;
		std::map<StateMachineState *, int> stackDepths;
		std::queue<std::pair<StateMachineState *, int> > pending;
		pending.push(std::pair<StateMachineState *, int>(root, 0));
		while (!pending.empty()) {
			StateMachineState *s = pending.front().first;
			/* pushedFrames == how many frames we've
			   pushed minus how many frames we've popped.
			   Negative if we've underflowed. */
			int pushedFrames = pending.front().second;
			auto it_did_insert = stackDepths.insert(pending.front());
			pending.pop();
			auto it = it_did_insert.first;
			auto did_insert = it_did_insert.second;
			if (!did_insert) {
				if (it->second != pushedFrames) {
					/* The layout at @s depends on
					   the path you take to reach
					   @s.  Consider every
					   path. */
				} else {
					/* Already done this bit */
					continue;
				}
			}
			if (pushedFrames < worst_underflow)
				worst_underflow = pushedFrames;
			if (s->getSideEffect() && s->getSideEffect()->type == StateMachineSideEffect::StartFunction)
				pushedFrames++;
			if (s->getSideEffect() && s->getSideEffect()->type == StateMachineSideEffect::EndFunction)
				pushedFrames--;
			std::vector<StateMachineState *> succ;
			s->targets(succ);
			for (auto it2 = succ.begin(); it2 != succ.end(); it2++) {
				pending.push(std::pair<StateMachineState *, int>(*it2, pushedFrames));
			}
		}
		/* +1 because we want to have a frame ID for the
		 * initial function. */
		initialStackDepth = -worst_underflow + 1;
	}

	if (debug_assign_frame_ids)
		printf("Initial stack depth %d\n", initialStackDepth);

	std::set<FrameId *> unlabelledFrames;
	std::set<FrameId *> preLabelledFrames;
	std::set<FrameId> allocatedFrameIds;

	/* Step two: Set up an initial stack. */
	std::vector<FrameId> entryFrames;
	entryFrames.resize(initialStackDepth, FrameId::invalid());
	callStackT initialStack;
	initialStack.resize(initialStackDepth);
	for (int x = 0; x < initialStackDepth; x++) {
		initialStack[x] = &entryFrames[x];
		unlabelledFrames.insert(&entryFrames[x]);
	}

	if (debug_assign_frame_ids) {
		printf("Initial stack: {");
		for (int x = 0; x < initialStackDepth; x++) {
			if (x != 0)
				printf(", ");
			printf("%p", initialStack[x]);
		}
		printf("}\n");
	}

	/* Step three: Explore the machine again, emitting equality
	 * constraints as we go.  These equality constraints tell you
	 * that the program's function structure is well-nested. */
	std::set<std::pair<FrameId *, FrameId *> > eqConstraints;
	{
		std::queue<std::pair<StateMachineState *, callStackT> > pending;
		pending.push(std::pair<StateMachineState *, callStackT>(root, initialStack));
		while (!pending.empty()) {
			StateMachineState *s = pending.front().first;
			callStackT stack = pending.front().second;
			pending.pop();
			StateMachineSideEffect *se = s->getSideEffect();
			if (se && se->type == StateMachineSideEffect::StartFunction) {
				auto *l = (StateMachineSideEffectStartFunction *)se;
				if (l->frame == FrameId::invalid())
					unlabelledFrames.insert(&l->frame);
				else
					preLabelledFrames.insert(&l->frame);
				stack.push_back(&l->frame);
			}
			if (se && se->type == StateMachineSideEffect::EndFunction) {
				/* Should be enough stuff in initial
				 * stack to avoid underflow. */
				auto l = (StateMachineSideEffectEndFunction *)se;
				assert(!stack.empty());
				FrameId *o = stack.back();
				if (l->frame == FrameId::invalid())
					unlabelledFrames.insert(&l->frame);
				else
					preLabelledFrames.insert(&l->frame);
				eqConstraints.insert(
					std::pair<FrameId *, FrameId *>
					(o, &l->frame));
				stack.pop_back();
			}
			std::vector<StateMachineState *> succ;
			s->targets(succ);
			for (auto it2 = succ.begin(); it2 != succ.end(); it2++)
				pending.push(std::pair<StateMachineState *, callStackT>(*it2, stack));
		}
	}

	if (debug_assign_frame_ids) {
		printf("Frame ID constraints:\n");
		for (auto it = eqConstraints.begin(); it != eqConstraints.end(); it++)
			printf("\t%p == %p\n", it->first, it->second);
		printf("Constrained frames:\n");
		for (auto it = preLabelledFrames.begin(); it != preLabelledFrames.end(); it++)
			printf("\t%p == %s\n", *it, (*it)->name());
	}

	/* Step 4: Propagate any labels which might already have been specified. */
	while (!preLabelledFrames.empty()) {
		auto it = preLabelledFrames.begin();
		FrameId *f = *it;
		const FrameId &label(*f);
		preLabelledFrames.erase(it);
		allocatedFrameIds.insert(label);

		if (debug_assign_frame_ids)
			printf("Propagate %s from %p\n", label.name(), f);

		assert(label != FrameId::invalid());
		std::queue<FrameId *> pending;
		std::set<FrameId *> done;
		pending.push(f);
		while (!pending.empty()) {
			f = pending.front();
			pending.pop();
			if (!done.insert(f).second)
				continue;
			if (debug_assign_frame_ids)
				printf("\tPropagate %s to %p\n", label.name(), f);
			if (*f == FrameId::invalid()) {
				*f = label;
				assert(unlabelledFrames.count(f));
				unlabelledFrames.erase(f);
			} else {
				assert(*f == label);
			}
			for (auto it = eqConstraints.begin(); it != eqConstraints.end(); it++) {
				if (it->first == f) {
					if (debug_assign_frame_ids)
						printf("\tEq rule: %p == %p\n", it->first, it->second);
					pending.push(it->second);
				}
				if (it->second == f) {
					if (debug_assign_frame_ids)
						printf("\tEq rule: %p == %p\n", it->second, it->first);
					pending.push(it->first);
				}
			}
		}
	}

	/* Step 5: Label the remaining frames, using the maximum
	   number of distinct labels which is compatible with the eq
	   constraints. */
	unsigned nextLabel = 0;
	while (!unlabelledFrames.empty()) {
		auto it = unlabelledFrames.begin();
		FrameId *f = *it;
		FrameId label(nextLabel, tid);
		nextLabel++;

		while (allocatedFrameIds.count(label)) {
			label = FrameId(nextLabel, tid);
			nextLabel++;
		}
		allocatedFrameIds.insert(label);

		if (debug_assign_frame_ids)
			printf("Assign %s to %p\n", label.name(), f);

		assert(*f == FrameId::invalid());
		/* Go and label the SCC */
		std::queue<FrameId *> pending;
		pending.push(f);
		while (!pending.empty()) {
			FrameId *fst = pending.front();
			pending.pop();
			if (*fst == label) {
				/* Already done this one */
				assert(!unlabelledFrames.count(fst));
				continue;
			}
			if (debug_assign_frame_ids)
				printf("\tAssign %s to %p for eq rule\n",
				       label.name(), fst);
			assert(*fst == FrameId::invalid());
			assert(unlabelledFrames.count(fst));
			*fst = label;
			unlabelledFrames.erase(fst);
			for (auto it = eqConstraints.begin(); it != eqConstraints.end(); it++) {
				if (it->first == fst) {
					if (debug_assign_frame_ids)
						printf("\tEq rule: %p == %p\n", it->first, it->second);
					pending.push(it->second);
				}
				if (it->second == fst) {
					if (debug_assign_frame_ids)
						printf("\tEq rule: %p == %p\n", it->second, it->first);
					pending.push(it->first);
				}
			}
		}
	}

	/* Check that the resulting labelling is valid */
#ifndef NDEBUG
	for (auto it = eqConstraints.begin(); it != eqConstraints.end(); it++)
		assert(*it->first == *it->second);
	for (auto it1 = entryFrames.begin(); it1 != entryFrames.end(); it1++)
		for (auto it2 = it1 + 1; it2 != entryFrames.end(); it2++)
			assert(*it1 != *it2);
#endif

	entryStack = entryFrames;

	return root;
}

static void
probeCFGsToMachine(Oracle *oracle,
		   unsigned tid,
		   std::set<CFGNode *> &roots,
		   std::set<const CFGNode *> &proximalNodes,
		   MemoryAccessIdentifierAllocator &mai,
		   std::set<StateMachine *> &out)
{
	struct _ : public cfg_translator {
		MemoryAccessIdentifierAllocator &mai;
		std::set<const CFGNode *> &proximalNodes;
		StateMachineState *operator()(CFGNode *e,
					      Oracle *oracle,
					      unsigned tid,
					      std::vector<reloc_t> &pendingRelocations) {
			if (proximalNodes.count(e)) {
				return getProximalCause(oracle->ms,
							mai,
							e->label,
							e->rip,
							tid);
			} else {
				return cfgNodeToState(oracle, tid, e, false, mai, pendingRelocations);
			}
		}
		_(MemoryAccessIdentifierAllocator &_mai,
		  std::set<const CFGNode *> &_proximalNodes)
			: mai(_mai), proximalNodes(_proximalNodes)
		{}
	} doOne(mai, proximalNodes);

	std::map<CFGNode *, StateMachineState *> results;
	for (auto it = roots.begin(); it != roots.end(); it++)
		performTranslation(results, *it, oracle, tid, doOne);

	if (TIMEOUT)
		return;

	for (auto it = roots.begin(); it != roots.end(); it++) {
		StateMachineState *root = results[*it];
		assert(root);
		std::vector<std::pair<unsigned, VexRip> > origin;
		origin.push_back(std::pair<unsigned, VexRip>(tid, root->origin));
		std::vector<const CFGNode *> roots_this_sm;
		roots_this_sm.push_back(*it);
		std::vector<FrameId> entryStack;
		root = assignFrameIds(root, tid, entryStack);
		root = addEntrySideEffects(oracle, tid, root, entryStack, root->origin);
		StateMachine *sm = new StateMachine(root, origin, roots_this_sm);
		sm->sanityCheck();
		out.insert(sm);
	}
}

static StateMachine *
storeCFGsToMachine(Oracle *oracle, unsigned tid, CFGNode *root,
		   MemoryAccessIdentifierAllocator &mai)
{
	struct _ : public cfg_translator {
		MemoryAccessIdentifierAllocator *mai;
		StateMachineState *operator()(CFGNode *e,
					      Oracle *oracle,
					      unsigned tid,
					      std::vector<reloc_t> &pendingRelocations)
		{
			return cfgNodeToState(oracle, tid, e, true, *mai, pendingRelocations);
		}
	} doOne;
	doOne.mai = &mai;
	std::map<CFGNode *, StateMachineState *> results;
	std::vector<std::pair<unsigned, VexRip> > origin;
	origin.push_back(std::pair<unsigned, VexRip>(tid, root->rip));
	std::vector<const CFGNode *> roots;
	roots.push_back(root);
	StateMachineState *s =
		performTranslation(
			results,
			root,
			oracle,
			tid,
			doOne);
	if (TIMEOUT)
		return NULL;
	std::vector<FrameId> entryStack;
	s = assignFrameIds(s, tid, entryStack);
	s = addEntrySideEffects(
			oracle,
			tid,
			s,
			entryStack,
			root->rip);
	StateMachine *sm = new StateMachine(
		s,
		origin,
		roots);
	return sm;
}

/* End of namespace */
};

void
probeCFGsToMachine(Oracle *oracle,
		   unsigned tid,
		   std::set<CFGNode *> &roots,
		   std::set<const CFGNode *> &proximalNodes,
		   MemoryAccessIdentifierAllocator &mai,
		   std::set<StateMachine *> &out)
{
	_probeCFGsToMachine::probeCFGsToMachine(oracle, tid, roots, proximalNodes, mai, out);
}

StateMachine *
storeCFGToMachine(Oracle *oracle,
		  unsigned tid,
		  CFGNode *root,
		  MemoryAccessIdentifierAllocator &mai)
{
	return _probeCFGsToMachine::storeCFGsToMachine(oracle, tid, root, mai);
}
