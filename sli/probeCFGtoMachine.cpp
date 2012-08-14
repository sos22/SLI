/* This file is somewhat misnamed, because it also handles store CFGs. */
#include "sli.h"
#include "state_machine.hpp"
#include "cfgnode.hpp"
#include "oracle.hpp"
#include "alloc_mai.hpp"
#include "offline_analysis.hpp"
#include "smb_builder.hpp"

#include "libvex_guest_offsets.h"

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
							Ity_I64)),
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
							Ity_I64)),
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
							Ity_I64)),
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
addEntrySideEffects(Oracle *oracle, unsigned tid, StateMachineState *final, const VexRip &vr)
{
	StateMachineState *cursor = final;
	long delta;
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
	Oracle::ThreadRegisterAliasingConfiguration alias =
		oracle->getAliasingConfigurationForRip(vr);
	cursor = new StateMachineSideEffecting(
		vr,
		new StateMachineSideEffectStackLeaked(
			alias.stackHasLeaked),
		cursor);
	for (int i = 0; i < Oracle::NR_REGS; i++)
		cursor = new StateMachineSideEffecting(
			vr,
			new StateMachineSideEffectPointerAliasing(
				threadAndRegister::reg(tid, i * 8, 0),
				alias.v[i]),
			cursor);
	return cursor;
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

	for (auto it = roots.begin(); it != roots.end(); it++) {
		StateMachineState *root = results[*it];
		assert(root);
		std::vector<std::pair<unsigned, VexRip> > origin;
		origin.push_back(std::pair<unsigned, VexRip>(tid, root->origin));
		std::vector<const CFGNode *> roots_this_sm;
		roots_this_sm.push_back(*it);
		root = addEntrySideEffects(oracle, tid, root, root->origin);
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
	StateMachine *sm = new StateMachine(
		addEntrySideEffects(
			oracle,
			tid,
			performTranslation(results, root, oracle, tid, doOne),
			root->rip),
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
