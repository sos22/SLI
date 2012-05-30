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
	      const VexRip &vr,
	      std::vector<reloc_t> &pendingRelocs,
	      std::vector<CFGNode *> &targets,
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
		pendingRelocs.push_back(
			reloc_t(slot, targets[0]));
	} else {
		StateMachineNdChoice *nd =
			new StateMachineNdChoice(vr);
		nd->successors.resize(targets.size());
		for (unsigned x = 0; x < targets.size(); x++) {
			if (usedExits)
				usedExits->insert(targets[x]);
			pendingRelocs.push_back(
				reloc_t(&nd->successors[x], targets[x]));
		}
		*slot = nd;
	}
}

static void
getTargets(CFGNode *node, const VexRip &vr, std::vector<CFGNode *> &targets)
{
	if (node->fallThrough.second &&
	    node->fallThrough.first == vr)
		targets.push_back(node->fallThrough.second);
	for (auto it = node->branches.begin(); it != node->branches.end(); it++)
		if (it->second && it->first == vr)
			targets.push_back(it->second);
}

static StateMachineState *
getLibraryStateMachine(CFGNode *cfgnode, unsigned tid,
		       std::vector<reloc_t> &pendingRelocs,
		       MemoryAccessIdentifierAllocator &mai)
{
	assert(cfgnode->fallThrough.second);
	assert(cfgnode->branches.empty());
	threadAndRegister rax(threadAndRegister::reg(tid, OFFSET_amd64_RAX, 0));
	threadAndRegister arg1(threadAndRegister::reg(tid, OFFSET_amd64_RDI, 0));
	threadAndRegister arg2(threadAndRegister::reg(tid, OFFSET_amd64_RSI, 0));
	threadAndRegister arg3(threadAndRegister::reg(tid, OFFSET_amd64_RDX, 0));
	SMBPtr<SMBState> end(Proxy(cfgnode->fallThrough.second));
	SMBPtr<SMBState> acc(NULL);
	switch (cfgnode->libraryFunction) {
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
		acc = (!rax <<= smb_expr(mai.freeVariable(Ity_I64, ThreadRip(tid, cfgnode->my_rip), true))) >>
			(AssertFalse(smb_expr(IRExpr_Unop(Iop_BadPtr, IRExpr_Get(rax, Ity_I64)))) >> end);
		break;
	}
	case LibraryFunctionTemplate::free: {
		acc = end;
		for (int i = 0; i < 8; i++) {
			SMBPtr<SMBExpression> fv(smb_expr(mai.freeVariable(Ity_I64, ThreadRip(tid, cfgnode->my_rip), false)));
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
	case LibraryFunctionTemplate::none:
		abort();
	}
	if (!acc.content) {
		printf("Need to add support for library function %d (",
		       (int)cfgnode->libraryFunction);
		LibraryFunctionTemplate::pp(cfgnode->libraryFunction, stdout);
		printf(")\n");
		abort();
	}
	return acc.content->compile(ThreadRip(tid, cfgnode->my_rip), pendingRelocs, mai);
}

static StateMachineState *
cfgNodeToState(Oracle *oracle,
	       unsigned tid,
	       CFGNode *target,
	       bool storeLike,
	       MemoryAccessIdentifierAllocator &mai,
	       std::vector<reloc_t> &pendingRelocs)
{
	ThreadRip tr(tid, target->my_rip);

	if (target->libraryFunction)
		return getLibraryStateMachine(target, tid, pendingRelocs, mai);

	IRSB *irsb;
	try {
		irsb = oracle->ms->addressSpace->getIRSBForAddress(tr);
	} catch (BadMemoryException &e) {
		return StateMachineUnreached::get();
	}
	std::set<CFGNode *> usedExits;
	StateMachineState *root = NULL;
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
					target->my_rip,
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
					mai(tr));
			StateMachineSideEffecting *smse =
				new StateMachineSideEffecting(
					target->my_rip,
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
					target->my_rip,
					new StateMachineSideEffectCopy(
						cas->oldLo,
						t_expr),
					NULL);
			StateMachineSideEffecting *l4 =
				new StateMachineSideEffecting(
					target->my_rip,
					StateMachineSideEffectEndAtomic::get(),
					l5);
			StateMachineState *l3 =
				new StateMachineSideEffecting(
					target->my_rip,
					new StateMachineSideEffectStore(
						cas->addr,
						cas->dataLo,
						mai(tr)),
					l4);
			StateMachineState *l2 =
				new StateMachineBifurcate(
					target->my_rip,
					expr_eq(t_expr, cas->expdLo),
					l3,
					l4);
			StateMachineState *l1 =
				new StateMachineSideEffecting(
					target->my_rip,
					new StateMachineSideEffectLoad(
						tempreg,
						cas->addr,
						mai(tr),
						ty),
					l2);
			StateMachineState *l0 =
				new StateMachineSideEffecting (
					target->my_rip,
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
					mai(tr),
					ity);
			} else if (!strcmp(dirty->cee->name, "amd64g_dirtyhelper_RDTSC")) {
				se = new StateMachineSideEffectCopy(
					dirty->tmp,
					mai.freeVariable(Ity_I64, tr, false));
			} else {
				abort();
			}
			StateMachineSideEffecting *smse =
				new StateMachineSideEffecting(
					target->my_rip,
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
				target->my_rip,
				stmt->guard,
				NULL,
				NULL);
			ndChoiceState(&smb->trueTarget, target->my_rip,
				      pendingRelocs, targets, storeLike, &usedExits);
			*cursor = smb;
			cursor = &smb->falseTarget;
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
				target->my_rip,
				NULL,
				NULL);
		root = smp;
		cursor = &smp->target;
	}

	assert(*cursor == NULL);

	std::vector<CFGNode *> targets;
	if (i == irsb->stmts_used) {
		if (irsb->next_is_const) {
			getTargets(target, irsb->next_const.rip, targets);
		} else {
			if (target->fallThrough.second &&
			    !usedExits.count(target->fallThrough.second))
				targets.push_back(target->fallThrough.second);
			for (auto it = target->branches.begin();
			     it != target->branches.end();
			     it++)
				if (it->second &&
				    !usedExits.count(it->second))
					targets.push_back(it->second);
		}
	} else {
		IRStmtIMark *mark = (IRStmtIMark *)irsb->stmts[i];
		getTargets(target, mark->addr.rip, targets);
	}
	ndChoiceState(cursor, target->my_rip, pendingRelocs, targets, storeLike, NULL);

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

/* The rest of the analysis can't use any more than four slots of RIP
   context, so there's not really much point in maintaining them. */
static StateMachine *
truncateRips(StateMachine *sm)
{
	struct : public StateMachineTransformer {
		bool truncateVexRip(const VexRip &in, VexRip *out) {
			if (in.stack.size() <= (unsigned)DynAnalysisRip::DATABASE_RIP_DEPTH)
				return false;
			std::vector<unsigned long> c;
			c.reserve(DynAnalysisRip::DATABASE_RIP_DEPTH);
			for (auto it = in.stack.rbegin(); it != in.stack.rend(); it++)
				c.push_back(*it);
			*out= VexRip(c);
			return true;
		}
		StateMachineSideEffectLoad *transformOneSideEffect(
			StateMachineSideEffectLoad *smsel, bool *done_something)
		{
			VexRip t;
			if (truncateVexRip(smsel->rip.rip.rip, &t)) {
				*done_something = true;
				return new StateMachineSideEffectLoad(
					smsel->target,
					smsel->addr,
					MemoryAccessIdentifier(
						ThreadRip(smsel->rip.rip.thread, t),
						smsel->rip.generation),
					smsel->type);
			} else {
				return NULL;
			}
		}
		StateMachineSideEffectStore *transformOneSideEffect(
			StateMachineSideEffectStore *smses, bool *done_something)
		{
			VexRip t;
			if (truncateVexRip(smses->rip.rip.rip, &t)) {
				*done_something = true;
				return new StateMachineSideEffectStore(
					smses->addr,
					smses->data,
					MemoryAccessIdentifier(ThreadRip(smses->rip.rip.thread, t), smses->rip.generation));
			} else {
				return NULL;
			}
		}
	} doit;
	return doit.transform(sm);
}

static void
probeCFGsToMachine(Oracle *oracle, unsigned tid, std::set<CFGNode *> &roots,
		   const DynAnalysisRip &proximalRip,
		   StateMachineState *proximal,
		   MemoryAccessIdentifierAllocator &mai,
		   std::set<StateMachine *> &out)
{
	struct _ : public cfg_translator {
		const DynAnalysisRip &proximalRip;
		MemoryAccessIdentifierAllocator &mai;		
		StateMachineState *proximal;
		StateMachineState *operator()(CFGNode *e,
					      Oracle *oracle,
					      unsigned tid,
					      std::vector<reloc_t> &pendingRelocations) {
			if (DynAnalysisRip(e->my_rip) == proximalRip) {
				return proximal;
			} else {
				return cfgNodeToState(oracle, tid, e, false, mai, pendingRelocations);
			}
		}
		_(const DynAnalysisRip &_proximalRip,
		  MemoryAccessIdentifierAllocator &_mai,
		  StateMachineState *_proximal)
			: proximalRip(_proximalRip), mai(_mai), proximal(_proximal)
		{}
	} doOne(proximalRip, mai, proximal);

	std::map<CFGNode *, StateMachineState *> results;
	for (auto it = roots.begin(); it != roots.end(); it++)
		performTranslation(results, *it, oracle, tid, doOne);

	for (auto it = roots.begin(); it != roots.end(); it++) {
		StateMachineState *root = results[*it];
		assert(root);
		std::vector<std::pair<unsigned, VexRip> > origin;
		origin.push_back(std::pair<unsigned, VexRip>(tid, root->origin));
		StateMachine *sm = new StateMachine(root, origin);
		sm->sanityCheck();
		out.insert(truncateRips(sm));
	}
}

static StateMachine *
storeCFGsToMachine(Oracle *oracle, unsigned tid, CFGNode *root, MemoryAccessIdentifierAllocator &mai)
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
	origin.push_back(std::pair<unsigned, VexRip>(tid, root->my_rip));
	StateMachine *sm = new StateMachine(performTranslation(results, root, oracle, tid, doOne),
					    origin);
	return truncateRips(sm);
}

/* End of namespace */
};

void
probeCFGsToMachine(Oracle *oracle, unsigned tid,
		   std::set<CFGNode *> &roots,
		   const DynAnalysisRip &targetRip,
		   StateMachineState *proximal,
		   MemoryAccessIdentifierAllocator &mai,
		   std::set<StateMachine *> &out)
{
	return _probeCFGsToMachine::probeCFGsToMachine(oracle, tid, roots, targetRip, proximal, mai, out);
}

StateMachine *
storeCFGToMachine(Oracle *oracle,
		  unsigned tid,
		  CFGNode *root,
		  MemoryAccessIdentifierAllocator &mai)
{
	return _probeCFGsToMachine::storeCFGsToMachine(oracle, tid, root, mai);
}
