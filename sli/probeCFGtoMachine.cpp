/* This file is somewhat misnamed, because it also handles store CFGs. */
#include "sli.h"
#include "state_machine.hpp"
#include "cfgnode.hpp"
#include "oracle.hpp"
#include "alloc_mai.hpp"

namespace _probeCFGsToMachine {

struct reloc_t {
	StateMachineState **ptr;
	CFGNode *target;
	reloc_t(StateMachineState **_ptr,
		CFGNode *_target)
		: ptr(_ptr), target(_target)
	{}
};

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
cfgNodeToState(Oracle *oracle,
	       unsigned tid,
	       CFGNode *target,
	       bool storeLike,
	       MemoryAccessIdentifierAllocator &mai,
	       std::vector<reloc_t> &pendingRelocs)
{
	ThreadRip tr(tid, target->my_rip);
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

			   l1: t <- *x then l2
			   l2: if (t == expd) then l3 else l4
			   l3: *x <- data
			   l4: old <- t
			*/
#warning This breaks the atomicity of the CAS
			/* Breaking the atomicity of the CAS like that
			   means that we'll sometimes report a crash
			   which can't happen, but we'll never miss a
			   crash which can. */
			IRTemp t = newIRTemp(irsb->tyenv);
			threadAndRegister tempreg = threadAndRegister::temp(tid, t, 0);
			IRType ty = cas->expdLo->type();
			IRExpr *t_expr = IRExpr_Get(tempreg, ty);
			StateMachineSideEffecting *l4 =
				new StateMachineSideEffecting(
					target->my_rip,
					new StateMachineSideEffectCopy(
						cas->oldLo,
						t_expr),
					NULL);
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
			*cursor = l1;
			cursor = &l4->target;
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
					mai.freeVariable(Ity_I64, tr));
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
		out.insert(sm);
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
	return new StateMachine(performTranslation(results, root, oracle, tid, doOne),
				origin);
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
