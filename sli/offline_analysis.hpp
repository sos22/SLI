#ifndef OFFLINE_ANALYSIS_HPP__
#define OFFLINE_ANALYSIS_HPP__

#include <map>

#include "state_machine.hpp"
#include "oracle.hpp"

#include "libvex_ir.h"

#define STORING_THREAD 97

class IRExprTransformer {
	IRExpr *_currentIRExpr;
protected:
	IRExpr *currentIRExpr() { return _currentIRExpr; }
	virtual IRExpr *transformIex(IRExprGet *) { return NULL; }
	virtual IRExpr *transformIex(IRExprGetI *e)
	{
		bool t = false;
		IRExpr *e2 = transformIRExpr(e->ix, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_GetI(e->descr, e2, e->bias, e->tid);
	}
	virtual IRExpr *transformIex(IRExprQop *e)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->arg1, &t);
		IRExpr *a2 = transformIRExpr(e->arg2, &t);
		IRExpr *a3 = transformIRExpr(e->arg3, &t);
		IRExpr *a4 = transformIRExpr(e->arg4, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_Qop(e->op, a1, a2, a3, a4);
	}
	virtual IRExpr *transformIex(IRExprTriop *e)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->arg1, &t);
		IRExpr *a2 = transformIRExpr(e->arg2, &t);
		IRExpr *a3 = transformIRExpr(e->arg3, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_Triop(e->op, a1, a2, a3);
	}
	virtual IRExpr *transformIex(IRExprBinop *e)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->arg1, &t);
		IRExpr *a2 = transformIRExpr(e->arg2, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_Binop(e->op, a1, a2);
	}
	virtual IRExpr *transformIex(IRExprUnop *e)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->arg, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_Unop(e->op, a1);
	}
	virtual IRExpr *transformIex(IRExprLoad *e)
	{
		bool t = false;
		IRExpr *addr = transformIRExpr(e->addr, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_Load(e->ty, addr, e->rip);
	}
	virtual IRExpr *transformIex(IRExprConst *)
	{
		return NULL;
	}
	virtual IRExpr *transformIex(IRExprMux0X *e)
	{
		bool t = false;
		IRExpr *c = transformIRExpr(e->cond, &t);
		IRExpr *z = transformIRExpr(e->expr0, &t);
		IRExpr *x = transformIRExpr(e->exprX, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_Mux0X(c, z, x);
	}
	virtual IRExpr *transformIex(IRExprCCall *);
	virtual IRExpr *transformIex(IRExprAssociative *);
	virtual IRExpr *transformIex(IRExprClientCall *);
	virtual IRExpr *transformIex(IRExprClientCallFailed *e)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->target, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_ClientCallFailed(a1);
	}
	virtual IRExpr *transformIex(IRExprHappensBefore *) { return NULL; }
	virtual IRExpr *transformIex(IRExprPhi *) { return NULL; }
	virtual IRExpr *transformIex(IRExprFreeVariable *) { return NULL; }
	virtual IRExpr *transformIRExpr(IRExpr *e, bool *done_something);
public:
	IRExpr *doit(IRExpr *e, bool *done_something) { return transformIRExpr(e, done_something); }
	IRExpr *doit(IRExpr *e) { bool t; return doit(e, &t); }
};

class StateMachineTransformer : public IRExprTransformer {
protected:
	virtual StateMachineSideEffectLoad *transformOneSideEffect(
		StateMachineSideEffectLoad *, bool *);
	virtual StateMachineSideEffectStore *transformOneSideEffect(
		StateMachineSideEffectStore *, bool *);
	virtual StateMachineSideEffectAssertFalse *transformOneSideEffect(
		StateMachineSideEffectAssertFalse *, bool *);
	virtual StateMachineSideEffectCopy *transformOneSideEffect(
		StateMachineSideEffectCopy *, bool *);
	virtual StateMachineSideEffectUnreached *transformOneSideEffect(
		StateMachineSideEffectUnreached *, bool *) {
		return NULL;
	}
	virtual StateMachineSideEffectPhi *transformOneSideEffect(
		StateMachineSideEffectPhi *, bool *);
	virtual StateMachineUnreached *transformOneState(StateMachineUnreached *,
							 bool *)
	{ return NULL; }
	virtual StateMachineCrash *transformOneState(StateMachineCrash *,
						     bool *)
	{ return NULL; }
	virtual StateMachineNoCrash *transformOneState(StateMachineNoCrash *,
						       bool *)
	{ return NULL; }
	virtual StateMachineStub *transformOneState(StateMachineStub *,
						    bool *)
	{ return NULL; }
	virtual StateMachineSideEffecting *transformOneState(StateMachineSideEffecting *smse,
							     bool *done_something)
	{
		bool b = false;
		StateMachineSideEffect *e =
			smse->sideEffect ? transformSideEffect(smse->sideEffect, &b) : NULL;
		if (b) {
			*done_something = true;
			return new StateMachineSideEffecting(smse->origin,
							     e,
							     smse->target);
		} else {
			return NULL;
		}
	}
	virtual StateMachineBifurcate *transformOneState(StateMachineBifurcate *s,
							 bool *done_something)
	{
		bool b = false;
		IRExpr *c = doit(s->condition, &b);
		if (b) {
			*done_something = true;
			return new StateMachineBifurcate(s->origin,
							 c,
							 s->trueTarget,
							 s->falseTarget);
		} else {
			return NULL;
		}
	}
	virtual StateMachineNdChoice *transformOneState(StateMachineNdChoice *,
							bool *)
	{
		return NULL;
	}

public:
	virtual StateMachineState *transformState(StateMachineState *, bool *);
	virtual StateMachineSideEffect *transformSideEffect(StateMachineSideEffect *,
							    bool *);
	static void rewriteMachine(const StateMachine *sm,
				   std::map<const StateMachineState *, StateMachineState *> &rewriteRules);

	StateMachine *transform(StateMachine *s, bool *done_something = NULL);
};

void findAllLoads(StateMachine *sm, std::set<StateMachineSideEffectLoad *> &out);
void findAllStores(StateMachine *sm, std::set<StateMachineSideEffectStore *> &out);
class MemoryAccessIdentifierAllocator;
StateMachineState *getProximalCause(MachineState *ms, const ThreadRip &rip,
				    MemoryAccessIdentifierAllocator &);
StateMachine *optimiseStateMachine(VexPtr<StateMachine, &ir_heap> &sm,
				   const AllowableOptimisations &opt,
				   VexPtr<Oracle> &oracle,
				   bool is_ssa,
				   GarbageCollectionToken token,
				   bool *progress = NULL);

/* Individual optimisation passes. */
void removeRedundantStores(StateMachine *sm, Oracle *oracle, bool *done_something,
			   const Oracle::RegisterAliasingConfiguration *alias,
			   const AllowableOptimisations &opt);
StateMachine *availExpressionAnalysis(StateMachine *sm,
				      const AllowableOptimisations &opt,
				      const Oracle::RegisterAliasingConfiguration *alias,
				      bool is_ssa,
				      Oracle *oracle,
				      bool *done_something);
StateMachine *deadCodeElimination(StateMachine *sm, bool *done_something, const AllowableOptimisations &opt);
StateMachine *bisimilarityReduction(StateMachine *sm, const AllowableOptimisations &opt);
StateMachine *useInitialMemoryLoads(StateMachine *sm, const AllowableOptimisations &opt,
				    Oracle *oracle, bool *done_something);

void findAllStates(StateMachine *sm, std::set<StateMachineState *> &out);

class FixConsumer;
void checkWhetherInstructionCanCrash(const DynAnalysisRip &rip,
				     unsigned tid,
				     VexPtr<Oracle> &oracle,
				     FixConsumer &df,
				     GarbageCollectionToken token);

#endif /* !OFFLINE_ANALYSIS_HPP__ */
