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
	virtual IRExpr *transformIex(IRExprGet *e) { return NULL; }
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
	virtual IRExpr *transformIex(IRExprConst *e)
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
	virtual IRExpr *transformIex(IRExprFreeVariable *e)
	{
		return NULL;
	}
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
	virtual IRExpr *transformIex(IRExprHappensBefore *e) { return NULL; }
public:
	virtual IRExpr *transformIRExpr(IRExpr *e, bool *done_something);
	IRExpr *transformIRExpr(IRExpr *e) { bool t; return transformIRExpr(e, &t); }
};

class StateMachineTransformer : public IRExprTransformer {
protected:
	std::vector<std::pair<FreeVariableKey, IRExpr *> > fvDelta;
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
		StateMachineSideEffectPhi *, bool *) {
		return NULL;
	}
	virtual StateMachineUnreached *transformOneState(StateMachineUnreached *,
							 bool *)
	{ return NULL; }
	virtual StateMachineCrash *transformOneState(StateMachineCrash *,
						     bool *)
	{ return NULL; }
	virtual StateMachineNoCrash *transformOneState(StateMachineNoCrash *,
						       bool *)
	{ return NULL; }
	virtual StateMachineStub *transformOneState(StateMachineStub *s,
						    bool *done_something)
	{
		bool b = false;
		IRExpr *d = transformIRExpr(s->target, &b);
		if (!b)
			return NULL;
		return new StateMachineStub(s->origin, d);
	}
	virtual StateMachineProxy *transformOneState(StateMachineProxy *p,
						     bool *done_something)
	{
		return NULL;
	}
	virtual StateMachineBifurcate *transformOneState(StateMachineBifurcate *s,
							 bool *done_something)
	{
		bool b = false;
		IRExpr *c = transformIRExpr(s->condition, &b);
		if (b)
			return new StateMachineBifurcate(s->origin,
							 c,
							 (StateMachineEdge *)NULL,
							 (StateMachineEdge *)NULL);
		else
			return NULL;
	}
	virtual StateMachineEdge *transformOneEdge(StateMachineEdge *, bool *);
	virtual StateMachineState *transformState(StateMachineState *, bool *);
public:
	virtual StateMachineSideEffect *transformSideEffect(StateMachineSideEffect *,
							    bool *);
	virtual void transformFreeVariables(FreeVariableMap *fvm, bool *done_something = NULL)
	{
		bool b;
		if (!done_something) done_something = &b;
		fvm->applyTransformation(*this, done_something);
	}
	StateMachine *transform(StateMachine *s, bool *done_something = NULL);
};

void findAllLoads(StateMachine *sm, std::set<StateMachineSideEffectLoad *> &out);
void findAllStores(StateMachine *sm, std::set<StateMachineSideEffectStore *> &out);
StateMachineEdge *getProximalCause(MachineState *ms, unsigned long rip, Thread *thr);
StateMachine *optimiseStateMachine(VexPtr<StateMachine, &ir_heap> &sm,
				   const AllowableOptimisations &opt,
				   VexPtr<Oracle> &oracle,
				   bool noExtendContext,
				   GarbageCollectionToken token);

/* Individual optimisation passes. */
void removeRedundantStores(StateMachine *sm, OracleInterface *oracle, bool *done_something,
			   const AllowableOptimisations &opt);
StateMachine *availExpressionAnalysis(StateMachine *sm, const AllowableOptimisations &opt,
				      const Oracle::RegisterAliasingConfiguration &alias, OracleInterface *oracle,
				      bool *done_something);
StateMachine *deadCodeElimination(StateMachine *sm, bool *done_something);
StateMachine *bisimilarityReduction(StateMachine *sm, const AllowableOptimisations &opt);

StateMachine *introduceFreeVariablesForRegisters(StateMachine *sm, bool *done_something);
StateMachine *optimiseFreeVariables(StateMachine *sm, bool *done_something);

void breakCycles(StateMachine *);

void findAllEdges(StateMachine *sm, std::set<StateMachineEdge *> &out);
void findAllStates(StateMachine *sm, std::set<StateMachineState *> &out);

#endif /* !OFFLINE_ANALYSIS_HPP__ */
