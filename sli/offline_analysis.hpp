#ifndef OFFLINE_ANALYSIS_HPP__
#define OFFLINE_ANALYSIS_HPP__

#include <map>

#include "state_machine.hpp"

#include "libvex_ir.h"

#define STORING_THREAD 97

class IRExprTransformer {
	IRExpr *_currentIRExpr;
protected:
	IRExpr *currentIRExpr() { return _currentIRExpr; }
	std::vector<std::pair<FreeVariableKey, IRExpr *> > fvDelta;
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
			return IRExpr_Load(e->isLL, e->end, e->ty, addr, e->rip);
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
private:
	/* Transformations are memoised.  This is important, because
	   it means that we preserve the state machine structure
	   rather than unrolling it. */
	std::map<const StateMachineState *, StateMachineState *> memoTable;
	StateMachineState *doit(StateMachineState *inp, bool *);
	StateMachineEdge *doit(StateMachineEdge *inp, bool *);

	StateMachineState *transform(StateMachineState *start, bool *done_something);
	StateMachineState *transform(StateMachineState *start)
	{
		bool b;
		return transform(start, &b);
	}
protected:
	virtual StateMachineState *transformedCrash(bool *done_something)
	{
		return StateMachineCrash::get();
	}
	virtual StateMachineState *transformedNoCrash(bool *done_something)
	{
		return StateMachineNoCrash::get();
	}
	virtual StateMachineState *transformedUnreached(bool *done_something)
	{
		return StateMachineUnreached::get();
	}
public:
	virtual void transform(FreeVariableMap *fvm, bool *done_something)
	{
		fvm->applyTransformation(*this, done_something);
	}
	void transform(FreeVariableMap *fvm)
	{
		bool b;
		transform(fvm, &b);
	}
	virtual StateMachineSideEffect *transform(StateMachineSideEffect *, bool *done_something);
	StateMachineSideEffect *transform(StateMachineSideEffect *se)
	{
		bool b;
		return transform(se, &b);
	}
	StateMachine *transform(StateMachine *s, bool *done_something = NULL)
	{
		bool b = false;
		FreeVariableMap fvm = s->freeVariables;
		transform(&fvm, &b);
		StateMachineState *r = transform(s->root, &b);
		if (b) {
			if (done_something)
				*done_something = true;
			StateMachine *sm = new StateMachine(s);
			sm->root = r;
			sm->freeVariables = fvm;
			for (auto it = fvDelta.begin(); it != fvDelta.end(); it++)
				sm->freeVariables.content->set(it->first, it->second);
			return sm;
		}
		return s;
	}
};

void findAllLoads(StateMachine *sm, std::set<StateMachineSideEffectLoad *> &out);
StateMachineEdge *getProximalCause(MachineState *ms, unsigned long rip, Thread *thr);
StateMachine *optimiseStateMachine(StateMachine *sm,
				   const AllowableOptimisations &opt,
				   Oracle *oracle,
				   bool noExtendContext);

#endif /* !OFFLINE_ANALYSIS_HPP__ */
