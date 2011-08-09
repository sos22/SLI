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
	virtual IRExpr *transformIex(IRExpr::Binder *e) { return NULL; }
	virtual IRExpr *transformIex(IRExpr::Get *e) { return NULL; }
	virtual IRExpr *transformIex(IRExpr::GetI *e)
	{
		bool t = false;
		IRExpr *e2 = transformIRExpr(e->ix, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_GetI(e->descr, e2, e->bias, e->tid);
	}
	virtual IRExpr *transformIex(IRExpr::RdTmp *e) { return NULL; }
	virtual IRExpr *transformIex(IRExpr::Qop *e)
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
	virtual IRExpr *transformIex(IRExpr::Triop *e)
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
	virtual IRExpr *transformIex(IRExpr::Binop *e)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->arg1, &t);
		IRExpr *a2 = transformIRExpr(e->arg2, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_Binop(e->op, a1, a2);
	}
	virtual IRExpr *transformIex(IRExpr::Unop *e)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->arg, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_Unop(e->op, a1);
	}
	virtual IRExpr *transformIex(IRExpr::Load *e)
	{
		bool t = false;
		IRExpr *addr = transformIRExpr(e->addr, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_Load(e->isLL, e->end, e->ty, addr, e->rip);
	}
	virtual IRExpr *transformIex(IRExpr::Const *e)
	{
		return NULL;
	}
	virtual IRExpr *transformIex(IRExpr::Mux0X *e)
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
	virtual IRExpr *transformIex(IRExpr::CCall *);
	virtual IRExpr *transformIex(IRExpr::Associative *);
	virtual IRExpr *transformIex(IRExpr::FreeVariable *e)
	{
		return NULL;
	}
	virtual IRExpr *transformIex(IRExpr::ClientCall *);
	virtual IRExpr *transformIex(IRExpr::ClientCallFailed *e)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->target, &t);
		
		if (!t)
			return NULL;
		else
			return IRExpr_ClientCallFailed(a1);
	}
	virtual IRExpr *transformIex(IRExpr::HappensBefore *e) { return NULL; }
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
	StateMachine *transform(StateMachine *s, bool *done_something = NULL)
	{
		bool b = false;
		StateMachineState *r = transform(s->root, &b);
		if (b) {
			if (done_something)
				*done_something = true;
			StateMachine *sm = new StateMachine(s, fvDelta);
			sm->root = r;
			return sm;
		}
		return s;
	}
};

void findAllLoads(StateMachine *sm, std::set<StateMachineSideEffectLoad *> &out);
StateMachine *getProximalCause(MachineState *ms, unsigned long rip, Thread *thr);

#endif /* !OFFLINE_ANALYSIS_HPP__ */
