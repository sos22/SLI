#ifndef OFFLINE_ANALYSIS_HPP__
#define OFFLINE_ANALYSIS_HPP__

#include <map>

#include "state_machine.hpp"

#define CRASHING_THREAD 73
#define STORING_THREAD 97

class IRExprTransformer {
protected:
	virtual StateMachineSideEffectMemoryAccess *transformStateMachineSideEffectMemoryAccess(StateMachineSideEffectMemoryAccess *,
												bool *);
	std::vector<std::pair<FreeVariableKey, IRExpr *> > fvDelta;
	virtual IRExpr *transformIexBinder(IRExpr *e, bool *done_something) { return e; }
	virtual IRExpr *transformIexGet(IRExpr *e, bool *done_something) { return e; }
	virtual IRExpr *transformIexGetI(IRExpr *e, bool *done_something)
	{
		bool t = false;
		IRExpr *e2 = transformIRExpr(e->Iex.GetI.ix, &t);
		*done_something |= t;
		if (!t)
			return e;
		else
			return IRExpr_GetI(e->Iex.GetI.descr,
					   e2,
					   e->Iex.GetI.bias,
					   e->Iex.GetI.tid);
	}
	virtual IRExpr *transformIexRdTmp(IRExpr *e, bool *done_something) { return e; }
	virtual IRExpr *transformIexQop(IRExpr *e, bool *done_something)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->Iex.Qop.arg1, &t);
		IRExpr *a2 = transformIRExpr(e->Iex.Qop.arg2, &t);
		IRExpr *a3 = transformIRExpr(e->Iex.Qop.arg3, &t);
		IRExpr *a4 = transformIRExpr(e->Iex.Qop.arg4, &t);
		*done_something |= t;
		if (!t)
			return e;
		else
			return IRExpr_Qop(e->Iex.Qop.op,
					  a1,
					  a2,
					  a3,
					  a4);
	}
	virtual IRExpr *transformIexTriop(IRExpr *e, bool *done_something)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->Iex.Qop.arg1, &t);
		IRExpr *a2 = transformIRExpr(e->Iex.Qop.arg2, &t);
		IRExpr *a3 = transformIRExpr(e->Iex.Qop.arg3, &t);
		*done_something |= t;
		if (!t)
			return e;
		else
			return IRExpr_Triop(e->Iex.Qop.op,
					    a1,
					    a2,
					    a3);
	}
	virtual IRExpr *transformIexBinop(IRExpr *e, bool *done_something)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->Iex.Qop.arg1, &t);
		IRExpr *a2 = transformIRExpr(e->Iex.Qop.arg2, &t);
		*done_something |= t;
		if (!t)
			return e;
		else
			return IRExpr_Binop(e->Iex.Qop.op,
					    a1,
					    a2);
	}
	virtual IRExpr *transformIexUnop(IRExpr *e, bool *done_something)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->Iex.Qop.arg1, &t);
		*done_something |= t;
		if (!t)
			return e;
		else
			return IRExpr_Unop(e->Iex.Qop.op,
					    a1);
	}
	virtual IRExpr *transformIexLoad(IRExpr *e, bool *done_something)
	{
		bool t = false;
		IRExpr *addr = transformIRExpr(e->Iex.Load.addr, &t);
		*done_something |= t;
		if (!t)
			return e;
		else
			return IRExpr_Load(e->Iex.Load.isLL,
					   e->Iex.Load.end,
					   e->Iex.Load.ty,
					   addr);
	}
	virtual IRExpr *transformIexConst(IRExpr *e, bool *done_something)
	{
		return e;
	}
	virtual IRExpr *transformIexMux0X(IRExpr *e, bool *done_something)
	{
		bool t = false;
		IRExpr *c = transformIRExpr(e->Iex.Mux0X.cond, &t);
		IRExpr *z = transformIRExpr(e->Iex.Mux0X.expr0, &t);
		IRExpr *x = transformIRExpr(e->Iex.Mux0X.exprX, &t);
		*done_something |= t;
		if (!t)
			return e;
		else
			return IRExpr_Mux0X(c, z, x);
	}
	virtual IRExpr *transformIexCCall(IRExpr *, bool *done_something);
	virtual IRExpr *transformIexAssociative(IRExpr *, bool *done_something);
	virtual IRExpr *transformIexFreeVariable(IRExpr *e, bool *done_something)
	{
		return e;
	}
	virtual IRExpr *transformIexClientCall(IRExpr *, bool *done_something);
	virtual IRExpr *transformIexClientCallFailed(IRExpr *e, bool *done_something)
	{
		bool t = false;
		IRExpr *a1 = transformIRExpr(e->Iex.ClientCallFailed.target, &t);
		*done_something |= t;
		if (!t)
			return e;
		else
			return IRExpr_ClientCallFailed(a1);
	}
	virtual IRExpr *transformIexHappensBefore(IRExpr *e, bool *done_something);
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

#endif /* !OFFLINE_ANALYSIS_HPP__ */
