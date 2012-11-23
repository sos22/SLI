#ifndef OFFLINE_ANALYSIS_HPP__
#define OFFLINE_ANALYSIS_HPP__

#include <map>

#include "state_machine.hpp"
#include "oracle.hpp"

#include "libvex_ir.h"
#include "bdd.hpp"

#define STORING_THREAD 97

class IRExprTransformer {
	IRExpr *_currentIRExpr;
protected:
	bool aborted;
	void abortTransform() { aborted = true; }
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
			return IRExpr_Load(e->ty, addr);
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
	virtual IRExpr *transformIex(IRExprHappensBefore *) { return NULL; }
	virtual IRExpr *transformIex(IRExprFreeVariable *) { return NULL; }
	virtual IRExpr *transformIex(IRExprEntryPoint *) { return NULL; }
	virtual IRExpr *transformIex(IRExprControlFlow *) { return NULL; }
	virtual IRExpr *transformIRExpr(IRExpr *e, bool *done_something);
public:
	IRExpr *doit(IRExpr *e, bool *done_something) { aborted = false; return transformIRExpr(e, done_something); }
	IRExpr *doit(IRExpr *e) { bool t; return doit(e, &t); }
	smrbdd *transform_smrbdd(bbdd::scope *, smrbdd::scope *, smrbdd *what, bool *done_something);
	smrbdd *transform_smrbdd(bbdd::scope *scope, smrbdd::scope *scope2, smrbdd *what) {
		bool b;
		return transform_smrbdd(scope, scope2, what, &b);
	}
	exprbdd *transform_exprbdd(bbdd::scope *, exprbdd::scope *, exprbdd *what, bool *done_something);
	exprbdd *transform_exprbdd(bbdd::scope *scope, exprbdd::scope *scope2, exprbdd *what) {
		bool b;
		return transform_exprbdd(scope, scope2, what, &b);
	}
	bbdd *transform_bbdd(bbdd::scope *scope, bbdd *what, bool *done_something);
	bbdd *transform_bbdd(bbdd::scope *scope, bbdd *what) {
		bool b;
		return transform_bbdd(scope, what, &b);
	}
};

class StateMachineTransformer : public IRExprTransformer {
protected:
	StateMachineState *currentState;

	virtual StateMachineSideEffectLoad *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectLoad *, bool *);
	virtual StateMachineSideEffectStore *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectStore *, bool *);
	virtual StateMachineSideEffectAssertFalse *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectAssertFalse *, bool *);
	virtual StateMachineSideEffectCopy *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectCopy *, bool *);
	virtual StateMachineSideEffectUnreached *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectUnreached *, bool *) {
		return NULL;
	}
	virtual StateMachineSideEffectStartAtomic *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectStartAtomic *, bool *) {
		return NULL;
	}
	virtual StateMachineSideEffectEndAtomic *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectEndAtomic *, bool *) {
		return NULL;
	}
	virtual StateMachineSideEffectPhi *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectPhi *, bool *);
	virtual StateMachineSideEffectStartFunction *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectStartFunction *, bool *);
	virtual StateMachineSideEffectEndFunction *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectEndFunction *, bool *);
	virtual StateMachineSideEffectPointerAliasing *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectPointerAliasing *, bool *)
	{ return NULL; }
	virtual StateMachineSideEffectStackLayout *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectStackLayout *, bool *)
	{ return NULL; }
	virtual StateMachineTerminal *transformOneState(SMScopes *scopes,
							StateMachineTerminal *smt,
							bool *done_something)
	{
		bool b = false;
		smrbdd *smr = transform_smrbdd(&scopes->bools, &scopes->smrs, smt->res, &b);
		if (b) {
			*done_something = true;
			return new StateMachineTerminal(smt, smr);
		} else {
			return NULL;
		}
	}
	virtual StateMachineSideEffecting *transformOneState(SMScopes *scopes,
							     StateMachineSideEffecting *smse,
							     bool *done_something)
	{
		bool b = false;
		StateMachineSideEffect *e =
			smse->sideEffect ? transformSideEffect(scopes, smse->sideEffect, &b) : NULL;
		if (b) {
			*done_something = true;
			return new StateMachineSideEffecting(smse, e);
		} else {
			return NULL;
		}
	}
	virtual StateMachineBifurcate *transformOneState(SMScopes *scopes,
							 StateMachineBifurcate *s,
							 bool *done_something)
	{
		bool b = false;
		bbdd *c = transform_bbdd(&scopes->bools, s->condition, &b);
		if (b) {
			*done_something = true;
			return new StateMachineBifurcate(s, c);
		} else {
			return NULL;
		}
	}

	virtual bool rewriteNewStates() const = 0;
public:
	virtual StateMachineState *transformState(SMScopes *, StateMachineState *, bool *);
	virtual StateMachineSideEffect *transformSideEffect(SMScopes *,
							    StateMachineSideEffect *,
							    bool *);
	static void rewriteMachine(const StateMachine *sm,
				   std::map<const StateMachineState *, StateMachineState *> &rewriteRules,
				   bool rewriteNewStates);

	StateMachine *transform(SMScopes *scopes, StateMachine *s, bool *done_something = NULL);
};

StateMachine *optimiseStateMachine(SMScopes *scopes,
				   VexPtr<MaiMap, &ir_heap> &mai,
				   VexPtr<StateMachine, &ir_heap> sm,
				   const AllowableOptimisations &opt,
				   const VexPtr<OracleInterface> &oracle,
				   bool is_ssa,
				   GarbageCollectionToken token,
				   bool *progress = NULL);
StateMachine *optimiseStateMachine(SMScopes *scopes,
				   VexPtr<MaiMap, &ir_heap> &mai,
				   VexPtr<StateMachine, &ir_heap> sm,
				   const AllowableOptimisations &opt,
				   const VexPtr<Oracle> &oracle,
				   bool is_ssa,
				   GarbageCollectionToken token,
				   bool *progress = NULL);

/* Individual optimisation passes. */
StateMachine *availExpressionAnalysis(SMScopes *,
				      const MaiMap &mai,
				      StateMachine *sm,
				      const AllowableOptimisations &opt,
				      bool is_ssa,
				      OracleInterface *oracle,
				      bool *done_something);
StateMachine *deadCodeElimination(bbdd::scope *, StateMachine *sm, bool *done_something, bool is_ssa);
StateMachine *bisimilarityReduction(SMScopes *, StateMachine *sm, bool is_ssa, MaiMap &mai, bool *done_something);
StateMachine *useInitialMemoryLoads(SMScopes *, const MaiMap &mai, StateMachine *sm, const AllowableOptimisations &opt,
				    OracleInterface *oracle, bool *done_something);
StateMachine *removeLocalSurvival(StateMachine *sm,
				  const AllowableOptimisations &opt,
				  bool *done_something);
class ControlDominationMap;
StateMachine *functionAliasAnalysis(SMScopes *scopes,
				    const MaiMap &mai,
				    StateMachine *machine,
				    const AllowableOptimisations &opt,
				    OracleInterface *oracle,
				    const ControlDominationMap &cdm,
				    bool *done_something);
StateMachine *phiElimination(SMScopes *scopes, StateMachine *sm, bool *done_something);
StateMachine *undefinednessSimplification(SMScopes *scopes, StateMachine *sm, const IRExprOptimisations &opt, bool *done_something);

StateMachine *removeAnnotations(SMScopes *scopes,
				VexPtr<MaiMap, &ir_heap> &mai,
				VexPtr<StateMachine, &ir_heap> sm,
				const AllowableOptimisations &opt,
				const VexPtr<OracleInterface> &oracle,
				bool is_ssa,
				GarbageCollectionToken token);

class FixConsumer;
void checkWhetherInstructionCanCrash(const DynAnalysisRip &rip,
				     unsigned tid,
				     const VexPtr<Oracle> &oracle,
				     FixConsumer &df,
				     const AllowableOptimisations &opt,
				     GarbageCollectionToken token);

StateMachineState *getProximalCause(SMScopes *scopes, MachineState *ms, Oracle *oracle, MaiMap &mai, const CFGNode *where, const VexRip &rip, int tid);

#endif /* !OFFLINE_ANALYSIS_HPP__ */
