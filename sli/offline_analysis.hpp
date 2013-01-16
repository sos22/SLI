#ifndef OFFLINE_ANALYSIS_HPP__
#define OFFLINE_ANALYSIS_HPP__

#include <map>

#include "state_machine.hpp"
#include "oracle.hpp"

#include "libvex_ir.h"
#include "bdd.hpp"

#define STORING_THREAD 97

class IRExprTransformer {
	exprbdd *transform_exprbdd(bbdd::scope *, exprbdd::scope *, exprbdd *what, std::map<exprbdd *, exprbdd *> &);
	smrbdd *transform_smrbdd(bbdd::scope *, smrbdd::scope *, smrbdd *what, std::map<smrbdd *, smrbdd *> &);
	bbdd *transform_bbdd(bbdd::scope *, bbdd *what, std::map<bbdd *, bbdd *> &);
	IRExpr *_currentIRExpr;
protected:
	bool aborted;
	void abortTransform() { aborted = true; }
	IRExpr *currentIRExpr() { return _currentIRExpr; }
	virtual IRExpr *transformIex(IRExprGet *g) { return g; }
	virtual IRExpr *transformIex(IRExprGetI *e)
	{
		IRExpr *ix = transformIRExpr(e->ix);
		if (ix == e->ix)
			return e;
		else
			return IRExpr_GetI(e->descr, ix, e->bias, e->tid);
	}
	virtual IRExpr *transformIex(IRExprQop *e)
	{
		IRExpr *a1 = transformIRExpr(e->arg1);
		IRExpr *a2 = transformIRExpr(e->arg2);
		IRExpr *a3 = transformIRExpr(e->arg3);
		IRExpr *a4 = transformIRExpr(e->arg4);
		if (a1 == e->arg1 && a2 == e->arg2 && a3 == e->arg3 &&
		    a4 == e->arg4)
			return e;
		else
			return IRExpr_Qop(e->op, a1, a2, a3, a4);

	}
	virtual IRExpr *transformIex(IRExprTriop *e)
	{
		IRExpr *a1 = transformIRExpr(e->arg1);
		IRExpr *a2 = transformIRExpr(e->arg2);
		IRExpr *a3 = transformIRExpr(e->arg3);
		if (a1 == e->arg1 && a2 == e->arg2 && a3 == e->arg3)
			return e;
		else
			return IRExpr_Triop(e->op, a1, a2, a3);
	}
	virtual IRExpr *transformIex(IRExprBinop *e)
	{
		IRExpr *a1 = transformIRExpr(e->arg1);
		IRExpr *a2 = transformIRExpr(e->arg2);
		if (a1 == e->arg1 && a2 == e->arg2)
			return e;
		else
			return IRExpr_Binop(e->op, a1, a2);
	}
	virtual IRExpr *transformIex(IRExprUnop *e)
	{
		IRExpr *a1 = transformIRExpr(e->arg);
		if (a1 == e->arg)
			return e;
		else
			return IRExpr_Unop(e->op, a1);
	}
	virtual IRExpr *transformIex(IRExprLoad *e)
	{
		IRExpr *addr = transformIRExpr(e->addr);
		if (addr == e->addr)
			return e;
		else
			return IRExpr_Load(e->ty, addr);
	}
	virtual IRExpr *transformIex(IRExprConst *c)
	{
		return c;
	}
	virtual IRExpr *transformIex(IRExprMux0X *e)
	{
		IRExpr *c = transformIRExpr(e->cond);
		IRExpr *z = transformIRExpr(e->expr0);
		IRExpr *x = transformIRExpr(e->exprX);

		if (c == e->cond && z == e->expr0 && x == e->exprX)
			return e;
		else
			return IRExpr_Mux0X(c, z, x);
	}
	virtual IRExpr *transformIex(IRExprCCall *);
	virtual IRExpr *transformIex(IRExprAssociative *);
	virtual IRExpr *transformIex(IRExprHappensBefore *e) { return e; }
	virtual IRExpr *transformIex(IRExprFreeVariable *e) { return e; }
	virtual IRExpr *transformIex(IRExprEntryPoint *e) { return e; }
	virtual IRExpr *transformIex(IRExprControlFlow *e) { return e; }
	virtual int transformIRExpr(IRExpr *, bool *) { return 0; }
	virtual IRExpr *transformIRExpr(IRExpr *e);
public:
	IRExpr *doit(IRExpr *e) { aborted = false; return transformIRExpr(e); }
	smrbdd *transform_smrbdd(bbdd::scope *s, smrbdd::scope *s2, smrbdd *what) {
		std::map<smrbdd *, smrbdd *> memo;
		return transform_smrbdd(s, s2, what, memo);
	}
	exprbdd *transform_exprbdd(bbdd::scope *bscope, exprbdd::scope *scope, exprbdd *what) {
		std::map<exprbdd *, exprbdd *> memo;
		return transform_exprbdd(bscope, scope, what, memo);
	}
	bbdd *transform_bbdd(bbdd::scope *scope, bbdd *what) {
		std::map<bbdd *, bbdd *> memo;
		return transform_bbdd(scope, what, memo);
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
	virtual StateMachineSideEffectImportRegister *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectImportRegister *, bool *)
	{ return NULL; }
	virtual StateMachineSideEffectStackLayout *transformOneSideEffect(
		SMScopes *, StateMachineSideEffectStackLayout *, bool *)
	{ return NULL; }
	virtual StateMachineTerminal *transformOneState(SMScopes *scopes,
							StateMachineTerminal *smt,
							bool *done_something)
	{
		smrbdd *smr = transform_smrbdd(&scopes->bools, &scopes->smrs, smt->res);
		if (smr != smt->res) {
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
		bbdd *c = transform_bbdd(&scopes->bools, s->condition);
		if (c != s->condition) {
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
StateMachine *deadCodeElimination(SMScopes *, StateMachine *sm, bool *done_something, bool is_ssa);
StateMachine *bisimilarityReduction(SMScopes *, StateMachine *sm, bool is_ssa, MaiMap &mai, bool *done_something);
StateMachine *useInitialMemoryLoads(SMScopes *, const MaiMap &mai, StateMachine *sm, const AllowableOptimisations &opt,
				    OracleInterface *oracle, bool *done_something);
class ControlDominationMap;
StateMachine *functionAliasAnalysis(SMScopes *scopes,
				    const MaiMap &mai,
				    StateMachine *machine,
				    const AllowableOptimisations &opt,
				    OracleInterface *oracle,
				    const ControlDominationMap &cdm,
				    bool *done_something);
class predecessor_map;
class control_dependence_graph;
StateMachine *phiElimination(SMScopes *scopes, StateMachine *sm,
			     predecessor_map &pred,
			     control_dependence_graph &cdg,
			     bool *done_something);

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

MemoryAccessIdentifier mkPendingMai(const CFGNode *node);
StateMachineState *getProximalCause(SMScopes *scopes, MachineState *ms, Oracle *oracle, const CFGNode *where, const VexRip &rip, int tid);

#endif /* !OFFLINE_ANALYSIS_HPP__ */
