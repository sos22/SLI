#include "sli.h"
#include "state_machine.hpp"
#include "eval_state_machine.hpp"
#include "offline_analysis.hpp"
#include "simplify_irexpr.hpp"

namespace _writeMachineCrashConstraint {

static IRExpr *stateCrashConstraint(StateMachineState *s,
				    std::map<StateMachineState *, IRExpr *> &stateValues,
				    const AllowableOptimisations &opt);

static IRExpr *
resolvePhis(const threadAndRegister &reg, IRExpr *e)
{
	struct _ : public IRExprTransformer {
		const threadAndRegister &reg;
		IRExpr *transformIex(IRExprPhi *iep) {
			if (threadAndRegister::partialEq(reg, iep->reg)) {
				for (auto it = iep->generations.begin();
				     it != iep->generations.end();
				     it++)
					if (*it == reg.gen())
						return IRExpr_Get(reg, iep->ty);
			}
			return NULL;
		}
		_(const threadAndRegister &_reg)
			: reg(_reg)
		{}
	} doit(reg);
	return doit.doit(e);
}

static void
removeDupes(std::vector<unsigned> &a)
{
	for (unsigned x = 0; x + 1 < a.size(); ) {
		if (a[x] == a[x+1]) {
			a.erase(a.begin() + x + 1);
		} else {
			x++;
		}
	}
}

static IRExpr *
insertPhi(StateMachineSideEffectPhi *phi, IRExpr *e)
{
	struct _ : public IRExprTransformer {
		StateMachineSideEffectPhi *sideEffect;
		IRExprPhi *phi;
		IRExpr *transformIex(IRExprPhi *iep) {
			if (threadAndRegister::partialEq(iep->reg, sideEffect->reg)) {
				std::vector<unsigned> newGenerations(iep->generations);
				newGenerations.insert(newGenerations.end(),
						      sideEffect->generations.begin(),
						      sideEffect->generations.end());
				std::sort(newGenerations.begin(),
					  newGenerations.end());
				removeDupes(newGenerations);
				return IRExpr_Phi(iep->reg,
						  newGenerations,
						  iep->ty);
			}
			return NULL;
		}
		IRExpr *transformIex(IRExprGet *ieg) {
			if (threadAndRegister::fullEq(sideEffect->reg, ieg->reg)) {
				if (!phi)
					phi = new IRExprPhi(sideEffect->reg.setGen(0),
							    sideEffect->generations,
							    ieg->type());
				assert(phi->ty == ieg->type());
				return phi;
			}
		}
		_(StateMachineSideEffectPhi *_phi)
			: sideEffect(_phi), phi(NULL)
		{}
	} doit(phi);
	return doit.doit(e);
}

static IRExpr *
sideEffectCrashConstraint(StateMachineSideEffect *smse, IRExpr *acc)
{
	switch (smse->type) {
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel =
			(StateMachineSideEffectLoad *)smse;
		acc = resolvePhis(smsel->target, acc);
		acc = IRExpr_Binop(
			Iop_And1,
			acc,
			IRExpr_Unop(
				Iop_Not1,
				IRExpr_Unop(
					Iop_BadPtr,
					smsel->addr)));
		break;
	}
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectStore *smsema =
			(StateMachineSideEffectStore *)smse;
		acc = IRExpr_Binop(
			Iop_And1,
			acc,
			IRExpr_Unop(
				Iop_Not1,
				IRExpr_Unop(
					Iop_BadPtr,
					smsema->addr)));
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec = (StateMachineSideEffectCopy *)smse;
		acc = resolvePhis(smsec->target, acc);
		break;
	}
	case StateMachineSideEffect::Unreached:
		acc = IRExpr_Const(IRConst_U1(0));
		break;
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			(StateMachineSideEffectAssertFalse *)smse;
		acc = IRExpr_Binop(
			Iop_And1,
			acc,
			IRExpr_Unop(
				Iop_Not1,
				smseaf->value));
		break;
	}
	case StateMachineSideEffect::Phi:
		acc = insertPhi((StateMachineSideEffectPhi *)smse, acc);
		break;
	}

	return acc;
}

static IRExpr *
edgeCrashConstraint(StateMachineEdge *e,
		    std::map<StateMachineState *, IRExpr *> &stateValues,
		    const AllowableOptimisations &opt)
{
	IRExpr *acc = stateCrashConstraint(e->target,
					   stateValues,
					   opt);

	for (auto it = e->sideEffects.rbegin(); it != e->sideEffects.rend(); it++) {
		StateMachineSideEffect *smse = *it;
		acc = sideEffectCrashConstraint(smse, acc);
		acc = simplifyIRExpr(acc, opt);
	}
	return acc;
}

static IRExpr *
stateCrashConstraint(StateMachineState *s,
		     std::map<StateMachineState *, IRExpr *> &stateValues,
		     const AllowableOptimisations &opt)
{
	auto it = stateValues.find(s);
	if (it != stateValues.end())
		return it->second;

	IRExpr *res;
	if (dynamic_cast<StateMachineTerminal *>(s)) {
		if (dynamic_cast<StateMachineCrash *>(s))
			res = IRExpr_Const(IRConst_U1(1));
		else
			res = IRExpr_Const(IRConst_U1(0));
	} else if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(s)) {
		res = edgeCrashConstraint(smp->target,
					  stateValues,
					  opt);
	} else {
		StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(s);
		assert(smb);
		res = IRExpr_Mux0X(
			smb->condition,
			edgeCrashConstraint(smb->trueTarget,
					    stateValues,
					    opt),
			edgeCrashConstraint(smb->falseTarget,
					    stateValues,
					    opt));
	}

	res = simplifyIRExpr(res, opt);
	stateValues[s] = res;
	return res;
}

#ifndef NDEBUG
static bool
freeFromPhis(IRExpr *e)
{
	struct : public IRExprTransformer {
		bool res;
		IRExpr *transformIex(IRExprPhi *) {
			res = false;
			return NULL;
		}
	} doit;
	doit.res = true;
	doit.doit(e);
	return doit.res;
}
#endif

static IRExpr *
writeMachineCrashConstraint(VexPtr<StateMachine, &ir_heap> &sm,
			    VexPtr<IRExpr, &ir_heap> &assumption,
			    const AllowableOptimisations &opt,
			    GarbageCollectionToken token)
{
	VexPtr<IRExpr, &ir_heap> e;
	{
		std::map<StateMachineState *, IRExpr *> stateConstraints;
		e = stateCrashConstraint(sm->root,
					 stateConstraints,
					 opt);
	}
	LibVEX_maybe_gc(token);

	IRExpr *res = simplifyIRExpr(
		IRExpr_Binop(
			Iop_And1,
			assumption,
			e),
		opt);
	assert(freeFromPhis(res));
	return res;
}

/* End of namespace */
};

IRExpr *
writeMachineCrashConstraint(VexPtr<StateMachine, &ir_heap> &sm,
			    VexPtr<IRExpr, &ir_heap> &assumption,
			    VexPtr<Oracle> &oracle,
			    const AllowableOptimisations &opt,
			    GarbageCollectionToken token)
{
	return _writeMachineCrashConstraint::writeMachineCrashConstraint(sm, assumption, opt, token);
}
