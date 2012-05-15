#include "sli.h"
#include "state_machine.hpp"
#include "eval_state_machine.hpp"
#include "offline_analysis.hpp"
#include "simplify_irexpr.hpp"

namespace _writeMachineCrashConstraint {

#ifdef NDEBUG
#define dump_state_constraints 0
#else
static int dump_state_constraints = 0;
#endif

struct crash_constraint_context {
	IRExpr *surviveExpression;
	IRExpr *crashExpression;
	IRExpr *escapeExpression;
	const AllowableOptimisations &opt;
	std::map<StateMachineState *, IRExpr *> stateValues;

	std::map<const StateMachineState *, int> edgeLabels;

	IRExpr *escapeConstraint(IRExpr *escape_if, IRExpr *non_escape)
	{
		return IRExpr_Mux0X(escape_if, non_escape, escapeExpression);
	}

	crash_constraint_context(const AllowableOptimisations &_opt)
		: opt(_opt)
	{}
};

static IRExpr *stateCrashConstraint(StateMachineState *s, crash_constraint_context &ctxt);

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

static IRExpr *
insertPhi(StateMachineSideEffectPhi *phi, IRExpr *e)
{
	struct _ : public IRExprTransformer {
		StateMachineSideEffectPhi *sideEffect;
		IRExprPhi *phi;
		IRExpr *getPhi(IRType ty) {
			if (!phi) {
				std::vector<unsigned> generations;
				generations.resize(sideEffect->generations.size());
				for (unsigned x = 0; x < sideEffect->generations.size(); x++)
					generations[x] = sideEffect->generations[x].first;
				phi = new IRExprPhi(sideEffect->reg.setGen(0),
						    generations,
						    ty);
			}
			assert(phi->ty == ty);
			return phi;
		}
		IRExpr *transformIex(IRExprPhi *iep) {
			if (threadAndRegister::partialEq(iep->reg, sideEffect->reg)) {
				for (auto it = iep->generations.begin();
				     it != iep->generations.end();
				     it++) {
					if (*it == sideEffect->reg.gen())
						return getPhi(iep->ty);
				}

			}
			return NULL;
		}
		IRExpr *transformIex(IRExprGet *ieg) {
			if (threadAndRegister::fullEq(sideEffect->reg, ieg->reg))
				return getPhi(ieg->ty);
			return NULL;
		}
		_(StateMachineSideEffectPhi *_phi)
			: sideEffect(_phi), phi(NULL)
		{}
	} doit(phi);
	return doit.doit(e);
}

static IRExpr *
setTemporary(const threadAndRegister &reg, IRExpr *value, IRExpr *input)
{
	struct _ : public IRExprTransformer {
		const threadAndRegister &reg;
		IRExpr *value;
		_(const threadAndRegister &_reg, IRExpr *_value)
			: reg(_reg), value(_value)
		{}
		IRExpr *transformIex(IRExprGet *ieg) {
			if (threadAndRegister::fullEq(reg, ieg->reg))
				return coerceTypes(ieg->type(), value);
			else
				return NULL;
		}
	} doit(reg, value);
	return doit.doit(input);
}

static IRExpr *
sideEffectCrashConstraint(StateMachineSideEffect *smse, IRExpr *acc, crash_constraint_context &ctxt)
{
	switch (smse->type) {
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel =
			(StateMachineSideEffectLoad *)smse;
		acc = resolvePhis(smsel->target, acc);
		acc = ctxt.escapeConstraint(IRExpr_Unop(Iop_BadPtr, smsel->addr), acc);
		break;
	}
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectStore *smsema =
			(StateMachineSideEffectStore *)smse;
		acc = ctxt.escapeConstraint(IRExpr_Unop(Iop_BadPtr, smsema->addr), acc);
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec = (StateMachineSideEffectCopy *)smse;
		acc = resolvePhis(smsec->target, acc);
		acc = setTemporary(smsec->target, smsec->value, acc);
		break;
	}
	case StateMachineSideEffect::Unreached:
		acc = ctxt.escapeExpression;
		break;
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			(StateMachineSideEffectAssertFalse *)smse;
		acc = ctxt.escapeConstraint(smseaf->value, acc);
		break;
	}
	case StateMachineSideEffect::Phi:
		acc = insertPhi((StateMachineSideEffectPhi *)smse, acc);
		break;
	}

	return acc;
}

static IRExpr *
stateCrashConstraint(StateMachineState *s, crash_constraint_context &ctxt)
{
	auto it = ctxt.stateValues.find(s);
	if (it != ctxt.stateValues.end())
		return it->second;

	IRExpr *res = NULL;
	switch (s->type) {
	case StateMachineState::Crash:
		res = ctxt.crashExpression;
		break;
	case StateMachineState::NoCrash:
		res = ctxt.surviveExpression;
		break;
	case StateMachineState::Unreached:
	case StateMachineState::Stub:
		res = ctxt.escapeExpression;
		break;
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *smse = (StateMachineSideEffecting *)s;
		res = stateCrashConstraint(smse->target, ctxt);
		if (smse->sideEffect)
			res = sideEffectCrashConstraint(smse->sideEffect, res, ctxt);
		break;
	}
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
		res = IRExpr_Mux0X(
			smb->condition,
			stateCrashConstraint(smb->falseTarget, ctxt),
			stateCrashConstraint(smb->trueTarget, ctxt));
		break;
	}
	case StateMachineState::NdChoice: {
		StateMachineNdChoice *smn = (StateMachineNdChoice *)s;
		IRExprAssociative *iex = IRExpr_Associative(
			smn->successors.size(), Iop_Or1);
		for (unsigned x = 0; x < smn->successors.size(); x++)
			iex->contents[x] =
				stateCrashConstraint(smn->successors[x], ctxt);
		res = iex;
		break;
	}
	}
	assert(res != NULL);
	res = simplifyIRExpr(res, ctxt.opt);
	ctxt.stateValues[s] = res;
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

/* We've reached the start of the machine.  Any remaining Phis must be
   due to use of the initial value of the register. */
static IRExpr *
resolveOpenPhis(IRExpr *what)
{
	struct : public IRExprTransformer {
		IRExpr *transformIex(IRExprPhi *phi) {
#ifndef NDEBUG
			{
				bool found_it = false;
				for (auto it = phi->generations.begin();
				     !found_it && it != phi->generations.end();
				     it++)
					if (*it == (unsigned)-1)
						found_it = true;
				assert(found_it);
			}
#endif
			return IRExpr_Get(phi->reg.setGen(-1), phi->ty);
		}
	} doit;
	return doit.doit(what);
}

static IRExpr *
writeMachineCrashConstraint(StateMachine *sm,
			    IRExpr *surviveExpression,
			    IRExpr *crashExpression,
			    IRExpr *escapeExpression,
			    const AllowableOptimisations &opt)
{
	struct crash_constraint_context ctxt(opt);
	
	ctxt.surviveExpression = surviveExpression;
	ctxt.crashExpression = crashExpression;
	ctxt.escapeExpression = escapeExpression;

	if (dump_state_constraints) {
		printf("writeMachineCrashConstraint(survive = ");
		ppIRExpr(surviveExpression, stdout);
		printf(", crash = ");
		ppIRExpr(crashExpression, stdout);
		printf(", escape = ");
		ppIRExpr(escapeExpression, stdout);
		printf(") on machine\n");
		printStateMachine(sm, stdout, ctxt.edgeLabels);
	}
	IRExpr *res = stateCrashConstraint(sm->root, ctxt);

	res = resolveOpenPhis(res);

	assert(freeFromPhis(res));

	if (dump_state_constraints) {
		printf("\n\n State labels -> \n\n");
		for (auto it = ctxt.stateValues.begin(); it != ctxt.stateValues.end(); it++) {
			it->first->prettyPrint(stdout, ctxt.edgeLabels);
			printf(" -> ");
			ppIRExpr(it->second, stdout);
			printf("\n\n");
		}
	}

	return res;
}

/* End of namespace */
};

IRExpr *
writeMachineCrashConstraint(StateMachine *sm,
			    IRExpr *surviveExpression,
			    IRExpr *crashExpression,
			    IRExpr *escapeExpression,
			    const AllowableOptimisations &opt)
{
	return _writeMachineCrashConstraint::writeMachineCrashConstraint(sm,
									 surviveExpression,
									 crashExpression,
									 escapeExpression,
									 opt);
}
