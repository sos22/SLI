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
	std::map<StateMachineEdge *, IRExpr *> edgeValues;

	std::map<const StateMachineEdge *, int> edgeLabels;

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
				newGenerations.reserve(newGenerations.size() + sideEffect->generations.size());
				for (auto it = sideEffect->generations.begin();
				     it != sideEffect->generations.end();
				     it++)
					newGenerations.push_back(it->first);
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
				if (!phi) {
					std::vector<unsigned> generations;
					generations.resize(sideEffect->generations.size());
					for (unsigned x = 0; x < sideEffect->generations.size(); x++)
						generations[x] = sideEffect->generations[x].first;
					phi = new IRExprPhi(sideEffect->reg.setGen(0),
							    generations,
							    ieg->type());
				}
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
				return value;
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
edgeCrashConstraint(StateMachineEdge *e, crash_constraint_context &ctxt)
{
	auto it = ctxt.edgeValues.find(e);
	if (it != ctxt.edgeValues.end())
		return it->second;

	IRExpr *acc = stateCrashConstraint(e->target, ctxt);

	for (auto it = e->sideEffects.rbegin(); it != e->sideEffects.rend(); it++) {
		StateMachineSideEffect *smse = *it;
		acc = sideEffectCrashConstraint(smse, acc, ctxt);
		acc = simplifyIRExpr(acc, ctxt.opt);
	}

	ctxt.edgeValues[e] = acc;

	if (dump_state_constraints) {
		printf("Computed constraint at top of edge l%d:\n", ctxt.edgeLabels[e]);
		e->prettyPrint(stdout, ctxt.edgeLabels);
		printf("Result ");
		ppIRExpr(acc, stdout);
		printf("\n");
	}
	return acc;
}

static IRExpr *
stateCrashConstraint(StateMachineState *s, crash_constraint_context &ctxt)
{
	auto it = ctxt.stateValues.find(s);
	if (it != ctxt.stateValues.end())
		return it->second;

	IRExpr *res;
	if (dynamic_cast<StateMachineTerminal *>(s)) {
		if (dynamic_cast<StateMachineCrash *>(s))
			res = ctxt.crashExpression;
		else if (dynamic_cast<StateMachineNoCrash *>(s))
			res = ctxt.surviveExpression;
		else if (dynamic_cast<StateMachineUnreached *>(s) ||
			 dynamic_cast<StateMachineStub *>(s))
			res = ctxt.escapeExpression;
		else
			abort();
	} else if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(s)) {
		res = edgeCrashConstraint(smp->target, ctxt);
	} else {
		StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(s);
		assert(smb);
		res = IRExpr_Mux0X(
			smb->condition,
			edgeCrashConstraint(smb->falseTarget, ctxt),
			edgeCrashConstraint(smb->trueTarget, ctxt));
	}

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

static IRExpr *
writeMachineCrashConstraint(StateMachine *sm,
			    IRExpr *assumption,
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

	res = simplifyIRExpr(
		IRExpr_Binop(
			Iop_And1,
			assumption,
			res),
		opt);
	return res;
}

/* End of namespace */
};

IRExpr *
writeMachineCrashConstraint(StateMachine *sm,
			    IRExpr *assumption,
			    IRExpr *surviveExpression,
			    IRExpr *crashExpression,
			    IRExpr *escapeExpression,
			    const AllowableOptimisations &opt)
{
	return _writeMachineCrashConstraint::writeMachineCrashConstraint(sm,
									 assumption,
									 surviveExpression,
									 crashExpression,
									 escapeExpression,
									 opt);
}
