#include "sli.h"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"
#include "visitor.hpp"

namespace _remove_local_survival {

static bool
exprIsLocal(const IRExpr *input)
{
	struct {
		static visit_result Get(void *, const IRExprGet *ieg) {
			if (ieg->reg.gen() != (unsigned)-1)
				return visit_abort;
			else
				return visit_continue;
		}
		static visit_result GetI(void *, const IRExprGetI *) {
			return visit_abort;
		}
		static visit_result HappensBefore(void *, const IRExprHappensBefore *) {
			return visit_abort;
		}
		static visit_result FreeVariable(void *, const IRExprFreeVariable *) {
			return visit_abort;
		}
	} foo;
	static irexpr_visitor<void> visitor;
	visitor.Get = foo.Get;
	visitor.GetI = foo.GetI;
	visitor.HappensBefore = foo.HappensBefore;
	visitor.FreeVariable = foo.FreeVariable;
	return visit_irexpr((void *)NULL, &visitor, input) == visit_continue;
}

static void
getExprLocalPart(IRExpr *input, IRExpr **localPart, IRExpr **remotePart, IROp splitop)
{
	*remotePart = input;
	*localPart = NULL;
	if (exprIsLocal(input)) {
		*localPart = input;
		*remotePart = NULL;
		return;
	}

	if (input->tag != Iex_Associative)
		return;
	IRExprAssociative *inp = (IRExprAssociative *)input;
	if (inp->op != splitop)
		return;

	IRExpr *localArgs[inp->nr_arguments];
	IRExpr *remoteArgs[inp->nr_arguments];
	int nrLocalArgs = 0;
	int nrRemoteArgs = 0;
	for (int i = 0; i < inp->nr_arguments; i++) {
		if (exprIsLocal(inp->contents[i])) {
			localArgs[nrLocalArgs] = inp->contents[i];
			nrLocalArgs++;
		} else {
			remoteArgs[nrRemoteArgs] = inp->contents[i];
			nrRemoteArgs++;
		}
	}

	/* Because otherwise the call to exprIsLocal() at the top
	   should have caught us. */
	assert(nrLocalArgs != inp->nr_arguments);
	if (nrLocalArgs == 0)
		return;

	IRExprAssociative *localAssoc, *remoteAssoc;
	localAssoc = IRExpr_Associative(nrLocalArgs, inp->op);
	memcpy(localAssoc->contents, localArgs, sizeof(IRExpr *) * nrLocalArgs);
	localAssoc->nr_arguments = nrLocalArgs;
	remoteAssoc = IRExpr_Associative(nrRemoteArgs, inp->op);
	memcpy(remoteAssoc->contents, remoteArgs, sizeof(IRExpr *) * nrRemoteArgs);
	remoteAssoc->nr_arguments = nrRemoteArgs;

	*localPart = localAssoc;
	*remotePart = remoteAssoc;
}

static StateMachine *
removeLocalSurvival(StateMachine *sm, const AllowableOptimisations &opt, bool *done_something)
{
	StateMachineRes assertFailedRes;

	if (opt.preferCrash())
		assertFailedRes = smr_crash;
	else
		assertFailedRes = smr_survive;

	std::set<StateMachineBifurcate *> bifurcations;
	enumStates(sm, &bifurcations);

	std::map<const StateMachineState *, StateMachineState *> rewriteRules;

	for (auto it = bifurcations.begin(); it != bifurcations.end(); it++) {
		StateMachineBifurcate *smb = *it;
		if (smb->trueTarget == smb->falseTarget) {
			/* The rest of the optimiser will remove this
			   state shortly, and the main loop of this
			   optimiser is easier if we don't have to
			   consider this case. */
			continue;
		}
		if (smb->trueTarget != assertFailedState &&
		    smb->falseTarget != assertFailedState)
			continue;

		/* Precisely one target of the bifurcation is
		 * <survive> */

		IRExpr *localCond;
		IRExpr *nonLocalCond;
		getExprLocalPart(
			smb->condition,
			&localCond,
			&nonLocalCond,
			smb->trueTarget == assertFailedState ?
				Iop_Or1 :
				Iop_And1);

		if (!localCond)
			continue;

		/* Precisely one target of the bifurcation is
		 * <survive> and at least part of the condition is on
		 * local state -> factor out the local part of the
		 * condition into an assertion. */
		StateMachineState *targ;
		if (nonLocalCond)
			targ = new StateMachineBifurcate(smb, nonLocalCond);
		else if (smb->trueTarget == assertFailedState)
			targ = smb->falseTarget;
		else
			targ = smb->trueTarget;

		rewriteRules[smb] =
			new StateMachineSideEffecting(
				smb->dbg_origin,
				new StateMachineSideEffectAssertFalse(
					smb->falseTarget == assertFailedState ?
						IRExpr_Unop(Iop_Not1, localCond) :
						localCond,
					true),
				targ);
	}
	if (rewriteRules.size() == 0)
		return sm;
	*done_something = true;

	StateMachineTransformer::rewriteMachine(sm, rewriteRules, true);
	assert(rewriteRules.count(sm->root));
	return new StateMachine(sm, rewriteRules[sm->root]);
}

/* End of namespace */
}

StateMachine *
removeLocalSurvival(StateMachine *sm, const AllowableOptimisations &opt, bool *done_something)
{
	return _remove_local_survival::removeLocalSurvival(sm, opt, done_something);
}
