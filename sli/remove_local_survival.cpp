#include "sli.h"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"

namespace _remove_local_survival {

static bool
exprIsLocal(IRExpr *input)
{
	struct : public IRExprTransformer {
		bool res;
		void stop() {
			res = false;
			abortTransform();
		}
		IRExpr *transformIex(IRExprGet *ieg) {
			if (ieg->reg.gen() != (unsigned)-1)
				stop();
			return ieg;
		}
		IRExpr *transformIex(IRExprGetI *ieg) {
			stop();
			return ieg;
		}
		IRExpr *transformIex(IRExprHappensBefore *ieg) {
			stop();
			return ieg;
		}
		IRExpr *transformIex(IRExprFreeVariable *ieg) {
			stop();
			return ieg;
		}
	} doit;
	doit.res = true;
	doit.doit(input);
	return doit.res;
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
	StateMachineState *assertFailedState;

	if (opt.preferCrash())
		assertFailedState = StateMachineCrash::get();
	else
		assertFailedState = StateMachineNoCrash::get();

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
			targ = new StateMachineBifurcate(smb->origin, nonLocalCond, smb->trueTarget, smb->falseTarget);
		else if (smb->trueTarget == assertFailedState)
			targ = smb->falseTarget;
		else
			targ = smb->trueTarget;

		rewriteRules[smb] =
			new StateMachineSideEffecting(
				smb->origin,
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
	return new StateMachine(rewriteRules[sm->root], sm->origin, sm->cfg_roots);
}

/* End of namespace */
}

StateMachine *
removeLocalSurvival(StateMachine *sm, const AllowableOptimisations &opt, bool *done_something)
{
	return _remove_local_survival::removeLocalSurvival(sm, opt, done_something);
}
