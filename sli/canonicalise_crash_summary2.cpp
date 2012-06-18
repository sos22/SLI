/* Like canonicalise_crash_summary, but use some more aggressive
   canonicalisations which are more computationally expensive. */
#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "intern.hpp"
#include "allowable_optimisations.hpp"
#include "offline_analysis.hpp"
#include "nf.hpp"

static StateMachine *
removeMarkers(VexPtr<StateMachine, &ir_heap> sm,
	      const AllowableOptimisations &opt,
	      VexPtr<Oracle> &oracle,
	      GarbageCollectionToken token)
{
	std::vector<StateMachineSideEffecting *> states;
	enumStates(sm, &states);
	for (auto it = states.begin(); it != states.end(); it++) {
		auto s = *it;
		if (s->sideEffect &&
		    (s->sideEffect->type == StateMachineSideEffect::StartFunction ||
		     s->sideEffect->type == StateMachineSideEffect::EndFunction))
			s->sideEffect = NULL;
	}
	return optimiseStateMachine(sm, opt, oracle, false, token);
}

static StateMachine *
optimiseStateMachineAssuming(StateMachine *sm,
			     IRExpr *assumption,
			     bool assumptionIsTrue)
{
	assert(assumption->type() == Ity_I1);
	if (assumption->tag == Iex_Associative) {
		IRExprAssociative *a = (IRExprAssociative *)assumption;
		if ( (assumptionIsTrue && a->op == Iop_And1) ||
		     (!assumptionIsTrue && a->op == Iop_Or1) ) {
			for (int i = 0; i < a->nr_arguments; i++)
				sm = optimiseStateMachineAssuming(sm, a->contents[i],
								  assumptionIsTrue);
			return sm;
		}
	}
	if (assumption->tag == Iex_Unop) {
		IRExprUnop *a = (IRExprUnop *)assumption;
		if (a->op == Iop_Not1)
			return optimiseStateMachineAssuming(sm, a->arg,
							    !assumptionIsTrue);
	}

	struct : public StateMachineTransformer {
		IRExpr *assumption;
		bool assumptionIsTrue;

		IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
			if (e == assumption) {
				*done_something = true;
				return IRExpr_Const(IRConst_U1(assumptionIsTrue));
			}
			return StateMachineTransformer::transformIRExpr(e, done_something);
		}
		bool rewriteNewStates() const { return false; }
	} doit;
	doit.assumption = assumption;
	doit.assumptionIsTrue = assumptionIsTrue;
	return doit.transform(sm);
}

static CrashSummary *
canonicalise_crash_summary(VexPtr<CrashSummary, &ir_heap> input,
			   VexPtr<Oracle> oracle,
			   const AllowableOptimisations &optIn,
			   GarbageCollectionToken token)
{
	VexPtr<StateMachine, &ir_heap> sm;
	{
		IRExpr * cnf_condition;
		cnf_condition = convert_to_cnf(input->verificationCondition);
		if (!cnf_condition)
			cnf_condition = input->verificationCondition;

		internStateMachineTable intern;
		input->loadMachine = internStateMachine(input->loadMachine, intern);
		input->storeMachine = internStateMachine(input->storeMachine, intern);
		input->verificationCondition = internIRExpr(input->verificationCondition, intern);

		cnf_condition = internIRExpr(cnf_condition, intern);
		input->loadMachine = optimiseStateMachineAssuming(input->loadMachine, cnf_condition,
								  true);
		input->storeMachine = optimiseStateMachineAssuming(input->storeMachine, cnf_condition,
								   true);
	}

	sm = input->loadMachine;
	input->loadMachine = removeMarkers(sm, optIn, oracle, token);
	input->loadMachine = removeAssertions(input->loadMachine, optIn, oracle, false, token);

	sm = input->storeMachine;
	input->storeMachine = removeMarkers(sm, optIn, oracle, token);
	input->storeMachine = removeAssertions(input->storeMachine, optIn, oracle, false, token);

	return input;
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(argv[1]);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, argv[2]);
	}

	VexPtr<CrashSummary, &ir_heap> summary;
	char *first_line;

	summary = readBugReport(argv[3], &first_line);

	summary = canonicalise_crash_summary(
		summary,
		oracle,
		AllowableOptimisations::defaultOptimisations.
			enableassumePrivateStack().
			enablenoExtend(),
		ALLOW_GC);

	FILE *f = fopen(argv[4], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);

	return 0;
}
