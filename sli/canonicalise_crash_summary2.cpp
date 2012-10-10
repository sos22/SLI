/* Like canonicalise_crash_summary, but use some more aggressive
   canonicalisations which are more computationally expensive. */
#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "intern.hpp"
#include "allowable_optimisations.hpp"
#include "offline_analysis.hpp"
#include "nf.hpp"
#include "dummy_oracle.hpp"

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

	if (assumption->tag == Iex_EntryPoint) {
		/* Simplify the CFGs a bit based on knowledge of the
		 * entry point. */
		IRExprEntryPoint *a = (IRExprEntryPoint *)assumption;
		for (auto it = sm->cfg_roots.begin();
		     it != sm->cfg_roots.end();
			) {
			unsigned tid = it->first;
			const CFGNode *root = it->second;
			if ( tid == a->thread &&
			     assumptionIsTrue != (root->label == a->label) ) {
				it = sm->cfg_roots.erase(it);
			} else {
				it++;
			}
		}
	}

	struct : public StateMachineTransformer {
		IRExpr *assumption;
		bool assumptionIsTrue;

		IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
			if (e == assumption) {
				*done_something = true;
				return IRExpr_Const(IRConst_U1(assumptionIsTrue));
			}
			if (assumptionIsTrue &&
			    e->tag == Iex_EntryPoint &&
			    assumption->tag == Iex_EntryPoint &&
			    ((IRExprEntryPoint *)e)->thread == ((IRExprEntryPoint *)assumption)->thread) {
				/* We're supposed to be interned here. */
				assert( ((IRExprEntryPoint *)e)->label != ((IRExprEntryPoint *)assumption)->label);
				/* If we entered at t1:labelA we can't
				 * also have entered at t1:labelB */
				return IRExpr_Const(IRConst_U1(0));
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
			   VexPtr<OracleInterface> oracle,
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
	VexPtr<MaiMap, &ir_heap> mai(input->mai);
	input->loadMachine = removeAnnotations(mai, input->loadMachine, optIn.enableignoreSideEffects(), oracle, true, token);

	sm = input->storeMachine;
	input->storeMachine = removeAnnotations(mai, input->storeMachine, optIn, oracle, true, token);

	if (input->loadMachine->root->type == StateMachineState::Unreached ||
	    input->storeMachine->root->type == StateMachineState::Unreached)
		input->verificationCondition = IRExpr_Const(IRConst_U1(0));

	return input;
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<CrashSummary, &ir_heap> summary;
	char *first_line;

	summary = readBugReport(argv[1], &first_line);
	VexPtr<OracleInterface> oracle(new DummyOracle(summary));

	summary = canonicalise_crash_summary(
		summary,
		oracle,
		AllowableOptimisations::defaultOptimisations.
			enableassumePrivateStack().
			enablenoExtend(),
		ALLOW_GC);

	FILE *f = fopen(argv[2], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);

	return 0;
}
