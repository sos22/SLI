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
	      VexPtr<OracleInterface> &oracle,
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
	input->loadMachine = removeMarkers(sm, optIn, oracle, token);
	input->loadMachine = removeAssertions(input->loadMachine, optIn, oracle, false, token);

	sm = input->storeMachine;
	input->storeMachine = removeMarkers(sm, optIn, oracle, token);
	input->storeMachine = removeAssertions(input->storeMachine, optIn, oracle, false, token);

	return input;
}

class DummyOracle : public OracleInterface {
	CrashSummary *summary;
	void visit(HeapVisitor &hv) {
		hv(summary);
	}
	bool memoryAccessesMightAlias(const MemoryAccessIdentifier &mai1,
				      const MemoryAccessIdentifier &mai2)
	{
		if (summary->aliasing.empty())
			return true;
		for (auto it = summary->aliasing.begin(); it != summary->aliasing.end(); it++) {
			if ((it->first == mai1 && it->second == mai2) ||
			    (it->first == mai2 && it->second == mai1))
				return true;
		}
		return false;
	}

public:
	DummyOracle(CrashSummary *_summary)
		: summary(_summary)
	{}
	bool memoryAccessesMightAlias(const AllowableOptimisations &, StateMachineSideEffectLoad *l1, StateMachineSideEffectLoad *l2) {
		return memoryAccessesMightAlias(l1->rip, l2->rip);
	}
	bool memoryAccessesMightAlias(const AllowableOptimisations &, StateMachineSideEffectLoad *l1, StateMachineSideEffectStore *l2) {
		return memoryAccessesMightAlias(l1->rip, l2->rip);
	}
	bool memoryAccessesMightAlias(const AllowableOptimisations &, StateMachineSideEffectStore *l1, StateMachineSideEffectStore *l2) {
		return memoryAccessesMightAlias(l1->rip, l2->rip);
	}
	bool memoryAccessesMightAliasCrossThread(const DynAnalysisRip &load, const DynAnalysisRip &store) {
		if (summary->aliasing.empty())
			return true;
		for (auto it = summary->aliasing.begin();
		     it != summary->aliasing.end();
		     it++) {
			if ((load == DynAnalysisRip(it->first.rip.rip) && store == DynAnalysisRip(it->second.rip.rip)) ||
			    (store == DynAnalysisRip(it->first.rip.rip) && load == DynAnalysisRip(it->second.rip.rip)))
				return true;
		}
		return false;
	}
        bool memoryAccessesMightAliasCrossThread(const VexRip &load, const VexRip &store) {
		return memoryAccessesMightAliasCrossThread(DynAnalysisRip(load),
							   DynAnalysisRip(store));
	}
	bool hasConflictingRemoteStores(const AllowableOptimisations &, StateMachineSideEffectMemoryAccess *) {
		return true;
	}
};

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
