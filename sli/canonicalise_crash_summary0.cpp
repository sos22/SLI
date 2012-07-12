#include "sli.h"
#include "offline_analysis.hpp"
#include "inferred_information.hpp"
#include "dummy_oracle.hpp"
#include "allowable_optimisations.hpp"
#include "state_machine.hpp"
#include "sat_checker.hpp"

static CrashSummary *
optimise_crash_summary(VexPtr<CrashSummary, &ir_heap> cs,
		       const VexPtr<OracleInterface> &oracle,
		       GarbageCollectionToken token)
{
	cs->loadMachine = optimiseStateMachine(
		cs->loadMachine,
		AllowableOptimisations::defaultOptimisations.
			enableassumePrivateStack().
			enableignoreSideEffects().
			enablenoLocalSurvival(),
		oracle,
		true,
		token);
	cs->storeMachine = optimiseStateMachine(
		cs->storeMachine,
		AllowableOptimisations::defaultOptimisations.
			enableassumePrivateStack().
			enableassumeNoInterferingStores(),
		oracle,
		true,
		token);
	cs->verificationCondition = simplifyIRExpr(
		cs->verificationCondition,
		AllowableOptimisations::defaultOptimisations);
	cs->verificationCondition = simplify_via_anf(
		cs->verificationCondition);
	cs->verificationCondition = simplifyIRExpr(
		cs->verificationCondition,
		AllowableOptimisations::defaultOptimisations);
	return cs;
}

int
main(int argc, char *argv[])
{
	init_sli();

	CrashSummary *summary;
	char *first_line;

	summary = readBugReport(argv[1], &first_line);

	CfgDecode decode;
	decode.addMachine(summary->loadMachine);
	decode.addMachine(summary->storeMachine);
	summary = optimise_crash_summary(summary, new DummyOracle(summary, &decode), ALLOW_GC);

	FILE *f = fopen(argv[2], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);

	return 0;
}
