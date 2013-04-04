/* Like canonicalise_crash_summary, but use some more aggressive
   canonicalisations which are more computationally expensive. */
#include "sli.h"
#include "oracle.hpp"
#include "inferred_information.hpp"
#include "allowable_optimisations.hpp"
#include "canon.hpp"
#include "state_machine.hpp"
#include "dummy_oracle.hpp"

int
main(int argc, char *argv[])
{
	if (argc != 3)
		errx(1, "need two arguments: input and output summaries");
	init_sli();

	VexPtr<CrashSummary, &ir_heap> summary;
	char *first_line;

	SMScopes scopes;
	summary = readBugReport(&scopes, argv[1], &first_line);
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
