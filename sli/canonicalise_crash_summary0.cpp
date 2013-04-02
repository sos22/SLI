#include "sli.h"
#include "inferred_information.hpp"
#include "canon.hpp"
#include "state_machine.hpp"
#include "dummy_oracle.hpp"

int
main(int argc, char *argv[])
{
	if (argc != 3)
		errx(1, "need two arguments: input and output summaries");

	init_sli();

	CrashSummary *summary;
	char *first_line;

	SMScopes scopes;
	summary = readBugReport(&scopes, argv[1], &first_line);

	summary = optimise_crash_summary(summary, new DummyOracle(summary), ALLOW_GC);

	FILE *f = fopen(argv[2], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);

	return 0;
}
