/* Look through the crash summaries in the current directory and
   remove any which never compute BadPtr expressions, because they
   tend to be far less interesting than those which do. */
#include <dirent.h>

#include "sli.h"
#include "offline_analysis.hpp"
#include "state_machine.hpp"
#include "inferred_information.hpp"

static bool
irexprUsesBadPtr(const IRExpr *e)
{
	struct : public IRExprTransformer {
		bool res;
		IRExpr *transformIex(IRExprUnop *ieg) {
			if (ieg->op == Iop_BadPtr)
				res = true;
			return IRExprTransformer::transformIex(ieg);
		}
	} doit;
	doit.res = false;
	doit.doit(const_cast<IRExpr *>(e));
	return doit.res;
}

static bool
machineUsesBadPtr(const StateMachine *sm)
{
	std::vector<const StateMachineBifurcate *> s;
	enumStates(sm, &s);
	for (auto it = s.begin(); it != s.end(); it++) {
		if (irexprUsesBadPtr( (*it)->condition) )
			return true;
	}
	return false;
}

static bool
summaryUsesBadPtr(const CrashSummary *summary)
{
	return machineUsesBadPtr(summary->loadMachine) ||
		machineUsesBadPtr(summary->storeMachine);
}

int
main(int argc, char *argv[])
{
	init_sli();

	if (argc == 2) {
		CrashSummary *summary;
		summary = readBugReport(argv[1], NULL);

		if (summaryUsesBadPtr(summary)){
			printf("Uses badptr\n");
			return 0;
		} else {
			printf("Does not use badptr\n");
			return 1;
		}
	}

	std::vector<std::pair<char *, CrashSummary *> > summaries;
	DIR *d = opendir(".");
	if (!d)
		err(1, "opening ./");
	while (1) {
		errno = 0;
		struct dirent *de = readdir(d);
		if (!de) {
			if (errno)
				err(1, "reading current directory");
			break;
		}
		if (!strcmp(de->d_name, ".") || !strcmp(de->d_name, ".."))
			continue;
		CrashSummary *summary = readBugReport(de->d_name, NULL);
		if (!summaryUsesBadPtr(summary))
			unlink(de->d_name);
	}
	return 0;
}
