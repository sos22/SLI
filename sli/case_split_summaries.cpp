#include <sys/types.h>
#include <dirent.h>
#include <errno.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "intern.hpp"

static CrashSummary *
addAssumption(bbdd::scope *scope,
	      bbdd *assumption,
	      bool isTrue,
	      CrashSummary *what)
{
	return new CrashSummary(
		what->scopes,
		what->loadMachine,
		what->storeMachine,
		bbdd::And(
			scope,
			what->verificationCondition,
			isTrue ? assumption : bbdd::invert(scope, assumption)),
		what->aliasing,
		what->mai);
}

static void
write_out(CrashSummary *what, const char *metadata, const char *dir, int *cntr)
{
	char *path = my_asprintf("%s/%d", dir, *cntr);
	FILE *f = fopen(path, "w");
	if (!f)
		err(1, "opening %s", path);
	fprintf(f, "%s\n", metadata);
	printCrashSummary(what, f);
	fclose(f);

	(*cntr)++;
}

static void
case_split_summary(CrashSummary *summary,
		   const char *metadata,
		   const char *dir,
		   int *cntr)
{
	summary = internCrashSummary(summary);
	if (summary->loadMachine->root->type == StateMachineState::Bifurcate) {
		CrashSummary *ifTrue =
			addAssumption(
				&summary->scopes->bools,
				((StateMachineBifurcate *)summary->loadMachine->root)->condition,
				true,
				summary);
		write_out(ifTrue, metadata, dir, cntr);
		CrashSummary *ifFalse =
			addAssumption(
				&summary->scopes->bools,
				((StateMachineBifurcate *)summary->loadMachine->root)->condition,
				false,
				summary);
		write_out(ifFalse, metadata, dir, cntr);
	} else {
		write_out(summary, metadata, dir, cntr);
	}
}

int
main(int argc, char *argv[])
{
	if (argc != 3)
		errx(1, "need two arguments: input and output directories");

	init_sli();

	int idx = 0;
	DIR *d = opendir(argv[1]);
	if (!d)
		err(1, "opening %s", argv[1]);
	while (1) {
		errno = 0;
		struct dirent *de = readdir(d);
		if (!de) {
			if (errno)
				err(1, "reading %s", argv[1]);
			break;
		}
		if (!strcmp(de->d_name, ".") || !strcmp(de->d_name, ".."))
			continue;
		char *path = my_asprintf("%s/%s", argv[1], de->d_name);
		char *metadata;
		SMScopes scopes;
		CrashSummary *summary = readBugReport(&scopes, path, &metadata);
		free(path);

		case_split_summary(summary, metadata, argv[2], &idx);

		free(metadata);

		LibVEX_maybe_gc(ALLOW_GC);
	}

	return 0;
}
