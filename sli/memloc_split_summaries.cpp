#include <sys/types.h>
#include <dirent.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "offline_analysis.hpp"

static int
nr_distinct_memory_locations(CrashSummary *summary)
{
	summary = internCrashSummary(summary);
	struct : public StateMachineTransformer {
		std::set<IRExpr *> addrs;
		StateMachineSideEffectLoad *transformOneSideEffect(
			StateMachineSideEffectLoad *sel, bool *) {
			addrs.insert(sel->addr);
			return NULL;
		}
		StateMachineSideEffectStore *transformOneSideEffect(
			StateMachineSideEffectStore *ses, bool *) {
			addrs.insert(ses->addr);
			return NULL;
		}
		bool rewriteNewStates() const { return false; }
	} doit;
	transformCrashSummary(summary, doit);
	return doit.addrs.size();
}

int
main(int argc, char *argv[])
{
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
		CrashSummary *summary = readBugReport(path, &metadata);
		free(path);

		int nr_locs = nr_distinct_memory_locations(summary);
		char *out_dir = my_asprintf("nr_locs=%d", nr_locs);
		mkdir(out_dir, 0750);
		char *out_file = my_asprintf("%s/%s", out_dir, de->d_name);
		free(out_dir);
		FILE *f = fopen(out_file, "w");
		if (!f)
			err(1, "opening %s", out_file);
		free(out_file);
		fprintf(f, "%s\n", metadata);
		printCrashSummary(summary, f);
		fclose(f);

		LibVEX_maybe_gc(ALLOW_GC);
	}

	return 0;
}
