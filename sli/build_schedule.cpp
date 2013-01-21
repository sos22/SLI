#include <stdio.h>

#include "sli.h"
#include "oracle.hpp"

int
main(int argc, char *argv[])
{
	if (argc != 4)
		errx(1, "need four args: binary, types db, and output file");
	init_sli();
	const char *binary = argv[1];
	const char *typesdb = argv[2];
	const char *out = argv[3];

	auto ms = MachineState::readELFExec(binary);
	auto thr = ms->findThread(ThreadId(1));
	auto oracle = new Oracle(ms, thr, typesdb);
	
	FILE *f = fopen(out, "w");
	if (!f)
		err(1, "opening %s", out);
	for (auto instrIterator = oracle->type_db->enumerateAllInstructions();
	     !instrIterator->finished();
	     instrIterator->advance()) {
		DynAnalysisRip dar;
		instrIterator->fetch(&dar);
		fprintf(f, "%s\n", dar.name());
	}

	if (fclose(f) != 0)
		err(1, "closing %s", out);

	return 0;
}
