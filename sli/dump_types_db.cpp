#include <err.h>

#include "sli.h"
#include "mapping.hpp"

#include "typesdb.hpp"

int
main(int argc, char *argv[])
{
	if (argc < 3)
		errx(1, "not enough arguments");

	init_sli();

	TypesDb *types = new TypesDb(argv[1]);
	DynAnalysisRip vr;

	const char *ign;
	if (!parseDynAnalysisRip(&vr, argv[2], &ign))
		errx(1, "cannot parse %s as vex rip", argv[2]);

	std::vector<TypesDb::types_entry> loads;
	std::vector<TypesDb::types_entry> stores;;
	if (!types->lookupEntry(vr, loads, stores))
		errx(1, "%s not in database", vr.name());
	printf("Loads:\n");
	for (auto it = loads.begin(); it != loads.end(); it++)
		printf("\t%s%s\n", it->rip.name(), it->is_private ? " (private)" : "");
	printf("Stores:\n");
	for (auto it = stores.begin(); it != stores.end(); it++)
		printf("\t%s%s\n", it->rip.name(), it->is_private ? " (private)" : "");

	return 0;
}
