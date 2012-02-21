#include <err.h>

#include "sli.h"
#include "mapping.hpp"

#include "typesdb.hpp"

int
main(int argc, char *argv[])
{
	init_sli();

	TypesDb *types = new TypesDb(argv[1]);
	VexRip vr;

	const char *ign;
	if (!parseVexRip(&vr, argv[2], &ign))
		errx(1, "cannot parse %s as vex rip", argv[2]);

	std::vector<unsigned long> o;
	types->findOffsets(vr, o);

	printf("Offsets: ");
	for (auto it = o.begin(); it != o.end(); it++)
		printf("%lx, ", *it);
	printf("\n");

	return 0;
}
