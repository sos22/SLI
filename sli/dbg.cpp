#include <err.h>
#include "sli.h"

int
main(int argc, char *argv[])
{
	init_sli();

	LogFile *lf;
	LogReaderPtr ptr;

	lf = LogFile::open(argv[1], &ptr);
	if (!lf)
		err(1, "opening %s", argv[1]);
	VexGcRoot((void **)&lf, "lf");

	MachineState<unsigned long> *ms_base = MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr, ALLOW_GC);
	VexGcRoot((void **)&ms_base, "ms_base");

	gdb_concrete(ms_base);

	return 0;
}
