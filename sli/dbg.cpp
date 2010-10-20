#include <err.h>
#include "sli.h"

int
main(int argc, char *argv[])
{
	init_sli();

	LogReaderPtr ptr;
	VexPtr<LogReader<unsigned long> > lf(LogFile::open(argv[1], &ptr));
	if (!lf)
		err(1, "opening %s", argv[1]);
	VexGcRoot((void **)&lf, "lf");

	VexPtr<MachineState> ms_base(MachineState::initialMachineState(lf, ptr, &ptr, ALLOW_GC));

	gdb_concrete(ms_base);

	return 0;
}
