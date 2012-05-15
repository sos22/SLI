#include <err.h>
#include "sli.h"

int
main(int argc, char *argv[])
{
	if (argc < 2)
		err(1, "need a logfile");

	init_sli();

	LogReaderPtr ptr;
	VexPtr<LogReader> lf(LogReader::open(argv[1], &ptr));
	if (!lf)
		err(1, "opening %s", argv[1]);

	VexPtr<MachineState> ms_base(MachineState::initialMachineState(lf, ptr, &ptr, ALLOW_GC));

	gdb_concrete(ms_base);

	return 0;
}
