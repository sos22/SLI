#include <err.h>

#include "sli.h"

int
main(int argc, char *argv[])
{
	init_sli();

	MachineState *ms = MachineState::readCoredump(argv[1]);
	if (!ms)
		err(1, "reading %s as core dump", argv[1]);
	gdb_concrete(ms);

	return 0;
}
