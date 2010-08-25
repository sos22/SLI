#include "sli.h"
#include <err.h>

int
main(int argc, char *argv[])
{
	init_sli();

	LogReaderPtr ptr;
	VexPtr<LogFile> lf_base(LogFile::open(argv[1], &ptr));
	if (!lf_base.get())
		err(1, "opening %s", argv[1]);
	VexPtr<LogReader<racetrack_value> > lf(lf_base->abstract<racetrack_value>());

        VexPtr<MachineState<racetrack_value> > ms(
		MachineState<racetrack_value>::initialMachineState(
			lf, ptr, &ptr));

	Interpreter<racetrack_value> i(ms);

	i.replayLogfile(lf, ptr);

	return 0;
}
