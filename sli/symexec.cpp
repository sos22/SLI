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

	MachineState<unsigned long> *concrete = MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr);
	MachineState<abstract_interpret_value> *abstract = concrete->abstract<abstract_interpret_value>();
	
	Interpreter<abstract_interpret_value> i(abstract);

	LogReader<abstract_interpret_value> *al = lf->abstract<abstract_interpret_value>();

	i.replayLogfile(al, ptr);

	printf("Replayed symbolically.\n");

	return 0;
}
