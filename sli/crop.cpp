#include <err.h>
#include <string.h>

#include "sli.h"

int
main(int argc, char *argv[])
{
	if (argc != 4)
		errx(1, "need precisely three arguments: input, output, and target size");

	const char *inp = argv[1];
	const char *outp = argv[2];
	unsigned long size = atol(argv[3]);

	init_sli();

	LogReaderPtr ptr;

	VexPtr<LogReader> lf(LogReader::open(inp, &ptr));
	if (!lf)
		err(1, "opening %s", inp);

	VexPtr<LogReader> reduced_lf(lf->truncate(LogReaderPtr(size, 0)));
	VexPtr<MachineState> ms(MachineState::initialMachineState(reduced_lf, ptr, &ptr, ALLOW_GC));

	//ms->findThread(ThreadId(3))->clear_child_tid = 0x7fbc4d69e9e0;

	Interpreter i(ms);
	i.replayLogfile(reduced_lf, ptr, ALLOW_GC, &ptr);
	ms = i.currentState;

	VexPtr<LogWriter> lw(LogFileWriter::open(outp));
	if (!lw)
		err(1, "opening %s", outp);

	ms->dumpSnapshot(lw);
	
	Interpreter i2(ms);
	VexPtr<LogReader> lf_downcast(lf);
	i2.replayLogfile(lf_downcast, ptr, ALLOW_GC, NULL, lw);

	return 0;
}
