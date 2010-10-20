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
	check_fpu_control();

	LogReaderPtr ptr;

	VexPtr<LogFile> lf(LogFile::open(inp, &ptr));
	if (!lf)
		err(1, "opening %s", inp);

	check_fpu_control();
	VexPtr<LogReader<unsigned long> > reduced_lf(lf->truncate(lf->mkPtr(size, 0)));
	check_fpu_control();
	MachineState *ms = MachineState::initialMachineState(reduced_lf, ptr, &ptr, ALLOW_GC);
	check_fpu_control();
	VexGcRoot ms_root((void **)&ms, "ms_root");

	//ms->findThread(ThreadId(3))->clear_child_tid = 0x7fbc4d69e9e0;

	Interpreter<unsigned long> i(ms);
	i.replayLogfile(reduced_lf, ptr, ALLOW_GC, &ptr);
	ms = i.currentState;

	VexPtr<LogWriter<unsigned long> > lw(LogFileWriter::open(outp));
	if (!lw)
		err(1, "opening %s", outp);

	ms->dumpSnapshot(lw);
	
	Interpreter<unsigned long> i2(ms);
	VexPtr<LogReader<unsigned long> > lf_downcast(lf);
	i2.replayLogfile(lf_downcast, ptr, ALLOW_GC, NULL, lw);

	return 0;
}
