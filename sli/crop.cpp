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

	VexPtr<LogFile> lf(LogFile::open(inp, &ptr));
	if (!lf)
		err(1, "opening %s", inp);

	VexPtr<LogReader<unsigned long> > reduced_lf(lf->truncate(lf->mkPtr(size, 0)));
	MachineState<unsigned long> *ms = MachineState<unsigned long>::initialMachineState(reduced_lf, ptr, &ptr, ALLOW_GC);
	VexGcRoot ms_root((void **)&ms, "ms_root");

	ms->findThread(ThreadId(7))->clear_child_tid = 0x7faa32f5d9e0;
	ms->findThread(ThreadId(7))->exitted = true;

	Interpreter<unsigned long> i(ms);
	i.replayLogfile(reduced_lf, ptr, ALLOW_GC, &ptr);

	VexPtr<LogWriter<unsigned long> > lw(LogFileWriter::open(outp));
	if (!lw)
		err(1, "opening %s", outp);

	ms->dumpSnapshot(lw);
	
	Interpreter<unsigned long> i2(ms);
	VexPtr<LogReader<unsigned long> > lf_downcast(lf);
	i2.replayLogfile(lf_downcast, ptr, ALLOW_GC, NULL, lw);

	return 0;
}
