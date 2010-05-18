#include <err.h>
#include <string.h>

#include "sli.h"

int
main(int argc, char *argv[])
{
	std::set_terminate(__gnu_cxx::__verbose_terminate_handler);

	if (argc != 4)
		errx(1, "need precisely three arguments: input, output, and target size");

	const char *inp = argv[1];
	const char *outp = argv[2];
	unsigned long size = atol(argv[3]);

	init_sli();

	LogFile *lf;
	LogReaderPtr ptr;

	lf = LogFile::open(inp, &ptr);
	if (!lf)
		err(1, "opening %s", inp);

	LogFile *reduced_lf;

	reduced_lf = lf->truncate(lf->mkPtr(size, 0));
	MachineState<unsigned long> *ms = MachineState<unsigned long>::initialMachineState(reduced_lf, ptr, &ptr);
	VexGcRoot ms_root((void **)&ms);

	Interpreter<unsigned long> i(ms);
	i.replayLogfile(reduced_lf, ptr, &ptr);

	LogFileWriter *lw;

	lw = LogFileWriter::open(outp);
	if (!lw)
		err(1, "opening %s", outp);

	ms->dumpSnapshot(lw);
	
	Interpreter<unsigned long> i2(ms);
	i2.replayLogfile(lf, ptr, NULL, lw);

	delete lw;

	return 0;
}
