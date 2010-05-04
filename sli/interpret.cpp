#include <err.h>
#include <stdio.h>
#include <stdlib.h>

#include <exception>

extern "C" {
#include "libvex.h"
}
#include "sli.h"

static __attribute__ ((noreturn)) void
failure_exit(void)
{
	abort();
}

static void
log_bytes(const char *buf, Int nbytes)
{
	fwrite(buf, nbytes, 1, stdout);
}

int
main(int argc, char *argv[])
{
	VexControl vcon;

	std::set_terminate(__gnu_cxx::__verbose_terminate_handler);

	LibVEX_default_VexControl(&vcon);
	vcon.iropt_level = 0;
	vcon.iropt_unroll_thresh = 0;
	vcon.guest_chase_thresh = 0;
	vcon.guest_max_insns = 1;
	LibVEX_Init(failure_exit, log_bytes, 0, 0, &vcon);

	LogReader *lf;
	LogReader::ptr ptr;
	LogReader::ptr nextPtr;

	lf = LogReader::open(argv[1], &ptr);
	if (!lf)
		err(1, "opening %s", argv[1]);

	LogRecord *lr = lf->read(ptr, &ptr);
	if (!lr)
		err(1, "reading first record of logfile");
	LogRecordInitialRegisters *lrir = dynamic_cast<LogRecordInitialRegisters*>(lr);
	if (!lrir)
		err(1, "first record should have been register state");
	Thread *rootThread = new Thread(*lrir);

	lr = lf->read(ptr, &ptr);
	LogRecordInitialBrk *lrib = dynamic_cast<LogRecordInitialBrk*>(lr);
	if (!lrib)
		err(1, "second record should have been initial brk");
	AddressSpace *as = new AddressSpace(lrib->brk);

	lr = lf->read(ptr, &ptr);
	LogRecordInitialSighandlers *lris = dynamic_cast<LogRecordInitialSighandlers*>(lr);
	if (!lris)
		err(1, "third record should have been initial signal handlers");
	
	while (1) {
		delete lr;
		lr = lf->read(ptr, &nextPtr);
		if (!lr)
			err(1, "reading initial memory population");
		if (LogRecordAllocateMemory *lram = dynamic_cast<LogRecordAllocateMemory*>(lr)) {
			as->allocateMemory(*lram);
		} else if (LogRecordMemory *lrm = dynamic_cast<LogRecordMemory*>(lr)) {
			as->populateMemory(*lrm);
		} else {
			break;
		}
		ptr = nextPtr;
	}

	delete lr;
	MachineState *ms = new MachineState(as, rootThread, *lris);
	Interpreter *i = new Interpreter(ms);

	i->replayLogfile(lf, ptr);

	return 0;
}
