#include <err.h>
#include <stdio.h>
#include <stdlib.h>

#include <exception>
#include <iostream>

#include "libvex.h"
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

	vexInitHeap();
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

	lr = lf->read(ptr, &ptr);
	LogRecordInitialBrk *lrib = dynamic_cast<LogRecordInitialBrk*>(lr);
	if (!lrib)
		err(1, "second record should have been initial brk");
	AddressSpace *as = AddressSpace::initialAddressSpace(lrib->brk);

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
	MachineState *ms_base = MachineState::initialMachineState(as, Thread::initialThread(*lrir), *lris);
	VexGcRoot base_root((void **)&ms_base);

#if 0
	printf("Doing initial replay...\n");
	Interpreter *i = new Interpreter(ms_adv);
	LogReader::ptr eof;
	i->replayLogfile(lf, ptr, &eof);
	delete i;

	printf("Replay from %lx to %d - 10000.. (%lx)\n",
	       ptr._off(),
	       eof.rn(),
	       (eof - 10000)._off());
	LogReader *partialLog = lf->truncate(eof - 10000);
#else
	LogReader *partialLog = lf->truncate(LogReader::ptr(0xde74e31, 4123917));
	Interpreter *i;
#endif

	printf("Replay to %d\n", 4123917);
	i = new Interpreter(ms_base);
	i->replayLogfile(partialLog, ptr, &ptr);
	delete i;

	for (unsigned x = 0; x < ms_base->threads->size(); x++) {
		MachineState *ms3 = ms_base->dupeSelf();
		printf("Collect trace of thread %d\n",
		       ms_base->threads->index(x)->tid._tid());
		i = new Interpreter(ms3);
		std::vector<MemoryAccess *> v;
		InterpretResult ir;
		ir = i->getThreadMemoryTrace(ms3->threads->index(x)->tid, &v);
		printf("Trace thread %d -> result %x, %zd items.\n",
		       x, ir, v.size());
		for (unsigned y = 0; y < v.size(); y++) {
			printf("%d: %s\n", y, v[y]->name());
			delete v[y];
		}
		delete i;
	}

	return 0;
}
