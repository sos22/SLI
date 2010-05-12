#include <err.h>

#include "sli.h"

DECLARE_VEX_TYPE(MachineState);
DEFINE_VEX_TYPE_NO_DESTRUCT(MachineState, {ths->visit(visit);});

void MachineState::visit(HeapVisitor &hv) const
{
	hv(threads);
	hv(addressSpace);
}

MachineState *MachineState::initialMachineState(AddressSpace *as,
						const LogRecordInitialSighandlers &handlers)
{
	MachineState *work = LibVEX_Alloc_MachineState();

	memset(work, 0, sizeof(*work));

	work->threads = LibvexVector<Thread>::empty();
	work->nextTid = ThreadId(1);
	work->addressSpace = as;
	work->signalHandlers = SignalHandlers(handlers);

	return work;
}

MachineState *MachineState::initialMachineState(LogReader *lf, LogFile::ptr ptr, LogFile::ptr *end)
{
	MachineState *work;
	LogRecord *lr;

	lr = lf->read(ptr, &ptr);
	LogRecordInitialBrk *lrib = dynamic_cast<LogRecordInitialBrk*>(lr);
	if (!lrib)
		errx(1, "first record should have been initial brk");
	AddressSpace *as = AddressSpace::initialAddressSpace(lrib->brk);
	delete lr;

	lr = lf->read(ptr, &ptr);
	LogRecordInitialSighandlers *lris = dynamic_cast<LogRecordInitialSighandlers*>(lr);
	if (!lris)
		errx(1, "second record should have been initial signal handlers");
	work = initialMachineState(as, *lris);

	while (1) {
		delete lr;
		LogFile::ptr nextPtr;
		lr = lf->read(ptr, &nextPtr);
		if (!lr)
			err(1, "reading initial memory population");
		if (LogRecordAllocateMemory *lram = dynamic_cast<LogRecordAllocateMemory*>(lr)) {
			as->allocateMemory(*lram);
		} else if (LogRecordMemory *lrm = dynamic_cast<LogRecordMemory*>(lr)) {
			as->populateMemory(*lrm);
		} else if (LogRecordInitialRegisters *lrir = dynamic_cast<LogRecordInitialRegisters*>(lr)) {
			work->registerThread(Thread::initialThread(*lrir));
		} else if (LogRecordVexThreadState *lrvts = dynamic_cast<LogRecordVexThreadState*>(lr)) {
			Thread *t = work->findThread(lrvts->thread());
			t->imposeState(*lrvts, as);
		} else {
			break;
		}
		ptr = nextPtr;
	}

	delete lr;
	
	*end = ptr;
	return work;
}

void MachineState::dumpSnapshot(LogWriter *lw) const
{
	addressSpace->dumpBrkPtr(lw);
	signalHandlers.dumpSnapshot(lw);
	addressSpace->dumpSnapshot(lw);
	for (unsigned x = 0; x < threads->size(); x++)
		threads->index(x)->dumpSnapshot(lw);
}

MachineState *MachineState::dupeSelf() const
{
	MachineState *work = LibVEX_Alloc_MachineState();
	*work = *this;

	work->addressSpace = addressSpace->dupeSelf();
	work->threads = LibvexVector<Thread>::empty();
	work->threads->_set_size(threads->size());
	for (unsigned x = 0; x < threads->size(); x++)
		work->threads->set(x, threads->index(x)->dupeSelf());
	return work;
}

void MachineState::sanityCheck() const
{
	addressSpace->sanityCheck();
}

bool MachineState::crashed() const
{
	unsigned x;
	for (x = 0; x < threads->size(); x++)
		if (threads->index(x)->crashed)
			return true;
	return false;
}
