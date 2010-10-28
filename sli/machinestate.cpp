#include <err.h>

#include "sli.h"

void MachineState::visit(HeapVisitor &hv)
{
	hv(threads);
	hv(addressSpace);
}

MachineState *
MachineState::initialMachineState(AddressSpace *as,
				  const LogRecordInitialSighandlers &handlers)
{
	MachineState *work = new MachineState();

	work->threads = LibvexVector<Thread >::empty();
	work->nextTid = ThreadId(1);
	work->addressSpace = as;
	work->signalHandlers = SignalHandlers(handlers);

	return work;
}

MachineState *
MachineState::initialMachineState(VexPtr<LogReader > &lf,
							  LogReaderPtr ptr,
							  LogReaderPtr *end,
							  GarbageCollectionToken token)
{
	VexPtr<MachineState > work;
	LogRecord *lr;
	
	lr = lf->read(ptr, &ptr);
	VexGcRoot lrkeeper((void **)&lr, "lrkeeper");
	LogRecordInitialBrk *lrib = dynamic_cast<LogRecordInitialBrk*>(lr);
	if (!lrib)
		errx(1, "first record should have been initial brk");
        VexPtr<AddressSpace > as(AddressSpace::initialAddressSpace(lrib->brk));

	lr = lf->read(ptr, &ptr);
        LogRecordInitialSighandlers *lris = dynamic_cast<LogRecordInitialSighandlers*>(lr);
	if (!lris)
		errx(1, "second record should have been initial signal handlers");
	work = initialMachineState(as, *lris);
	VexGcRoot keeper((void **)&work, "initialMachineState");

	while (1) {
		LogReaderPtr nextPtr;
		lr = lf->read(ptr, &nextPtr);
		if (!lr)
			break;
		if (LogRecordAllocateMemory *lram = dynamic_cast<LogRecordAllocateMemory*>(lr)) {
			as->allocateMemory(*lram);
	        } else if (LogRecordMemory *lrm = dynamic_cast<LogRecordMemory*>(lr)) {
			as->populateMemory(*lrm);
		} else if (LogRecordInitialRegisters *lrir = dynamic_cast<LogRecordInitialRegisters*>(lr)) {
			work->registerThread(Thread::initialThread(*lrir));
	        } else if (LogRecordVexThreadState *lrvts = dynamic_cast<LogRecordVexThreadState*>(lr)) {
			VexPtr<LogRecordVexThreadState > l(lrvts);
			VexPtr<Thread > t(work->findThread(lrvts->thread()));
			t->imposeState(t, l, as, work, ptr, token);
		} else {
			break;
		}
		ptr = nextPtr;
	}

	for (unsigned x = 0; x < work->threads->size(); x++)
		work->threads->index(x)->snapshotLog.push(
			Thread::snapshot_log_entry(work, ptr));
	*end = ptr;
	return work->dupeSelf();;
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
	MachineState *work = new MachineState();
	*work = *this;

	work->addressSpace = addressSpace->dupeSelf();
	work->threads = LibvexVector<Thread >::empty();
	work->threads->_set_size(threads->size());
	for (unsigned x = 0; x < threads->size(); x++)
		work->threads->set(x, threads->index(x)->dupeSelf());
	return work;
}

bool MachineState::crashed() const
{
	unsigned x;
	for (x = 0; x < threads->size(); x++)
		if (threads->index(x)->crashed)
			return true;
	return false;
}

#define MK_MACHINE_STATE(t)
