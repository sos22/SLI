#include <err.h>

#include "sli.h"

void MachineState::visit(HeapVisitor &hv)
{
	visit_container<std::vector<Thread *> >(threads, hv);
	hv(addressSpace);
}

MachineState *
MachineState::initialMachineState(AddressSpace *as,
				  const LogRecordInitialSighandlers &handlers)
{
	MachineState *work = new MachineState();

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
	VexPtr<LogRecord> lr;
	
	lr = lf->read(ptr, &ptr);
	LogRecordInitialBrk *lrib = dynamic_cast<LogRecordInitialBrk*>(lr.get());
	if (!lrib)
		errx(1, "first record should have been initial brk");
        VexPtr<AddressSpace > as(AddressSpace::initialAddressSpace(lrib->brk));

	lr = lf->read(ptr, &ptr);
        LogRecordInitialSighandlers *lris = dynamic_cast<LogRecordInitialSighandlers*>(lr.get());
	if (!lris)
		errx(1, "second record should have been initial signal handlers");
	work = initialMachineState(as, *lris);

	while (1) {
		LogReaderPtr nextPtr;
		lr = lf->read(ptr, &nextPtr);
		if (!lr)
			break;
		if (LogRecordAllocateMemory *lram = dynamic_cast<LogRecordAllocateMemory*>(lr.get())) {
			as->allocateMemory(*lram);
	        } else if (LogRecordMemory *lrm = dynamic_cast<LogRecordMemory*>(lr.get())) {
			as->populateMemory(*lrm);
		} else if (LogRecordInitialRegisters *lrir = dynamic_cast<LogRecordInitialRegisters*>(lr.get())) {
			work->registerThread(Thread::initialThread(*lrir));
	        } else if (LogRecordVexThreadState *lrvts = dynamic_cast<LogRecordVexThreadState*>(lr.get())) {
			VexPtr<LogRecordVexThreadState > l(lrvts);
			VexPtr<Thread > t(work->findThread(lrvts->thread()));
			t->imposeState(t, l, as, work, ptr, token);
		} else {
			break;
		}
		ptr = nextPtr;
	}

	for (unsigned x = 0; x < work->threads.size(); x++)
		work->threads[x]->snapshotLog.push(
			Thread::snapshot_log_entry(work, ptr));
	*end = ptr;
	return work->dupeSelf();;
}

void MachineState::dumpSnapshot(LogWriter *lw) const
{
	addressSpace->dumpBrkPtr(lw);
	signalHandlers.dumpSnapshot(lw);
	addressSpace->dumpSnapshot(lw);
	for (unsigned x = 0; x < threads.size(); x++)
		threads[x]->dumpSnapshot(lw);
}

MachineState *MachineState::dupeSelf() const
{
	MachineState *work = new MachineState();
	*work = *this;

	work->addressSpace = addressSpace->dupeSelf();
	work->threads.resize(threads.size());
	for (unsigned x = 0; x < threads.size(); x++)
		work->threads[x] = threads[x]->dupeSelf();
	return work;
}

bool MachineState::crashed() const
{
	unsigned x;
	for (x = 0; x < threads.size(); x++)
		if (threads[x]->crashed)
			return true;
	return false;
}
