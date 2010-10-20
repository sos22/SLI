#include <err.h>

#include "sli.h"

void MachineState::visit(HeapVisitor &hv)
{
	hv(threads);
	hv(addressSpace);
}

static void
visit_machine_state(void *_ctxt, HeapVisitor &hv)
{
	MachineState *ctxt = (MachineState *)_ctxt;
	ctxt->visit(hv);
}

/* C++ doesn't allow template global variables, so wrap it up in its
   own class.  Sigh. */
template<typename ait>
class StupidTemplateHack1 {
public:
	VexAllocType t;
	StupidTemplateHack1() {
		t.nbytes = sizeof(MachineState);
		t.gc_visit = visit_machine_state;
		t.destruct = NULL;
		t.name = "MachineState";
	}
};

MachineState *
MachineState::initialMachineState(AddressSpace *as,
				  const LogRecordInitialSighandlers<unsigned long> &handlers)
{
	MachineState *work = new MachineState();

	work->threads = LibvexVector<Thread >::empty();
	work->nextTid = ThreadId(1);
	work->addressSpace = as;
	work->signalHandlers = SignalHandlers(handlers);

	return work;
}

MachineState *
MachineState::initialMachineState(VexPtr<LogReader<unsigned long> > &lf,
							  LogReaderPtr ptr,
							  LogReaderPtr *end,
							  GarbageCollectionToken token)
{
	VexPtr<MachineState > work;
	LogRecord<unsigned long> *lr;
	
	lr = lf->read(ptr, &ptr);
	VexGcRoot lrkeeper((void **)&lr, "lrkeeper");
	LogRecordInitialBrk<unsigned long> *lrib = dynamic_cast<LogRecordInitialBrk<unsigned long>*>(lr);
	if (!lrib)
		errx(1, "first record should have been initial brk");
        VexPtr<AddressSpace > as(AddressSpace::initialAddressSpace(lrib->brk));

	lr = lf->read(ptr, &ptr);
        LogRecordInitialSighandlers<unsigned long> *lris = dynamic_cast<LogRecordInitialSighandlers<unsigned long>*>(lr);
	if (!lris)
		errx(1, "second record should have been initial signal handlers");
	work = initialMachineState(as, *lris);
	VexGcRoot keeper((void **)&work, "initialMachineState");

	while (1) {
		LogReaderPtr nextPtr;
		lr = lf->read(ptr, &nextPtr);
		if (!lr)
			break;
		if (LogRecordAllocateMemory<unsigned long> *lram = dynamic_cast<LogRecordAllocateMemory<unsigned long>*>(lr)) {
			as->allocateMemory(*lram);
	        } else if (LogRecordMemory<unsigned long> *lrm = dynamic_cast<LogRecordMemory<unsigned long>*>(lr)) {
			as->populateMemory(*lrm);
		} else if (LogRecordInitialRegisters<unsigned long> *lrir = dynamic_cast<LogRecordInitialRegisters<unsigned long>*>(lr)) {
			work->registerThread(Thread::initialThread(*lrir));
	        } else if (LogRecordVexThreadState<unsigned long> *lrvts = dynamic_cast<LogRecordVexThreadState<unsigned long>*>(lr)) {
			VexPtr<LogRecordVexThreadState<unsigned long> > l(lrvts);
			VexPtr<Thread > t(work->findThread(lrvts->thread()));
			t->imposeState(t, l, as, work, ptr, token);
		} else {
			break;
		}
		ptr = nextPtr;
	}

	as->addVsyscalls();
	as->findInterestingFunctions();

	for (unsigned x = 0; x < work->threads->size(); x++)
		work->threads->index(x)->snapshotLog.push(
			Thread::snapshot_log_entry(work, ptr));
	*end = ptr;
	return work->dupeSelf();;
}

void MachineState::dumpSnapshot(LogWriter<unsigned long> *lw) const
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

#define MK_MACHINE_STATE(t)
