#include <err.h>

#include "sli.h"

template<typename abs_int_type>
void MachineState<abs_int_type>::visit(HeapVisitor &hv) const
{
	hv(threads);
	hv(addressSpace);
}

template<typename abs_int_type>
void visit_machine_state(const void *_ctxt, HeapVisitor &hv)
{
	const MachineState<abs_int_type> *ctxt = (const MachineState<abs_int_type> *)_ctxt;
	ctxt->visit(hv);
}

/* C++ doesn't allow template global variables, so wrap it up in its
   own class.  Sigh. */
template<typename ait>
class StupidTemplateHack1 {
public:
	VexAllocType t;
	StupidTemplateHack1() {
		t.nbytes = sizeof(MachineState<ait>);
		t.gc_visit = visit_machine_state<ait>;
		t.destruct = NULL;
		t.name = "MachineState";
	}
};

template<typename abs_int_type>
MachineState<abs_int_type> *MachineState<abs_int_type>::initialMachineState(AddressSpace *as,
									    const LogRecordInitialSighandlers &handlers)
{
	MachineState<abs_int_type> *work = allocator.alloc();

	memset(work, 0, sizeof(*work));

	work->threads = LibvexVector<Thread<abs_int_type> >::empty();
	work->nextTid = ThreadId(1);
	work->addressSpace = as;
	work->signalHandlers = SignalHandlers(handlers);

	return work;
}

template <typename ait>
MachineState<ait> *MachineState<ait>::initialMachineState(LogReader *lf, LogFile::ptr ptr, LogFile::ptr *end)
{
	MachineState<ait> *work;
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
	VexGcRoot keeper((void **)&work);

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
			work->registerThread(Thread<unsigned long>::initialThread(*lrir));
		} else if (LogRecordVexThreadState *lrvts = dynamic_cast<LogRecordVexThreadState*>(lr)) {
			Thread<unsigned long> *t = work->findThread(lrvts->thread());
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

template<typename ait>
void MachineState<ait>::dumpSnapshot(LogWriter *lw) const
{
	addressSpace->dumpBrkPtr(lw);
	signalHandlers.dumpSnapshot(lw);
	addressSpace->dumpSnapshot(lw);
	for (unsigned x = 0; x < threads->size(); x++)
		threads->index(x)->dumpSnapshot(lw);
}

template<typename ait>
MachineState<ait> *MachineState<ait>::dupeSelf() const
{
	MachineState<ait> *work = allocator.alloc();
	*work = *this;

	work->addressSpace = addressSpace->dupeSelf();
	work->threads = LibvexVector<Thread<ait> >::empty();
	work->threads->_set_size(threads->size());
	for (unsigned x = 0; x < threads->size(); x++)
		work->threads->set(x, threads->index(x)->dupeSelf());
	return work;
}

template<typename ait>
void MachineState<ait>::sanityCheck() const
{
	addressSpace->sanityCheck();
}

template<typename ait>
bool MachineState<ait>::crashed() const
{
	unsigned x;
	for (x = 0; x < threads->size(); x++)
		if (threads->index(x)->crashed)
			return true;
	return false;
}

template <typename ait> VexAllocTypeWrapper<MachineState<ait> > MachineState<ait>::allocator;

#define MK_MACHINE_STATE(t)						\
	template MachineState<t> *MachineState<t>::dupeSelf() const;	\
	template bool MachineState<t>::crashed() const;			\
	template MachineState<t> *MachineState<t>::initialMachineState(AddressSpace *as, \
								       const LogRecordInitialSighandlers &handlers); \
	template MachineState<t> *MachineState<t>::initialMachineState(LogReader *lf, \
								       LogFile::ptr ptr, \
								       LogFile::ptr *end); \
	template void MachineState<t>::dumpSnapshot(LogWriter *lw) const; \
	template VexAllocTypeWrapper<MachineState<t> > MachineState<t>::allocator 

