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
MachineState<abs_int_type> *MachineState<abs_int_type>::initialMachineState(AddressSpace<abs_int_type> *as,
									    const LogRecordInitialSighandlers<abs_int_type> &handlers)
{
	MachineState<abs_int_type> *work = allocator.alloc();

	memset(work, 0, sizeof(*work));

	work->threads = LibvexVector<Thread<abs_int_type> >::empty();
	work->nextTid = ThreadId(1);
	work->addressSpace = as;
	work->signalHandlers = SignalHandlers<abs_int_type>(handlers);

	return work;
}

template <typename ait>
MachineState<ait> *MachineState<ait>::initialMachineState(LogReader<ait> *lf, LogReaderPtr ptr, LogReaderPtr *end)
{
	MachineState<ait> *work;
	LogRecord<ait> *lr;
	
	lr = lf->read(ptr, &ptr);
	VexGcRoot lrkeeper((void **)&lr, "lrkeeper");
	LogRecordInitialBrk<ait> *lrib = dynamic_cast<LogRecordInitialBrk<ait>*>(lr);
	if (!lrib)
		errx(1, "first record should have been initial brk");
        AddressSpace<ait> *as = AddressSpace<ait>::initialAddressSpace(lrib->brk);

	lr = lf->read(ptr, &ptr);
        LogRecordInitialSighandlers<ait> *lris = dynamic_cast<LogRecordInitialSighandlers<ait>*>(lr);
	if (!lris)
		errx(1, "second record should have been initial signal handlers");
	work = initialMachineState(as, *lris);
	VexGcRoot keeper((void **)&work, "initialMachineState");

	while (1) {
		LogReaderPtr nextPtr;
		lr = lf->read(ptr, &nextPtr);
		if (!lr)
			err(1, "reading initial memory population");
		if (LogRecordAllocateMemory<ait> *lram = dynamic_cast<LogRecordAllocateMemory<ait>*>(lr)) {
			as->allocateMemory(*lram);
	        } else if (LogRecordMemory<ait> *lrm = dynamic_cast<LogRecordMemory<ait>*>(lr)) {
			as->populateMemory(*lrm);
		} else if (LogRecordInitialRegisters<ait> *lrir = dynamic_cast<LogRecordInitialRegisters<ait>*>(lr)) {
			work->registerThread(Thread<ait>::initialThread(*lrir));
	        } else if (LogRecordVexThreadState<ait> *lrvts = dynamic_cast<LogRecordVexThreadState<ait>*>(lr)) {
			Thread<ait> *t = work->findThread(lrvts->thread());
			t->imposeState(lrvts, as);
		} else {
			break;
		}
		ptr = nextPtr;
	}

	*end = ptr;
	return work;
}

template<typename ait>
void MachineState<ait>::dumpSnapshot(LogWriter<ait> *lw) const
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

template <typename ait> template <typename new_type>
MachineState<new_type> *MachineState<ait>::abstract() const
{
	MachineState<new_type> *work = MachineState<new_type>::allocator.alloc();

	memset(work, 0, sizeof(*work));
	work->exitted = exitted;
	work->exit_status = new_type::import(exit_status, ImportOriginInitialValue::get());
	work->nextTid = nextTid;
	signalHandlers.abstract<new_type>(&work->signalHandlers);
	work->addressSpace = addressSpace->abstract<new_type>();
	work->threads = LibvexVector<Thread<new_type> >::empty();
	work->threads->_set_size(threads->size());
	for (unsigned x = 0; x < threads->size(); x++)
		work->threads->set(x, threads->index(x)->abstract<new_type>());
	return work;
}


template <typename ait> VexAllocTypeWrapper<MachineState<ait> > MachineState<ait>::allocator;

#define MK_MACHINE_STATE(t)						\
	template MachineState<t> *MachineState<t>::dupeSelf() const;	\
	template bool MachineState<t>::crashed() const;			\
	template MachineState<t> *MachineState<t>::initialMachineState(AddressSpace<t> *as, \
								       const LogRecordInitialSighandlers<t> &handlers); \
	template void MachineState<t>::dumpSnapshot(LogWriter<t> *lw) const; \
	template VexAllocTypeWrapper<MachineState<t> > MachineState<t>::allocator; \
	template MachineState<t> *MachineState<t>::initialMachineState(LogReader<t> *lf, \
								       LogReaderPtr ptr, \
								       LogReaderPtr *end)

#define MK_MACH_CONVERTOR(from, to)		\
	template MachineState<to> *MachineState<from>::abstract() const
 
