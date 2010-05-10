#include "sli.h"

DECLARE_VEX_TYPE(MachineState);
DEFINE_VEX_TYPE_NO_DESTRUCT(MachineState, {ths->visit(visit);});

void MachineState::visit(HeapVisitor &hv) const
{
	hv(threads);
	hv(addressSpace);
}

MachineState *MachineState::initialMachineState(AddressSpace *as,
						Thread *rootThread,
						const LogRecordInitialSighandlers &handlers)
{
	MachineState *work = LibVEX_Alloc_MachineState();

	memset(work, 0, sizeof(*work));

	work->threads = LibvexVector<Thread>::empty();
	work->nextTid = ThreadId(1);
	work->addressSpace = as;
	work->signalHandlers = SignalHandlers(handlers);
	work->registerThread(rootThread);

	return work;
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

