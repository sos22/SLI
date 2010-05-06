#include "sli.h"

template class LibvexVector<Thread>;

DECLARE_VEX_TYPE(Thread);
DEFINE_VEX_TYPE_NO_DESTRUCT(Thread, {visit(ths->currentIRSB);ths->temporaries.visit(visit);});

Thread *Thread::initialThread(const LogRecordInitialRegisters &initRegs)
{
	Thread *work;

	work = LibVEX_Alloc_Thread();
	memset(work, 0, sizeof(*work));
	work->tid = ThreadId(1);
	work->regs = initRegs.regs;
	return work;
}

Thread *Thread::forkThread(unsigned newPid, const Thread &parent)
{
	Thread *work;

	work = LibVEX_Alloc_Thread();
	memset(work, 0, sizeof(*work));
	work->pid = newPid;
	work->regs = parent.regs;
	return work;
}

