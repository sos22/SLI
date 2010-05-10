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

Thread *Thread::fork(unsigned newPid)
{
	Thread *work;

	work = LibVEX_Alloc_Thread();
	memset(work, 0, sizeof(*work));
	work->pid = newPid;
	work->regs = regs;
	return work;
}

Thread *Thread::dupeSelf() const
{
	Thread *work;
	work = LibVEX_Alloc_Thread();
	*work = *this;
	return work;
}
