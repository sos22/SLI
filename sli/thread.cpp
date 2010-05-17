#include "sli.h"

template class LibvexVector<Thread>;

DECLARE_VEX_TYPE(Thread);
DEFINE_VEX_TYPE_NO_DESTRUCT(Thread, {visit(ths->currentIRSB);ths->temporaries.visit(visit);});

RegisterSet::RegisterSet(VexGuestAMD64State const&r)
{
	for (unsigned x = 0; x < NR_REGS; x++)
		registers[x] = ((unsigned long *)&r)[x];
}

Thread *Thread::initialThread(const LogRecordInitialRegisters &initRegs)
{
	Thread *work;

	work = LibVEX_Alloc_Thread();
	memset(work, 0, sizeof(*work));
	work->tid = initRegs.thread();
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

void Thread::dumpSnapshot(LogWriter *lw) const
{
	VexGuestAMD64State r;

	for (unsigned x = 0; x < RegisterSet::NR_REGS; x++)
		((unsigned long *)&r)[x] = regs.get_reg(x);
	lw->append(LogRecordInitialRegisters(tid, r));
	if (currentIRSB && currentIRSBOffset != 0)
		lw->append(LogRecordVexThreadState(tid, currentIRSBOffset, temporaries));
}

void Thread::imposeState(const LogRecordVexThreadState &rec,
			 AddressSpace *as)
{
	translateNextBlock(as);
	assert(currentIRSB);

	/* == is valid here, and just means we're right at the end of
	   the block and will re-translate as soon as we try to
	   resume. */
	assert(rec.statement_nr <= (unsigned)currentIRSB->stmts_used);
	currentIRSBOffset = rec.statement_nr;

	temporaries = rec.tmp;
}

