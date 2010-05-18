#include "sli.h"

template class LibvexVector<Thread<unsigned long> >;

template<>
RegisterSet<unsigned long>::RegisterSet(VexGuestAMD64State const&r)
{
	for (unsigned x = 0; x < NR_REGS; x++)
		registers[x] = ((unsigned long *)&r)[x];
}

template<typename ait>
Thread<ait> *Thread<ait>::initialThread(const LogRecordInitialRegisters<ait> &initRegs)
{
	Thread<ait> *work;

	work = allocator.alloc();
	memset(work, 0, sizeof(*work));
	work->tid = initRegs.thread();
	work->regs = initRegs.regs;
	return work;
}

template <typename ait>
Thread<ait> *Thread<ait>::fork(unsigned newPid)
{
	Thread<ait> *work;

	work = allocator.alloc();
	memset(work, 0, sizeof(*work));
	work->pid = newPid;
	work->regs = regs;
	return work;
}

template <typename ait>
Thread<ait> *Thread<ait>::dupeSelf() const
{
	Thread<ait> *work = allocator.alloc();
	*work = *this;
	return work;
}

template<>
void Thread<unsigned long>::dumpSnapshot(LogWriter<unsigned long> *lw) const
{
	VexGuestAMD64State r;

	for (unsigned x = 0; x < RegisterSet<unsigned long>::NR_REGS; x++)
		((unsigned long *)&r)[x] = regs.get_reg(x);
	lw->append(LogRecordInitialRegisters<unsigned long>(tid, r));
	if (currentIRSB && currentIRSBOffset != 0)
		lw->append(LogRecordVexThreadState<unsigned long>(tid, currentIRSBOffset, temporaries));
}

template<typename ait>
void Thread<ait>::imposeState(const LogRecordVexThreadState<ait> &rec,
			      AddressSpace<ait> *as)
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

template <typename ait>
void Thread<ait>::visit(HeapVisitor &hv) const
{
	hv(currentIRSB);
	temporaries.visit(hv);
}

template <typename ait> VexAllocTypeWrapper<Thread<ait> > Thread<ait>::allocator;

#define MK_THREAD(t)					\
	template VexAllocTypeWrapper<Thread<t> > Thread<t>::allocator
