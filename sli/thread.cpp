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

template<typename ait>
void Thread<ait>::dumpSnapshot(LogWriter<ait> *lw) const
{
	VexGuestAMD64State r;

	for (unsigned x = 0; x < RegisterSet<ait>::NR_REGS; x++)
		((unsigned long *)&r)[x] = force(regs.get_reg(x));
	lw->append(LogRecordInitialRegisters<ait>(tid, r));
	if (currentIRSB && currentIRSBOffset != 0)
		lw->append(LogRecordVexThreadState<ait>(tid, currentIRSBOffset, temporaries));
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

template <typename ait> template <typename new_type>
Thread<new_type> *Thread<ait>::abstract() const
{
	Thread<new_type> *work = Thread<new_type>::allocator.alloc();
	memset(work, 0, sizeof(*work));
	work->tid = tid;
	work->pid = pid;
	regs.abstract<new_type>(&work->regs);
	work->clear_child_tid = new_type::import(clear_child_tid);
	work->robust_list = new_type::import(robust_list);
	work->set_child_tid = new_type::import(set_child_tid);
	work->exitted = exitted;
	work->crashed = crashed;
	work->cannot_make_progress = cannot_make_progress;
	work->currentIRSB = currentIRSB;
	temporaries.abstract<new_type>(&work->temporaries);
	work->currentIRSBOffset = currentIRSBOffset;
	work->currentControlCondition = new_type::import(currentControlCondition);
	return work;
}

template <typename ait> template <typename new_type>
void RegisterSet<ait>::abstract(RegisterSet<new_type> *out) const
{
	memset(out, 0, sizeof(*out));
	for (unsigned x = 0; x < NR_REGS; x++)
		out->registers[x] = new_type::import(registers[x]);
}

template <typename ait> template <typename new_type>
void expression_result_array<ait>::abstract(expression_result_array<new_type> *out) const
{
	memset(out, 0, sizeof(*out));
	out->setSize(nr_entries);
	for (unsigned x = 0; x < nr_entries; x++)
		arr[x].abstract<new_type>(&out->arr[x]);
}

template <typename ait> VexAllocTypeWrapper<Thread<ait> > Thread<ait>::allocator;

#define MK_THREAD(t)					\
	template VexAllocTypeWrapper<Thread<t> > Thread<t>::allocator

