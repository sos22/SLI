#include "sli.h"

template class LibvexVector<Thread<unsigned long> >;

const ThreadId ThreadId::invalidTid;
const EventTimestamp EventTimestamp::invalid;

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

	work = new Thread<ait>();
	work->tid = initRegs.thread();
	work->regs = initRegs.regs;
	return work;
}

template <typename ait>
Thread<ait> *Thread<ait>::fork(unsigned newPid)
{
	Thread<ait> *work;

	work = new Thread<ait>();
	work->pid = newPid;
	work->regs = regs;
	return work;
}

template <typename ait>
Thread<ait> *Thread<ait>::dupeSelf() const
{
	Thread<ait> *work = new Thread<ait>();
	*work = *this;
	return work;
}

template<typename ait>
void Thread<ait>::dumpSnapshot(LogWriter<ait> *lw)
{
	VexGuestAMD64State r;

	for (unsigned x = 0; x < RegisterSet<ait>::NR_REGS; x++)
		((unsigned long *)&r)[x] = force(regs.get_reg(x));
	lw->append(new LogRecordInitialRegisters<ait>(tid, r), 0);
	if (currentIRSB && currentIRSBOffset != 0)
		lw->append(new LogRecordVexThreadState<ait>(tid, currentIRSBRip, currentIRSBOffset, temporaries), 0);

	printf("Tid %d is at %d, irsb: \n", tid._tid(),
	       currentIRSBOffset);
	if (currentIRSB)
		ppIRSB(currentIRSB);
	else
		printf("<null>\n");
}

template<typename ait>
void Thread<ait>::imposeState(VexPtr<Thread<ait> > &ths,
			      VexPtr<LogRecordVexThreadState<ait> > &rec,
			      VexPtr<AddressSpace<ait> > &as,
			      GarbageCollectionToken t)
{
	translateNextBlock(ths, as, rec->currentIRSBRip, t);
	assert(ths->currentIRSB);

	/* == is valid here, and just means we're right at the end of
	   the block and will re-translate as soon as we try to
	   resume. */
	assert(rec->statement_nr <= (unsigned)ths->currentIRSB->stmts_used);
	ths->currentIRSBOffset = rec->statement_nr;

	ths->temporaries = rec->tmp;
}

template <typename ait>
void Thread<ait>::visit(HeapVisitor &hv)
{
	hv(currentIRSB);
	temporaries.visit(hv);
	regs.visit(hv);
	visit_aiv(currentControlCondition, hv);
	visit_aiv(clear_child_tid, hv);
	visit_aiv(robust_list, hv);
	visit_aiv(set_child_tid, hv);
	visit_aiv(futex_block_address, hv);
}

template <typename ait>
EventTimestamp Thread<ait>::bumpEvent(MachineState<ait> *ms)
{
	lastEvent = EventTimestamp(tid, nrEvents++, ms->nrEvents++,
				   force(regs.rip()));
	return lastEvent;
}

template <typename ait> template <typename new_type>
Thread<new_type> *Thread<ait>::abstract() const
{
	Thread<new_type> *work = new Thread<new_type>();
	work->tid = tid;
	work->nrEvents = nrEvents;
	work->pid = pid;
	regs.abstract<new_type>(&work->regs);
	work->clear_child_tid = mkConst<new_type>(clear_child_tid);
	work->robust_list = mkConst<new_type>(robust_list);
	work->set_child_tid = mkConst<new_type>(set_child_tid);
	work->exitted = exitted;
	work->crashed = crashed;
	work->cannot_make_progress = cannot_make_progress;
	work->currentIRSB = currentIRSB;
	temporaries.abstract<new_type>(&work->temporaries);
	work->currentIRSBOffset = currentIRSBOffset;
	work->currentControlCondition =
		mkConst<new_type>(currentControlCondition);
	return work;
}

template <typename ait> template <typename new_type>
void RegisterSet<ait>::abstract(RegisterSet<new_type> *out) const
{
	memset(out, 0, sizeof(*out));
	for (unsigned x = 0; x < NR_REGS; x++)
		out->registers[x] = mkConst<new_type>(registers[x]);
}

template <typename ait> template <typename new_type>
void expression_result_array<ait>::abstract(expression_result_array<new_type> *out) const
{
	out->setSize(content.size());
	for (unsigned x = 0; x < content.size(); x++)
		content[x].abstract(&out->content[x]);
}

#define MK_THREAD(t)

