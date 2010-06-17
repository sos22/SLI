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
void Thread<ait>::dumpSnapshot(LogWriter<ait> *lw) const
{
	VexGuestAMD64State r;

	for (unsigned x = 0; x < RegisterSet<ait>::NR_REGS; x++)
		((unsigned long *)&r)[x] = force(regs.get_reg(x));
	lw->append(LogRecordInitialRegisters<ait>(tid, r), 0);
	if (currentIRSB && currentIRSBOffset != 0)
		lw->append(LogRecordVexThreadState<ait>(tid, currentIRSBOffset, temporaries), 0);
}

template<typename ait>
void Thread<ait>::imposeState(const LogRecordVexThreadState<ait> *rec,
			      AddressSpace<ait> *as)
{
	translateNextBlock(as);
	assert(currentIRSB);

	/* == is valid here, and just means we're right at the end of
	   the block and will re-translate as soon as we try to
	   resume. */
	assert(rec->statement_nr <= (unsigned)currentIRSB->stmts_used);
	currentIRSBOffset = rec->statement_nr;

	temporaries = rec->tmp;
}

template <typename ait>
void Thread<ait>::visit(HeapVisitor &hv) const
{
	hv(currentIRSB);
	temporaries.visit(hv);
	regs.visit(hv);
	visit_aiv(currentControlCondition, hv);
	visit_aiv(clear_child_tid, hv);
	visit_aiv(robust_list, hv);
	visit_aiv(set_child_tid, hv);
}

template <typename ait>
EventTimestamp Thread<ait>::bumpEvent(MachineState<ait> *ms)
{
	lastEvent = EventTimestamp(tid, nrEvents++, ms->nrEvents++);
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
	work->clear_child_tid = new_type::import(
		clear_child_tid,
		ImportOriginInitialValue::get());
	work->robust_list = new_type::import(
		robust_list,
		ImportOriginInitialValue::get());
	work->set_child_tid = new_type::import(
		set_child_tid,
		ImportOriginInitialValue::get());
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
	memset(out, 0, sizeof(*out));
	out->setSize(nr_entries);
	for (unsigned x = 0; x < nr_entries; x++) {
		out->arr[x].lo = mkConst<new_type>(arr[x].lo);
		out->arr[x].hi = mkConst<new_type>(arr[x].hi);
	}
}

#define MK_THREAD(t)

