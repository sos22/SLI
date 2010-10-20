#include "sli.h"

template class LibvexVector<Thread>;

const ThreadId ThreadId::invalidTid;
const EventTimestamp EventTimestamp::invalid;

RegisterSet::RegisterSet(VexGuestAMD64State const&r)
{
	for (unsigned x = 0; x < NR_REGS; x++)
		registers[x] = ((unsigned long *)&r)[x];
}

Thread *Thread::initialThread(const LogRecordInitialRegisters &initRegs)
{
	Thread *work;

	work = new Thread();
	work->tid = initRegs.thread();
	work->regs = initRegs.regs;
	return work;
}

Thread *Thread::fork(unsigned newPid)
{
	Thread *work;

	work = new Thread();
	work->pid = newPid;
	work->regs = regs;
	return work;
}

Thread *Thread::dupeSelf() const
{
	Thread *work = new Thread();
	*work = *this;

	/* Clear out our old machine snapshots.  This is necessary to
	   prevent a massive memory leak, as otherwise you build up an
	   enormous chain of the things and nothing ever gets GCed. */
	for (class ring_buffer<snapshot_log_entry, 2>::iterator it =
		     this->snapshotLog.begin();
	     it != this->snapshotLog.end();
	     it++)
		it->ms = NULL;
	return work;
}

void Thread::dumpSnapshot(LogWriter *lw)
{
	VexGuestAMD64State r;

	for (unsigned x = 0; x < RegisterSet::NR_REGS; x++)
		((unsigned long *)&r)[x] = force(regs.get_reg(x));
	lw->append(new LogRecordInitialRegisters(tid, r), 0);
	if (currentIRSB && currentIRSBOffset != 0) {
		/* First statement in block should be a mark */
		assert(currentIRSB->stmts[0]->tag == Ist_IMark);
		/* Should be a mark for the IRSB rip */
		assert(currentIRSB->stmts[0]->Ist.IMark.addr ==
		       force(currentIRSBRip));
		lw->append(new LogRecordVexThreadState(tid, currentIRSBRip, currentIRSBOffset, temporaries), 0);
	}

	printf("Tid %d is at %d, irsb: \n", tid._tid(),
	       currentIRSBOffset);
	if (currentIRSB)
		ppIRSB(currentIRSB);
	else
		printf("<null>\n");
}

void Thread::imposeState(VexPtr<Thread > &ths,
			      VexPtr<LogRecordVexThreadState > &rec,
			      VexPtr<AddressSpace> &as,
			      VexPtr<MachineState > &ms,
			      const LogReaderPtr &ptr,
			      GarbageCollectionToken t)
{
	translateNextBlock(ths, as, ms, ptr, rec->currentIRSBRip, t);
	assert(ths->currentIRSB);

	/* == is valid here, and just means we're right at the end of
	   the block and will re-translate as soon as we try to
	   resume. */
	assert(rec->statement_nr <= (unsigned)ths->currentIRSB->stmts_used);
	ths->currentIRSBOffset = rec->statement_nr;

	ths->temporaries = rec->tmp;
}

void Thread::visit(HeapVisitor &hv)
{
	hv(currentIRSB);
	temporaries.visit(hv);
	regs.visit(hv);
	visit_aiv(currentControlCondition, hv);
	visit_aiv(clear_child_tid, hv);
	visit_aiv(robust_list, hv);
	visit_aiv(set_child_tid, hv);
	visit_aiv(futex_block_address, hv);

	for (class ring_buffer<snapshot_log_entry, 2>::iterator it = snapshotLog.begin();
	     it != snapshotLog.end();
	     it++)
		hv(it->ms);
}

EventTimestamp Thread::bumpEvent(MachineState *ms)
{
	lastEvent = EventTimestamp(tid, nrEvents++, ms->nrEvents++,
				   force(regs.rip()));
	if (lastEvent.tid._tid() == 9 && lastEvent.idx == 0x1ab6fe)
		printf("Producing the magic event %d:%lx\n",
		       lastEvent.tid._tid(), lastEvent.idx);
	return lastEvent;
}

void
Thread::pretty_print(void) const
{
	printf("Thread tid %d, pid %d access %ld event %ld, last event %lx:%lx:%lx %s%s%s%s%s\n",
	       tid._tid(), pid,
	       nrAccesses,
	       nrEvents,
	       lastEvent.idx,
	       lastEvent.total_timestamp,
	       lastEvent.rip,
#define f(n) n ? "(" #n ")" : ""
	       f(exitted),
	       f(crashed),
	       f(idle),
	       f(cannot_make_progress),
	       f(blocked));
#undef f
	regs.pretty_print();
	temporaries.pretty_print();

	if (currentIRSB) {
		printf("Current IRSB:\n");
		ppIRSB(currentIRSB);
		printf("Offset %d, origin %s, CCC %s\n",
		       currentIRSBOffset,
		       name_aiv(currentIRSBRip),
		       name_aiv(currentControlCondition));
	}
}

#define MK_THREAD(t)

