/* Slightly more intelligent schedule exploration, starting with a
   known schedule and then playing with nearby ones to characterise
   the cone of badness. */
#include <err.h>
#include <stdio.h>

#include <set>

#include "sli.h"

/* A constraint on schedules, requiring that tid1:idx1 happens before
 * tid2:idx2 */
class SchedConstraint {
public:
	ThreadId tid1;
	unsigned long idx1;
	ThreadId tid2;
	unsigned long idx2;

	unsigned long inducingAddress;
	SchedConstraint(ThreadId _tid1, unsigned long _idx1,
			ThreadId _tid2, unsigned long _idx2,
			unsigned long addr)
		: tid1(_tid1), idx1(_idx1), tid2(_tid2), idx2(_idx2),
		  inducingAddress(addr)
	{
	}
};

class ConstraintMaker : public GarbageCollected<ConstraintMaker> {
	void emitConstraint(ThreadId beforeTid, unsigned long beforeIdx,
			    ThreadId afterTid, unsigned long afterIdx, unsigned long addr)
	{
		if (threadSeen[afterTid][beforeTid] >= beforeIdx)
			return;
		threadSeen[afterTid][beforeTid] = beforeIdx;
		constraints.push_back(SchedConstraint(beforeTid, beforeIdx,
						      afterTid, afterIdx, addr));
	}

	std::map<unsigned long, std::pair<ThreadId, unsigned long> > lastWriter;
	std::map<unsigned long, std::pair<ThreadId, unsigned long> > lastReader;
	std::map<ThreadId, std::map<ThreadId, unsigned long> > threadSeen;
	std::map<ThreadId, unsigned long> threadCounters;

	void issueRead(ThreadId tid, unsigned long addr)
	{
		std::pair<ThreadId, unsigned long> lw = lastWriter[addr];
		if (lw.first.valid() && lw.first != tid)
			emitConstraint(lw.first, lw.second, tid, threadCounters[tid], addr);
		if (lastReader[addr].first != tid)
			lastReader[addr] = std::pair<ThreadId, unsigned long>(tid, threadCounters[tid]);
		threadCounters[tid]++;
	}

	void issueWrite(ThreadId tid, unsigned long addr)
	{
		std::pair<ThreadId, unsigned long> lw = lastReader[addr];
		if (lw.first.valid() && lw.first != tid)
			emitConstraint(lw.first, lw.second, tid, threadCounters[tid], addr);
		lw = lastWriter[addr];
		if (lw.first.valid() && lw.first != tid)
			emitConstraint(lw.first, lw.second, tid, threadCounters[tid], addr);
		lastWriter[addr] = std::pair<ThreadId, unsigned long>(tid, threadCounters[tid]);
		threadCounters[tid]++;
	}

public:
	std::vector<SchedConstraint> constraints;
	std::map<ThreadId, MemLog<unsigned long> *> threadLogs;

	void playLogfile(LogReader<unsigned long> *lr, LogReaderPtr start);

	void visit(HeapVisitor &hv) const {
		for (std::map<ThreadId, MemLog<unsigned long> *>::const_iterator it = threadLogs.begin();
		     it != threadLogs.end();
		     it++)
			hv(it->second);
	}
	void destruct() { this->~ConstraintMaker(); }
	NAMED_CLASS
};

void
ConstraintMaker::playLogfile(LogReader<unsigned long> *lf, LogReaderPtr ptr)
{
	ThreadId effTid;

	while (1) {
		LogRecord<unsigned long> *lr = lf->read(ptr, &ptr);
		if (!lr)
			break;
		if (LogRecordLoad<unsigned long> *lrl =
		    dynamic_cast<LogRecordLoad<unsigned long> *>(lr)) {
			issueRead(lr->thread(), lrl->ptr);
		}
		if (LogRecordStore<unsigned long> *lrs =
		    dynamic_cast<LogRecordStore<unsigned long> *>(lr)) {
			issueWrite(lr->thread(), lrs->ptr);
		}

		/* Hack: push all of the initialisation stuff into
		 * thread 0's log. */
		effTid = lr->thread();
		if (dynamic_cast<LogRecordInitialRegisters<unsigned long> *>(lr) ||
		    dynamic_cast<LogRecordVexThreadState<unsigned long> *>(lr))
			effTid = ThreadId(0);

		if (!threadLogs[effTid]) {
			threadLogs[effTid] = MemLog<unsigned long>::emptyMemlog();
		}
		threadLogs[effTid]->append(lr, 0);
	}
}

static void
replayToSchedule(ConstraintMaker *cm)
{
	LogReaderPtr p;
	VexPtr<MachineState<unsigned long> > ms(
		MachineState<unsigned long>::initialMachineState(
			cm->threadLogs[ThreadId(0)],
			cm->threadLogs[ThreadId(0)]->startPtr(),
			&p));

	std::vector<SchedConstraint> liveConstraints(cm->constraints);

	std::map<ThreadId, unsigned long> threadCounters;
	std::map<ThreadId, LogReaderPtr> threadPtrs;

	std::map<ThreadId, VexPtr<ThreadEvent<unsigned long> > > stashedEvents;
	unsigned record_nr = 0;

	while (1) {
		/* Get list of available threads */
		std::set<ThreadId> availThreads;
		for (std::map<ThreadId, MemLog<unsigned long> *>::iterator it = cm->threadLogs.begin();
		     it != cm->threadLogs.end();
		     it++)
			if (it->first._tid() != 0 && ms->findThread(it->first)->runnable())
				availThreads.insert(it->first);
		for (std::vector<SchedConstraint>::iterator it = liveConstraints.begin();
		     it != liveConstraints.end();
		     ) {
			if (threadCounters[it->tid1] > it->idx1) {
				/* The constraint is that tid1:idx1
				   must happen before tid2:idx2.
				   tid1:idx1 has now happened, so
				   we're done. */
				it = liveConstraints.erase(it);
			} else {
				/* tid1:idx1 hasn't happened yet, so
				   we need to make sure that tid2:idx2
				   doesn't happen. */
				assert(threadCounters[it->tid2] <= it->idx2);
				if (threadCounters[it->tid2] == it->idx2)
					availThreads.erase(it->tid2);
				it++;
			}
		}

		if (availThreads.empty())
			break;

		/* Replay an event in that thread. */
		ThreadId tid = *availThreads.begin();
		Thread<unsigned long> *thr = ms->findThread(tid);
		MemLog<unsigned long> *logfile = cm->threadLogs[tid];
		LogReaderPtr &logptr(threadPtrs[tid]);
		VexPtr<LogRecord<unsigned long> > lr(logfile->read(logptr, &logptr));
		if (!lr) {
			thr->cannot_make_progress = true;
			continue;
		}

		assert(tid == lr->thread());
		ThreadEvent<unsigned long> *evt;

		if (stashedEvents[tid])
			evt = stashedEvents[tid];
		else
			evt = thr->runToEvent(ms->addressSpace, ms);

#if 0
		printf("%d:%lx:%d: %s\t%s\n", tid._tid(), threadCounters[tid], record_nr++, evt->name(),
		       lr->name());
#endif

		if (dynamic_cast<LogRecordLoad<unsigned long> *>(lr.get()) ||
		    dynamic_cast<LogRecordStore<unsigned long> *>(lr.get()))
			threadCounters[tid]++;

		stashedEvents[tid] = evt->replay(lr, ms);

		process_memory_records(ms->addressSpace, logfile, logptr,
				       &logptr, (LogWriter<unsigned long> *)NULL);
	}
}

int
main(int argc, char *argv[])
{
	init_sli();

	LogFile *lf;
	LogReaderPtr ptr;

	lf = LogFile::open(argv[1], &ptr);
	if (!lf)
		err(1, "opening %s", argv[1]);
	VexGcRoot((void **)&lf, "lf");

	VexPtr<ConstraintMaker> cm(new ConstraintMaker());
	cm->playLogfile(lf, ptr);

	for (std::vector<SchedConstraint>::iterator it = cm->constraints.begin();
	     it != cm->constraints.end();
	     it++) {
		printf("%d:%lx <-< %d:%lx\t\t%lx\n",
		       it->tid1._tid(), it->idx1,
		       it->tid2._tid(), it->idx2,
		       it->inducingAddress);
	}

	replayToSchedule(cm);

	return 0;
}

