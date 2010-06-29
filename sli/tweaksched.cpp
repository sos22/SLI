/* Slightly more intelligent schedule exploration, starting with a
   known schedule and then playing with nearby ones to characterise
   the cone of badness. */
#include <err.h>
#include <stdio.h>

#include <set>

#include "sli.h"

/* We have two ways of naming a memory access.  One, the canonical
   form, uses just the thread and the number of instructions executed
   by that thread.  The other uses the thread, the issuing RIP, the
   number of times which that thread has issued that RIP, and the
   number of memory accesses issued by that instruction.  For a given
   schedule, the two will be equivalent, but if you modify the
   schedule then non-canonical form is sometimes a better choice. */
class MemoryIdent : public Named {
protected:
	char *mkName() const {
		if (isCanon)
			return my_asprintf("%d:%lx", tid._tid(), idx);
		else
			return my_asprintf("%d@%lx:%d:%d", tid._tid(),
					   nonCanon.rip, nonCanon.cntr,
					   nonCanon.nr_instr);
	}
public:
	ThreadId tid;
	bool isCanon;
	unsigned long idx;
	struct {
		unsigned long rip;
		unsigned cntr; /* Number of times the rip has been issued */
		unsigned nr_instr; /* Number of memory ops in the
				    * instruction */
	} nonCanon;

	MemoryIdent(ThreadId _tid, unsigned long _idx)
		: tid(_tid), isCanon(true), idx(_idx)
	{
	}

	void decanon(unsigned long r, unsigned c, unsigned c2) {
		assert(isCanon);
		isCanon = false;
		idx = -1;
		nonCanon.rip = r;
		nonCanon.cntr = c;
		nonCanon.nr_instr = c2;
		clearName();
	}
};

/* A constraint on schedules, requiring that tid1:idx1 happens before
 * tid2:idx2 */
class SchedConstraint : public Named {
protected:
	char *mkName() const { return my_asprintf("%s <-< %s (%lx)",
						  before.name(),
						  after.name(),
						  inducingAddress); }
public:
	MemoryIdent before;
	MemoryIdent after;

	unsigned long inducingAddress;
	SchedConstraint(MemoryIdent _before, MemoryIdent _after,
			unsigned long addr)
		: before(_before), after(_after),
		  inducingAddress(addr)
	{
	}

	void flip()
	{
		MemoryIdent t = before;
		before = after;
		after = t;
	}

	void clearName() { Named::clearName(); }
};

class ConstraintMaker : public GarbageCollected<ConstraintMaker> {
	void emitConstraint(ThreadId beforeTid, unsigned long beforeIdx,
			    ThreadId afterTid, unsigned long afterIdx, unsigned long addr)
	{
		if (threadSeen[afterTid][beforeTid] >= beforeIdx)
			return;
		threadSeen[afterTid][beforeTid] = beforeIdx;
		constraints.push_back(SchedConstraint(MemoryIdent(beforeTid, beforeIdx),
						      MemoryIdent(afterTid, afterIdx), addr));
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

	void decanonAccessMemory(ThreadId tid, unsigned long addr, unsigned long rip,
				 std::map<ThreadId, unsigned long> &threadCounters,
				 std::pair<unsigned, unsigned> *me,
				 std::vector<SchedConstraint> &canonical);
public:
	std::vector<SchedConstraint> constraints;
	std::map<ThreadId, MemLog<unsigned long> *> threadLogs;

	void playLogfile(LogReader<unsigned long> *lr, LogReaderPtr start);
	void decanonise(LogReader<unsigned long> *lr, LogReaderPtr start);

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

void
ConstraintMaker::decanonAccessMemory(ThreadId tid, unsigned long addr, unsigned long rip,
				     std::map<ThreadId, unsigned long> &threadCounters,
				     std::pair<unsigned,unsigned> *me,
				     std::vector<SchedConstraint> &canonical)
{
	bool needed = false;
	for (std::vector<SchedConstraint>::iterator it = canonical.begin();
	     !needed && it != canonical.end();
	     it++) {
		if (it->inducingAddress == addr)
			needed = true;
	}
	if (!needed)
		return;

	for (std::vector<SchedConstraint>::iterator it = canonical.begin();
	     it != canonical.end();
		) {
		if (it->before.isCanon &&
		    it->before.tid == tid &&
		    it->before.idx == threadCounters[tid]) {
			it->before.decanon(rip, me->first, me->second);
		}
		if (it->after.isCanon &&
		    it->after.tid == tid &&
		    it->after.idx == threadCounters[tid]) {
			it->after.decanon(rip, me->first, me->second);
		}
		if (!it->before.isCanon && !it->after.isCanon) {
			it->clearName();
			constraints.push_back(*it);
			it = canonical.erase(it);
		} else {
			it++;
		}
	}
	me->second++;
}

void
ConstraintMaker::decanonise(LogReader<unsigned long> *lf, LogReaderPtr start)
{
	std::map<std::pair<ThreadId, unsigned long>, std::pair<unsigned, unsigned> > ripCounters;
	std::map<ThreadId, unsigned long> threadRips;
	std::map<ThreadId, unsigned long> threadCounters;

	std::vector<SchedConstraint> canonical(constraints);
	constraints.clear();

	while (!canonical.empty()) {
		LogRecord<unsigned long> *lr = lf->read(start, &start);

		assert(lr);

		if (LogRecordFootstep<unsigned long> *lrf =
		    dynamic_cast<LogRecordFootstep<unsigned long> *>(lr)) {
			threadRips[lr->thread()] = lrf->rip;
			std::map<std::pair<ThreadId, unsigned long>, std::pair<unsigned, unsigned> >::iterator it;
			it = ripCounters.find(std::pair<ThreadId, unsigned long>(lr->thread(), lrf->rip));
			if (it != ripCounters.end()) {
				it->second.first++;
				it->second.second = 0;
			}
		} else if (LogRecordLoad<unsigned long> *lrl =
			   dynamic_cast<LogRecordLoad<unsigned long> *>(lr)) {
			decanonAccessMemory(lr->thread(),
					    lrl->ptr,
					    threadRips[lr->thread()],
					    threadCounters,
					    &ripCounters[std::pair<ThreadId, unsigned long>(lr->thread(),
											    threadRips[lr->thread()])],
					    canonical);
			threadCounters[lr->thread()]++;
		} else if (LogRecordStore<unsigned long> *lrs =
			   dynamic_cast<LogRecordStore<unsigned long> *>(lr)) {
			decanonAccessMemory(lr->thread(),
					    lrs->ptr,
					    threadRips[lr->thread()],
					    threadCounters,
					    &ripCounters[std::pair<ThreadId, unsigned long>(lr->thread(),
											    threadRips[lr->thread()])],
					    canonical);
			threadCounters[lr->thread()]++;
		}
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

	std::map<std::pair<ThreadId, unsigned long>, std::pair<unsigned, unsigned> > ripCounters;

	for (std::vector<SchedConstraint>::iterator it = liveConstraints.begin();
	     it != liveConstraints.end();
	     it++) {
		assert(!it->before.isCanon);
		assert(!it->after.isCanon);
		ripCounters[std::pair<ThreadId, unsigned long>(it->before.tid,
							       it->before.nonCanon.rip)] =
			std::pair<unsigned, unsigned>(0, 0);
		ripCounters[std::pair<ThreadId, unsigned long>(it->after.tid,
							       it->after.nonCanon.rip)] =
			std::pair<unsigned, unsigned>(0, 0);
	}

	std::map<ThreadId, VexPtr<ThreadEvent<unsigned long> > > stashedEvents;

	unsigned record_nr;

	while (1) {
		/* Get list of available threads */
		std::set<ThreadId> availThreads;
		for (std::map<ThreadId, MemLog<unsigned long> *>::iterator it = cm->threadLogs.begin();
		     it != cm->threadLogs.end();
		     it++)
			if (it->first._tid() != 0 &&
			    ms->findThread(it->first)->runnable())
				availThreads.insert(it->first);

	select_new_thread:
		if (availThreads.empty())
			break;

		/* Replay an event in that thread. */
		ThreadId tid = *availThreads.begin();
		availThreads.erase(tid);
		Thread<unsigned long> *thr = ms->findThread(tid);

		std::map<std::pair<ThreadId, unsigned long>, std::pair<unsigned, unsigned> >::iterator probe;
		probe = ripCounters.find(std::pair<ThreadId, unsigned long>(tid,
									    thr->regs.rip()));
		if (probe != ripCounters.end()) {
			for (std::vector<SchedConstraint>::iterator it = liveConstraints.begin();
			     it != liveConstraints.end();
			     it++) {
				if (it->after.tid == tid &&
				    it->after.nonCanon.rip == thr->regs.rip() &&
				    it->after.nonCanon.cntr <= probe->second.first &&
				    it->after.nonCanon.nr_instr <= probe->second.second) {
					goto select_new_thread;
				}
			}
		}


		ThreadEvent<unsigned long> *evt;
		if (stashedEvents[tid])
			evt = stashedEvents[tid];
		else
			evt = thr->runToEvent(ms->addressSpace, ms);


#if 0
		printf("%d:%lx:%lx:%d:%d: (%d) %s\n",
		       tid._tid(),
		       threadCounters[tid],
		       thr->regs.rip(),
		       (probe == ripCounters.end()) ? -1 : probe->second.first,
		       (probe == ripCounters.end()) ? -1 : probe->second.second,
		       record_nr++,
		       evt->name());
#endif

		if ( dynamic_cast<InstructionEvent<unsigned long> *> (evt)) {
			if (probe != ripCounters.end()) {
				probe->second.first++;
				probe->second.second = 0;
			}
		}

		if ( dynamic_cast<LoadEvent<unsigned long> *>(evt) ||
		     dynamic_cast<StoreEvent<unsigned long> *>(evt) ||
		     dynamic_cast<CasEvent<unsigned long> *>(evt) ) {
			threadCounters[tid]++;
			probe->second.second++;
			if (probe != ripCounters.end()) {
				for (std::vector<SchedConstraint>::iterator it = liveConstraints.begin();
				     it != liveConstraints.end();
					) {
					if (it->before.tid == tid &&
					    it->before.nonCanon.rip == thr->regs.rip() &&
					    it->before.nonCanon.cntr <= probe->second.first &&
					    it->before.nonCanon.nr_instr < probe->second.second) {
						it = liveConstraints.erase(it);
					} else {
						it++;
					}
				}
			}
		}

		MemLog<unsigned long> *logfile = cm->threadLogs[tid];
		LogReaderPtr &logptr(threadPtrs[tid]);
#if 1
		stashedEvents[tid] = evt->fuzzyReplay(ms, logfile, logptr, &logptr);
#else
		VexPtr<LogRecord<unsigned long> > lr(logfile->read(logptr, &logptr));
		if (!lr) {
			thr->cannot_make_progress = true;
			continue;
		}
		stashedEvents[tid] = evt->replay(lr, ms);
		process_memory_records(ms->addressSpace, logfile, logptr,
				       &logptr, (LogWriter<unsigned long> *)NULL);
#endif
	}

	printf("Ran %d records.\n", record_nr);
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

	printf("Initial race set:\n");
	for (std::vector<SchedConstraint>::iterator it = cm->constraints.begin();
	     it != cm->constraints.end();
	     it++) {
		printf("%s\n", it->name());
	}

	cm->decanonise(lf, ptr);

	printf("Decanoned:\n");
	for (std::vector<SchedConstraint>::iterator it = cm->constraints.begin();
	     it != cm->constraints.end();
	     it++) {
		printf("%s\n", it->name());
	}

	replayToSchedule(cm);

	for (std::vector<SchedConstraint>::iterator it = cm->constraints.begin();
	     it != cm->constraints.end();
	     it++) {
		printf("Flip %s\n", it->name());
		it->flip();
		replayToSchedule(cm);
	}

	return 0;
}

