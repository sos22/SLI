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
		clearName();
	}

	void clearName() { Named::clearName(); }
};

class ConstraintMaker : public GarbageCollected<ConstraintMaker> {
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
	LogReaderPtr idx = ptr;
	ThreadId effTid;

	/* Phase 1: find all racing addresses */
	std::map<unsigned long, std::pair<ThreadId, unsigned long> > lastWriter;
	std::map<unsigned long, std::pair<ThreadId, unsigned long> > lastReader;
	std::map<ThreadId, std::map<ThreadId, unsigned long> > threadSeen;
	std::map<ThreadId, unsigned long> threadCounters;
	std::set<unsigned long> racingAddresses;

	while (1) {
		LogRecord<unsigned long> *lr = lf->read(idx, &idx);
		if (!lr)
			break;
		ThreadId tid = lr->thread();
		std::pair<ThreadId, unsigned long> tidCntr(tid, threadCounters[tid]);

		if (LogRecordLoad<unsigned long> *lrl =
		    dynamic_cast<LogRecordLoad<unsigned long> *>(lr)) {
			unsigned long addr = lrl->ptr;
			std::pair<ThreadId, unsigned long> lw = lastWriter[addr];
			if (lw.first.valid() &&
			    lw.first != tid &&
			    threadSeen[tid][lw.first] < lw.second) {
				threadSeen[tid][lw.first] = lw.second;
				racingAddresses.insert(addr);
			}
			if (lastReader[addr].first != tid)
				lastReader[addr] = tidCntr;
			threadCounters[tid]++;
		}

		if (LogRecordStore<unsigned long> *lrs =
		    dynamic_cast<LogRecordStore<unsigned long> *>(lr)) {
			unsigned long addr = lrs->ptr;
			std::pair<ThreadId, unsigned long> lw = lastReader[addr];
			if (lw.first.valid() &&
			    lw.first != tid &&
			    threadSeen[tid][lw.first] < lw.second) {
				threadSeen[tid][lw.first] = lw.second;
				racingAddresses.insert(addr);
			}
			lw = lastWriter[addr];
			if (lw.first.valid() &&
			    lw.first != tid &&
			    threadSeen[tid][lw.first] < lw.second) {
				threadSeen[tid][lw.first] = lw.second;
				racingAddresses.insert(addr);
			}
			lastWriter[addr] = tidCntr;
			threadCounters[tid]++;
		}
	}

	/* Phase 2: Find the races.  Split the log into per-thread
	   components at the same time. */
	idx = ptr;
	threadSeen.clear();
	threadCounters.clear();

	/* <is_read, <tid, cntr> > */
	typedef std::vector<std::pair<bool, std::pair<ThreadId, unsigned> > > memlog_t;
	std::map<unsigned long, memlog_t> memLogs;

	while (1) {
		LogRecord<unsigned long> *lr = lf->read(idx, &idx);
		if (!lr)
			break;
		ThreadId tid = lr->thread();
		std::pair<ThreadId, unsigned long> tidCntr(tid, threadCounters[tid]);

		if (LogRecordLoad<unsigned long> *lrl =
		    dynamic_cast<LogRecordLoad<unsigned long> *>(lr)) {
			if (racingAddresses.count(lrl->ptr)) {
				memlog_t &mlog = memLogs[lrl->ptr];
				/* We race with any write which we
				   can't order based on ``seen''
				   relations */
				for (memlog_t::iterator it = mlog.begin();
				     it != mlog.end();
				     it++) {
					if (!it->first &&
					    it->second.first != tid &&
					    it->second.second > threadSeen[tid][it->first]) {
						threadSeen[tid][it->second.first] = it->second.second;
						constraints.push_back(
							SchedConstraint(
								MemoryIdent(it->second.first,
									    it->second.second),
								MemoryIdent(tid, threadCounters[tid]),
								lrl->ptr));
					}
				}
				mlog.push_back(std::pair<bool, std::pair<ThreadId, unsigned> >
					       (true, tidCntr));
			}
			threadCounters[tid]++;
		}

		if (LogRecordStore<unsigned long> *lrs =
		    dynamic_cast<LogRecordStore<unsigned long> *>(lr)) {
			if (racingAddresses.count(lrs->ptr)) {
				memlog_t &mlog = memLogs[lrs->ptr];
				/* We race with any access which we
				   can't order based on ``seen''
				   relations */
				for (memlog_t::iterator it = mlog.begin();
				     it != mlog.end();
				     it++) {
					if (it->second.first != tid &&
					    it->second.second > threadSeen[tid][it->first]) {
						threadSeen[tid][it->second.first] = it->second.second;
						constraints.push_back(
							SchedConstraint(
								MemoryIdent(it->second.first,
									    it->second.second),
								MemoryIdent(tid, threadCounters[tid]),
								lrs->ptr));
					}
				}
				mlog.push_back(std::pair<bool, std::pair<ThreadId, unsigned> >
					       (false, tidCntr));
			}
			threadCounters[tid]++;
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

	unsigned event_nr = 0;

	while (!ms->exitted) {
		/* Get list of available threads */
		std::set<ThreadId> availThreads;
		for (std::map<ThreadId, MemLog<unsigned long> *>::iterator it = cm->threadLogs.begin();
		     it != cm->threadLogs.end();
		     it++)
			if (it->first._tid() != 0 &&
			    ms->findThread(it->first)->runnable()) {
				availThreads.insert(it->first);
			}

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
				) {
				if (it->after.tid == tid &&
				    it->after.nonCanon.rip == thr->regs.rip() &&
				    it->after.nonCanon.cntr <= probe->second.first &&
				    it->after.nonCanon.nr_instr <= probe->second.second) {
					if (availThreads.empty()) {
						/* Okay, can't satisfy
						   all constraints.
						   Remove one and see
						   what happens. */
						it = liveConstraints.erase(it);
					} else {
						goto select_new_thread;
					}
				} else {
					it++;
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
		       event_nr,
		       evt->name());
#endif

		event_nr++;

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

	printf("Ran %d events.\n", event_nr);
	if (ms->exitted)
		printf("Machine exitted, status %ld\n", ms->exit_status);
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

	cm->decanonise(lf, ptr);

	printf("Base schedule (%zd items):\n", cm->constraints.size());
	for (std::vector<SchedConstraint>::iterator it = cm->constraints.begin();
	     it != cm->constraints.end();
	     it++) {
		printf("%s\n", it->name());
	}

	replayToSchedule(cm);

	for (std::vector<SchedConstraint>::reverse_iterator it = cm->constraints.rbegin();
	     it != cm->constraints.rend();
	     it++) {
		printf("\n\nFlip %s  -> ", it->name());
		it->flip();
		printf("%s: ", it->name());
		replayToSchedule(cm);
		it->flip();
	}

	return 0;
}

