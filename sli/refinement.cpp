#include <deque>
#include <set>

#include "sli.h"

class ExplorationState : public GarbageCollected<ExplorationState> {
public:
	MachineState<abstract_interpret_value> *ms;
	MemLog<abstract_interpret_value> *lf;

	void visit(HeapVisitor &hv) const { hv(lf); hv(ms); }
	void destruct() {}
	ExplorationState(MachineState<abstract_interpret_value> *_ms,
			 MemLog<abstract_interpret_value> *_lf)
		: ms(_ms), lf(_lf)
	{
	}
	ExplorationState *dupeSelf()
	{
		return new ExplorationState(ms->dupeSelf(), lf->dupeSelf());
	}
	NAMED_CLASS
};

class Explorer : public GarbageCollected<Explorer> {
	std::deque<ExplorationState *> grayStates;
public:
	std::vector<ExplorationState *> futures;

	Explorer(const MachineState<abstract_interpret_value> *ms,
		 ThreadId ignoredTid);
	void visit(HeapVisitor &hv) const
	{
		visit_container(futures, hv);
		visit_container(grayStates, hv);
	}
	void destruct() {}
	NAMED_CLASS
};

Explorer::Explorer(const MachineState<abstract_interpret_value> *ms,
		   ThreadId ignoredThread)
	: grayStates(), futures()
{
	Explorer *thisK = this;
	VexGcRoot thisKeeper((void **)&thisK, "this");

	grayStates.push_back(new ExplorationState(ms->dupeSelf(),
						  MemLog<abstract_interpret_value>::emptyMemlog()));

	while (grayStates.size() != 0 &&
	       (grayStates.size() + futures.size()) < 10) {
		printf("%zd futures, %zd grays\n", futures.size(),
		       grayStates.size());
		ExplorationState *s = grayStates.front();
		VexGcRoot sroot((void **)&s, "sroot");
		grayStates.pop_front();

		printf("Consider %p\n", s);

		bool stopped = true;
		for (unsigned x = 0; stopped && x < s->ms->threads->size(); x++) {
			Thread<abstract_interpret_value> *thr = s->ms->threads->index(x);
			if (thr->tid == ignoredThread)
				continue;
			if (!thr->cannot_make_progress)
				stopped = false;
		}
		if (stopped) {
			/* No thread can make progress. */
			futures.push_back(s);
			printf("No progress possible.\n");
			continue;
		}

		MemTracePool<abstract_interpret_value> *thread_traces =
			new MemTracePool<abstract_interpret_value>(s->ms, ignoredThread);
		VexGcRoot ttraces((void **)&thread_traces, "ttraces");
		std::map<ThreadId, Maybe<unsigned> > *first_racing_access =
			thread_traces->firstRacingAccessMap();
		PointerKeeper<std::map<ThreadId, Maybe<unsigned> > > keeper(first_racing_access);

		/* If there are no races then we can just run one
		   thread after another, and we don't need to do
		   anything else.  We can even get away with reusing
		   the old MachineState. */
		/* This includes the case where only one thread can
		   make progress at all. */
		bool noRaces = true;
		for (std::map<ThreadId, Maybe<unsigned> >::iterator it = first_racing_access->begin();
		     it != first_racing_access->end();
		     it++) {
			if (it->first == ignoredThread)
				continue;
			if (it->second.full)
				noRaces = false;
		}
		if (noRaces) {
			for (unsigned x = 0; x < s->ms->threads->size(); x++) {
				Thread<abstract_interpret_value> *thr = s->ms->threads->index(x);
				if (thr->tid == ignoredThread)
					continue;
				if (thr->cannot_make_progress)
					continue;
				Interpreter<abstract_interpret_value> i(s->ms);
				i.runToFailure(thr->tid, s->lf, 10000000);
			}
			futures.push_back(s);
			continue;
		}

		/* Have some actual races -> have to do full
		 * repertoire. */
		for (std::map<ThreadId, Maybe<unsigned> >::iterator it = first_racing_access->begin();
		     it != first_racing_access->end();
		     it++) {
			ThreadId tid = it->first;
			Maybe<unsigned> r = it->second;
			Thread<abstract_interpret_value> *thr = s->ms->findThread(tid);
			if (thr->tid == ignoredThread)
				continue;
			if (thr->cannot_make_progress)
				continue;
			ExplorationState *newGray = s->dupeSelf();
			VexGcRoot grayKeeper((void **)&newGray, "newGray");
			Interpreter<abstract_interpret_value> i(newGray->ms);
			if (r.full) {
				printf("%p: run %d to %ld\n", newGray, tid._tid(), r.value + thr->nrAccesses);
				i.runToAccessLoggingEvents(tid, r.value + 1, newGray->lf);
			} else {
				printf("%p: run %d to failure from %ld\n", newGray, tid._tid(), thr->nrAccesses);
				i.runToFailure(tid, newGray->lf, 10000000);
			}

			grayStates.push_back(newGray);
		}
	}

	while (!grayStates.empty()) {
		futures.push_back(grayStates.front());
		grayStates.pop_front();
	}
}

Expression *
LoadExpression::refine(const MachineState<abstract_interpret_value> *ms,
		       LogReader<abstract_interpret_value> *lf,
		       LogReaderPtr ptr,
		       bool *progress,
		       const std::map<ThreadId, unsigned long> &validity,
		       EventTimestamp ev)
{
	*progress = true;
	return onlyif::get(
		logicaland::get(
			ExpressionLastStore::get(when, store, addr),
			equals::get(addr, storeAddr)),
		val);
}

Expression *
BinaryExpression::refine(const MachineState<abstract_interpret_value> *ms,
			 LogReader<abstract_interpret_value> *lf,
			 LogReaderPtr ptr,
			 bool *progress,
			 const std::map<ThreadId, unsigned long> &validity,
			 EventTimestamp ev)
{
	bool subprogress;
	Expression *_l = l;
	Expression *_r = r;
	Relevance lr = l->relevance(ev, Relevance::irrelevant, Relevance::perfect);

	subprogress = false;
	if (lr > r->relevance(ev, Relevance::irrelevant, lr)) {
		_l = l->refine(ms, lf, ptr, &subprogress, validity, ev);
		if (!subprogress)
			_r = r->refine(ms, lf, ptr, &subprogress, validity, ev);
	} else {
		_r = r->refine(ms, lf, ptr, &subprogress, validity, ev);
		if (!subprogress)
			_l = l->refine(ms, lf, ptr, &subprogress, validity, ev);
	}
	if (subprogress) {
		*progress = true;
		return semiDupe(_l, _r);
	}
	return this;
}

Expression *
UnaryExpression::refine(const MachineState<abstract_interpret_value> *ms,
			LogReader<abstract_interpret_value> *lf,
			LogReaderPtr ptr,
			bool *progress,
			const std::map<ThreadId, unsigned long> &validity,
			EventTimestamp ev)
{
	bool subprogress = false;
	Expression *l2 = l->refine(ms, lf, ptr, &subprogress, validity, ev);
	if (subprogress) {
		*progress = true;
		return semiDupe(l2);
	} else {
		return this;
	}
}

/* Takes the content of a last-store expression and compares it with a
   sample execution, building an expression which captures what's
   necessary for the last store to happen in that execution.  We do
   not look at anything past the end of the execution, though. */
class LastStoreRefiner : public EventRecorder<abstract_interpret_value> {
	EventTimestamp store;
	EventTimestamp load;
	Expression *addr;
	static VexAllocTypeWrapper<LastStoreRefiner> allocator;

	std::map<ThreadId, History *> thread_histories;
	LogReader<abstract_interpret_value> *modelExec;
	LogReaderPtr modelExecStart;
	const std::map<ThreadId, unsigned long> &validity;
	History *getHistory(EventTimestamp evt)
	{
		History *&ptr = thread_histories[evt.tid];
		if (!ptr)
			ptr = new History(ConstExpression::get(1),
					  evt,
					  NULL);
		return ptr;
	}
	void setHistory(ThreadId tid, History *hs)
	{
		thread_histories[tid] = hs;
	}
public:
	Expression *result;
	void record(Thread<abstract_interpret_value> *thr,
		    ThreadEvent<abstract_interpret_value> *evt);
	LastStoreRefiner(EventTimestamp _store,
			 EventTimestamp _load,
			 Expression *_addr,
			 Expression *_result,
			 LogReader<abstract_interpret_value> *_modelExec,
			 LogReaderPtr _modelExecStart,
			 const std::map<ThreadId, unsigned long> &_validity)
		: store(_store),
		  load(_load),
		  addr(_addr),
		  modelExec(_modelExec),
		  modelExecStart(_modelExecStart),
		  validity(_validity),
		  result(_result)
	{
	}
	static void *operator new(size_t s)
	{
		return (void *)LibVEX_Alloc_Sized(&allocator.type, s);
	}
	static void operator delete(void *x)
	{
		abort();
	}
	void visit(HeapVisitor &hv) const
	{
		hv(addr);
		hv(result);
		for (std::map<ThreadId, History *>::const_iterator it = thread_histories.begin();
		     it != thread_histories.end();
		     it++)
			hv(it->second);
		hv(modelExec);
	}
	void destruct() {}
	void finish(const MachineState<abstract_interpret_value> *ms) {
		for (std::map<ThreadId, History *>::const_iterator it = thread_histories.begin();
		     it != thread_histories.end();
		     it++)
			it->second->finish(ms->findThread(it->first)->nrEvents);
	}
	NAMED_CLASS
};
VexAllocTypeWrapper<LastStoreRefiner> LastStoreRefiner::allocator;
void
LastStoreRefiner::record(Thread<abstract_interpret_value> *thr,
			 ThreadEvent<abstract_interpret_value> *evt)
{
	if (const InstructionEvent<abstract_interpret_value> *fe =
	    dynamic_cast<const InstructionEvent<abstract_interpret_value> *>(evt)) {
		unsigned long c;
		if (!fe->rip.origin->isConstant(&c))
			this->setHistory(thr->tid,
					 this->getHistory(evt->when)->control_expression(
						 evt->when,
						 equals::get(fe->rip.origin, ConstExpression::get(fe->rip.v))));
		this->getHistory(evt->when)->footstep(fe->rip.v);
	}

	if (const StoreEvent<abstract_interpret_value> *se =
	    dynamic_cast<const StoreEvent<abstract_interpret_value> *>(evt)) {
		if (evt->when != store) {
			Expression *happensInRange =
				logicaland::get(
					ExpressionHappensBefore::get(
						store,
						evt->when),
					ExpressionHappensBefore::get(
						evt->when,
						load));
			/* If necessary, introduce a rip expression
			   which brings the relevant memory access
			   into scope. */
			if (evt->when.idx > validity.find(evt->when.tid)->second)
				happensInRange =
					ExpressionRip::get(
						evt->when.tid,
						thread_histories[evt->when.tid],
						happensInRange,
						modelExec,
						modelExecStart);
			result =
				logicaland::get(
					result,
					logicalor::get(
						logicalnot::get(
							alias::get(
								equals::get(
									se->addr.origin,
									addr))),
						logicalnot::get(happensInRange)));
		}
	}
}

class TruncateToEvent : public LogWriter<abstract_interpret_value>,
			public GarbageCollected<TruncateToEvent> {
	EventTimestamp lastEvent;
	bool finished;
public:
	MemLog<abstract_interpret_value> *work;

	TruncateToEvent(EventTimestamp _lastEvent)
		: lastEvent(_lastEvent),
		  finished(false),
		  work(MemLog<abstract_interpret_value>::emptyMemlog())
	{
	}

	void append(LogRecord<abstract_interpret_value> *lr,
		    unsigned long idx);

	void visit(HeapVisitor &hv) const { hv(work); }
	void destruct() { this->~TruncateToEvent(); }
	NAMED_CLASS
};
void
TruncateToEvent::append(LogRecord<abstract_interpret_value> *lr,
			unsigned long idx)
{
	if (finished)
		return;
	work->append(lr, idx);
	if (lr->thread() == lastEvent.tid &&
	    idx == lastEvent.idx)
		finished = true;
}
static LogReader<abstract_interpret_value> *
truncate_logfile(const MachineState<abstract_interpret_value> *ms,
		 LogReader<abstract_interpret_value> *lf,
		 LogReaderPtr ptr,
		 EventTimestamp lastEvent,
		 LogReaderPtr *outPtr)
{
	Interpreter<abstract_interpret_value> i(ms->dupeSelf());
	TruncateToEvent *tte = new TruncateToEvent(lastEvent);
	VexGcRoot tteroot((void **)&tte, "tte");
	i.replayLogfile(lf, ptr, NULL, tte);
	*outPtr = tte->work->startPtr();
	return tte->work;
}

Expression *
ExpressionLastStore::refine(const MachineState<abstract_interpret_value> *ms,
			    LogReader<abstract_interpret_value> *lf,
			    LogReaderPtr ptr,
			    bool *progress,
			    const std::map<ThreadId, unsigned long> &validity,
			    EventTimestamp ev)
{
	LastStoreRefiner *lsr =
		new LastStoreRefiner(
			store,
			load,
			vaddr,
			ExpressionHappensBefore::get(store, load),
			lf,
			ptr,
			validity);
	VexGcRoot r((void **)&lsr, "r");
	MachineState<abstract_interpret_value> *localMs = ms->dupeSelf();
	VexGcRoot r2((void **)&localMs, "r2");
	Interpreter<abstract_interpret_value> i(localMs);
	LogReaderPtr truncatedPtr;
	LogReader<abstract_interpret_value> *truncatedLog =
		truncate_logfile(ms, lf, ptr, load, &truncatedPtr);
	VexGcRoot rr((void **)&truncatedLog, "rr");
	i.replayLogfile(truncatedLog, truncatedPtr, NULL, NULL, lsr);
	lsr->finish(localMs);

	Explorer *e = new Explorer(localMs, load.tid);
	VexGcRoot eroot((void **)&e, "eroot");
	Expression *work = lsr->result;
	VexGcRoot workroot((void **)&work, "workroot");

	for (std::vector<ExplorationState *>::iterator it = e->futures.begin();
	     it != e->futures.end();
	     it++) {
		MachineState<abstract_interpret_value> *ms2 = localMs->dupeSelf();
		Interpreter<abstract_interpret_value> i2(ms2);
		LastStoreRefiner *lsr2 =
			new LastStoreRefiner(
				store,
				load,
				vaddr,
				work,
				lf,
				ptr,
				validity);
		VexGcRoot r3((void **)&lsr2, "r3");
		i2.replayLogfile((*it)->lf, (*it)->lf->startPtr(), NULL, NULL, lsr2);
		lsr2->finish(ms2);
		work = lsr2->result;
	}

	*progress = true;
	return work;
}

Expression *
ExpressionRip::refineSubCond(const MachineState<abstract_interpret_value> *ms,
			     LogReader<abstract_interpret_value> *lf,
			     LogReaderPtr ptr,
			     const std::map<ThreadId, unsigned long> &validity,
			     EventTimestamp ev)
{
	bool subCondProgress = false;
	std::map<ThreadId, unsigned long> newValidity(validity);
	newValidity[tid] = history->last_valid_idx;
	Expression *newSubCond = cond->refine(ms, model_execution, model_exec_start,
					      &subCondProgress, newValidity, ev);
	if (subCondProgress) {
		Expression *res = ExpressionRip::get(
			tid,
			history,
			newSubCond,
			model_execution,
			model_exec_start);
		considerPotentialFixes(res);
		return res;
	} else {
		return NULL;
	}
}

Expression *
ExpressionRip::refineHistory(const MachineState<abstract_interpret_value> *ms,
			     LogReader<abstract_interpret_value> *lf,
			     LogReaderPtr ptr,
			     const std::map<ThreadId, unsigned long> &validity,
			     EventTimestamp ev)
{
	std::set<History *> unrefinable;

	while (1) {
		History *hs = history;

		while (hs && unrefinable.count(hs))
			hs = hs->parent;
		if (!hs) {
			/* Cannot refine history */
			return NULL;
		}

		History *mostRelevantEntry = hs;
		Relevance mostRelevantRelevance = hs->condition->relevance(ev, Relevance::irrelevant, Relevance::perfect);
		hs = hs->parent;
		while (hs) {
			Relevance thisRelevance = hs->condition->relevance(ev, Relevance::irrelevant, Relevance::perfect);
			if (thisRelevance > mostRelevantRelevance) {
				mostRelevantRelevance = thisRelevance;
				mostRelevantEntry = hs;
			}
			hs = hs->parent;
		}

		std::map<ThreadId, unsigned long> newValidity(validity);
		newValidity[tid] = mostRelevantEntry->last_valid_idx;
		bool subCondProgress = false;
		Expression *newCond = mostRelevantEntry->condition->refine(ms, lf, ptr, &subCondProgress,
									   newValidity, ev);
		if (subCondProgress) {
			Expression *res = ExpressionRip::get(
				tid,
				history->dupeWithParentReplace(
					mostRelevantEntry,
					new History(newCond,
						    mostRelevantEntry->last_valid_idx,
						    mostRelevantEntry->when,
						    mostRelevantEntry->rips,
						    mostRelevantEntry->parent)),
				cond,
				model_execution,
				model_exec_start);
			considerPotentialFixes(res);
			return res;
		}
		unrefinable.insert(mostRelevantEntry);
	}

	return NULL;
}

/* We refine a RIP expression by just splitting the very last segment
   off of the history and turning it into a direct expression. */
Expression *
ExpressionRip::refine(const MachineState<abstract_interpret_value> *ms,
		      LogReader<abstract_interpret_value> *lf,
		      LogReaderPtr ptr,
		      bool *progress,
		      const std::map<ThreadId, unsigned long> &validity,
		      EventTimestamp ev)
{
	Expression *n;
	Relevance cr = cond->relevance(ev, Relevance::irrelevant, Relevance::perfect);
	if (cr > history->relevance(ev, Relevance::irrelevant, cr)) {
		if ((n = refineSubCond(ms, lf, ptr, validity, ev))) {
			*progress = true;
			return n;
		}
		if ((n = refineHistory(ms, lf, ptr, validity, ev))) {
			*progress = true;
			return n;
		}
	} else {
		if ((n = refineHistory(ms, lf, ptr, validity, ev))) {
			*progress = true;
			return n;
		}
		if ((n = refineSubCond(ms, lf, ptr, validity, ev))) {
			*progress = true;
			return n;
		}
	}
	return this;
}
