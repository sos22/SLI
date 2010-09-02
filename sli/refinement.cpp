#include <deque>
#include <set>

#include "sli.h"

class ExplorationState : public GarbageCollected<ExplorationState> {
public:
	MachineState<abstract_interpret_value> *ms;
	MemLog<abstract_interpret_value> *lf;

	void visit(HeapVisitor &hv) { hv(lf); hv(ms); }
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

	static Explorer *get(const MachineState<abstract_interpret_value> *ms,
			     ThreadId ignoredTid, GarbageCollectionToken t);
	void visit(HeapVisitor &hv)
	{
		visit_container(futures, hv);
		visit_container(grayStates, hv);
	}
	void destruct() {}
	NAMED_CLASS
};

Explorer *
Explorer::get(const MachineState<abstract_interpret_value> *ms,
	      ThreadId ignoredThread, GarbageCollectionToken t)
{
	VexPtr<Explorer> work(new Explorer());

	work->grayStates.push_back(new ExplorationState(ms->dupeSelf(),
							MemLog<abstract_interpret_value>::emptyMemlog()));

	while (work->grayStates.size() != 0 &&
	       (work->grayStates.size() + work->futures.size()) < 10) {
		printf("%zd futures, %zd grays\n", work->futures.size(),
		       work->grayStates.size());
		VexPtr<ExplorationState> s(work->grayStates.front());
		work->grayStates.pop_front();

		printf("Consider %p\n", s.get());

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
			work->futures.push_back(s);
			printf("No progress possible.\n");
			continue;
		}

		VexPtr<MachineState<abstract_interpret_value> > ms(s->ms);
		VexPtr<MemTracePool<abstract_interpret_value> > thread_traces(
			MemTracePool<abstract_interpret_value>::get(ms, ignoredThread, t));
		VexPtr<gc_map<ThreadId, Maybe<unsigned> > > first_racing_access
			(thread_traces->firstRacingAccessMap());

		/* If there are no races then we can just run one
		   thread after another, and we don't need to do
		   anything else.  We can even get away with reusing
		   the old MachineState. */
		/* This includes the case where only one thread can
		   make progress at all. */
		bool noRaces = true;
		for (gc_map<ThreadId, Maybe<unsigned> >::iterator it = first_racing_access->begin();
		     it != first_racing_access->end();
		     it++) {
			if (it.key() == ignoredThread)
				continue;
			if (it.value().full)
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
				VexPtr<LogWriter<abstract_interpret_value> > lf(s->lf);
				i.runToFailure(thr->tid, lf, t, 10000000);
			}
		        work->futures.push_back(s);
			continue;
		}

		/* Have some actual races -> have to do full
		 * repertoire. */
		for (gc_map<ThreadId, Maybe<unsigned> >::iterator it = first_racing_access->begin();
		     it != first_racing_access->end();
		     it++) {
			ThreadId tid = it.key();
			Maybe<unsigned> r = it.value();
			Thread<abstract_interpret_value> *thr = s->ms->findThread(tid);
			if (thr->tid == ignoredThread)
				continue;
			if (thr->cannot_make_progress)
				continue;
			ExplorationState *newGray = s->dupeSelf();
			VexGcRoot grayKeeper((void **)&newGray, "newGray");
			Interpreter<abstract_interpret_value> i(newGray->ms);
			VexPtr<LogWriter<abstract_interpret_value> > lf(newGray->lf);
			if (r.full) {
				printf("%p: run %d to %ld\n", newGray, tid._tid(), r.value + thr->nrAccesses);
				i.runToAccessLoggingEvents(tid, r.value + 1, t, lf);
			} else {
				printf("%p: run %d to failure from %ld\n", newGray, tid._tid(), thr->nrAccesses);
				i.runToFailure(tid, lf, t, 10000000);
			}

			work->grayStates.push_back(newGray);
		}
	}

	while (!work->grayStates.empty()) {
		work->futures.push_back(work->grayStates.front());
		work->grayStates.pop_front();
	}

        return work;
}

Expression *
LoadExpression::refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
		       VexPtr<LogReader<abstract_interpret_value> > &lf,
		       LogReaderPtr ptr,
		       bool *progress,
		       VexPtr<gc_map<ThreadId, unsigned long> >&validity,
		       EventTimestamp ev,
		       GarbageCollectionToken)
{
	*progress = true;
	return onlyif::get(
		logicaland::get(
			ExpressionLastStore::get(when, store, addr),
			equals::get(addr, storeAddr)),
		val);
}

Expression *
BinaryExpression::refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
			 VexPtr<LogReader<abstract_interpret_value> > &lf,
			 LogReaderPtr ptr,
			 bool *progress,
			 VexPtr<gc_map<ThreadId, unsigned long> >&validity,
			 EventTimestamp ev,
			 GarbageCollectionToken t)
{
	bool subprogress;
	VexPtr<BinaryExpression> ths(this);
	VexPtr<Expression> _l(l);
	VexPtr<Expression> _r(r);
	Relevance lr = l->relevance(ev, Relevance::irrelevant, Relevance::perfect);

	subprogress = false;
	if (lr > r->relevance(ev, Relevance::irrelevant, lr)) {
		_l = _l->refine(ms, lf, ptr, &subprogress, validity, ev, t);
		if (!subprogress)
			_r = _r->refine(ms, lf, ptr, &subprogress, validity, ev, t);
	} else {
		_r = _r->refine(ms, lf, ptr, &subprogress, validity, ev, t);
		if (!subprogress)
			_l = _l->refine(ms, lf, ptr, &subprogress, validity, ev, t);
	}
	if (subprogress) {
		*progress = true;
		return ths->semiDupe(_l, _r);
	}
	return ths;
}

Expression *
UnaryExpression::refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
			VexPtr<LogReader<abstract_interpret_value> > &lf,
			LogReaderPtr ptr,
			bool *progress,
			VexPtr<gc_map<ThreadId, unsigned long> >&validity,
			EventTimestamp ev,
			GarbageCollectionToken t)
{
	bool subprogress = false;
	VexPtr<UnaryExpression> ths(this);
	Expression *l2 = l->refine(ms, lf, ptr, &subprogress, validity, ev, t);
	if (subprogress) {
		*progress = true;
		return ths->semiDupe(l2);
	} else {
		return ths;
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

	static void visitHistoryPointer(History *&h, HeapVisitor &hv)
	{
		hv(h);
	}

	typedef gc_map<ThreadId, History *, __default_hash_function<ThreadId>, __default_eq_function<ThreadId>,
		       visitHistoryPointer> thread_histories_t;
	thread_histories_t *thread_histories;
	LogReader<abstract_interpret_value> *modelExec;
	LogReaderPtr modelExecStart;
	gc_map<ThreadId, unsigned long> *validity;
	History *getHistory(EventTimestamp evt)
	{
		History *&ptr = (*thread_histories)[evt.tid];
		if (!ptr)
			ptr = new History(ConstExpression::get(1),
					  evt,
					  NULL);
		return ptr;
	}
	void setHistory(ThreadId tid, History *hs)
	{
		(*thread_histories)[tid] = hs;
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
			 gc_map<ThreadId, unsigned long> *_validity)
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
	void visit(HeapVisitor &hv)
	{
		hv(addr);
		hv(result);
		hv(thread_histories);
		hv(modelExec);
		hv(validity);
	}
	void destruct() {}
	void finish(const MachineState<abstract_interpret_value> *ms) {
		for (thread_histories_t::iterator it = thread_histories->begin();
		     it != thread_histories->end();
		     it++)
			it.value()->finish(ms->findThread(it.key())->nrEvents);
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
			if (evt->when.idx > (*validity)[evt->when.tid])
				happensInRange =
					ExpressionRip::get(
						evt->when.tid,
						(*thread_histories)[evt->when.tid],
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

	void visit(HeapVisitor &hv) { hv(work); }
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
truncate_logfile(VexPtr<MachineState<abstract_interpret_value> > &ms,
		 VexPtr<LogReader<abstract_interpret_value> > &lf,
		 LogReaderPtr ptr,
		 EventTimestamp lastEvent,
		 LogReaderPtr *outPtr,
		 GarbageCollectionToken t)
{
	Interpreter<abstract_interpret_value> i(ms->dupeSelf());
	VexPtr<TruncateToEvent> tte(new TruncateToEvent(lastEvent));
	VexPtr<LogWriter<abstract_interpret_value> > tte2(tte.get());
	i.replayLogfile(lf, ptr, t, NULL, tte2);
	*outPtr = tte->work->startPtr();
	return tte->work;
}

Expression *
ExpressionLastStore::refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
			    VexPtr<LogReader<abstract_interpret_value> > &lf,
			    LogReaderPtr ptr,
			    bool *progress,
			    VexPtr<gc_map<ThreadId, unsigned long> > &validity,
			    EventTimestamp ev,
			    GarbageCollectionToken t)
{
	VexPtr<LastStoreRefiner> lsr(
		new LastStoreRefiner(
			store,
			load,
			vaddr,
			ExpressionHappensBefore::get(store, load),
			lf.get(),
			ptr,
			validity));
	VexPtr<MachineState<abstract_interpret_value> > localMs(ms->dupeSelf());
	Interpreter<abstract_interpret_value> i(localMs);
	LogReaderPtr truncatedPtr;
	VexPtr<LogReader<abstract_interpret_value> > truncatedLog(
		truncate_logfile(ms, lf, ptr, load, &truncatedPtr, t));
	VexPtr<EventRecorder<abstract_interpret_value> > lsr2(lsr.get());
	VexPtr<LogWriter<abstract_interpret_value> > dummyWriter(NULL);
	i.replayLogfile(truncatedLog, truncatedPtr, t, NULL, dummyWriter, lsr2);
	lsr->finish(localMs);

	VexPtr<Explorer> e(Explorer::get(localMs, load.tid, t));
	VexPtr<Expression> work(lsr->result);

	for (std::vector<ExplorationState *>::iterator it = e->futures.begin();
	     it != e->futures.end();
	     it++) {
		MachineState<abstract_interpret_value> *ms2 = localMs->dupeSelf();
		Interpreter<abstract_interpret_value> i2(ms2);
		VexPtr<LastStoreRefiner> lsr2(
			new LastStoreRefiner(
				store,
				load,
				vaddr,
				work,
				lf,
				ptr,
				validity));
		VexPtr<EventRecorder<abstract_interpret_value> > lsr3;
		VexPtr<LogReader<abstract_interpret_value> > lf2((*it)->lf);
		i2.replayLogfile(lf2, (*it)->lf->startPtr(), t, NULL, dummyWriter, lsr3);
		lsr2->finish(ms2);
		work = lsr2->result;
	}

	*progress = true;
	return work;
}

Expression *
ExpressionRip::refineSubCond(VexPtr<ExpressionRip> &ths,
			     VexPtr<MachineState<abstract_interpret_value> > &ms,
			     VexPtr<LogReader<abstract_interpret_value> > &lf,
			     LogReaderPtr ptr,
			     VexPtr<gc_map<ThreadId, unsigned long> > &validity,
			     EventTimestamp ev,
			     GarbageCollectionToken t)
{
	bool subCondProgress = false;
	VexPtr<gc_map<ThreadId, unsigned long> > newValidity
		(new gc_map<ThreadId, unsigned long>(*validity.get()));
	(*newValidity)[ths->tid] = ths->history->last_valid_idx;
	VexPtr<LogReader<abstract_interpret_value> > me(ths->model_execution);
	Expression *newSubCond = ths->cond->refine(ms, me, ths->model_exec_start,
						   &subCondProgress, newValidity, ev, t);
	if (subCondProgress) {
		Expression *res = ExpressionRip::get(
			ths->tid,
			ths->history,
			newSubCond,
			ths->model_execution,
			ths->model_exec_start);
		considerPotentialFixes(res);
		return res;
	} else {
		return NULL;
	}
}

Expression *
ExpressionRip::refineHistory(VexPtr<ExpressionRip> &ths,
			     VexPtr<MachineState<abstract_interpret_value> > &ms,
			     VexPtr<LogReader<abstract_interpret_value> > &lf,
			     LogReaderPtr ptr,
			     VexPtr<gc_map<ThreadId, unsigned long> > &validity,
			     EventTimestamp ev,
			     GarbageCollectionToken t)
{
	std::set<History *> unrefinable;

	while (1) {
		History *hs = ths->history;

		while (hs && unrefinable.count(hs))
			hs = hs->parent;
		if (!hs) {
			/* Cannot refine history */
			return NULL;
		}

		VexPtr<History> mostRelevantEntry(hs);
		Relevance mostRelevantRelevance = hs->condition->relevance(ev, Relevance::irrelevant, Relevance::perfect);
		hs = hs->parent;
		while (hs) {
			while (hs && unrefinable.count(hs))
				hs = hs->parent;
			if (!hs)
				break;
			Relevance thisRelevance = hs->condition->relevance(ev, Relevance::irrelevant, Relevance::perfect);
			if (thisRelevance > mostRelevantRelevance) {
				mostRelevantRelevance = thisRelevance;
				mostRelevantEntry = hs;
			}
			hs = hs->parent;
		}

		VexPtr<gc_map<ThreadId, unsigned long> > newValidity(new gc_map<ThreadId, unsigned long>(*validity.get()));
		(*newValidity)[ths->tid] = mostRelevantEntry->last_valid_idx;
		bool subCondProgress = false;
		Expression *newCond = mostRelevantEntry->condition->refine(ms, lf, ptr, &subCondProgress,
									   newValidity, ev, t);
		if (subCondProgress) {
			Expression *res = ExpressionRip::get(
				ths->tid,
				ths->history->dupeWithParentReplace(
					mostRelevantEntry,
					new History(newCond,
						    mostRelevantEntry->last_valid_idx,
						    mostRelevantEntry->when,
						    mostRelevantEntry->rips,
						    mostRelevantEntry->parent)),
				ths->cond,
				ths->model_execution,
				ths->model_exec_start);
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
ExpressionRip::refine(VexPtr<MachineState<abstract_interpret_value> > &ms,
		      VexPtr<LogReader<abstract_interpret_value> > &lf,
		      LogReaderPtr ptr,
		      bool *progress,
		      VexPtr<gc_map<ThreadId, unsigned long> > &validity,
		      EventTimestamp ev,
		      GarbageCollectionToken t)
{
	Expression *n;
	Relevance cr = cond->relevance(ev, Relevance::irrelevant, Relevance::perfect);
	VexPtr<ExpressionRip> ths(this);
	if (cr > history->relevance(ev, Relevance::irrelevant, cr)) {
		if ((n = refineSubCond(ths, ms, lf, ptr, validity, ev, t))) {
			*progress = true;
			return n;
		}
		if ((n = refineHistory(ths, ms, lf, ptr, validity, ev, t))) {
			*progress = true;
			return n;
		}
	} else {
		if ((n = refineHistory(ths, ms, lf, ptr, validity, ev, t))) {
			*progress = true;
			return n;
		}
		if ((n = refineSubCond(ths, ms, lf, ptr, validity, ev, t))) {
			*progress = true;
			return n;
		}
	}
	return this;
}
