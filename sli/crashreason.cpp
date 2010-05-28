#include <err.h>

#include "sli.h"

#define FOOTSTEP_REGS_ONLY
#include "ppres.h"

/* A HistorySegment represents a chunk of per-thread history.  In
   theory, the only part which is really necessary, and the only part
   which is semantically important, is the condition, which is just a
   condition which is evaluated at the start of the segment and has to
   be true.

   We also store a timestamp, which is the point in the model
   execution at which the condition was evaluated.  This is used in
   the heuristic which decides which branch of an expression to refine
   first.

   We also store a log of the RIPs touched between each conditional
   expression (the ones in the vector are touched *after* the current
   condition is evaluated).  This is in theory redundant with the
   condition, because if you pass the condition then you ought to
   always follow the same RIP path, but it makes it a *lot* easier to
   see if something's gone wrong. */
class HistorySegment : public Named {
public:
	Expression *condition;
	EventTimestamp when;
	std::vector<unsigned long> rips;
private:
	static const VexAllocTypeWrapper<HistorySegment> allocator;
	HistorySegment(Expression *_condition,
		       EventTimestamp _when)
		: condition(_condition),
		  when(_when),
		  rips()
	{
	}
	HistorySegment()
		: condition(ConstExpression::get(1)),
		  when(),
		  rips()
	{
	}
	HistorySegment(std::vector<unsigned long> &_rips)
		: condition(ConstExpression::get(1)),
		  when(),
		  rips(_rips)
	{
	}
protected:
	char *mkName() const {
		char *buf = my_asprintf("%s@%d:%lx", condition->name(), when.tid._tid(), when.idx);
		for (std::vector<unsigned long>::const_iterator it = rips.begin();
		     it != rips.end();
		     it++) {
			char *b2 = my_asprintf("%s:%lx", buf, *it);
			free(buf);
			buf = b2;
		}
		return buf;
	}
public:
	static HistorySegment *get(Expression *condition,
				   EventTimestamp when)
	{
		return new (allocator.alloc()) HistorySegment(condition,
							      when);
	}
	static HistorySegment *get()
	{
		return new (allocator.alloc()) HistorySegment();
	}
	static HistorySegment *get(std::vector<unsigned long> &rips)
	{
		return new (allocator.alloc()) HistorySegment(rips);
	}
	void destruct()
	{
		this->~HistorySegment();
	}
	void visit(HeapVisitor &hv) const
	{
		hv(condition);
	}

	bool isEqual(const HistorySegment *h) const
	{
		if (when != h->when)
			return false;
		if (rips.size() != h->rips.size())
			return false;
		if (!condition->isEqual(h->condition))
			return false;
		std::vector<unsigned long>::const_iterator it1;
		std::vector<unsigned long>::const_iterator it2;
		it1 = rips.begin();
		it2 = h->rips.begin();
		while (it1 != rips.end()) {
			assert(it2 != h->rips.end());
			if (*it1 != *it2)
				return false;
		}
		return false;
	}
};
const VexAllocTypeWrapper<HistorySegment> HistorySegment::allocator;

class History : public Named {
public:
	std::vector<HistorySegment *>history;
private:
	static const VexAllocTypeWrapper<History> allocator;
	History(std::vector<HistorySegment *>::const_iterator start,
		std::vector<HistorySegment *>::const_iterator end)
		: history(start, end)
	{
	}
	History(std::vector<unsigned long> rips)
	{
		history.push_back(HistorySegment::get(rips));
	}
	History()
	{
		history.push_back(HistorySegment::get());
	}
protected:
	char *mkName() const {
		char *buf = NULL;
		for (std::vector<HistorySegment *>::const_iterator it = history.begin();
		     it != history.end();
		     it++) {
			const char *component = (*it)->name();
			if (buf) {
				char *b2 = my_asprintf("%s{%s}", buf, component);
				free(buf);
				buf = b2;
			} else {
				buf = my_asprintf("{%s}", component);
			}
		}
		if (buf)
			return buf;
		else
			return strdup("<empty history>");
	}
public:
	static History *get(std::vector<HistorySegment *>::const_iterator start,
			    std::vector<HistorySegment *>::const_iterator end)
	{
		return new (allocator.alloc()) History(start, end);
	}
	static History *get(std::vector<unsigned long> &rips)
	{
		return new (allocator.alloc()) History(rips);
	}
	static History *get()
	{
		return new (allocator.alloc()) History();
	}
	void destruct()
	{
		this->~History();
	}
	void visit(HeapVisitor &hv) const
	{
		for (std::vector<HistorySegment *>::const_iterator it = history.begin();
		     it != history.end();
		     it++)
			hv(*it);
	}
	bool isEqual(const History *h) const
	{
		if (history.size() != h->history.size())
			return false;
		std::vector<HistorySegment *>::const_iterator it1;
		std::vector<HistorySegment *>::const_iterator it2;
		it1 = history.begin();
		it2 = h->history.begin();
		while (it1 != history.end()) {
			assert(it2 != h->history.end());
			if (!(*it1)->isEqual(*it2))
				return false;
		}
		return false;
	}
	void control_expression(EventTimestamp when, Expression *e)
	{
		history.push_back(HistorySegment::get(e, when));
	}
	void footstep(unsigned long rip)
	{
		history.back()->rips.push_back(rip);
	}
	EventTimestamp timestamp() const
	{
		return history.back()->when;
	}
	void extractSubModel(
		ThreadId tid,
		const MachineState<abstract_interpret_value> *ms,
		LogReader<abstract_interpret_value> *lf,
		LogReaderPtr ptr,
		LogReader<abstract_interpret_value> **newModel,
		LogReaderPtr *newPtr,
		LogReader<abstract_interpret_value> **newModel2,
		LogReaderPtr *newPtr2);
};
const VexAllocTypeWrapper<History> History::allocator;

/* A RIP expression asserts that a particular thread will follow a
 * particular control flow path, and hence that memory operations can
 * be identified by their position in the memory operation stream.
 */
class ExpressionRip : public Expression {
public:
	ThreadId tid;
	History *history;
	Expression *cond;
	LogReader<abstract_interpret_value> *model_execution;
	LogReaderPtr model_exec_start;
private:
	static VexAllocTypeWrapper<ExpressionRip> allocator;
	ExpressionRip(ThreadId _tid, History *_history, Expression *_cond,
		      LogReader<abstract_interpret_value> *model,
		      LogReaderPtr start)
		: tid(_tid),
		  history(_history),
		  cond(_cond),
		  model_execution(model),
		  model_exec_start(start)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(rip %d:{...}:%s)", tid._tid(), cond->name());
	}
	unsigned _hash() const {
		return history->history.size() ^ tid._tid() ^ cond->hash();
	}
	bool _isEqual(const Expression *other) const {
		const ExpressionRip *oth = dynamic_cast<const ExpressionRip *>(other);
		if (oth && oth->tid == tid && cond->isEqual(oth->cond) &&
		    oth->history->isEqual(history))
			return true;
		else
			return false;
	}
public:
	static Expression *get(ThreadId tid, History *history, Expression *cond,
			       LogReader<abstract_interpret_value> *model,
			       LogReaderPtr start)
	{
		return new (allocator.alloc()) ExpressionRip(tid, history, cond,
							     model, start);
	}
	void visit(HeapVisitor &hv) const
	{
		hv(history);
		hv(cond);
		hv(model_execution);
	}
	EventTimestamp timestamp() const {
		return max<EventTimestamp>(history->timestamp(),
					    cond->timestamp());
	}
};

VexAllocTypeWrapper<ExpressionRip> ExpressionRip::allocator;

/* A bad pointer expression asserts that a particular memory location
 * is inaccessible at a particular time. */
class ExpressionBadPointer : public Expression {
	Expression *addr;
	EventTimestamp when;
	static VexAllocTypeWrapper<ExpressionBadPointer> allocator;
	ExpressionBadPointer(EventTimestamp _when, Expression *_addr)
		: addr(_addr), when(_when)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(bad ptr %d:%lx:%s)", when.tid._tid(), when.idx, addr->name());
	}
	unsigned _hash() const {
		return addr->hash() ^ when.hash();
	}
	bool _isEqual(const Expression *other) const {
		const ExpressionBadPointer *oth = dynamic_cast<const ExpressionBadPointer *>(other);
		if (oth && oth->addr->isEqual(addr) && oth->when == when)
			return true;
		else
			return false;
	}
public:
	static Expression *get(EventTimestamp _when, Expression *_addr)
	{
		return new (allocator.alloc()) ExpressionBadPointer(_when, _addr);
	}
	void visit(HeapVisitor &hv) const { hv(addr); }
	EventTimestamp timestamp() const { return when; }
};

VexAllocTypeWrapper<ExpressionBadPointer> ExpressionBadPointer::allocator;


/* Given a trace, extract a precondition which is necessary for it to
   crash in the observed way. */
class CrashReasonExtractor : public EventRecorder<abstract_interpret_value> {
	static VexAllocTypeWrapper<CrashReasonExtractor> allocator;
public:
	std::map<ThreadId, History *> thread_histories;

	SignalEvent<abstract_interpret_value> *signal;
	Thread<abstract_interpret_value> *thr;


private:
	CrashReasonExtractor()
		: thread_histories(), signal(NULL), thr(NULL)
	{
	}
public:
	static CrashReasonExtractor *get()
	{
		return new (allocator.alloc()) CrashReasonExtractor();
	}

	History *operator[](ThreadId tid)
	{
		std::map<ThreadId, History *>::iterator it = thread_histories.find(tid);
		if (it == thread_histories.end()) {
			History *r = History::get();
			thread_histories[tid] = r;
			return r;
		} else {
			return it->second;
		}
	}

	void record(Thread<abstract_interpret_value> *thr, const ThreadEvent<abstract_interpret_value> *evt);

	void destruct() { this->~CrashReasonExtractor(); }
	void visit(HeapVisitor &hv) const {
		hv(thr);
		hv(signal);
		for (std::map<ThreadId, History *>::const_iterator it = thread_histories.begin();
		     it != thread_histories.end();
		     it++)
			hv(it->second);
	}
};
VexAllocTypeWrapper<CrashReasonExtractor> CrashReasonExtractor::allocator;
void CrashReasonExtractor::record(Thread<abstract_interpret_value> *_thr, const ThreadEvent<abstract_interpret_value> *evt)
{
	if (const InstructionEvent<abstract_interpret_value> *fe =
	    dynamic_cast<const InstructionEvent<abstract_interpret_value> *>(evt)) {
		unsigned long c;
		if (!fe->rip.origin->isConstant(&c))
			(*this)[_thr->tid]->control_expression(
				evt->when,
				equals::get(fe->rip.origin, ConstExpression::get(fe->rip.v)));
		(*this)[_thr->tid]->footstep(fe->rip.v);
	}

	if (const SignalEvent<abstract_interpret_value> *es =
	    dynamic_cast<const SignalEvent<abstract_interpret_value> *>(evt)) {
		thr = _thr;
		signal = (SignalEvent<abstract_interpret_value> *)es->dupe();
	}
}
static Expression *getCrashReason(MachineState<abstract_interpret_value> *ms,
				  LogReader<abstract_interpret_value> *script,
				  LogReaderPtr ptr)
{
	Interpreter<abstract_interpret_value> i(ms);
	CrashReasonExtractor *extr = CrashReasonExtractor::get();
	VexGcRoot root1((void **)&extr, "root1");

	i.replayLogfile(script, ptr, NULL, NULL, extr);

	if (!ms->crashed())
		return NULL;

	/* For now, we assume that the only reason to crash is
	   dereferencing a bad pointer, which has only two cases:

	   1) Chasing bad data.
	   2) Chasing bad instructions.

	   We further assume that a crash is due to a bad instruction
	   if the faulting address matches the RIP, and bad data
	   otherwise. */
	assert(extr->signal);
	assert(extr->thr->crashed);
	if (force(extr->thr->regs.rip() == extr->signal->virtaddr))
		return ExpressionRip::get(extr->thr->tid, (*extr)[extr->thr->tid],
					  equals::get(extr->thr->regs.rip().origin,
						      ConstExpression::get(extr->thr->regs.rip().v)),
					  script,
					  ptr);
	else
		return ExpressionRip::get(extr->thr->tid, (*extr)[extr->thr->tid],
					  ExpressionBadPointer::get(extr->signal->when, extr->signal->virtaddr.origin),
					  script,
					  ptr);
}

static Expression *refine(Expression *expr,
			  const MachineState<abstract_interpret_value> *ms,
			  LogReader<abstract_interpret_value> *lf,
			  LogReaderPtr ptr,
			  bool *progress);

/* We refine a RIP expression by just splitting the very last segment
   off of the history and turning it into a direct expression. */
static Expression *refine(ExpressionRip *er,
			  const MachineState<abstract_interpret_value> *ms,
			  LogReader<abstract_interpret_value> *lf,
			  LogReaderPtr ptr,
			  bool *progress)
{
	printf("Refine %s\n", er->name());

	/* Try to refine the subcondition first, since that's usually
	 * cheaper. */
	Expression *newSubCond;
	bool subCondProgress = false;
	newSubCond = refine(er->cond, ms, lf, ptr, &subCondProgress);
	if (subCondProgress) {
		/* Yay. */
		*progress = true;
		return ExpressionRip::get(
			er->tid,
			er->history,
			newSubCond,
			er->model_execution,
			er->model_exec_start);
	}

	/* Okay, done as much as we can here.  Go back to previous
	   conditional branch. */

	if (er->history->history.size() == 1) {
		/* Okay, there were no previous conditional branches.
		   We're doomed. */
		return er;
	}

	std::vector<HistorySegment *>::const_iterator start =
		er->history->history.begin();
	std::vector<HistorySegment *>::const_iterator end =
		er->history->history.end();
	end--;

	History *newHist = History::get(start, end);
	LogReaderPtr newPtr;
	LogReaderPtr newPtr2;
	LogReader<abstract_interpret_value> *newModel;
	LogReader<abstract_interpret_value> *newModel2;

	newHist->extractSubModel(er->tid, ms, lf, ptr, &newModel, &newPtr,
				 &newModel2, &newPtr2);
	*progress = true;

	return ExpressionRip::get(
		er->tid,
		newHist,
		logicaland::get((*end)->condition,
				ExpressionRip::get(er->tid,
						   History::get((*end)->rips),
						   er->cond,
						   newModel2,
						   newPtr2)),
		newModel,
		newPtr);
}

Expression *refine(Expression *expr,
		   const MachineState<abstract_interpret_value> *ms,
		   LogReader<abstract_interpret_value> *lf,
		   LogReaderPtr ptr,
		   bool *progress)
{
	if (ExpressionRip *er = dynamic_cast<ExpressionRip *>(expr))
		return refine(er, ms, lf, ptr, progress);
	else {
		printf("Cannot refine %s\n", expr->name());
		return expr;
	}
}

class HistoryLogTruncater : public LogWriter<abstract_interpret_value> {
	History *hist;
	std::vector<HistorySegment *>::iterator current_history_segment;
	unsigned current_segment_index;
	ThreadId desired_thread;
	static const VexAllocTypeWrapper<HistoryLogTruncater> allocator;
public:
	static void *operator new(size_t s)
	{
		return (void *)LibVEX_Alloc_Sized(&allocator.type, s);
	}
	MemLog<abstract_interpret_value> *model1;
	MemLog<abstract_interpret_value> *model2;
	bool finishedFirstPhase;
	void append(const LogRecord<abstract_interpret_value> &lr);
	HistoryLogTruncater(ThreadId tid, History *_hist)
		: hist(_hist),
		  current_history_segment(hist->history.begin()),
		  current_segment_index(0),
		  desired_thread(tid),
		  model1(MemLog<abstract_interpret_value>::emptyMemlog()),
		  model2(MemLog<abstract_interpret_value>::emptyMemlog()),
		  finishedFirstPhase(false)
	{
	}
	void destruct() { this->~HistoryLogTruncater(); }
	void visit(HeapVisitor &hv) const { hv(hist); hv(model1); hv(model2); }
};
const VexAllocTypeWrapper<HistoryLogTruncater> HistoryLogTruncater::allocator;

void HistoryLogTruncater::append(const LogRecord<abstract_interpret_value> &lr)
{
	while (!finishedFirstPhase &&
	       current_segment_index ==
	       (*current_history_segment)->rips.size()) {
		current_segment_index = 0;
		current_history_segment++;
		if (current_history_segment == hist->history.end())
			finishedFirstPhase = true;
	}

	if (finishedFirstPhase) {
		model2->append(lr);
		return;
	}

	if (lr.thread() == desired_thread) {
		const LogRecordFootstep<abstract_interpret_value> *lrf =
			dynamic_cast<const LogRecordFootstep<abstract_interpret_value> *>(&lr);
		if (lrf) {
			assert(lrf->rip.v ==
			       (*current_history_segment)->rips[current_segment_index]);
			current_segment_index++;
		}
	}

	return model1->append(lr);
}
void History::extractSubModel(
	ThreadId tid,
	const MachineState<abstract_interpret_value> *ms,
	LogReader<abstract_interpret_value> *lf,
	LogReaderPtr ptr,
	LogReader<abstract_interpret_value> **newModel,
	LogReaderPtr *newPtr,
	LogReader<abstract_interpret_value> **newModel2,
	LogReaderPtr *newPtr2)
{
	HistoryLogTruncater *work = new HistoryLogTruncater(tid, this);
	VexGcRoot root((void **)&work, "extractSubModel");

	Interpreter<abstract_interpret_value> i(ms->dupeSelf());
	i.replayLogfile(lf, ptr, NULL, work);

	*newModel = work->model1;
	*newPtr = work->model1->startPtr();
	*newModel2 = work->model2;
	*newPtr2 = work->model2->startPtr();
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
	VexGcRoot logroot((void **)&lf, "logroot");

	MachineState<unsigned long> *concrete = MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr);
	MachineState<abstract_interpret_value> *abstract = concrete->abstract<abstract_interpret_value>();
	VexGcRoot keeper((void **)&abstract, "keeper");

	LogReader<abstract_interpret_value> *al = lf->abstract<abstract_interpret_value>();
	VexGcRoot al_keeper((void **)&al, "al_keeper");

	Expression *cr = getCrashReason(abstract->dupeSelf(), al, ptr);
	printf("%s\n", cr->name());
	VexGcRoot crkeeper((void **)&cr, "crkeeper");

	bool progress;

	do {
		progress = false;
		printf("Crash reason %s\n", cr->name());
		cr = refine(cr, abstract, al, ptr, &progress);
	} while (progress);
	printf("Crash reason %s\n", cr->name());

	return 0;
}
