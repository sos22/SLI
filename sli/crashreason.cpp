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
	ReplayTimestamp when;
	std::vector<unsigned long> rips;
private:
	static const VexAllocTypeWrapper<HistorySegment> allocator;
	HistorySegment(Expression *_condition,
		       ReplayTimestamp _when)
		: condition(_condition),
		  when(_when)
	{
	}
	HistorySegment()
		: condition(ConstExpression::get(1))
	{
	}
protected:
	char *mkName() const {
		char *buf = my_asprintf("%s@%lx", condition->name(), when.val);
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
				   ReplayTimestamp when)
	{
		return new (allocator.alloc()) HistorySegment(condition,
							      when);
	}
	static HistorySegment *get()
	{
		return new (allocator.alloc()) HistorySegment();
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
	void control_expression(ReplayTimestamp when, Expression *e)
	{
		history.push_back(HistorySegment::get(e, when));
	}
	void footstep(unsigned long rip)
	{
		history.back()->rips.push_back(rip);
	}
	ReplayTimestamp timestamp() const
	{
		return history.back()->when;
	}
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
private:
	static VexAllocTypeWrapper<ExpressionRip> allocator;
	ExpressionRip(ThreadId _tid, History *_history)
		: tid(_tid),
		  history(_history)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(rip %d:%s)", tid._tid(), history->name());
	}
	unsigned _hash() const {
		return history->history.size() ^ tid._tid();
	}
	bool _isEqual(const Expression *other) const {
		const ExpressionRip *oth = dynamic_cast<const ExpressionRip *>(other);
		if (oth && oth->history->isEqual(history) &&
		    oth->tid == tid)
			return true;
		else
			return false;
	}
public:
	static Expression *get(ThreadId tid, History *history)
	{
		return new (allocator.alloc()) ExpressionRip(tid, history);
	}
	void visit(HeapVisitor &hv) const
	{
		hv(history);
	}
	ReplayTimestamp timestamp() const { return history->timestamp(); }
};

VexAllocTypeWrapper<ExpressionRip> ExpressionRip::allocator;

/* A bad pointer expression asserts that a particular memory location
 * is inaccessible at a particular time. */
class ExpressionBadPointer : public Expression {
	Expression *addr;
	ReplayTimestamp when;
	static VexAllocTypeWrapper<ExpressionBadPointer> allocator;
	ExpressionBadPointer(ReplayTimestamp _when, Expression *_addr)
		: addr(_addr), when(_when)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(bad ptr %lx:%s)", when.val, addr->name());
	}
	unsigned _hash() const {
		return addr->hash() ^ when.val;
	}
	bool _isEqual(const Expression *other) const {
		const ExpressionBadPointer *oth = dynamic_cast<const ExpressionBadPointer *>(other);
		if (oth && oth->addr->isEqual(addr) && oth->when == when)
			return true;
		else
			return false;
	}
public:
	static Expression *get(ReplayTimestamp _when, Expression *_addr)
	{
		return new (allocator.alloc()) ExpressionBadPointer(_when, _addr);
	}
	void visit(HeapVisitor &hv) const { hv(addr); }
	ReplayTimestamp timestamp() const { return when; }
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
	VexGcRoot((void **)&extr);

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
		return ExpressionRip::get(extr->thr->tid, (*extr)[extr->thr->tid]);
	else
		return logicaland::get(ExpressionRip::get(extr->thr->tid, (*extr)[extr->thr->tid]),
				       ExpressionBadPointer::get(extr->signal->when, extr->signal->virtaddr.origin));
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

	/* Extract the desired condition. */
	Expression *condition = (*end)->condition;

	/* Build the new RIP expression */
	History *newHistory = History::get(start, end);
	Expression *newRip = ExpressionRip::get(er->tid, newHistory);

	*progress = true;

	return logicaland::get(newRip, condition);
}

static Expression *refine(logicaland *er,
			  const MachineState<abstract_interpret_value> *ms,
			  LogReader<abstract_interpret_value> *lf,
			  LogReaderPtr ptr,
			  bool *progress)
{
	/* Prefer to refine the later argument first, if possible. */
	if (er->l->timestamp() > er->r->timestamp()) {
		bool lprogress = false;
		Expression *refined_l = refine(er->l, ms, lf, ptr,
					       &lprogress);
		if (lprogress) {
			*progress = true;
			return logicaland::get(refined_l, er->r);
		}
	}

	/* Either r is after l or l can't make progress.  Either way,
	   we're going to be refining r now. */
	bool rprogress = false;
	Expression *refined_r = refine(er->r, ms, lf, ptr, &rprogress);
	if (rprogress) {
		*progress = true;
		return logicaland::get(er->l, refined_r);
	} else {
		/* Completely failed to perform and kind of
		   refinement.  Oh well. */
		return er;
	}
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

int
main(int argc, char *argv[])
{
	init_sli();

	LogFile *lf;
	LogReaderPtr ptr;

	lf = LogFile::open(argv[1], &ptr);
	if (!lf)
		err(1, "opening %s", argv[1]);

	MachineState<unsigned long> *concrete = MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr);
	MachineState<abstract_interpret_value> *abstract = concrete->abstract<abstract_interpret_value>();
	VexGcRoot keeper((void **)&abstract);

	LogReader<abstract_interpret_value> *al = lf->abstract<abstract_interpret_value>();

	Expression *cr = getCrashReason(abstract->dupeSelf(), al, ptr);
	printf("%s\n", cr->name());
#if 0
	VexGcRoot crkeeper((void **)&cr);

	bool progress;

	do {
		progress = false;
		printf("Crash reason %s\n", cr->name());
		cr = refine(cr, abstract, al, ptr, &progress);
	} while (progress);
	printf("Crash reason %s\n", cr->name());
#endif
	return 0;
}
