#include <err.h>

#include "sli.h"

/* A RIP expression is an assertion that a particular thread is
   executing a particular instruction at a particular time. */
class ExpressionRip : public Expression {
	Expression *rip;
	ThreadId tid;
	ReplayTimestamp when;
	static VexAllocTypeWrapper<ExpressionRip> allocator;
	ExpressionRip(Expression *_rip, ThreadId _tid, ReplayTimestamp _when) :
		rip(_rip),
		tid(_tid),
		when(_when)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(bad rip %d:%lx:%s)",
				   tid._tid(),
				   when.val,
				   rip->name());
	}
public:
	static Expression *get(ThreadId tid, ReplayTimestamp when,
			       Expression *rip)
	{
		return new (allocator.alloc()) ExpressionRip(rip, tid, when);
	}
	void visit(HeapVisitor &hv) const
	{
		hv(rip);
	}
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
public:
	static Expression *get(ReplayTimestamp _when, Expression *_addr)
	{
		return new (allocator.alloc()) ExpressionBadPointer(_when, _addr);
	}
	void visit(HeapVisitor &hv) const { hv(addr); }
};

VexAllocTypeWrapper<ExpressionBadPointer> ExpressionBadPointer::allocator;


/* Given a trace, extract a precondition which is necessary for it to
   crash in the observed way. */
class CrashReasonExtractor : public EventRecorder<abstract_interpret_value> {
public:
	SignalEvent<abstract_interpret_value> *signal;
	Thread<abstract_interpret_value> *thr;

	VexGcRoot sroot;
	void record(Thread<abstract_interpret_value> *thr, const ThreadEvent<abstract_interpret_value> *evt);

	CrashReasonExtractor() : signal(NULL),sroot((void **)&signal) {}
};
void CrashReasonExtractor::record(Thread<abstract_interpret_value> *_thr, const ThreadEvent<abstract_interpret_value> *evt)
{
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
	CrashReasonExtractor extr;

	i.replayLogfile(script, ptr, NULL, NULL, &extr);

	if (!ms->crashed())
		return NULL;

	/* For now, we assume that the only reason to crash is
	   dereferencing a bad pointer, which has only two cases:

	   1) Chasing bad data.
	   2) Chasing bad instructions.

	   We further assume that a crash is due to a bad instruction
	   if the faulting address matches the RIP, and bad data
	   otherwise. */
	assert(extr.signal);
	assert(extr.thr->crashed);
	if (force(extr.thr->regs.rip() == extr.signal->virtaddr))
		return ExpressionRip::get(extr.thr->tid, extr.signal->when, extr.thr->regs.rip().origin);
	else
		return logicaland::get(ExpressionRip::get(extr.thr->tid, extr.signal->when, extr.thr->regs.rip().origin),
				       ExpressionBadPointer::get(extr.signal->when, extr.signal->virtaddr.origin));
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
	VexGcRoot crkeeper((void **)&cr);

	printf("Crash reason %s\n", cr->name());

	return 0;
}
