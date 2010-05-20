#include <err.h>

#include "sli.h"

class CrashReason : public Named {
protected:
	CrashReason() {}
public:
	virtual CrashReason *refine(MachineState<abstract_interpret_value> *, LogReader<abstract_interpret_value> *, LogReaderPtr)
	{
		return this;
	}
	virtual void visit(HeapVisitor &hv) const {}
};

class CrashReasonAnd : public CrashReason {
	CrashReason *left;
	CrashReason *right;
	CrashReasonAnd(CrashReason *_left, CrashReason *_right)
		: left(_left),
		  right(_right)
	{
	}
	static VexAllocTypeWrapper<CrashReasonAnd> allocator;
protected:
	char *mkName(void) const {
		return my_asprintf("(%s && %s)", left->name(), right->name());
	}
public:
	static CrashReason *get(CrashReason *l, CrashReason *r)
	{
		return new (allocator.alloc()) CrashReasonAnd(l, r);
	}
	void visit(HeapVisitor &hv) const { hv(left); hv(right); }
};

VexAllocTypeWrapper<CrashReasonAnd> CrashReasonAnd::allocator;

class CrashReasonControl : public CrashReason {
	abstract_interpret_value badRip;
	ThreadId tid;
	static VexAllocTypeWrapper<CrashReasonControl> allocator;
	CrashReasonControl(ThreadId _tid, abstract_interpret_value _badRip)
		: badRip(_badRip),
		  tid(_tid)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(rip %d:%s)", tid._tid(), badRip.origin->name());
	}
public:
	static CrashReason *get(ThreadId _tid, abstract_interpret_value _rip)
	{
		return new (allocator.alloc()) CrashReasonControl(_tid, _rip);
	}
	void visit(HeapVisitor &hv) const { visit_aiv(badRip, hv); }
};

VexAllocTypeWrapper<CrashReasonControl> CrashReasonControl::allocator;

class CrashReasonBadPointer : public CrashReason {
	abstract_interpret_value bad;
	ThreadId tid;
	static VexAllocTypeWrapper<CrashReasonBadPointer> allocator;
	CrashReasonBadPointer(ThreadId _tid, abstract_interpret_value _bad)
		: bad(_bad),
		  tid(_tid)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(ptr %d:%lx)", tid._tid(), bad.v);
	}
public:
	static CrashReason *get(ThreadId _tid, abstract_interpret_value _rip)
	{
		return new (allocator.alloc()) CrashReasonBadPointer(_tid, _rip);
	}
	void visit(HeapVisitor &hv) const { visit_aiv(bad, hv); }
};

VexAllocTypeWrapper<CrashReasonBadPointer> CrashReasonBadPointer::allocator;

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

static CrashReason *getCrashReason(MachineState<abstract_interpret_value> *ms,
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
		return CrashReasonControl::get(extr.thr->tid, extr.signal->virtaddr);
	else
		return CrashReasonAnd::get(CrashReasonControl::get(extr.thr->tid, extr.thr->regs.rip()),
					   CrashReasonBadPointer::get(extr.thr->tid, extr.signal->virtaddr));
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

	CrashReason *cr = getCrashReason(abstract->dupeSelf(), al, ptr);
	printf("Replayed symbolically, crash reason %s\n", cr->name());

	return 0;
}
