#include <err.h>

#include "sli.h"

class CrashReason : public Named {
public:
	virtual CrashReason *refine(MachineState<abstract_interpret_value> *, LogReader<abstract_interpret_value> *, LogReaderPtr)
	{
		return this;
	}
};

class CrashReasonAnd : public CrashReason {
	CrashReason *left;
	CrashReason *right;
protected:
	char *mkName(void) const {
		return my_asprintf("(%s && %s)", left->name(), right->name());
	}
public:
	CrashReasonAnd(CrashReason *_left, CrashReason *_right)
		: left(_left),
		  right(_right)
	{
	}
};

class CrashReasonControl : public CrashReason {
	abstract_interpret_value badRip;
	ThreadId tid;
protected:
	char *mkName(void) const {
		return my_asprintf("(rip %d:%s)", tid._tid(), badRip.origin->name());
	}
public:
	CrashReasonControl(ThreadId _tid, abstract_interpret_value _badRip)
		: badRip(_badRip),
		  tid(_tid)
	{
	}
};

class CrashReasonBadPointer : public CrashReason {
	abstract_interpret_value bad;
	ThreadId tid;
protected:
	char *mkName(void) const {
		return my_asprintf("(ptr %d:%lx)", tid._tid(), bad.v);
	}
public:
	CrashReasonBadPointer(ThreadId _tid, abstract_interpret_value _bad)
		: bad(_bad),
		  tid(_tid)
	{
	}
};

class CrashReasonExtractor : public EventRecorder<abstract_interpret_value> {
public:
	SignalEvent<abstract_interpret_value> *signal;
	Thread<abstract_interpret_value> *thr;

	void record(Thread<abstract_interpret_value> *thr, const ThreadEvent<abstract_interpret_value> *evt);

	CrashReasonExtractor() : signal(NULL) {}
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
		return new CrashReasonControl(extr.thr->tid, extr.signal->virtaddr);
	else
		return new CrashReasonAnd(new CrashReasonControl(extr.thr->tid, extr.thr->regs.rip()),
					  new CrashReasonBadPointer(extr.thr->tid, extr.signal->virtaddr));
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
