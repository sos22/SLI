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
		return my_asprintf("(rip %d:%lx)", tid._tid(), badRip.v);
	}
public:
	CrashReasonControl(ThreadId _tid, abstract_interpret_value _badRip)
		: badRip(_badRip),
		  tid(_tid)
	{
	}
	CrashReason *refine(MachineState<abstract_interpret_value> *, LogReader<abstract_interpret_value> *, LogReaderPtr);
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

class CrashReasonExtractor : public LogWriter<abstract_interpret_value> {
public:
	bool full;
	abstract_interpret_value crash_va;
	ThreadId tid;

	void append(const LogRecord<abstract_interpret_value> &lr);

	CrashReasonExtractor() : full(false), tid(0) {}
};

void CrashReasonExtractor::append(const LogRecord<abstract_interpret_value> &lr)
{
	const LogRecord<abstract_interpret_value> *lrp = &lr;

	if (const LogRecordSignal<abstract_interpret_value> *lrs =
	    dynamic_cast<const LogRecordSignal<abstract_interpret_value> *>(lrp)) {
		full = true;
		tid = lr.thread();
		crash_va = lrs->virtaddr;
	}
}

class FootstepRecorder : public LogWriter<abstract_interpret_value> {
public:
	typedef std::vector<LogRecordFootstep<abstract_interpret_value> *> vect_type;
	vect_type content;

	void append(const LogRecord<abstract_interpret_value> &lr) {
		if (const LogRecordFootstep<abstract_interpret_value> *lrf =
		    dynamic_cast<const LogRecordFootstep<abstract_interpret_value> *>(&lr))
			content.push_back(lrf->dupe());
	}
};

CrashReason *CrashReasonControl::refine(MachineState<abstract_interpret_value> *ms, LogReader<abstract_interpret_value> *lf,
					LogReaderPtr ptr)
{
	Interpreter<abstract_interpret_value> i(ms);
	FootstepRecorder fr;
	i.replayLogfile(lf, ptr, NULL, &fr);
	for (FootstepRecorder::vect_type::reverse_iterator it = fr.content.rbegin();
	     it != fr.content.rend();
	     it++) {
		printf("footstep %s\n", (*it)->name());
		delete *it;
	}
	return this;
}

static CrashReason *getCrashReason(MachineState<abstract_interpret_value> *ms,
				   LogReader<abstract_interpret_value> *script,
				   LogReaderPtr ptr)
{
	Interpreter<abstract_interpret_value> i(ms);
	CrashReasonExtractor extr;

	i.replayLogfile(script, ptr, NULL, &extr);

	if (!ms->crashed())
		return NULL;

	/* For now, we assume that the only reason to crash is
	   dereferencing a bad pointer, which has only two cases:

	   1) Chasing bad data.
	   2) Chasing bad instructions.

	   We further assume that a crash is due to a bad instruction
	   if the faulting address matches the RIP, and bad data
	   otherwise. */
	assert(extr.full);
	ThreadId crashingTid = extr.tid;
	Thread<abstract_interpret_value> *thr = ms->findThread(crashingTid);
	assert(thr->crashed);
	if (force(thr->regs.rip() == extr.crash_va))
		return new CrashReasonControl(crashingTid, extr.crash_va);
	else
		return new CrashReasonAnd(new CrashReasonControl(crashingTid, thr->regs.rip()),
					  new CrashReasonBadPointer(crashingTid, extr.crash_va));
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
	CrashReason *cr2 = cr->refine(abstract->dupeSelf(), al, ptr);
	printf("Refines to %s\n", cr2->name());

	return 0;
}
