#include <err.h>

#include "sli.h"

#define FOOTSTEP_REGS_ONLY
#include "ppres.h"

/* A RIP expression is an assertion that a particular thread is
   executing a particular instruction at a particular time. */
class ExpressionRip : public Expression {
public:
	Expression *rip;
	ThreadId tid;
	ReplayTimestamp when;
private:
	static VexAllocTypeWrapper<ExpressionRip> allocator;
	ExpressionRip(Expression *_rip, ThreadId _tid, ReplayTimestamp _when) :
		rip(_rip),
		tid(_tid),
		when(_when)
	{
	}
protected:
	char *mkName(void) const {
		return my_asprintf("(rip %d:%lx:%s)",
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

static Expression *refine(Expression *expr,
			  const MachineState<abstract_interpret_value> *ms,
			  LogReader<abstract_interpret_value> *lf,
			  LogReaderPtr ptr,
			  bool *progress);

/* A CrashReasonControl indicates that we executed some RIP which we
 * shouldn't have done.  There are two possible explanations:
 *
 * 1) The previous control flow instruction branched the wrong way.
 * 2) The previous control flow instruction should never have been
 * executed.
 *
 * We refine by finding the previous control flow branch for this
 * thread and generating new crash reasons for each possible
 * subcase.
 *
 * (It's also possible that the contents of the relevant bit of memory
 * changed, whether due to mmap() manipulations or direct writes, but
 * we ignore that possibility, because it's hard and unlikely.)
 */
class GetFootstepsOneThread : public EventRecorder<abstract_interpret_value> {
public:
        typedef std::vector<const InstructionEvent<abstract_interpret_value> *> contentT;
	contentT content;
	ThreadId tid;
        VexGcVisitor<GetFootstepsOneThread> visitor;

	GetFootstepsOneThread(ThreadId _tid) :
		EventRecorder<abstract_interpret_value>(),
		tid(_tid),
		visitor(this)
	{
	}
	void record(Thread<abstract_interpret_value> *thr, const ThreadEvent<abstract_interpret_value> *evt)
	{
		if (thr->tid != tid)
			return;
		if (const InstructionEvent<abstract_interpret_value> *ie =
		    dynamic_cast<const InstructionEvent<abstract_interpret_value> *>(evt))
			content.push_back(ie);
		if (dynamic_cast<const SignalEvent<abstract_interpret_value> *>(evt))
			content.push_back(
				InstructionEvent<abstract_interpret_value>::get(
					evt->thr, evt->when, thr->regs.rip(),
#define GR(x) thr->regs.get_reg(REGISTER_IDX(x))
					GR(FOOTSTEP_REG_0_NAME),
					GR(FOOTSTEP_REG_1_NAME),
					thr->regs.get_reg(REGISTER_IDX(XMM0) + 1),
					GR(FOOTSTEP_REG_3_NAME),
					GR(FOOTSTEP_REG_4_NAME)));
#undef GR
	}
	void visit(HeapVisitor &hv) const
	{
                for (contentT::const_iterator it = content.begin();
                     it != content.end();
                     it++)
                        hv(*it);
	}
};
static Expression *refine(ExpressionRip *er,
			  const MachineState<abstract_interpret_value> *ms,
			  LogReader<abstract_interpret_value> *lf,
			  LogReaderPtr ptr,
			  bool *progress)
{
	Interpreter<abstract_interpret_value> i(ms->dupeSelf());
	GetFootstepsOneThread fltr(er->tid);
	i.replayLogfile(lf, ptr, NULL, NULL, &fltr);

	printf("Refine %s\n", er->name());
	const InstructionEvent<abstract_interpret_value> *cond;
	GetFootstepsOneThread::contentT::reverse_iterator it;
	for (it = fltr.content.rbegin();
	     it != fltr.content.rend();
	     it++) {
		cond = *it;
		if (cond->when > er->when)
			continue;
		unsigned long ign;
		if (!cond->rip.origin->isConstant(&ign))
			break;
	}

	if (it == fltr.content.rend()) {
		/* Okay, there were no previous conditional branches.
		   We're doomed. */
		*progress = true;
		return ConstExpression::get(1);
	}

	it++;
	if (it == fltr.content.rend()) {
		*progress = true;
		return ConstExpression::get(1);
	}
	const InstructionEvent<abstract_interpret_value> *branch = *it;

	*progress = true;

	/* We get here if... */
	return logicaland::get(
		/* We make it to the previous conditional branch, and ... */
		ExpressionRip::get(er->tid, branch->when, branch->rip.origin),
		/* ... the branch goes the right way */
		equals::get(cond->rip.origin,
			    ConstExpression::get(cond->rip.v)));
}

static Expression *refine(logicaland *er,
			  const MachineState<abstract_interpret_value> *ms,
			  LogReader<abstract_interpret_value> *lf,
			  LogReaderPtr ptr,
			  bool *progress)
{
	bool lprogress, rprogress;
	lprogress = false;
	rprogress = false;
	Expression *l2 = refine(er->l, ms, lf, ptr, &lprogress);
	Expression *r2 = refine(er->r, ms, lf, ptr, &rprogress);
	if (!lprogress && !rprogress)
		return er;
	*progress = true;
	return logicaland::get(l2, r2);
}

Expression *refine(Expression *expr,
		   const MachineState<abstract_interpret_value> *ms,
		   LogReader<abstract_interpret_value> *lf,
		   LogReaderPtr ptr,
		   bool *progress)
{
	if (ExpressionRip *er = dynamic_cast<ExpressionRip *>(expr))
		return refine(er, ms, lf, ptr, progress);
	else if (logicaland *la = dynamic_cast<logicaland *>(expr))
		return refine(la, ms, lf, ptr, progress);
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
	VexGcRoot crkeeper((void **)&cr);

	bool progress;

	do {
		progress = false;
		printf("Crash reason %s\n", cr->name());
		cr = refine(cr, abstract, al, ptr, &progress);
	} while (progress);
	printf("Crash reason %s\n", cr->name());

	return 0;
}
