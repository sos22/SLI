/* This file is somewhat misnamed: it includes both replay and record
 * methods on events. */
#include "sli.h"

template <typename ait>
void RdtscEvent<ait>::replay(LogRecord<ait> *lr, MachineState<ait> *ms)
{
	LogRecordRdtsc<ait> *lrr = dynamic_cast<LogRecordRdtsc<ait> *>(lr);
	if (!lrr)
		throw ReplayFailedException("wanted a rdtsc, got %s",
					    lr->name());
        ms->findThread(this->when.tid)->temporaries[tmp].lo = lrr->tsc;
}

template <typename ait>
InterpretResult RdtscEvent<ait>::fake(MachineState<ait> *ms, LogRecord<ait> **lr)
{
	printf("fake rdtsc\n");
	*lr = NULL;
	return InterpretResultIncomplete;
}

template <typename ait>
StoreEvent<ait>::StoreEvent(EventTimestamp when, ait _addr, unsigned _size, expression_result<ait> _data)
	: ThreadEvent<ait>(when),
	  addr(_addr),
	  size(_size),
	  data(_data)
{
}

template <typename ait>
static void checkSegv(LogRecord<ait> *lr, ait addr)
{
	LogRecordSignal<ait> *lrs = dynamic_cast<LogRecordSignal<ait> *>(lr);
	if (!lrs)
		throw ReplayFailedException("wanted a segv for store to %lx, got %s",
					    force(addr), lr->name());
	if (lrs->signr != 11)
		throw ReplayFailedException("wanted a segv, got signal %d",
					    lrs->signr);
        if (force(lrs->virtaddr != addr))
		throw ReplayFailedException("wanted a segv at %lx, got one at %lx\n",
					    force(lrs->virtaddr), force(addr));
}

template <typename ait>
void StoreEvent<ait>::replay(LogRecord<ait> *lr, MachineState<ait> *ms)
{
	Thread<ait> *thr = ms->findThread(this->when.tid);
	LogRecordStore<ait> *lrs = dynamic_cast<LogRecordStore<ait> *>(lr);
	if (!lrs)
		throw ReplayFailedException("wanted a store, got %s",
					    lr->name());
	if (size != lrs->size || force(addr != lrs->ptr))
		throw ReplayFailedException("wanted %d byte store to %lx, got %d to %lx",
					    lrs->size, force(lrs->ptr),
					    size, force(addr));
	if (force(data != lrs->value))
		throw ReplayFailedException("memory mismatch on store to %lx",
					    force(addr));
	ms->addressSpace->store(this->when, addr, size, data, false, thr);
	thr->nrAccesses++;
}

template <typename ait>
InterpretResult StoreEvent<ait>::fake(MachineState<ait> *ms,
				      LogRecord<ait> **lr)
{
	Thread<ait> *thr = ms->findThread(this->when.tid);
	if (lr)
		*lr = new LogRecordStore<ait>(thr->tid, size, addr, data);
	ms->addressSpace->store(this->when, addr, size, data, false, thr);
	thr->nrAccesses++;
	return InterpretResultContinue;
}

template <typename ait>
void LoadEvent<ait>::replay(LogRecord<ait> *lr, MachineState<ait> *ms)
{
	Thread<ait> *thr = ms->findThread(this->when.tid);
	if (ms->addressSpace->isReadable(addr, size, thr)) {
		LogRecordLoad<ait> *lrl = dynamic_cast<LogRecordLoad<ait> *>(lr);
		if (!lrl)
			throw ReplayFailedException("wanted a load, got %s",
						    lr->name());
		if (size != lrl->size || force(addr != lrl->ptr))
			throw ReplayFailedException("wanted %d byte load from %lx, got %d from %lx",
						    lrl->size, force(lrl->ptr),
						    size, force(addr));
		expression_result<ait> buf =
			ms->addressSpace->load(this->when, addr, size, false, thr);
		if (force(buf != lrl->value))
			throw ReplayFailedException("memory mismatch on load from %lx",
						    force(addr));
		thr->temporaries[tmp] = buf;
		thr->nrAccesses++;
	} else {
		checkSegv(lr, addr);
	}
}

template <typename ait>
InterpretResult LoadEvent<ait>::fake(MachineState<ait> *ms, LogRecord<ait> **lr)
{
	Thread<ait> *thr = ms->findThread(this->when.tid);
	if (ms->addressSpace->isReadable(addr, size, thr)) {
		expression_result<ait> buf =
			ms->addressSpace->load(this->when, addr, size, false, thr);
		thr->temporaries[tmp] = buf;
		if (lr)
			*lr = new LogRecordLoad<ait>(thr->tid, size, addr, buf);
		thr->nrAccesses++;
		return InterpretResultContinue;
	} else {
		if (lr)
			*lr = NULL;
		thr->crashed = true;
		return InterpretResultCrash;
	}
}

template <typename ait>
void InstructionEvent<ait>::replay(LogRecord<ait> *lr, MachineState<ait> *ms)
{
	LogRecordFootstep<ait> *lrf = dynamic_cast<LogRecordFootstep<ait> *>(lr);
	if (!lrf)
		throw ReplayFailedException("wanted a footstep, got %s",
					    lr->name());
        if (force(rip != lrf->rip))
		throw ReplayFailedBadRip(force(rip), force(lrf->rip));
#define PASTE(x, y) x ## y
#define PASTE2(x, y) PASTE(x, y)
#define STRING(x) #x
#define STRING2(x) STRING(x)
#define FR_REG_NAME(x) PASTE2(PASTE2(FOOTSTEP_REG_, x), _NAME)
#define CHECK_REGISTER(x)						\
	do {                                                            \
		if (force(reg ## x != lrf-> reg ## x))			\
			throw ReplayFailedBadRegister(			\
				STRING2( FR_REG_NAME(x)),		\
				force(reg ## x),			\
				force(lrf-> reg ## x));			\
	} while (0)
       CHECK_REGISTER(0);
       CHECK_REGISTER(1);
       CHECK_REGISTER(2);
       CHECK_REGISTER(3);
       CHECK_REGISTER(4);
}

template <typename ait>
InterpretResult InstructionEvent<ait>::fake(MachineState<ait> *ms,
					    LogRecord<ait> **lr)
{
	if (lr)
		*lr = new LogRecordFootstep<ait>(this->when.tid, rip, reg0, reg1, reg2, reg3, reg4);
	return InterpretResultContinue;
}

template <typename ait>
void SyscallEvent<ait>::replay(LogRecord<ait> *lr, MachineState<ait> *ms)
{
	LogRecordSyscall<ait> *lrs = dynamic_cast<LogRecordSyscall<ait> *>(lr);
	if (!lrs)
		throw ReplayFailedException("wanted a syscall, got %s",
					    lr->name());
		
	replay_syscall(lrs, ms->findThread(this->when.tid), ms);
}

template <typename ait>
void CasEvent<ait>::replay(LogRecord<ait> *lr, MachineState<ait> *ms)
{
	throw SliException("CAS events need a special replay method");
}

template <typename ait>
void CasEvent<ait>::replay(LogRecord<ait> *lr, MachineState<ait> *ms,
			   const LogReader<ait> *lf, LogReaderPtr ptr,
			   LogReaderPtr *outPtr, LogWriter<ait> *lw)
{
	LogRecordLoad<ait> *lrl = dynamic_cast<LogRecordLoad<ait> *>(lr);
	if (!lrl)
		throw ReplayFailedException("wanted a load for CAS, got %s",
					    lr->name());
        if (size != lrl->size || force(addr.lo != lrl->ptr))
		throw ReplayFailedException("wanted %d byte CAS from %lx, got %d from %lx",
					    lrl->size, force(lrl->ptr),
					    size, force(addr.lo));

        expression_result<ait> seen;
	Thread<ait> *thr = ms->findThread(this->when.tid);
        seen = ms->addressSpace->load(this->when, addr.lo, size, false, thr);
        if (force(seen != lrl->value))
		throw ReplayFailedException("memory mismatch on CAS load from %lx",
					    force(addr.lo));
	thr->temporaries[dest] = seen;
        if (force(seen != expected))
		return;

        LogRecord<ait> *lr2 = lf->read(ptr, outPtr);
	if (lw)
		lw->append(*lr2, this->when.idx);
        LogRecordStore<ait> *lrs = dynamic_cast<LogRecordStore<ait> *>(lr2);
	if (!lrs)
		throw ReplayFailedException("wanted a store for CAS, got something else");
        if (size != lrs->size || force(addr.lo != lrs->ptr))
		throw ReplayFailedException("wanted %d byte CAS to %lx, got %d to %lx",
					    lrs->size, force(lrs->ptr),
					    size, force(addr.lo));
        if (force(data != lrs->value))
		throw ReplayFailedException("memory mismatch on CAS to %lx",
					    force(addr.lo));

	ms->addressSpace->store(this->when, addr.lo, size, data, false, thr);
}

template <typename ait>
InterpretResult CasEvent<ait>::fake(MachineState<ait> *ms, LogRecord<ait> **lr1,
				    LogRecord<ait> **lr2)
{
	Thread<ait> *thr = ms->findThread(this->when.tid);
	expression_result<ait> seen = ms->addressSpace->load(this->when, addr.lo, size, false, thr);
	if (lr1)
		*lr1 = new LogRecordLoad<ait>(this->when.tid, size, addr.lo, seen);
	thr->temporaries[dest] = seen;
	if (force(seen == expected)) {
		ms->addressSpace->store(this->when, addr.lo, size, data, false, thr);
		if (lr2)
			*lr2 = new LogRecordStore<ait>(this->when.tid, size, addr.lo, data);
	} else if (lr2)
		*lr2 = NULL;
	return InterpretResultContinue;
}

template <typename ait>
InterpretResult CasEvent<ait>::fake(MachineState<ait> *ms, LogRecord<ait> **lr1)
{
	return fake(ms, lr1, NULL);
}

template <typename ait>
void SignalEvent<ait>::replay(LogRecord<ait> *lr, MachineState<ait> *ms)
{
	Thread<ait> *thr = ms->findThread(this->when.tid);
	LogRecordSignal<ait> *lrs = dynamic_cast<LogRecordSignal<ait> *>(lr);
	if (!lrs)
		throw ReplayFailedException("wanted a signal record, got %s",
					    lr->name());
	if (lrs->signr != 11)
		throw NotImplementedException("Only handle SIGSEGV, got %d",
					      lrs->signr);
	if (ms->addressSpace->isReadable(lrs->virtaddr, 1, thr))
		throw ReplayFailedException("got a segv at %lx, but that location is readable?",
					    force(lrs->virtaddr));
	/* Can't actually do much with this, because we pick up the
	   Valgrind sighandlers when we start.  Oh well. */
#if 0
	if (ms->signalHandlers.handlers[11].sa_handler != SIG_DFL)
		throw NotImplementedException("don't handle custom signal handlers");
#endif
	printf("Crash in thread %d\n", thr->tid._tid());
	thr->crashed = true;
}

template <typename ait>
InterpretResult SignalEvent<ait>::fake(MachineState<ait> *ms, LogRecord<ait> **lr)
{
	Thread<ait> *thr = ms->findThread(this->when.tid);
	if (lr)
		*lr = new LogRecordSignal<ait>(thr->tid, thr->regs.rip(), signr, mkConst<ait>(0), virtaddr);
	thr->crashed = true;
	return InterpretResultCrash;
}
