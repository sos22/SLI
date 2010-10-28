/* This file is somewhat misnamed: it includes both replay and record
 * methods on events. */
#include "sli.h"

ThreadEvent *RdtscEvent::replay(LogRecord *lr, MachineState **ms,
					  bool &, LogReaderPtr)
{
	LogRecordRdtsc *lrr = dynamic_cast<LogRecordRdtsc *>(lr);
	if (!lrr)
		throw ReplayFailedException("wanted a rdtsc, got %s",
					    lr->name());
        (*ms)->findThread(this->tid)->temporaries[tmp].lo = lrr->tsc;

	return NULL;
}

InterpretResult RdtscEvent::fake(MachineState *ms, LogRecord **lr)
{
	printf("fake rdtsc\n");
	if (lr)
		*lr = NULL;
	return InterpretResultIncomplete;
}

StoreEvent::StoreEvent(ThreadId tid, unsigned long _addr, unsigned _size, expression_result _data)
	: ThreadEvent(tid),
	  addr(_addr),
	  size(_size),
	  data(_data)
{
}


static void checkSegv(LogRecord *lr, unsigned long addr)
{
	LogRecordSignal *lrs = dynamic_cast<LogRecordSignal *>(lr);
	if (!lrs)
		throw ReplayFailedException("wanted a segv for store to %lx, got %s",
					    addr, lr->name());
	if (lrs->signr != 11)
		throw ReplayFailedException("wanted a segv, got signal %d",
					    lrs->signr);
        if (lrs->virtaddr != addr)
		throw ReplayFailedException("wanted a segv at %lx, got one at %lx\n",
					    lrs->virtaddr, addr);
}


ThreadEvent *StoreEvent::replay(LogRecord *lr, MachineState **ms,
					  bool &, LogReaderPtr)
{
	Thread *thr = (*ms)->findThread(this->tid);
	LogRecordStore *lrs = dynamic_cast<LogRecordStore *>(lr);
	if (!lrs)
		throw ReplayFailedException("wanted a store, got %s",
					    lr->name());
	if (size != lrs->size || addr != lrs->ptr)
		printf("WARNING: wanted %d byte store to %lx, got %d to %lx\n",
		       lrs->size, lrs->ptr,
		       size, addr);
	if (data != lrs->value)
		printf("WARNING: memory mismatch on store to %lx: %s != %s\n",
		       addr, data.name(), lrs->value.name());
	(*ms)->addressSpace->store(lrs->ptr, lrs->size, lrs->value, false, thr);

	return NULL;
}


InterpretResult StoreEvent::fake(MachineState *ms,
				      LogRecord **lr)
{
	Thread *thr = ms->findThread(this->tid);
	if (lr)
		*lr = new LogRecordStore(thr->tid, size, addr, data);
	ms->addressSpace->store(addr, size, data, false, thr);
	return InterpretResultContinue;
}


ThreadEvent *LoadEvent::replay(LogRecord *lr, MachineState **ms,
					 bool &, LogReaderPtr)
{
	Thread *thr = (*ms)->findThread(this->tid);
	if ((*ms)->addressSpace->isReadable(addr, size, thr)) {
		LogRecordLoad *lrl = dynamic_cast<LogRecordLoad *>(lr);
		if (!lrl)
			throw ReplayFailedException("wanted a load, got %s",
						    lr->name());
		if (size != lrl->size || addr != lrl->ptr)
			printf("ReplayFailedException(\"wanted %d byte load from %lx, got %d from %lx\","
			       "lrl->size, lrl->ptr,"
			       "size, addr);\n",
			       lrl->size, lrl->ptr,
			       size, addr);
		expression_result buf =
			(*ms)->addressSpace->load(addr, size, false, thr);
		if (buf != lrl->value &&
		    addr < 0xFFFFFFFFFF600000)
			printf("WARNING: memory mismatch on load from %lx (%s != %s)",
			       addr, buf.name(), lrl->value.name());
		thr->temporaries[tmp] = lrl->value;
	} else {
		checkSegv(lr, addr);
	}

	return NULL;
}


InterpretResult LoadEvent::fake(MachineState *ms, LogRecord **lr)
{
	Thread *thr = ms->findThread(this->tid);
	if (ms->addressSpace->isReadable(addr, size, thr)) {
		expression_result buf =
			ms->addressSpace->load(addr, size, false, thr);
		thr->temporaries[tmp] = buf;
		if (lr)
			*lr = new LogRecordLoad(thr->tid, size, addr, buf);
		return InterpretResultContinue;
	} else {
		if (lr)
			*lr = NULL;
		thr->crashed = true;
		return InterpretResultCrash;
	}
}


ThreadEvent *InstructionEvent::replay(LogRecord *lr, MachineState **ms,
						bool &consumedRecord, LogReaderPtr)
{
#if 0
	LogRecordFootstep *lrf = dynamic_cast<LogRecordFootstep *>(lr);
	if (!lrf)
		throw ReplayFailedException("wanted a footstep, got %s",
					    lr->name());
        if (!allowRipMismatch && rip != lrf->rip)
		printf("ReplayFailedBadRip(%lx, %lx)", rip, lrf->rip);
#define PASTE(x, y) x ## y
#define PASTE2(x, y) PASTE(x, y)
#define STRING(x) #x
#define STRING2(x) STRING(x)
#define FR_REG_NAME(x) PASTE2(PASTE2(FOOTSTEP_REG_, x), _NAME)
#define CHECK_REGISTER(x)						\
	do {                                                            \
		if (reg ## x != lrf-> reg ## x)			\
			printf("ReplayFailedBadRegister("		\
			       STRING2( FR_REG_NAME(x))", %lx, %lx)",	\
			       reg ## x,				\
			       lrf-> reg ## x);			\
	} while (0)
       CHECK_REGISTER(0);
       CHECK_REGISTER(1);
       CHECK_REGISTER(2);
       CHECK_REGISTER(3);
       CHECK_REGISTER(4);
#else
       consumedRecord = false;
#endif
       return NULL;
}


InterpretResult InstructionEvent::fake(MachineState *ms,
					    LogRecord **lr)
{
#if 0
	if (lr)
		*lr = new LogRecordFootstep(this->tid, rip, reg0, reg1, reg2, reg3, reg4);
#else
	if (lr)
		*lr = NULL;
#endif
	return InterpretResultContinue;
}


ThreadEvent *SyscallEvent::replay(LogRecord *lr, MachineState **ms,
				       bool &, LogReaderPtr ptr)
{
	LogRecordSyscall *lrs = dynamic_cast<LogRecordSyscall *>(lr);
	if (!lrs)
		throw ReplayFailedException("wanted a syscall, got %s",
					    lr->name());
		
	return replay_syscall(lrs, (*ms)->findThread(this->tid), *ms, ptr);
}


ThreadEvent *CasEvent::replay(LogRecord *lr, MachineState **ms,
					bool &, LogReaderPtr)
{
	LogRecordLoad *lrl = dynamic_cast<LogRecordLoad *>(lr);
	if (!lrl)
		throw ReplayFailedException("wanted a load for CAS, got %s",
					    lr->name());
        if (size != lrl->size || addr.lo != lrl->ptr)
		throw ReplayFailedException("wanted %d byte CAS from %lx, got %d from %lx",
					    lrl->size, lrl->ptr,
					    size, addr.lo);

        expression_result seen;
	Thread *thr = (*ms)->findThread(this->tid);
        seen = (*ms)->addressSpace->load(addr.lo, size, false, thr);
        if (seen != lrl->value)
		throw ReplayFailedException("memory mismatch on CAS load from %lx",
					    addr.lo);
	thr->temporaries[dest] = seen;
        if (seen != expected)
		return NULL;

	return StoreEvent::get(this->tid, addr.lo, size, data);
}


ThreadEvent *CasEvent::replay(LogRecord *lr, MachineState *ms,
					const LogReader *lf, LogReaderPtr ptr,
					LogReaderPtr *outPtr, LogWriter *lw)
{
	LogRecordLoad *lrl = dynamic_cast<LogRecordLoad *>(lr);
	if (!lrl)
		throw ReplayFailedException("wanted a load for CAS, got %s",
					    lr->name());
        if (size != lrl->size || addr.lo != lrl->ptr)
		throw ReplayFailedException("wanted %d byte CAS from %lx, got %d from %lx",
					    lrl->size, lrl->ptr,
					    size, addr.lo);

        expression_result seen;
	Thread *thr = ms->findThread(this->tid);
        seen = ms->addressSpace->load(addr.lo, size, false, thr);
        if (seen != lrl->value)
		throw ReplayFailedException("memory mismatch on CAS load from %lx",
					    addr.lo);
	thr->temporaries[dest] = seen;
        if (seen != expected)
		return NULL;

        LogRecord *lr2 = lf->read(ptr, outPtr);
	if (!lr2) {
		/* We've hit the end of the log, which means that we
		   were supposed to replay the load part of the CAS
		   but not the store.  Meh. */
		return NULL;
	}
	if (lw)
		lw->append(lr2);
        LogRecordStore *lrs = dynamic_cast<LogRecordStore *>(lr2);
	if (!lrs)
		throw ReplayFailedException("wanted a store for CAS, got something else");
        if (size != lrs->size || addr.lo != lrs->ptr)
		throw ReplayFailedException("wanted %d byte CAS to %lx, got %d to %lx",
					    lrs->size, lrs->ptr,
					    size, addr.lo);
        if (data != lrs->value)
		throw ReplayFailedException("memory mismatch on CAS to %lx",
					    addr.lo);

	ms->addressSpace->store(addr.lo, size, data, false, thr);

	return NULL;
}


InterpretResult CasEvent::fake(MachineState *ms, LogRecord **lr1,
				    LogRecord **lr2)
{
	Thread *thr = ms->findThread(this->tid);
	expression_result seen = ms->addressSpace->load(addr.lo, size, false, thr);
	if (lr1)
		*lr1 = new LogRecordLoad(this->tid, size, addr.lo, seen);
	thr->temporaries[dest] = seen;
	if (seen == expected) {
		ms->addressSpace->store(addr.lo, size, data, false, thr);
		if (lr2)
			*lr2 = new LogRecordStore(this->tid, size, addr.lo, data);
	} else if (lr2)
		*lr2 = NULL;
	return InterpretResultContinue;
}


InterpretResult CasEvent::fake(MachineState *ms, LogRecord **lr1)
{
	return fake(ms, lr1, NULL);
}


ThreadEvent *SignalEvent::replay(LogRecord *lr, MachineState **ms,
					   bool &, LogReaderPtr)
{
	Thread *thr = (*ms)->findThread(this->tid);
	LogRecordSignal *lrs = dynamic_cast<LogRecordSignal *>(lr);
	if (!lrs)
		throw ReplayFailedException("wanted a signal record, got %s",
					    lr->name());
	if (lrs->signr != signr)
		throw ReplayFailedException("wanted signal %d, got signal %d",
					    lrs->signr, signr);
	switch (lrs->signr) {
	case 6:
		break;
	case 11:
		if ((*ms)->addressSpace->isReadable(lrs->virtaddr, 1, thr))
			throw ReplayFailedException("got a segv at %lx, but that location is readable?",
						    lrs->virtaddr);
		/* Can't actually do much with this, because we pick
		   up the Valgrind sighandlers when we start.  Oh
		   well. */
#if 0
		if (ms->signalHandlers.handlers[11].sa_handler != SIG_DFL)
			throw NotImplementedException("don't handle custom signal handlers");
#endif
		break;
	default:
		throw NotImplementedException("Only handle SIGSEGV and SIGABRT, got %d",
					      lrs->signr);
	}

	printf("Crash in thread %d signal %d\n", thr->tid._tid(), signr);
	thr->crashed = true;

	return NULL;
}


InterpretResult SignalEvent::fake(MachineState *ms, LogRecord **lr)
{
	Thread *thr = ms->findThread(this->tid);
	if (lr)
		*lr = new LogRecordSignal(thr->tid, thr->regs.rip(), signr, 0, virtaddr);
	printf("Crash in thread %d signal %d\n", thr->tid._tid(),signr);
	thr->crashed = true;
	return InterpretResultCrash;
}

ThreadEvent *
RdtscEvent::fuzzyReplay(VexPtr<MachineState > &ms,
			     VexPtr<LogReader > &lf,
			     LogReaderPtr startPtr,
			     LogReaderPtr *endPtr,
			     GarbageCollectionToken)
{
	/* Try to satisfy it with the next rdtsc in the log */
	while (1) {
		LogRecord *lr = lf->read(startPtr, &startPtr);
		if (!lr)
			break;
		if (!dynamic_cast<LogRecordRdtsc *>(lr))
			continue;
		*endPtr = startPtr;
		bool ign;
		return replay(lr, &ms.get(), ign, startPtr);
	}

	/* Nothing left in the log.  Fake it. */
	fake(ms, NULL);
	return NULL;
}

ThreadEvent *
SyscallEvent::fuzzyReplay(VexPtr<MachineState > &ms,
			       VexPtr<LogReader > &lf,
			       LogReaderPtr startPtr,
			       LogReaderPtr *endPtr,
			       GarbageCollectionToken t)
{
	while (1) {
		LogRecord *lr = lf->read(startPtr, &startPtr);
		if (!lr)
			break;
		if (!dynamic_cast<LogRecordSyscall *>(lr))
			continue;
		try {
			bool ign;
			ThreadEvent *r = replay(lr, &ms.get(), ign, startPtr);
			*endPtr = startPtr;
			VexPtr<AddressSpace> as(ms->addressSpace);
		        VexPtr<LogWriter> dummy(NULL);
			/* This might invalidate the this pointer... */
			process_memory_records(as, lf, startPtr, endPtr, dummy, t);
			return r;
		} catch (ReplayFailedException &excpt) {
			/* Replay failed.  Keep trying more calls out
			 * of the log. */
		}
	}

	fake(ms, NULL);
	return NULL;
}

ThreadEvent *
CasEvent::fuzzyReplay(VexPtr<MachineState > &ms,
			   VexPtr<LogReader > &lf,
			   LogReaderPtr startPtr,
			   LogReaderPtr *endPtr,
			   GarbageCollectionToken)
{
        expression_result seen;
	Thread *thr = ms->findThread(this->tid);
        seen = ms->addressSpace->load(addr.lo, size, false, thr);
	thr->temporaries[dest] = seen;
        if (seen != expected)
		return NULL;
	return StoreEvent::get(this->tid, addr.lo, size, data);
}

