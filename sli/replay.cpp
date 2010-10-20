/* This file is somewhat misnamed: it includes both replay and record
 * methods on events. */
#include "sli.h"

template <typename ait>
ThreadEvent<ait> *RdtscEvent<ait>::replay(LogRecord *lr, MachineState **ms,
					  bool &, LogReaderPtr)
{
	LogRecordRdtsc *lrr = dynamic_cast<LogRecordRdtsc *>(lr);
	if (!lrr)
		throw ReplayFailedException("wanted a rdtsc, got %s",
					    lr->name());
        (*ms)->findThread(this->when.tid)->temporaries[tmp].lo = lrr->tsc;

	return NULL;
}

template <typename ait> ThreadEvent<ait> *
UseFreeMemoryEvent<ait>::replay(LogRecord *lr, MachineState **ms,
				bool &, LogReaderPtr)
{
	(*ms)->findThread(this->when.tid)->crashed = true;
	return NULL;
}

template <typename ait> InterpretResult
UseFreeMemoryEvent<ait>::fake(MachineState *ms, LogRecord **lr)
{
        ms->findThread(this->when.tid)->crashed = true;
	if (lr)
		*lr = NULL;
	return InterpretResultCrash;
}

template <typename ait>
InterpretResult RdtscEvent<ait>::fake(MachineState *ms, LogRecord **lr)
{
	printf("fake rdtsc\n");
	if (lr)
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
	sanity_check_ait(data.lo);
	sanity_check_ait(data.hi);
}

template <typename ait>
static void checkSegv(LogRecord *lr, ait addr)
{
	LogRecordSignal *lrs = dynamic_cast<LogRecordSignal *>(lr);
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
ThreadEvent<ait> *StoreEvent<ait>::replay(LogRecord *lr, MachineState **ms,
					  bool &, LogReaderPtr)
{
	Thread *thr = (*ms)->findThread(this->when.tid);
	LogRecordStore *lrs = dynamic_cast<LogRecordStore *>(lr);
	if (!lrs)
		throw ReplayFailedException("wanted a store, got %s",
					    lr->name());
	if (size != lrs->size || force(addr != lrs->ptr))
		printf("WARNING: wanted %d byte store to %lx, got %d to %lx\n",
		       lrs->size, force(lrs->ptr),
		       size, force(addr));
	if (force(data != lrs->value))
		printf("WARNING: memory mismatch on store to %lx: %s != %s\n",
		       force(addr), data.name(), lrs->value.name());
	(*ms)->addressSpace->store(this->when, lrs->ptr, lrs->size, lrs->value, false, thr);
	thr->nrAccesses++;

	return NULL;
}

template <typename ait>
InterpretResult StoreEvent<ait>::fake(MachineState *ms,
				      LogRecord **lr)
{
	Thread *thr = ms->findThread(this->when.tid);
	if (lr)
		*lr = new LogRecordStore(thr->tid, size, addr, data);
	ms->addressSpace->store(this->when, addr, size, data, false, thr);
	thr->nrAccesses++;
	return InterpretResultContinue;
}

template <typename ait>
ThreadEvent<ait> *LoadEvent<ait>::replay(LogRecord *lr, MachineState **ms,
					 bool &, LogReaderPtr)
{
	Thread *thr = (*ms)->findThread(this->when.tid);
	if ((*ms)->addressSpace->isReadable(addr, size, thr)) {
		LogRecordLoad *lrl = dynamic_cast<LogRecordLoad *>(lr);
		if (!lrl)
			throw ReplayFailedException("wanted a load, got %s",
						    lr->name());
		if (size != lrl->size || force(addr != lrl->ptr))
			printf("ReplayFailedException(\"wanted %d byte load from %lx, got %d from %lx\","
			       "lrl->size, force(lrl->ptr),"
			       "size, force(addr));\n",
			       lrl->size, force(lrl->ptr),
			       size, force(addr));
		expression_result<ait> buf =
			(*ms)->addressSpace->load(this->when, addr, size, false, thr);
		if (force(buf != lrl->value) &&
		    force(addr) < 0xFFFFFFFFFF600000)
			printf("WARNING: memory mismatch on load from %lx (%s != %s)",
			       force(addr), buf.name(), lrl->value.name());
		thr->temporaries[tmp] = lrl->value;
		thr->nrAccesses++;
	} else {
		checkSegv(lr, addr);
	}

	return NULL;
}

template <typename ait>
InterpretResult LoadEvent<ait>::fake(MachineState *ms, LogRecord **lr)
{
	Thread *thr = ms->findThread(this->when.tid);
	if (ms->addressSpace->isReadable(addr, size, thr)) {
		expression_result<ait> buf =
			ms->addressSpace->load(this->when, addr, size, false, thr);
		thr->temporaries[tmp] = buf;
		if (lr)
			*lr = new LogRecordLoad(thr->tid, size, addr, buf);
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
ThreadEvent<ait> *InstructionEvent<ait>::replay(LogRecord *lr, MachineState **ms,
						bool &consumedRecord, LogReaderPtr)
{
#if 0
	LogRecordFootstep *lrf = dynamic_cast<LogRecordFootstep *>(lr);
	if (!lrf)
		throw ReplayFailedException("wanted a footstep, got %s",
					    lr->name());
        if (!allowRipMismatch && force(rip != lrf->rip))
		printf("ReplayFailedBadRip(%lx, %lx)", force(rip), force(lrf->rip));
#define PASTE(x, y) x ## y
#define PASTE2(x, y) PASTE(x, y)
#define STRING(x) #x
#define STRING2(x) STRING(x)
#define FR_REG_NAME(x) PASTE2(PASTE2(FOOTSTEP_REG_, x), _NAME)
#define CHECK_REGISTER(x)						\
	do {                                                            \
		if (force(reg ## x != lrf-> reg ## x))			\
			printf("ReplayFailedBadRegister("		\
			       STRING2( FR_REG_NAME(x))", %lx, %lx)",	\
			       force(reg ## x),				\
			       force(lrf-> reg ## x));			\
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

template <typename ait>
InterpretResult InstructionEvent<ait>::fake(MachineState *ms,
					    LogRecord **lr)
{
#if 0
	if (lr)
		*lr = new LogRecordFootstep(this->when.tid, rip, reg0, reg1, reg2, reg3, reg4);
#else
	if (lr)
		*lr = NULL;
#endif
	return InterpretResultContinue;
}

template <typename ait>
ThreadEvent<ait> *SyscallEvent<ait>::replay(LogRecord *lr, MachineState **ms,
					    bool &, LogReaderPtr ptr)
{
	LogRecordSyscall *lrs = dynamic_cast<LogRecordSyscall *>(lr);
	if (!lrs)
		throw ReplayFailedException("wanted a syscall, got %s",
					    lr->name());
		
	return replay_syscall<ait>(lrs, (*ms)->findThread(this->when.tid), *ms, ptr);
}

template <typename ait>
ThreadEvent<ait> *CasEvent<ait>::replay(LogRecord *lr, MachineState **ms,
					bool &, LogReaderPtr)
{
	LogRecordLoad *lrl = dynamic_cast<LogRecordLoad *>(lr);
	if (!lrl)
		throw ReplayFailedException("wanted a load for CAS, got %s",
					    lr->name());
        if (size != lrl->size || force(addr.lo != lrl->ptr))
		throw ReplayFailedException("wanted %d byte CAS from %lx, got %d from %lx",
					    lrl->size, force(lrl->ptr),
					    size, force(addr.lo));

        expression_result<ait> seen;
	Thread *thr = (*ms)->findThread(this->when.tid);
        seen = (*ms)->addressSpace->load(this->when, addr.lo, size, false, thr);
        if (force(seen != lrl->value))
		throw ReplayFailedException("memory mismatch on CAS load from %lx",
					    force(addr.lo));
	thr->temporaries[dest] = seen;
        if (force(seen != expected))
		return NULL;

	return StoreEvent<ait>::get(this->when, addr.lo, size, data);
}

template <typename ait>
ThreadEvent<ait> *CasEvent<ait>::replay(LogRecord *lr, MachineState *ms,
					const LogReader<ait> *lf, LogReaderPtr ptr,
					LogReaderPtr *outPtr, LogWriter<ait> *lw)
{
	LogRecordLoad *lrl = dynamic_cast<LogRecordLoad *>(lr);
	if (!lrl)
		throw ReplayFailedException("wanted a load for CAS, got %s",
					    lr->name());
        if (size != lrl->size || force(addr.lo != lrl->ptr))
		throw ReplayFailedException("wanted %d byte CAS from %lx, got %d from %lx",
					    lrl->size, force(lrl->ptr),
					    size, force(addr.lo));

        expression_result<ait> seen;
	Thread *thr = ms->findThread(this->when.tid);
        seen = ms->addressSpace->load(this->when, addr.lo, size, false, thr);
        if (force(seen != lrl->value))
		throw ReplayFailedException("memory mismatch on CAS load from %lx",
					    force(addr.lo));
	thr->temporaries[dest] = seen;
        if (force(seen != expected))
		return NULL;

        LogRecord *lr2 = lf->read(ptr, outPtr);
	if (!lr2) {
		/* We've hit the end of the log, which means that we
		   were supposed to replay the load part of the CAS
		   but not the store.  Meh. */
		return NULL;
	}
	if (lw)
		lw->append(lr2, this->when.idx);
        LogRecordStore *lrs = dynamic_cast<LogRecordStore *>(lr2);
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

	return NULL;
}

template <typename ait>
InterpretResult CasEvent<ait>::fake(MachineState *ms, LogRecord **lr1,
				    LogRecord **lr2)
{
	Thread *thr = ms->findThread(this->when.tid);
	expression_result<ait> seen = ms->addressSpace->load(this->when, addr.lo, size, false, thr);
	if (lr1)
		*lr1 = new LogRecordLoad(this->when.tid, size, addr.lo, seen);
	thr->temporaries[dest] = seen;
	if (force(seen == expected)) {
		ms->addressSpace->store(this->when, addr.lo, size, data, false, thr);
		if (lr2)
			*lr2 = new LogRecordStore(this->when.tid, size, addr.lo, data);
	} else if (lr2)
		*lr2 = NULL;
	return InterpretResultContinue;
}

template <typename ait>
InterpretResult CasEvent<ait>::fake(MachineState *ms, LogRecord **lr1)
{
	return fake(ms, lr1, NULL);
}

template <typename ait>
ThreadEvent<ait> *SignalEvent<ait>::replay(LogRecord *lr, MachineState **ms,
					   bool &, LogReaderPtr)
{
	Thread *thr = (*ms)->findThread(this->when.tid);
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
						    force(lrs->virtaddr));
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

template <typename ait>
InterpretResult SignalEvent<ait>::fake(MachineState *ms, LogRecord **lr)
{
	Thread *thr = ms->findThread(this->when.tid);
	if (lr)
		*lr = new LogRecordSignal(thr->tid, thr->regs.rip(), signr, mkConst<ait>(0), virtaddr);
	printf("Crash in thread %d signal %d\n", thr->tid._tid(),signr);
	thr->crashed = true;
	return InterpretResultCrash;
}

template <typename ait> ThreadEvent<ait> *
RdtscEvent<ait>::fuzzyReplay(VexPtr<MachineState > &ms,
			     VexPtr<LogReader<ait> > &lf,
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

template <typename ait> ThreadEvent<ait> *
SyscallEvent<ait>::fuzzyReplay(VexPtr<MachineState > &ms,
			       VexPtr<LogReader<ait> > &lf,
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
			ThreadEvent<ait> *r = replay(lr, &ms.get(), ign, startPtr);
			*endPtr = startPtr;
			VexPtr<AddressSpace> as(ms->addressSpace);
		        VexPtr<LogWriter<ait> > dummy(NULL);
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

template <typename ait> ThreadEvent<ait> *
CasEvent<ait>::fuzzyReplay(VexPtr<MachineState > &ms,
			   VexPtr<LogReader<ait> > &lf,
			   LogReaderPtr startPtr,
			   LogReaderPtr *endPtr,
			   GarbageCollectionToken)
{
        expression_result<ait> seen;
	Thread *thr = ms->findThread(this->when.tid);
        seen = ms->addressSpace->load(this->when, addr.lo, size, false, thr);
	thr->temporaries[dest] = seen;
        if (force(seen != expected))
		return NULL;
	return StoreEvent<ait>::get(this->when, addr.lo, size, data);
}

