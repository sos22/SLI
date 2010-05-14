/* This file is somewhat misnamed: it includes both replay and record
 * methods on events. */
#include "sli.h"

void RdtscEvent::replay(Thread *thr, LogRecord *lr, MachineState *ms)
{
	LogRecordRdtsc *lrr = dynamic_cast<LogRecordRdtsc *>(lr);
	if (!lrr)
		throw ReplayFailedException("wanted a rdtsc, got %s",
					    lr->name());
	thr->temporaries[tmp].lo.v = lrr->tsc;
}

InterpretResult RdtscEvent::fake(Thread *thr, MachineState *ms, LogRecord **lr)
{
	printf("fake rdtsc\n");
	return InterpretResultIncomplete;
}

StoreEvent::StoreEvent(unsigned long _addr, unsigned _size, const void *_data)
	: addr(_addr),
	  size(_size)
{
	data = malloc(size);
	memcpy(data, _data, size);
}

StoreEvent::~StoreEvent()
{
	free(data);
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

void StoreEvent::replay(Thread *thr, LogRecord *lr, MachineState *ms)
{
	if (ms->addressSpace->isWritable(addr, size, thr)) {
		LogRecordStore *lrs = dynamic_cast<LogRecordStore *>(lr);
		if (!lrs)
			throw ReplayFailedException("wanted a store, got %s",
						    lr->name());
		if (size != lrs->size || addr != lrs->ptr)
			throw ReplayFailedException("wanted %d byte store to %lx, got %d to %lx",
						    lrs->size, lrs->ptr,
						    size, addr);
		if (memcmp(data, lrs->buf, size))
			throw ReplayFailedException("memory mismatch on store to %lx",
						    addr);
		ms->addressSpace->writeMemory(addr, size, data, false, thr);
		thr->nrAccesses++;
	} else {
		checkSegv(lr, addr);
	}
}

InterpretResult StoreEvent::fake(Thread *thr, MachineState *ms,
				 LogRecord **lr)
{
	if (lr) {
		void *sb = malloc(size);
		memcpy(sb, data, size);
		*lr = new LogRecordStore(thr->tid, size, addr, sb);
	}
	if (ms->addressSpace->isWritable(addr, size, thr)) {
		ms->addressSpace->writeMemory(addr, size, data, false, thr);
		thr->nrAccesses++;
		return InterpretResultContinue;
	} else {
		thr->crashed = true;
		return InterpretResultCrash;
	}
}

void LoadEvent::replay(Thread *thr, LogRecord *lr, MachineState *ms)
{
	if (ms->addressSpace->isReadable(addr, size, thr)) {
		LogRecordLoad *lrl = dynamic_cast<LogRecordLoad *>(lr);
		if (!lrl)
			throw ReplayFailedException("wanted a load, got %s",
						    lr->name());
		if (size != lrl->size || addr != lrl->ptr)
			throw ReplayFailedException("wanted %d byte load from %lx, got %d from %lx",
						    lrl->size, lrl->ptr,
						    size, addr);
		unsigned char buf[16];
		ms->addressSpace->readMemory(addr, size, buf, false, thr);
		if (memcmp(buf, lrl->buf, size))
			throw ReplayFailedException("memory mismatch on load from %lx",
						    addr);
		
		if (size <= 8) {
			memcpy(&thr->temporaries[tmp].lo.v, buf, size);
		} else if (size <= 16) {
			memcpy(&thr->temporaries[tmp].lo.v, buf, 8);
			memcpy(&thr->temporaries[tmp].hi.v, buf + 8, size - 8);
		} else {
			throw NotImplementedException();
		}
		thr->nrAccesses++;
	} else {
		checkSegv(lr, addr);
	}
}

InterpretResult LoadEvent::fake(Thread *thr, MachineState *ms, LogRecord **lr)
{
	if (ms->addressSpace->isReadable(addr, size, thr)) {
		unsigned char buf[16];
		ms->addressSpace->readMemory(addr, size, buf, false, thr);
		if (size <= 8) {
			memcpy(&thr->temporaries[tmp].lo.v, buf, size);
		} else if (size <= 16) {
			memcpy(&thr->temporaries[tmp].lo.v, buf, 8);
			memcpy(&thr->temporaries[tmp].hi.v, buf + 8, size - 8);
		} else {
			throw NotImplementedException();
		}
		if (lr) {
			void *rb = malloc(size);
			memcpy(rb, buf, size);
			*lr = new LogRecordLoad(thr->tid, size, addr, rb);
		}
		thr->nrAccesses++;
		return InterpretResultContinue;
	} else {
		if (lr)
			*lr = NULL;
		thr->crashed = true;
		return InterpretResultCrash;
	}
}

void InstructionEvent::replay(Thread *thr, LogRecord *lr, MachineState *ms)
{
	LogRecordFootstep *lrf = dynamic_cast<LogRecordFootstep *>(lr);
	if (!lrf)
		throw ReplayFailedException("wanted a footstep, got %s",
					    lr->name());
	if (rip != lrf->rip)
		throw ReplayFailedBadRip(rip, lrf->rip);
#define PASTE(x, y) x ## y
#define PASTE2(x, y) PASTE(x, y)
#define STRING(x) #x
#define STRING2(x) STRING(x)
#define FR_REG_NAME(x) PASTE2(PASTE2(FOOTSTEP_REG_, x), _NAME)
#define CHECK_REGISTER(x)						\
	do {                                                            \
               if (reg ## x != lrf-> reg ## x)				\
                       throw ReplayFailedBadRegister(			\
                               STRING2( FR_REG_NAME(x)),		\
			       reg ## x,				\
                               lrf-> reg ## x);                         \
       } while (0)
       CHECK_REGISTER(0);
       CHECK_REGISTER(1);
       CHECK_REGISTER(2);
       CHECK_REGISTER(3);
       CHECK_REGISTER(4);
}

InterpretResult InstructionEvent::fake(Thread *thr, MachineState *ms,
				       LogRecord **lr)
{
	if (lr)
		*lr = new LogRecordFootstep(thr->tid, rip, reg0, reg1, reg2, reg3, reg4);
	return InterpretResultContinue;
}

void SyscallEvent::replay(Thread *thr, LogRecord *lr, MachineState *ms)
{
	LogRecordSyscall *lrs = dynamic_cast<LogRecordSyscall *>(lr);
	if (!lrs)
		throw ReplayFailedException("wanted a syscall, got %s",
					    lr->name());
		
	replay_syscall(lrs, thr, ms);
}

void CasEvent::replay(Thread *thr, LogRecord *lr, MachineState *ms)
{
	throw SliException("CAS events need a special replay method");
}

void CasEvent::replay(Thread *thr, LogRecord *lr, MachineState *ms,
		      const LogReader *lf, LogReader::ptr ptr,
		      LogReader::ptr *outPtr, LogWriter *lw)
{
	unsigned long expected_buf[2] = {expected.lo.v, expected.hi.v};
	unsigned long data_buf[2] = {data.lo.v, data.hi.v};


	LogRecordLoad *lrl = dynamic_cast<LogRecordLoad *>(lr);
	if (!lrl)
		throw ReplayFailedException("wanted a load for CAS, got %s",
					    lr->name());
	if (size != lrl->size || addr.lo.v != lrl->ptr)
		throw ReplayFailedException("wanted %d byte CAS from %lx, got %d from %lx",
					    lrl->size, lrl->ptr,
					    size, addr.lo.v);

	unsigned long seen_buf[2];
	memset(seen_buf, 0, sizeof(seen_buf));
	ms->addressSpace->readMemory(addr.lo.v, size, seen_buf, false, thr);
	if (memcmp(seen_buf, lrl->buf, size))
		throw ReplayFailedException("memory mismatch on CAS load from %lx",
					    addr.lo.v);
	thr->temporaries[dest].lo.v = seen_buf[0];
	thr->temporaries[dest].hi.v = seen_buf[1];
	if (memcmp(seen_buf, expected_buf, size))
		return;

	LogRecord *lr2 = lf->read(ptr, outPtr);
	if (lw)
		lw->append(*lr2);
	LogRecordStore *lrs = dynamic_cast<LogRecordStore *>(lr2);
	if (!lrs)
		throw ReplayFailedException("wanted a store for CAS, got something else");
	if (size != lrs->size || addr.lo.v != lrs->ptr)
		throw ReplayFailedException("wanted %d byte CAS to %lx, got %d to %lx",
					    lrs->size, lrs->ptr,
					    size, addr.lo.v);
	if (memcmp(data_buf, lrs->buf, size))
		throw ReplayFailedException("memory mismatch on CAS to %lx",
					    addr.lo.v);

	ms->addressSpace->writeMemory(addr.lo.v, size, data_buf, false, thr);
}

InterpretResult CasEvent::fake(Thread *thr, MachineState *ms, LogRecord **lr1,
			       LogRecord **lr2)
{
	unsigned long expected_buf[2] = {expected.lo.v, expected.hi.v};
	unsigned long data_buf[2] = {data.lo.v, data.hi.v};
	unsigned long seen_buf[2];
	memset(seen_buf, 0, sizeof(seen_buf));
	ms->addressSpace->readMemory(addr.lo.v, size, seen_buf, false, thr);
	if (lr1) {
		void *sb = malloc(size);
		memcpy(sb, seen_buf, size);
		*lr1 = new LogRecordLoad(thr->tid, size, addr.lo.v, sb);
	}
	thr->temporaries[dest].lo.v = seen_buf[0];
	thr->temporaries[dest].hi.v = seen_buf[1];
	if (!memcmp(seen_buf, expected_buf, size)) {
		ms->addressSpace->writeMemory(addr.lo.v, size, data_buf, false, thr);
		if (lr2) {
			void *sb = malloc(size);
			memcpy(sb, data_buf, size);
			*lr2 = new LogRecordStore(thr->tid, size, addr.lo.v, sb);
		}
	} else if (lr2)
		*lr2 = NULL;
	return InterpretResultContinue;
}

InterpretResult CasEvent::fake(Thread *thr, MachineState *ms, LogRecord **lr1)
{
	return fake(thr, ms, lr1, NULL);
}

void SignalEvent::replay(Thread *thr, LogRecord *lr, MachineState *ms)
{
	LogRecordSignal *lrs = dynamic_cast<LogRecordSignal *>(lr);
	if (!lrs)
		throw ReplayFailedException("wanted a signal record, got %s",
					    lr->name());
	if (lrs->signr != 11)
		throw NotImplementedException("Only handle SIGSEGV, got %d",
					      lrs->signr);
	if (ms->addressSpace->isReadable(lrs->virtaddr, 1, thr))
		throw ReplayFailedException("got a segv at %lx, but that location is readable?",
					    lrs->virtaddr);
	/* Can't actually do much with this, because we pick up the
	   Valgrind sighandlers when we start.  Oh well. */
#if 0
	if (ms->signalHandlers.handlers[11].sa_handler != SIG_DFL)
		throw NotImplementedException("don't handle custom signal handlers");
#endif
	printf("Crash in thread %d\n", thr->tid._tid());
	thr->crashed = true;
}

InterpretResult SignalEvent::fake(Thread *thr, MachineState *ms, LogRecord **lr)
{
	if (lr)
		*lr = new LogRecordSignal(thr->tid, thr->regs.regs.guest_RIP, signr, 0, virtaddr);
	thr->crashed = true;
	return InterpretResultCrash;
}
