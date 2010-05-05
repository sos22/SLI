#include "sli.h"

void RdtscEvent::replay(Thread *thr, LogRecord *lr, MachineState *ms)
{
	LogRecordRdtsc *lrr = dynamic_cast<LogRecordRdtsc *>(lr);
	if (!lrr)
		throw ReplayFailedException("wanted a rdtsc, got %s",
					    lr->name());
	thr->temporaries[tmp].lo.v = lrr->tsc;
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

void StoreEvent::replay(Thread *thr, LogRecord *lr, MachineState *ms)
{
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
}

void LoadEvent::replay(Thread *thr, LogRecord *lr, MachineState *ms)
{
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
		      LogReader::ptr *outPtr)
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
