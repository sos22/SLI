/* This file is somewhat misnamed: it includes both replay and record
 * methods on events. */
#include "sli.h"

static unsigned long operator ==(expression_result a, expression_result b)
{
	return a.lo == b.lo && a.hi == b.hi;
}

static unsigned long operator !=(expression_result a, expression_result b)
{
	return !(a == b);
}

ThreadEvent *RdtscEvent::replay(LogRecord *lr, MachineState **ms,
					  bool &, LogReaderPtr)
{
	LogRecordRdtsc *lrr = dynamic_cast<LogRecordRdtsc *>(lr);
	if (!lrr)
		throw ReplayFailedException("wanted a rdtsc, got %s",
					    lr->name());
	Thread *thr = (*ms)->findThread(this->tid);
	if (tmp.isTemp())
		thr->temporaries[tmp.asTemp()].lo = lrr->tsc;
	else
		thr->regs.set_reg(tmp.asReg() / 8, lrr->tsc);

	return NULL;
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
		if (tmp.isTemp())
			thr->temporaries[tmp.asTemp()] = lrl->value;
		else
			thr->regs.set_reg(tmp.asReg() / 8, lrl->value.lo);
	} else {
		checkSegv(lr, addr);
	}

	return NULL;
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


