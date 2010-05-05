#define _XOPEN_SOURCE 500
#include <sys/types.h>
#include <sys/fcntl.h>
#include <stdlib.h>
#include <unistd.h>

#include "sli.h"

typedef unsigned long Word;
typedef unsigned long UWord;
typedef unsigned char Bool;
typedef struct {
	UWord _val;
	Bool  _isError;
} SysRes;

typedef struct sigaction sigaction_t;

#include "ppres.h"

LogReader *LogReader::open(const char *path, LogReader::ptr *initial_ptr)
{
	int fd;
	fd = ::open(path, O_RDONLY);
	if (fd < 0)
		return NULL;

	LogReader *work = new LogReader();
	work->fd = fd;
	*initial_ptr = ptr(0, 0);
	return work;
}

LogReader::~LogReader()
{
	close(fd);
}

LogRecord *LogReader::read(LogReader::ptr startPtr, LogReader::ptr *nextPtr) const
{
	struct record_header rh;

skip:
	if (pread(fd, &rh, sizeof(rh), startPtr.offset()) <= 0)
		return NULL;
	ThreadId tid(rh.tid);
	*nextPtr = ptr(startPtr.offset() + rh.size, startPtr.record_nr+1);
	switch (rh.cls) {
	case RECORD_footstep: {
		footstep_record fr;
		int r = pread(fd, &fr, sizeof(fr), startPtr.offset() + sizeof(rh));
		(void)r;
		return new LogRecordFootstep(tid,
					     fr.rip,
					     fr.FOOTSTEP_REG_0_NAME,
					     fr.FOOTSTEP_REG_1_NAME,
					     fr.FOOTSTEP_REG_2_NAME,
					     fr.FOOTSTEP_REG_3_NAME,
					     fr.FOOTSTEP_REG_4_NAME);
	}
	case RECORD_syscall: {
		syscall_record sr;
		int r = pread(fd, &sr, sizeof(sr), startPtr.offset() + sizeof(rh));
		(void)r;
		return new LogRecordSyscall(tid,
					    sr.syscall_nr,
					    sr.syscall_res._isError ? -(long)sr.syscall_res._val : sr.syscall_res._val,
					    sr.arg1,
					    sr.arg2,
					    sr.arg3);
	}
	case RECORD_memory: {
		memory_record mr;
		int r = pread(fd, &mr, sizeof(mr), startPtr.offset() + sizeof(rh));
		void *buf = malloc(rh.size - sizeof(mr) - sizeof(rh));
		r = pread(fd, buf, rh.size - sizeof(mr) - sizeof(rh),
			  startPtr.offset() + sizeof(rh) + sizeof(mr));
		(void)r;
		return new LogRecordMemory(tid,
					   rh.size - sizeof(mr) - sizeof(rh),
					   (unsigned long)mr.ptr,
					   buf);
	}
	case RECORD_rdtsc: {
		rdtsc_record rr;
		int r = pread(fd, &rr, sizeof(rr), startPtr.offset() + sizeof(rh));
		(void)r;
		return new LogRecordRdtsc(tid, rr.stashed_tsc);
	}
	case RECORD_mem_read: {
		mem_read_record mrr;
		int r = pread(fd, &mrr, sizeof(mrr), startPtr.offset() + sizeof(rh));
		void *buf = malloc(rh.size - sizeof(mrr) - sizeof(rh));
		r = pread(fd, buf, rh.size - sizeof(mrr) - sizeof(rh),
			  startPtr.offset() + sizeof(rh) + sizeof(mrr));
		(void)r;
		return new LogRecordLoad(tid,
					 rh.size - sizeof(mrr) - sizeof(rh),
					 mrr.ptr,
					 buf);
	}
	case RECORD_mem_write: {
		mem_write_record mwr;
		int r = pread(fd, &mwr, sizeof(mwr), startPtr.offset() + sizeof(rh));
		void *buf = malloc(rh.size - sizeof(mwr) - sizeof(rh));
		r = pread(fd, buf, rh.size - sizeof(mwr) - sizeof(rh),
			  startPtr.offset() + sizeof(rh) + sizeof(mwr));
		(void)r;
		return new LogRecordStore(tid,
					  rh.size - sizeof(mwr) - sizeof(rh),
					  mwr.ptr,
					  buf);
	}

	case RECORD_new_thread:
	case RECORD_thread_blocking:
	case RECORD_thread_unblocked:
	{
		/* Don't need these in the current world order */
		startPtr = *nextPtr;
		goto skip;
	}

	case RECORD_signal: {
		signal_record sr;
		int r = pread(fd, &sr, sizeof(sr), startPtr.offset() + sizeof(rh));
		(void)r;
		return new LogRecordSignal(tid, sr.rip, sr.signo, sr.err,
					   sr.virtaddr);
	}
		
	case RECORD_allocate_memory: {
		allocate_memory_record amr;
		int r = pread(fd, &amr, sizeof(amr), startPtr.offset() + sizeof(rh));
		(void)r;
		return new LogRecordAllocateMemory(tid,
						   amr.start,
						   amr.size,
						   amr.prot,
						   amr.flags);
	}
	case RECORD_initial_registers: {
		VexGuestAMD64State regs;
		int r = pread(fd, &regs, sizeof(regs), startPtr.offset() + sizeof(rh));
		(void)r;
		return new LogRecordInitialRegisters(tid, regs);
	}
	case RECORD_initial_brk: {
		initial_brk_record ibr;
		int r = pread(fd, &ibr, sizeof(ibr), startPtr.offset() + sizeof(rh));
		(void)r;
		return new LogRecordInitialBrk(tid, ibr.initial_brk);
	}
	case RECORD_initial_sighandlers: {
		initial_sighandlers_record isr;
		int r = pread(fd, &isr, sizeof(isr), startPtr.offset() + sizeof(rh));
		(void)r;
		return new LogRecordInitialSighandlers(tid, isr.handlers);
	}

	default:
		abort();
	}
}


LogRecord::~LogRecord()
{
}

