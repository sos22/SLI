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
		pread(fd, &fr, sizeof(fr), startPtr.offset() + sizeof(rh));
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
		pread(fd, &sr, sizeof(sr), startPtr.offset() + sizeof(rh));
		return new LogRecordSyscall(tid,
					    sr.syscall_nr,
					    sr.syscall_res._isError ? -(long)sr.syscall_res._val : sr.syscall_res._val,
					    sr.arg1,
					    sr.arg2,
					    sr.arg3);
	}
	case RECORD_memory: {
		memory_record mr;
		pread(fd, &mr, sizeof(mr), startPtr.offset() + sizeof(rh));
		void *buf = malloc(rh.size - sizeof(mr) - sizeof(rh));
		pread(fd, buf, rh.size - sizeof(mr) - sizeof(rh),
		      startPtr.offset() + sizeof(rh) + sizeof(mr));
		return new LogRecordMemory(tid,
					   rh.size - sizeof(mr) - sizeof(rh),
					   (unsigned long)mr.ptr,
					   buf);
	}
	case RECORD_rdtsc: {
		rdtsc_record rr;
		pread(fd, &rr, sizeof(rr), startPtr.offset() + sizeof(rh));
		return new LogRecordRdtsc(tid, rr.stashed_tsc);
	}
	case RECORD_mem_read:
	case RECORD_mem_write:
	case RECORD_new_thread:
	case RECORD_thread_blocking:
	case RECORD_thread_unblocked:
	{
		/* Don't need these in the current world order */
		startPtr = *nextPtr;
		goto skip;
	}
	case RECORD_allocate_memory: {
		allocate_memory_record amr;
		pread(fd, &amr, sizeof(amr), startPtr.offset() + sizeof(rh));
		return new LogRecordAllocateMemory(tid,
						   amr.start,
						   amr.size,
						   amr.prot,
						   amr.flags);
	}
	case RECORD_initial_registers: {
		VexGuestAMD64State regs;
		pread(fd, &regs, sizeof(regs), startPtr.offset() + sizeof(rh));
		return new LogRecordInitialRegisters(tid, regs);
	}
	case RECORD_initial_brk: {
		initial_brk_record ibr;
		pread(fd, &ibr, sizeof(ibr), startPtr.offset() + sizeof(rh));
		return new LogRecordInitialBrk(tid, ibr.initial_brk);
	}
	case RECORD_initial_sighandlers: {
		initial_sighandlers_record isr;
		pread(fd, &isr, sizeof(isr), startPtr.offset() + sizeof(rh));
		return new LogRecordInitialSighandlers(tid, isr.handlers);
	}

	default:
		abort();
	}
}


LogRecord::~LogRecord()
{
}

