#include <sys/types.h>
#include <sys/fcntl.h>
#include <stdlib.h>
#include <unistd.h>

#include "sli.h"

typedef unsigned long Word;
typedef unsigned long UWord;
typedef unsigned char Bool;

typedef struct sigaction sigaction_t;

#include "ppres.h"

LogFile *LogFile::open(const char *path, LogReaderPtr *initial_ptr)
{
	int fd;
	fd = ::open(path, O_RDONLY);
	if (fd < 0)
		return NULL;

	LogFile *work = new LogFile();
	work->fd = fd;
	*initial_ptr = work->mkPtr(0, 0);
	return work;
}

LogFile *LogFile::truncate(LogReaderPtr eof)
{
	LogFile *work;
	work = new LogFile();
	work->forcedEof = unwrapPtr(eof);
	work->fd = fd;
	return work;
}

LogFile::~LogFile()
{
	close(fd);
}

LogRecord<unsigned long> *LogFile::read(LogReaderPtr _startPtr, LogReaderPtr *_nextPtr) const
{
	struct record_header rh;
	_ptr startPtr = unwrapPtr(_startPtr);

	assert(startPtr.valid);
skip:
	if (forcedEof.valid && startPtr >= forcedEof)
		return NULL;
	if (pread(fd, &rh, sizeof(rh), startPtr.off) <= 0)
		return NULL;
	ThreadId tid(rh.tid);
	*_nextPtr = mkPtr(startPtr.off + rh.size, startPtr.record_nr+1);
	switch (rh.cls) {
	case RECORD_footstep: {
		footstep_record<unsigned long> fr;
		int r = pread(fd, &fr, sizeof(fr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordFootstep<unsigned long>(tid,
							    fr.rip,
							    fr.FOOTSTEP_REG_0_NAME,
							    fr.FOOTSTEP_REG_1_NAME,
							    fr.FOOTSTEP_REG_2_NAME,
							    fr.FOOTSTEP_REG_3_NAME,
							    fr.FOOTSTEP_REG_4_NAME);
	}
	case RECORD_syscall: {
		syscall_record<unsigned long> sr;
		int r = pread(fd, &sr, sizeof(sr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordSyscall<unsigned long>(tid,
							   sr.syscall_nr & 0xffffffff,
							   sr.syscall_res._isError ? -(long)sr.syscall_res._val : sr.syscall_res._val,
							   sr.arg1,
							   sr.arg2,
							   sr.arg3);
	}
	case RECORD_memory: {
		memory_record<unsigned long> mr;
		int r = pread(fd, &mr, sizeof(mr), startPtr.off + sizeof(rh));
		void *buf = malloc(rh.size - sizeof(mr) - sizeof(rh));
		r = pread(fd, buf, rh.size - sizeof(mr) - sizeof(rh),
			  startPtr.off + sizeof(rh) + sizeof(mr));
		(void)r;
		return new LogRecordMemory<unsigned long>(tid,
							  rh.size - sizeof(mr) - sizeof(rh),
							  (unsigned long)mr.ptr,
							  buf);
	}
	case RECORD_rdtsc: {
		rdtsc_record<unsigned long> rr;
		int r = pread(fd, &rr, sizeof(rr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordRdtsc<unsigned long>(tid, rr.stashed_tsc);
	}
	case RECORD_mem_read: {
		mem_read_record<unsigned long> mrr;
		int r = pread(fd, &mrr, sizeof(mrr), startPtr.off + sizeof(rh));
		expression_result<unsigned long> val;
		unsigned long b[2];
		memset(b, 0, sizeof(b));
		r = pread(fd, b, rh.size - sizeof(mrr) - sizeof(rh),
			  startPtr.off + sizeof(rh) + sizeof(mrr));
		val.lo = b[0];
		val.hi = b[1];
		return new LogRecordLoad<unsigned long>(tid,
							rh.size - sizeof(mrr) - sizeof(rh),
							mrr.ptr,
							val);
	}
	case RECORD_mem_write: {
		mem_write_record<unsigned long> mwr;
		int r = pread(fd, &mwr, sizeof(mwr), startPtr.off + sizeof(rh));
		expression_result<unsigned long> val;
		unsigned long b[2];
		memset(b, 0, sizeof(b));
		r = pread(fd, b, rh.size - sizeof(mwr) - sizeof(rh),
			  startPtr.off + sizeof(rh) + sizeof(mwr));
		val.lo = b[0];
		val.hi = b[1];
		(void)r;
		return new LogRecordStore<unsigned long>(tid,
							 rh.size - sizeof(mwr) - sizeof(rh),
							 mwr.ptr,
							 val);
	}

	case RECORD_new_thread:
	case RECORD_thread_blocking:
	case RECORD_thread_unblocked:
	{
		/* Don't need these in the current world order */
		startPtr = unwrapPtr(*_nextPtr);
		goto skip;
	}

	case RECORD_signal: {
		signal_record<unsigned long> sr;
		int r = pread(fd, &sr, sizeof(sr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordSignal<unsigned long>(tid, sr.rip, sr.signo, sr.err,
							  sr.virtaddr);
	}
		
	case RECORD_allocate_memory: {
		allocate_memory_record<unsigned long> amr;
		int r = pread(fd, &amr, sizeof(amr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordAllocateMemory<unsigned long>(tid,
								  amr.start,
								  amr.size,
								  amr.prot,
								  amr.flags);
	}
	case RECORD_initial_registers: {
		VexGuestAMD64State regs;
		int r = pread(fd, &regs, sizeof(regs), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordInitialRegisters<unsigned long>(tid, regs);
	}
	case RECORD_initial_brk: {
		initial_brk_record<unsigned long> ibr;
		int r = pread(fd, &ibr, sizeof(ibr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordInitialBrk<unsigned long>(tid, ibr.initial_brk);
	}
	case RECORD_initial_sighandlers: {
		initial_sighandlers_record<unsigned long> isr;
		int r = pread(fd, &isr, sizeof(isr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordInitialSighandlers<unsigned long>(tid, isr.handlers);
	}
	case RECORD_vex_thread_state: {
		vex_thread_state_record<unsigned long> *vtsr;
		vtsr = (vex_thread_state_record<unsigned long> *)malloc(rh.size - sizeof(rh));
		int r = pread(fd, vtsr, rh.size - sizeof(rh), startPtr.off + sizeof(rh));
		(void)r;
		expression_result_array<unsigned long> era;
		era.setSize((rh.size - sizeof(rh) - sizeof(*vtsr)) / 16);
		for (unsigned x = 0; x < era.nr_entries; x++) {
			era[x].lo = vtsr->temporaries[x * 2];
			era[x].hi = vtsr->temporaries[x * 2 + 1];
		}
		unsigned sn = vtsr->statement_nr;
		free(vtsr);
		return new LogRecordVexThreadState<unsigned long>(tid, sn, era);
	}

	default:
		abort();
	}
}


template <typename ait>
LogRecord<ait>::~LogRecord()
{
}

#define MK_LOGREADER(t)				\
	template LogRecord<t>::~LogRecord()
