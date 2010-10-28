#include <sys/types.h>
#include <sys/fcntl.h>
#include <stdlib.h>
#include <unistd.h>

#include "sli.h"

typedef unsigned long Word;
typedef unsigned long UWord;
typedef unsigned char Bool;

typedef struct sigaction sigaction_t;

LogReader *LogReader::open(const char *path, LogReaderPtr *initial_ptr)
{
	int fd;
	fd = ::open(path, O_RDONLY);
	if (fd < 0)
		return NULL;

	LogReader *work = new LogReader();
	work->fd = fd;
	*initial_ptr = LogReaderPtr(0, 0);
	return work;
}

LogReader *LogReader::truncate(LogReaderPtr eof)
{
	LogReader *work;
	work = new LogReader();
	work->forcedEof = eof;
	work->fd = fd;
	return work;
}

LogReader::~LogReader()
{
	close(fd);
}

ssize_t
LogReader::buffered_pread(void *output, size_t output_size, off_t start_offset) const
{
	off_t end_offset = start_offset + output_size;
	off_t next_offset = start_offset;

	while (next_offset != end_offset) {
		if (next_offset >= buffer_start && next_offset < buffer_end) {
			/* Grab as much as possible from the buffer */
			unsigned from_buffer;
			if (end_offset > buffer_end)
				from_buffer = buffer_end - next_offset;
			else
				from_buffer = end_offset - next_offset;
			memcpy((void *)((unsigned long)output + next_offset - start_offset),
			       (void *)((unsigned long)buffer + next_offset - buffer_start),
			       from_buffer);
			next_offset += from_buffer;
			if (next_offset == end_offset)
				break;
		}

		/* Replenish the buffer */
		buffer_start = next_offset;
		ssize_t s = pread(fd, buffer, sizeof(buffer), buffer_start);
		if (s < 0) {
			if (next_offset == start_offset)
				return s;
			else
				break;
		}
		if (s == 0)
			break;
		buffer_end = buffer_start + s;
	}

	return next_offset - start_offset;
}

LogRecord *LogReader::read(LogReaderPtr _startPtr, LogReaderPtr *_nextPtr) const
{
	struct record_header rh;
	LogReaderPtr startPtr = _startPtr;

	assert(startPtr.valid);
skip:
	if (forcedEof.valid && startPtr.off >= forcedEof.off)
		return NULL;
	if (buffered_pread(&rh, sizeof(rh), startPtr.off) <= 0)
		return NULL;
	ThreadId tid(rh.tid);
	*_nextPtr = LogReaderPtr(startPtr.off + rh.size, startPtr.record_nr+1);
	if (startPtr.off / 1000000 != (startPtr.off + rh.size) / 1000000)
		printf("Read %ldM\n", startPtr.off / 1000000);

	switch (rh.cls) {
	case RECORD_footstep: {
		startPtr = *_nextPtr;
		goto skip;
	}
	case RECORD_syscall: {
		syscall_record<unsigned long> sr;
		int r = buffered_pread(&sr, sizeof(sr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordSyscall(tid,
							   sr.syscall_nr & 0xffffffff,
							   sr.syscall_res._isError ? -(long)sr.syscall_res._val : sr.syscall_res._val,
							   sr.arg1,
							   sr.arg2,
							   sr.arg3);
	}
	case RECORD_memory: {
		memory_record<unsigned long> mr;
		unsigned s;
		int r = buffered_pread(&mr, sizeof(mr), startPtr.off + sizeof(rh));
		s = rh.size - sizeof(mr) - sizeof(rh);
		void *buf = alloca(s);
		r = buffered_pread(buf, s, startPtr.off + sizeof(rh) + sizeof(mr));
		(void)r;
		unsigned long *b = (unsigned long *)malloc(sizeof(unsigned long) * s);
		for (unsigned x = 0; x < s; x++)
			b[x] = ((unsigned char *)buf)[x];
		return new LogRecordMemory(tid,
							  rh.size - sizeof(mr) - sizeof(rh),
							  (unsigned long)mr.ptr,
							  b);
	}
	case RECORD_rdtsc: {
		rdtsc_record<unsigned long> rr;
		int r = buffered_pread(&rr, sizeof(rr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordRdtsc(tid, rr.stashed_tsc);
	}
	case RECORD_mem_read: {
		mem_read_record<unsigned long> mrr;
		int r = buffered_pread(&mrr, sizeof(mrr), startPtr.off + sizeof(rh));
		expression_result val;
		unsigned long b[2];
		memset(b, 0, sizeof(b));
		r = buffered_pread(b, rh.size - sizeof(mrr) - sizeof(rh),
				   startPtr.off + sizeof(rh) + sizeof(mrr));
		val.lo = b[0];
		val.hi = b[1];
		return new LogRecordLoad(tid,
					 rh.size - sizeof(mrr) - sizeof(rh),
					 mrr.ptr,
					 val);
	}
	case RECORD_mem_write: {
		mem_write_record<unsigned long> mwr;
		int r = buffered_pread(&mwr, sizeof(mwr), startPtr.off + sizeof(rh));
		expression_result val;
		unsigned long b[2];
		memset(b, 0, sizeof(b));
		r = buffered_pread(b, rh.size - sizeof(mwr) - sizeof(rh),
				   startPtr.off + sizeof(rh) + sizeof(mwr));
		val.lo = b[0];
		val.hi = b[1];
		(void)r;
		return new LogRecordStore(tid,
					  rh.size - sizeof(mwr) - sizeof(rh),
					  mwr.ptr,
					  val);
	}

	case RECORD_new_thread:
	case RECORD_thread_blocking:
	case RECORD_thread_unblocked:
	{
		/* Don't need these in the current world order */
		startPtr = *_nextPtr;
		goto skip;
	}

	case RECORD_signal: {
		signal_record<unsigned long> sr;
		int r = buffered_pread(&sr, sizeof(sr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordSignal(tid, sr.rip, sr.signo, sr.err,
							  sr.virtaddr);
	}
		
	case RECORD_allocate_memory: {
		allocate_memory_record<unsigned long> amr;
		int r = buffered_pread(&amr, sizeof(amr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordAllocateMemory(tid,
								  amr.start,
								  amr.size,
								  amr.prot,
								  amr.flags);
	}
	case RECORD_initial_registers: {
		VexGuestAMD64State regs;
		int r = buffered_pread(&regs, sizeof(regs), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordInitialRegisters(tid, regs);
	}
	case RECORD_initial_brk: {
		initial_brk_record<unsigned long> ibr;
		int r = buffered_pread(&ibr, sizeof(ibr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordInitialBrk(tid, ibr.initial_brk);
	}
	case RECORD_initial_sighandlers: {
		initial_sighandlers_record<unsigned long> isr;
		int r = buffered_pread(&isr, sizeof(isr), startPtr.off + sizeof(rh));
		(void)r;
		return new LogRecordInitialSighandlers(tid, isr.handlers);
	}
	case RECORD_vex_thread_state_1: {
		vex_thread_state_record_1<unsigned long> *vtsr;
		vtsr = (vex_thread_state_record_1<unsigned long> *)alloca(rh.size - sizeof(rh));
		int r = buffered_pread(vtsr, rh.size - sizeof(rh), startPtr.off + sizeof(rh));
		(void)r;
		expression_result_array era;
		unsigned sz = (rh.size - sizeof(rh) - sizeof(*vtsr)) / 16;
		era.setSize(sz);
		for (unsigned x = 0; x < sz; x++) {
			era[x].lo = vtsr->temporaries[x * 2];
			era[x].hi = vtsr->temporaries[x * 2 + 1];
		}
		unsigned sn = vtsr->statement_nr;
		return new LogRecordVexThreadState(tid, 0, sn, era);
	}
	case RECORD_vex_thread_state_2: {
		vex_thread_state_record_2<unsigned long> *vtsr;
		vtsr = (vex_thread_state_record_2<unsigned long> *)alloca(rh.size - sizeof(rh));
		int r = buffered_pread(vtsr, rh.size - sizeof(rh), startPtr.off + sizeof(rh));
		(void)r;
		expression_result_array era;
		unsigned sz = (rh.size - sizeof(rh) - sizeof(*vtsr)) / 16;
		era.setSize(sz);
		for (unsigned x = 0; x < sz; x++) {
			era[x].lo = vtsr->temporaries[x * 2];
			era[x].hi = vtsr->temporaries[x * 2 + 1];
		}
		unsigned sn = vtsr->statement_nr;
		return new LogRecordVexThreadState(tid, vtsr->translation_origin, sn, era);
	}

	default:
		abort();
	}
}


#define MK_LOGREADER(t)				

