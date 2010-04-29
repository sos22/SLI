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

#include "ppres.h"

LogReader *LogReader::open(const char *path, LogReader::ptr *initial_ptr)
{
	int fd;
	fd = ::open(path, O_RDONLY);
	if (fd < 0)
		return NULL;

	LogReader *work = new LogReader();
	work->fd = fd;
	*initial_ptr = ptr(0);
	return work;
}

LogReader::~LogReader()
{
	close(fd);
}

LogRecord *LogReader::read(LogReader::ptr startPtr, LogReader::ptr *nextPtr) const
{
	struct record_header rh;

	if (pread(fd, &rh, sizeof(rh), startPtr.offset()) <= 0)
		return NULL;
	ThreadId tid(rh.tid);
	*nextPtr = ptr(startPtr.offset() + rh.size);
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
	default:
		abort();
	}
}


LogRecord::~LogRecord()
{
}

