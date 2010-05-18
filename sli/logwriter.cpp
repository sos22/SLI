#include <sys/types.h>
#include <sys/fcntl.h>
#include <err.h>
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

void *LogRecord::marshal(unsigned cls, unsigned psize, unsigned *sz, void **r) const
{
	*sz = sizeof(record_header) + psize;
	*r = malloc(*sz);
	((record_header *)*r)->cls = cls;
	((record_header *)*r)->size = *sz;
	((record_header *)*r)->tid = thread()._tid();
	return (void *)((unsigned long)*r + sizeof(record_header));
}

void *LogRecordFootstep::marshal(unsigned *sz) const
{
	void *r;
	footstep_record *fr = (footstep_record *)LogRecord::marshal(RECORD_footstep, sizeof(footstep_record), sz, &r);
	fr->rip = rip;
	fr->FOOTSTEP_REG_0_NAME = reg0;
	fr->FOOTSTEP_REG_1_NAME = reg1;
	fr->FOOTSTEP_REG_2_NAME = reg2;
	fr->FOOTSTEP_REG_3_NAME = reg3;
	fr->FOOTSTEP_REG_4_NAME = reg4;
	return r;
}

void *LogRecordSyscall::marshal(unsigned *sz) const
{
	void *r;
	syscall_record *sr = (syscall_record *)LogRecord::marshal(RECORD_syscall, sizeof(syscall_record), sz, &r);
	sr->syscall_nr = sysnr;
	if ((long)res >= 0 || (long)res < -4096) {
		sr->syscall_res._isError = false;
		sr->syscall_res._val = res;
	} else {
		sr->syscall_res._isError = true;
		sr->syscall_res._val = -res;
	}
	sr->arg1 = arg1;
	sr->arg2 = arg2;
	sr->arg3 = arg3;
	return r;
}

void *LogRecordMemory::marshal(unsigned *sz) const
{
	void *r;
	memory_record *mr = (memory_record *)LogRecord::marshal(RECORD_memory,
								sizeof(memory_record) + size,
								sz,
								&r);
	mr->ptr = (void *)start;
	memcpy(mr + 1, contents, size);
	return r;
}

void *LogRecordRdtsc::marshal(unsigned *sz) const
{
	void *r;
	rdtsc_record *rr = (rdtsc_record *)LogRecord::marshal(RECORD_rdtsc,
							      sizeof(rdtsc_record),
							      sz,
							      &r);
	rr->stashed_tsc = tsc;
	return r;
}

void *LogRecordLoad::marshal(unsigned *sz) const
{
	void *r;
	mem_read_record *lr = (mem_read_record *)LogRecord::marshal(RECORD_mem_read,
								    sizeof(*lr) + size,
								    sz,
								    &r);
	lr->ptr = ptr;
	memcpy(lr + 1, buf, size);
	return r;
}

void *LogRecordStore::marshal(unsigned *sz) const
{
	void *r;
	mem_write_record *sr = (mem_write_record *)LogRecord::marshal(RECORD_mem_write,
								      sizeof(*sr) + size,
								      sz,
								      &r);
	sr->ptr = ptr;
	memcpy(sr + 1, buf, size);
	return r;
}

void *LogRecordSignal::marshal(unsigned *sz) const
{
	void *r;
	signal_record *sr = (signal_record *)LogRecord::marshal(RECORD_signal,
								sizeof(*sr),
								sz,
								&r);
	sr->rip = rip;
	sr->signo = signr;
	sr->err = err;
	sr->virtaddr = virtaddr;
	return r;
}

void *LogRecordAllocateMemory::marshal(unsigned *sz) const
{
	void *r;
	allocate_memory_record *amr = (allocate_memory_record *)LogRecord::marshal(RECORD_allocate_memory,
										   sizeof(*amr),
										   sz,
										   &r);
	amr->start = start;
	amr->size = size;
	amr->prot = prot;
	amr->flags = flags;
	return r;
}

void *LogRecordInitialRegisters::marshal(unsigned *sz) const
{
	void *r;
	VexGuestAMD64State *s = (VexGuestAMD64State *)LogRecord::marshal(RECORD_initial_registers,
									 sizeof(*s),
									 sz,
									 &r);
	*s = regs;
	return r;
}

void *LogRecordInitialBrk::marshal(unsigned *sz) const
{
	void *r;
	initial_brk_record *ibr = (initial_brk_record *)LogRecord::marshal(RECORD_initial_brk,
									   sizeof(*ibr),
									   sz,
									   &r);
	ibr->initial_brk = brk;
	return r;
}

void *LogRecordInitialSighandlers::marshal(unsigned *sz) const
{
	void *r;
	initial_sighandlers_record *isr =
		(initial_sighandlers_record *)LogRecord::marshal(RECORD_initial_sighandlers,
								 sizeof(*isr),
								 sz,
								 &r);
	memcpy(isr->handlers, handlers, sizeof(isr->handlers));
	return r;
}

void *LogRecordVexThreadState::marshal(unsigned *sz) const
{
	void *r;
	vex_thread_state_record *vtsr =
		(vex_thread_state_record *)LogRecord::marshal(RECORD_vex_thread_state,
							      sizeof(*vtsr) + 16 * tmp.nr_entries,
							      sz,
							      &r);
	vtsr->statement_nr = statement_nr;
	for (unsigned x = 0; x < tmp.nr_entries; x++) {
		vtsr->temporaries[x*2] = tmp.arr[x].lo;
		vtsr->temporaries[x*2+1] = tmp.arr[x].hi;
	}
	return r;
}

LogFileWriter *LogFileWriter::open(const char *path)
{
	int fd;
	fd = ::open(path, O_WRONLY|O_APPEND|O_CREAT|O_EXCL, 0666);
	if (fd < 0)
		return NULL;
	LogFileWriter *work = new LogFileWriter();
	work->fd = fd;
	return work;
}

LogFileWriter::~LogFileWriter()
{
	close(fd);
}

void LogFileWriter::append(const LogRecord &lr)
{
	void *b;
	unsigned s;

	b = lr.marshal(&s);
	int this_time;
	for (unsigned written = 0; written < s; written += this_time) {
		this_time = write(fd, (const void *)((unsigned long)b + written), s - written);
		if (this_time < 0)
			err(1, "writing to logfile");
		if (this_time == 0)
			errx(1, "eof writing logfile?");
	}
	free(b);
}

void LogRecordVexThreadState::visit(HeapVisitor &hv) const
{
	tmp.visit(hv);
}

static void visit_special_keeper(const void *_ctxt, HeapVisitor &hv)
{
	const LogRecordVexThreadState *ctxt = *(const LogRecordVexThreadState **)_ctxt;
	ctxt->visit(hv);
}

LogRecordVexThreadState::LogRecordVexThreadState(ThreadId tid, unsigned _statement_nr,
						 expression_result_array<unsigned long> _tmp)
		: LogRecord(tid),
		  root((void **)&root_data),
		  tmp(_tmp),
		  statement_nr(_statement_nr)
{
	static VexAllocType vat = {
	nbytes: sizeof(LogRecordVexThreadState *),
	gc_visit: visit_special_keeper,
	destruct: NULL,
	name: "LogRecordVexThreadState keeper"
	};
	root_data = (LogRecordVexThreadState **)__LibVEX_Alloc(&vat);
	*root_data = this;	
}

void SignalHandlers::dumpSnapshot(LogWriter *lw) const
{
	lw->append(LogRecordInitialSighandlers(ThreadId(0), handlers));
}
