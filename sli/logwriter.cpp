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
	memset(*r, 0, *sz);
	((record_header *)*r)->cls = cls;
	((record_header *)*r)->size = *sz;
	((record_header *)*r)->tid = thread()._tid();
	return (void *)((unsigned long)*r + sizeof(record_header));
}

unsigned
LogRecordFootstep::marshal_size() const
{
	return sizeof(footstep_record<unsigned long>);
}

void *LogRecordFootstep::marshal(unsigned *sz) const
{
	void *r;
	footstep_record<unsigned long> *fr = (footstep_record<unsigned long> *)LogRecord::marshal(RECORD_footstep, sizeof(footstep_record<unsigned long>), sz, &r);
	fr->rip = rip;
	fr->FOOTSTEP_REG_0_NAME = reg0;
	fr->FOOTSTEP_REG_1_NAME = reg1;
	fr->FOOTSTEP_REG_2_NAME = reg2;
	fr->FOOTSTEP_REG_3_NAME = reg3;
	fr->FOOTSTEP_REG_4_NAME = reg4;
	return r;
}

unsigned
LogRecordSyscall::marshal_size() const
{
	return sizeof(syscall_record<unsigned long>);
}

void *LogRecordSyscall::marshal(unsigned *sz) const
{
	void *r;
	syscall_record<unsigned long> *sr = (syscall_record<unsigned long> *)LogRecord::marshal(RECORD_syscall, sizeof(syscall_record<unsigned long>), sz, &r);
	sr->syscall_nr = sysnr;
	if ((long)force(res) >= 0 || (long)force(res) < -4096) {
		sr->syscall_res._isError = false;
		sr->syscall_res._val = force(res);
	} else {
		sr->syscall_res._isError = true;
		sr->syscall_res._val = -force(res);
	}
	sr->arg1 = arg1;
	sr->arg2 = arg2;
	sr->arg3 = arg3;
	return r;
}

unsigned
LogRecordMemory::marshal_size() const
{
	return sizeof(memory_record<unsigned long>) + size;
}

void *LogRecordMemory::marshal(unsigned *sz) const
{
	void *r;
	unsigned x;
	memory_record<unsigned long> *mr = (memory_record<unsigned long> *)LogRecord::marshal(RECORD_memory,
									       sizeof(memory_record<unsigned long>) + size,
									       sz,
									       &r);
	mr->ptr = start;
	for (x = 0; x < size; x++)
		((unsigned char *)(mr + 1))[x] = force(contents[x]);
	return r;
}

unsigned
LogRecordRdtsc::marshal_size() const
{
	return sizeof(rdtsc_record<unsigned long>);
}


void *LogRecordRdtsc::marshal(unsigned *sz) const
{
	void *r;
	rdtsc_record<unsigned long> *rr = (rdtsc_record<unsigned long> *)LogRecord::marshal(RECORD_rdtsc,
									     sizeof(rdtsc_record<unsigned long>),
									     sz,
									     &r);
	rr->stashed_tsc = tsc;
	return r;
}

unsigned
LogRecordLoad::marshal_size() const
{
	return sizeof(mem_read_record<unsigned long>) + size;
}

void *LogRecordLoad::marshal(unsigned *sz) const
{
	void *r;
	mem_read_record<unsigned long> *lr = (mem_read_record<unsigned long> *)LogRecord::marshal(RECORD_mem_read,
												  sizeof(*lr) + size,
												  sz,
												  &r);
	unsigned long v[2];
	lr->ptr = ptr;
	v[0] = force(value.lo);
	v[1] = force(value.hi);
	memcpy(lr + 1, v, size);
	return r;
}

unsigned
LogRecordStore::marshal_size() const
{
	return sizeof(mem_write_record<unsigned long>) + size;
}

void *LogRecordStore::marshal(unsigned *sz) const
{
	void *r;
	mem_write_record<unsigned long> *sr =
		(mem_write_record<unsigned long> *)LogRecord::marshal(RECORD_mem_write,
								      sizeof(*sr) + size,
								      sz,
								      &r);
	unsigned long v[2];
	sr->ptr = ptr;
	v[0] = force(value.lo);
	v[1] = force(value.hi);
	memcpy(sr + 1, v, size);
	return r;
}

unsigned
LogRecordSignal::marshal_size() const
{
	return sizeof(signal_record<unsigned long>);
}


void *LogRecordSignal::marshal(unsigned *sz) const
{
	void *r;
	signal_record<unsigned long> *sr = (signal_record<unsigned long> *)LogRecord::marshal(RECORD_signal,
									       sizeof(*sr),
									       sz,
									       &r);
	sr->rip = rip;
	sr->signo = signr;
	sr->err = err;
	sr->virtaddr = virtaddr;
	return r;
}

unsigned
LogRecordAllocateMemory::marshal_size() const
{
	return sizeof(allocate_memory_record<unsigned long>);
}


void *LogRecordAllocateMemory::marshal(unsigned *sz) const
{
	void *r;
	allocate_memory_record<unsigned long> *amr = (allocate_memory_record<unsigned long> *)LogRecord::marshal(RECORD_allocate_memory,
												  sizeof(*amr),
												  sz,
												  &r);
	amr->start = start;
	amr->size = size;
	amr->prot = mkConst<unsigned long>(prot);
	amr->flags = flags;
	return r;
}

unsigned
LogRecordInitialRegisters::marshal_size() const
{
	return sizeof(VexGuestAMD64State);
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

unsigned
LogRecordInitialBrk::marshal_size() const
{
	return sizeof(initial_brk_record<unsigned long>);
}


void *LogRecordInitialBrk::marshal(unsigned *sz) const
{
	void *r;
	initial_brk_record<unsigned long> *ibr = (initial_brk_record<unsigned long> *)LogRecord::marshal(RECORD_initial_brk,
											  sizeof(*ibr),
											  sz,
											  &r);
	ibr->initial_brk = brk;
	return r;
}

unsigned
LogRecordInitialSighandlers::marshal_size() const
{
	return sizeof(initial_sighandlers_record<unsigned long>);
}

void *LogRecordInitialSighandlers::marshal(unsigned *sz) const
{
	void *r;
	initial_sighandlers_record<unsigned long> *isr =
		(initial_sighandlers_record<unsigned long> *)LogRecord::marshal(RECORD_initial_sighandlers,
										sizeof(*isr),
										sz,
										&r);
	memcpy(isr->handlers, handlers, sizeof(isr->handlers));
	return r;
}

unsigned
LogRecordVexThreadState::marshal_size() const
{
	return sizeof(vex_thread_state_record_2<unsigned long>);
}


void *LogRecordVexThreadState::marshal(unsigned *sz) const
{
	void *r;
	vex_thread_state_record_2<unsigned long> *vtsr =
		(vex_thread_state_record_2<unsigned long> *)LogRecord::marshal(RECORD_vex_thread_state_2,
									  sizeof(*vtsr) + 16 * tmp.content.size(),
									  sz,
									  &r);
	vtsr->statement_nr = statement_nr;
	vtsr->translation_origin = currentIRSBRip;
	for (unsigned x = 0; x < tmp.content.size(); x++) {
		vtsr->temporaries[x*2] = tmp.content[x].lo;
		vtsr->temporaries[x*2+1] = tmp.content[x].hi;
	}
	return r;
}

LogFileWriter *LogFileWriter::open(const char *path)
{
	int fd;
	fd = ::open(path, O_WRONLY|O_APPEND|O_CREAT|O_TRUNC, 0666);
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

void LogFileWriter::append(LogRecord *lr, unsigned long ignore)
{
	void *b;
	unsigned s;

	b = lr->marshal(&s);
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

LogRecordVexThreadState::LogRecordVexThreadState(ThreadId tid, unsigned long _currentIRSBRip,
						 unsigned _statement_nr,
						 expression_result_array<unsigned long> _tmp)
	: LogRecord(tid),
	  currentIRSBRip(_currentIRSBRip),
	  tmp(_tmp),
	  statement_nr(_statement_nr)
{
}

void SignalHandlers::dumpSnapshot(LogWriter<unsigned long> *lw) const
{
	lw->append(new LogRecordInitialSighandlers(ThreadId(0), handlers), 0);
}

#define MK_LOGWRITER(t)
