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

template <typename ait>
void *LogRecord<ait>::marshal(unsigned cls, unsigned psize, unsigned *sz, void **r) const
{
	*sz = sizeof(record_header) + psize;
	*r = malloc(*sz);
	((record_header *)*r)->cls = cls;
	((record_header *)*r)->size = *sz;
	((record_header *)*r)->tid = thread()._tid();
	return (void *)((unsigned long)*r + sizeof(record_header));
}

template <typename ait>
void *LogRecordFootstep<ait>::marshal(unsigned *sz) const
{
	void *r;
	footstep_record<ait> *fr = (footstep_record<ait> *)LogRecord<ait>::marshal(RECORD_footstep, sizeof(footstep_record<ait>), sz, &r);
	fr->rip = rip;
	fr->FOOTSTEP_REG_0_NAME = reg0;
	fr->FOOTSTEP_REG_1_NAME = reg1;
	fr->FOOTSTEP_REG_2_NAME = reg2;
	fr->FOOTSTEP_REG_3_NAME = reg3;
	fr->FOOTSTEP_REG_4_NAME = reg4;
	return r;
}

template<typename ait>
void *LogRecordSyscall<ait>::marshal(unsigned *sz) const
{
	void *r;
	syscall_record<ait> *sr = (syscall_record<ait> *)LogRecord<ait>::marshal(RECORD_syscall, sizeof(syscall_record<ait>), sz, &r);
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

template <typename ait>
void *LogRecordMemory<ait>::marshal(unsigned *sz) const
{
	void *r;
	memory_record<ait> *mr = (memory_record<ait> *)LogRecord<ait>::marshal(RECORD_memory,
									       sizeof(memory_record<ait>) + size,
									       sz,
									       &r);
	mr->ptr = start;
	memcpy(mr + 1, contents, size);
	return r;
}

template <typename ait>
void *LogRecordRdtsc<ait>::marshal(unsigned *sz) const
{
	void *r;
	rdtsc_record<ait> *rr = (rdtsc_record<ait> *)LogRecord<ait>::marshal(RECORD_rdtsc,
									     sizeof(rdtsc_record<ait>),
									     sz,
									     &r);
	rr->stashed_tsc = tsc;
	return r;
}

template <typename ait>
void *LogRecordLoad<ait>::marshal(unsigned *sz) const
{
	void *r;
	mem_read_record<ait> *lr = (mem_read_record<ait> *)LogRecord<ait>::marshal(RECORD_mem_read,
										   sizeof(*lr) + size,
										   sz,
										   &r);
	lr->ptr = ptr;
	memcpy(lr + 1, &value, size);
	return r;
}

template <typename ait>
void *LogRecordStore<ait>::marshal(unsigned *sz) const
{
	void *r;
	mem_write_record<ait> *sr = (mem_write_record<ait> *)LogRecord<ait>::marshal(RECORD_mem_write,
										     sizeof(*sr) + size,
										     sz,
										     &r);
	sr->ptr = ptr;
	memcpy(sr + 1, &value, size);
	return r;
}

template <typename ait>
void *LogRecordSignal<ait>::marshal(unsigned *sz) const
{
	void *r;
	signal_record<ait> *sr = (signal_record<ait> *)LogRecord<ait>::marshal(RECORD_signal,
									       sizeof(*sr),
									       sz,
									       &r);
	sr->rip = rip;
	sr->signo = signr;
	sr->err = err;
	sr->virtaddr = virtaddr;
	return r;
}

template <typename ait>
void *LogRecordAllocateMemory<ait>::marshal(unsigned *sz) const
{
	void *r;
	allocate_memory_record<ait> *amr = (allocate_memory_record<ait> *)LogRecord<ait>::marshal(RECORD_allocate_memory,
												  sizeof(*amr),
												  sz,
												  &r);
	amr->start = start;
	amr->size = size;
	amr->prot = mkConst<ait>(prot);
	amr->flags = flags;
	return r;
}

template <typename ait>
void *LogRecordInitialRegisters<ait>::marshal(unsigned *sz) const
{
	void *r;
	VexGuestAMD64State *s = (VexGuestAMD64State *)LogRecord<ait>::marshal(RECORD_initial_registers,
									      sizeof(*s),
									      sz,
									      &r);
	*s = regs;
	return r;
}

template <typename ait>
void *LogRecordInitialBrk<ait>::marshal(unsigned *sz) const
{
	void *r;
	initial_brk_record<ait> *ibr = (initial_brk_record<ait> *)LogRecord<ait>::marshal(RECORD_initial_brk,
											  sizeof(*ibr),
											  sz,
											  &r);
	ibr->initial_brk = brk;
	return r;
}

template <typename ait>
void *LogRecordInitialSighandlers<ait>::marshal(unsigned *sz) const
{
	void *r;
	initial_sighandlers_record<ait> *isr =
		(initial_sighandlers_record<ait> *)LogRecord<ait>::marshal(RECORD_initial_sighandlers,
									   sizeof(*isr),
									   sz,
									   &r);
	memcpy(isr->handlers, handlers, sizeof(isr->handlers));
	return r;
}

template <typename ait>
void *LogRecordVexThreadState<ait>::marshal(unsigned *sz) const
{
	void *r;
	vex_thread_state_record<ait> *vtsr =
		(vex_thread_state_record<ait> *)LogRecord<ait>::marshal(RECORD_vex_thread_state,
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

void LogFileWriter::append(const LogRecord<unsigned long> &lr)
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

template <typename ait>
LogRecordVexThreadState<ait>::LogRecordVexThreadState(ThreadId tid, unsigned _statement_nr,
						      expression_result_array<ait> _tmp)
	: LogRecord<ait>(tid),
	  visitor(this),
	  tmp(_tmp),
	  statement_nr(_statement_nr)
{
}

template <typename ait>
void SignalHandlers<ait>::dumpSnapshot(LogWriter<ait> *lw) const
{
	lw->append(LogRecordInitialSighandlers<ait>(ThreadId(0), handlers));
}

#define MK_LOGWRITER(t)							\
	template LogRecordVexThreadState<t>::LogRecordVexThreadState(ThreadId, \
								     unsigned, \
								     expression_result_array<t>); \
	template void *LogRecordRdtsc<t>::marshal(unsigned *sz) const;	\
	template void *LogRecordSyscall<t>::marshal(unsigned *sz) const
