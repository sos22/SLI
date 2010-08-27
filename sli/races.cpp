#include <asm/unistd.h>
#include <err.h>

#include "sli.h"

#include "main_util.h"

typedef unsigned long timestamp_t;

typedef std::map<ThreadId, timestamp_t> vector_clock;

struct thread_state {
	/* For every {a,b} in seen_times, we have already emitted
	   edges which imply {self,my_time} > {a,b} */
	vector_clock seen_times;
};

struct location_state {
	/* An entry {a,b} in here implies that thread a first read the
	   current value (i.e. the one written by the last write) at
	   time b */
	vector_clock readers;

	ThreadId last_writing_thread;
	/* last_writing_thread's seen_times when it wrote to the
	 * location */
	vector_clock last_write;
};

static std::map<ThreadId, thread_state> thread_states;
static std::map<unsigned long, location_state> location_states;

static void
process_load_record(LogRecordLoad<unsigned long> *lrl)
{
	unsigned long addr = lrl->ptr;
	ThreadId tid = lrl->thread();

	thread_state *ts = &thread_states[tid];
	location_state *as = &location_states[addr];

	if (as->last_writing_thread.valid() &&
	    as->last_writing_thread != tid) {
		/* Are we racing with the last write to this
		 * location? */
		if (ts->seen_times[as->last_writing_thread] < as->last_write[as->last_writing_thread]) {
			/* Yes */
			printf("RAW race on %lx: R: %d:%lx, W: %d:%lx (last seen %lx)\n",
			       addr,
			       tid._tid(),
			       ts->seen_times[tid],
			       as->last_writing_thread._tid(),
			       as->last_write[as->last_writing_thread],
			       ts->seen_times[as->last_writing_thread]);
			for (vector_clock::iterator it = as->last_write.begin();
			     it != as->last_write.end();
			     it++) {
				if (it->second > ts->seen_times[it->first])
					ts->seen_times[it->first] = it->second;
			}
		}
	}

	as->readers[tid] = ts->seen_times[tid];
	ts->seen_times[tid]++;
}


static void
process_store_record(LogRecordStore<unsigned long> *lrs)
{
	unsigned long addr = lrs->ptr;
	ThreadId tid = lrs->thread();

	thread_state *ts = &thread_states[tid];
	location_state *as = &location_states[addr];

	if (as->last_writing_thread.valid() &&
	    as->last_writing_thread != tid) {
		/* Are we racing with the last write to this
		 * location? */
		if (ts->seen_times[as->last_writing_thread] < as->last_write[as->last_writing_thread]) {
			/* Yes */
			printf("WAW race on %lx: W: %d:%lx, W: %d:%lx (last seen %lx)\n",
			       addr,
			       as->last_writing_thread._tid(),
			       as->last_write[as->last_writing_thread],
			       tid._tid(),
			       ts->seen_times[tid],
			       ts->seen_times[as->last_writing_thread]);
		}
	}

	/* Are we racing with any reads from this location? */
	for (vector_clock::iterator it = as->readers.begin();
	     it != as->readers.end();
	     it++) {
		if (it->first == tid)
			continue;
		if (ts->seen_times[it->first] < it->second) {
			/* Yes */
			printf("WAR race on %lx: W: %d:%lx, R: %d:%lx (last seen %lx)\n",
			       addr,
			       tid._tid(),
			       ts->seen_times[tid],
			       it->first._tid(),
			       it->second,
			       ts->seen_times[it->first]);
		}
	}

	as->readers.clear();
	as->last_writing_thread = tid;
	as->last_write = ts->seen_times;

	ts->seen_times[tid]++;
}

static void
process_syscall_record(LogRecordSyscall<unsigned long> *lrs)
{
	if (lrs->sysnr != __NR_exit)
		return;
	thread_state *ts = &thread_states[lrs->thread()];
	ts->seen_times.clear();
}

int
main(int argc, char *argv[])
{
	init_sli();

	LogReaderPtr ptr;
	VexPtr<LogFile> lf(LogFile::open(argv[1], &ptr));
	if (!lf.get())
		err(1, "opening %s", argv[1]);

	while (1) {
		LogRecord<unsigned long> *lr =
			lf->read(ptr, &ptr);
		if (!lr)
			break;
		if (LogRecordLoad<unsigned long> *lrl =
		    dynamic_cast<LogRecordLoad<unsigned long> *>(lr))
			process_load_record(lrl);
		else if (LogRecordStore<unsigned long> *lrs =
			 dynamic_cast<LogRecordStore<unsigned long> *>(lr))
			process_store_record(lrs);
		else if (LogRecordSyscall<unsigned long> *lrsys =
			 dynamic_cast<LogRecordSyscall<unsigned long> *>(lr))
			process_syscall_record(lrsys);

		vexSetAllocModeTEMP_and_clear(ALLOW_GC);
	}

	return 0;
}
