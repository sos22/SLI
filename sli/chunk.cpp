#include <err.h>
#include <string.h>

#include "sli.h"

class LogChunker : public LogWriter<unsigned long> {
	unsigned long next_input_offset;
	unsigned long chunk_size;
	unsigned long chunk_period;
	const char *prefix;
	unsigned next_index;

	MachineState *ms;
	std::vector<std::pair<unsigned long, LogFileWriter *> > writers;
public:
	LogChunker(unsigned long _chunk_size, unsigned long _chunk_period,
		   const char *_prefix, MachineState *_ms)
		: next_input_offset(0), chunk_size(_chunk_size),
		  chunk_period(_chunk_period), prefix(_prefix),
		  next_index(0), ms(_ms), writers()
	{
	}
	void append(LogRecord *lr, unsigned long idx);
	void destruct() { this->~LogChunker(); }
	void visit(HeapVisitor &hv);
	NAMED_CLASS
};

void
LogChunker::visit(HeapVisitor &hv)
{
	hv(ms);
	for (std::vector<std::pair<unsigned long, LogFileWriter *> >::iterator it = writers.begin();
	     it != writers.end();
	     it++)
		hv(it->second);
}

void
LogChunker::append(LogRecord *lr, unsigned long idx)
{
	unsigned long start = next_input_offset;
	unsigned long end = start + lr->marshal_size();

	for (std::vector<std::pair<unsigned long, LogFileWriter *> >::iterator it = writers.begin();
	     it != writers.end();
	     ) {
		if (it->first + chunk_size < end) {
			printf("Closed %ld\n", it->first);
			it = writers.erase(it);
		} else {
			it->second->append(lr, idx);
			it++;
		}
	}

	if ( (start - 1)/chunk_period != (end - 1)/chunk_period ) {
		char *p = my_asprintf("%s/%d", prefix, next_index);
		next_index++;
		LogFileWriter *f = LogFileWriter::open(p);
		if (!f)
			err(1, "opening %s", p);
		ms->dumpSnapshot(f);
		writers.push_back(std::pair<unsigned long, LogFileWriter *>(start, f));
		printf("Opened %s for %ld\n", p, start);
	}

	next_input_offset = end;
}

int
main(int argc, char *argv[])
{
	if (argc != 5)
		errx(1, "need precisely four arguments: input, output directory, chunk size, and chunk period");

	const char *inp = argv[1];
	const char *prefix = argv[2];
	unsigned long size = atol(argv[3]);
	unsigned long period = atol(argv[4]);

	init_sli();

	LogReaderPtr ptr;

	VexPtr<LogReader> lf(LogFile::open(inp, &ptr));
	if (!lf)
		err(1, "opening %s", inp);

	VexPtr<MachineState> ms(MachineState::initialMachineState(lf, ptr, &ptr, ALLOW_GC));

	ms->findThread(ThreadId(7))->clear_child_tid = 0x7faa32f5d9e0;
	
	printf("Slurped initial state\n");

	Interpreter i(ms);
	VexPtr<LogWriter<unsigned long> > chunker(new LogChunker(size, period, prefix, ms));

	i.replayLogfile(lf, ptr, ALLOW_GC, NULL, chunker);

	return 0;
}
