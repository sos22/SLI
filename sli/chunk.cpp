#include <err.h>
#include <string.h>

#include "sli.h"

class LogChunker : public LogWriter<unsigned long>, public GarbageCollected<LogChunker> {
	unsigned long next_input_offset;
	unsigned long chunk_size;
	unsigned long chunk_period;
	const char *prefix;
	unsigned next_index;

	MachineState<unsigned long> *ms;
	std::vector<std::pair<unsigned long, LogFileWriter *> > writers;
public:
	LogChunker(unsigned long _chunk_size, unsigned long _chunk_period,
		   const char *_prefix, MachineState<unsigned long> *_ms)
		: next_input_offset(0), chunk_size(_chunk_size),
		  chunk_period(_chunk_period), prefix(_prefix),
		  next_index(0), ms(_ms), writers()
	{
	}
	void append(LogRecord<unsigned long> *lr, unsigned long idx);
	void destruct() { this->~LogChunker(); }
	~LogChunker();
	void visit(HeapVisitor &hv) const;
	NAMED_CLASS
};

LogChunker::~LogChunker()
{
	for (std::vector<std::pair<unsigned long, LogFileWriter *> >::const_iterator it = writers.begin();
	     it != writers.end();
	     it++)
		delete it->second;	
}

void
LogChunker::visit(HeapVisitor &hv) const
{
	hv(ms);
}

void
LogChunker::append(LogRecord<unsigned long> *lr, unsigned long idx)
{
	unsigned long start = next_input_offset;
	unsigned long end = start + lr->marshal_size();

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

	for (std::vector<std::pair<unsigned long, LogFileWriter *> >::iterator it = writers.begin();
	     it != writers.end();
	     ) {
		if (it->first + chunk_size < end) {
			printf("Closed %ld\n", it->first);
			delete it->second;
			it = writers.erase(it);
		} else {
			it->second->append(lr, idx);
			it++;
		}
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

	LogFile *lf;
	LogReaderPtr ptr;

	lf = LogFile::open(inp, &ptr);
	VexGcRoot lf_root((void **)&lf, "lf");
	if (!lf)
		err(1, "opening %s", inp);

	MachineState<unsigned long> *ms = MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr, ALLOW_GC);
	VexGcRoot ms_root((void **)&ms, "ms_root");

	ms->findThread(ThreadId(7))->clear_child_tid = 0x7faa32f5d9e0;
	
	printf("Slurped initial state\n");

	Interpreter<unsigned long> i(ms);
	LogChunker *chunker = new LogChunker(size, period, prefix, ms);
	VexGcRoot chunker_root((void **)&chunker, "chunker root");
	i.replayLogfile(lf, ptr, ALLOW_GC, NULL, chunker);

	return 0;
}
