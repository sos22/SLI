#include <err.h>
#include <stdio.h>
#include <stdlib.h>

#include <exception>
#include <iostream>
#include <map>

#include "libvex.h"
#include "sli.h"

int
main(int argc, char *argv[])
{
	init_sli();

	LogFile *lf;
	LogReader::ptr ptr;
	LogReader::ptr nextPtr;

	lf = LogFile::open(argv[1], &ptr);
	if (!lf)
		err(1, "opening %s", argv[1]);

	MachineState *ms_base = MachineState::initialMachineState(lf, ptr, &ptr);
	VexGcRoot base_root((void **)&ms_base);

#if 0
	printf("Doing initial replay...\n");
	Interpreter *i = new Interpreter(ms_adv);
	LogReader::ptr eof;
	i->replayLogfile(lf, ptr, &eof);
	delete i;

	printf("Replay from %lx to %d - 10000.. (%lx)\n",
	       ptr._off(),
	       eof.rn(),
	       (eof - 10000)._off());
	LogReader *partialLog = lf->truncate(eof - 10000);
#else
	LogReader *partialLog = lf->truncate(lf->mkPtr(0xde74e31, 4123917));
	Interpreter *i;
#endif

	printf("Replay to %d\n", 4123917);
	i = new Interpreter(ms_base);
	i->replayLogfile(partialLog, ptr, &ptr);
	delete i;

	MemTracePool thread_traces(ms_base);
	std::map<ThreadId, Maybe<unsigned> > *first_racing_access =
		thread_traces.firstRacingAccessMap();

	for (std::map<ThreadId, Maybe<unsigned> >::iterator it = first_racing_access->begin();
	     it != first_racing_access->end();
	     it++) {
		ThreadId tid = it->first;
		Maybe<unsigned> r = it->second;
		if (r.full) {
			printf("Thread %d races at %d\n", tid._tid(), r.value);
			MemLog *ml = MemLog::emptyMemlog();
			VexGcRoot ml_keeper((void **)&ml);
			MachineState *ms = ms_base->dupeSelf();
			Interpreter i(ms);
			printf("Collecting log...\n");
			i.runToAccessLoggingEvents(tid, r.value + 1, ml);
			printf("Log:\n");
			ml->dump();
		} else
			printf("Thread %d doesn't race\n", tid._tid());
	}

	return 0;
}
