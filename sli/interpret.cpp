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

	lf = LogFile::open(argv[1], &ptr);
	if (!lf)
		err(1, "opening %s", argv[1]);

	MachineState *ms_base = MachineState::initialMachineState(lf, ptr, &ptr);
	VexGcRoot base_root((void **)&ms_base);

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
