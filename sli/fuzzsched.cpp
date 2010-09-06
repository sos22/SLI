/* Simple thing which tries a whole bunch of schedules in an attempt
   to discover which memory locations are likely to suffer races. */
#include <err.h>
#include <stdio.h>
#include <stdlib.h>

#include <exception>
#include <iostream>
#include <map>

#include "libvex.h"
#include "sli.h"

class ExplorationState {
public:
	MachineState<unsigned long> *ms;
	MemLog<unsigned long> *history;
	static ExplorationState *init(MachineState<unsigned long> *ms);
	ExplorationState *dupeSelf() const;
};

DECLARE_VEX_TYPE(ExplorationState)
DEFINE_VEX_TYPE_NO_DESTRUCT(ExplorationState, {visit(ths->ms);visit(ths->history);});

ExplorationState *ExplorationState::init(MachineState<unsigned long> *ms)
{
	ExplorationState *es = LibVEX_Alloc_ExplorationState();
	es->ms = ms;
	es->history = MemLog<unsigned long>::emptyMemlog();
	return es;
}

ExplorationState *ExplorationState::dupeSelf() const
{
	ExplorationState *es = LibVEX_Alloc_ExplorationState();
	es->ms = ms->dupeSelf();
	es->history = history->dupeSelf();
	return es;
}

class Explorer {
public:
	LibvexVector<ExplorationState> *grayStates;

	static Explorer *init(ExplorationState *initState);

	bool advance(GarbageCollectionToken tok);
};

DECLARE_VEX_TYPE(Explorer);
DEFINE_VEX_TYPE_NO_DESTRUCT(Explorer, {visit(ths->grayStates);});

Explorer *Explorer::init(ExplorationState *initState)
{
	Explorer *e = LibVEX_Alloc_Explorer();
	memset(e, 0, sizeof(*e));
	e->grayStates = LibvexVector<ExplorationState>::empty();
	e->grayStates->push(initState);
	return e;
}

bool Explorer::advance(GarbageCollectionToken tok)
{
	if (grayStates->size() == 0)
		return false;

	ExplorationState *basis = grayStates->pop_first();
	VexGcRoot basis_keeper((void **)&basis, "basis_keeper");

	/* Check for no-progress-possible condition */
	bool stopped = true;
	bool everyone_idle = true;
	for (unsigned x = 0; stopped && x < basis->ms->threads->size(); x++) {
		Thread<unsigned long> *thr = basis->ms->threads->index(x);
		if (!thr->cannot_make_progress) {
			if (!thr->idle)
				everyone_idle = false;
			stopped = false;
		}
	}
	if (stopped || everyone_idle)
		return true;

	/* Okay, have to actually do something. */

	VexPtr<MachineState<unsigned long> > basis_ms(basis->ms);
        VexPtr<MemTracePool<unsigned long> > thread_traces
	        (MemTracePool<unsigned long>::get(basis_ms, ThreadId(), tok));
	VexPtr<gc_map<ThreadId, Maybe<unsigned> > > first_racing_access(
		thread_traces->firstRacingAccessMap());

	/* If there are no races then we can just run one thread after
	   another, and we don't need to do anything else.  We can
	   even get away with reusing the old MachineState. */
	/* This includes the case where only one thread can make
	   progress at all. */
	bool noRaces = true;
	for (gc_map<ThreadId, Maybe<unsigned> >::iterator it = first_racing_access->begin();
	     it != first_racing_access->end();
	     it++) {
		if (it.value().full)
			noRaces = false;
	}
	if (noRaces) {
		for (unsigned x = 0; x < basis->ms->threads->size(); x++) {
			Thread<unsigned long> *thr = basis->ms->threads->index(x);
			if (thr->cannot_make_progress)
				continue;
			Interpreter<unsigned long> i(basis->ms);
			VexPtr<LogWriter<unsigned long> > basis_history(basis->history->writer);
			i.runToFailure(thr->tid, basis_history, tok, 10000);
			thr->idle = false;
		}
		grayStates->push(basis);
		delete first_racing_access;
		return true;
	}

	for (gc_map<ThreadId, Maybe<unsigned> >::iterator it = first_racing_access->begin();
	     it != first_racing_access->end();
	     it++) {
		ThreadId tid = it.key();
		Maybe<unsigned> r = it.value();
		Thread<unsigned long> *thr = basis->ms->findThread(tid);
		if (thr->cannot_make_progress)
			continue;
		ExplorationState *newGray = basis->dupeSelf();
		VexGcRoot grayKeeper((void **)&newGray, "newGray");
		Interpreter<unsigned long> i(newGray->ms);
		VexPtr<LogWriter<unsigned long> > newGrayHist(newGray->history->writer);
		if (r.full) {
			i.runToAccessLoggingEvents(tid, r.value + 1, tok, newGrayHist);
		} else {
			i.runToFailure(tid, newGrayHist, tok, 10000);
		}

		thr->idle = false;
		grayStates->push(newGray);
	}

	delete first_racing_access;

	return true;
}

int
main(int argc, char *argv[])
{
	init_sli();

	LogReaderPtr ptr;
	VexPtr<LogReader<unsigned long> > lf(LogFile::open(argv[1], &ptr));
	if (!lf)
		err(1, "opening %s", argv[1]);
	VexGcRoot((void **)&lf, "lf");

	MachineState<unsigned long> *ms_base = MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr, ALLOW_GC);
	VexGcRoot((void **)&ms_base, "ms_base");

	Explorer *e = Explorer::init(ExplorationState::init(ms_base));
	VexGcRoot e_base((void **)&e, "e_base");

	while (e->advance(ALLOW_GC))
		;

	return 0;
}
