#include <err.h>
#include <stdio.h>
#include <stdlib.h>

#include <exception>
#include <iostream>

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

class Explorer : public GarbageCollected<Explorer> {
public:
	Explorer(gc_map<ThreadId, unsigned long> *thresholds, ExplorationState *initState)
	{
		goodStates = LibvexVector<ExplorationState>::empty();
		badStates = LibvexVector<ExplorationState>::empty();
		grayStates = LibvexVector<ExplorationState>::empty();
		grayStates->push(initState);
		successThresholds = thresholds;
	}
	LibvexVector<ExplorationState> *goodStates;
	LibvexVector<ExplorationState> *badStates;
	LibvexVector<ExplorationState> *grayStates;
	gc_map<ThreadId, unsigned long> *successThresholds;

	bool advance(GarbageCollectionToken tok);

	void visit(HeapVisitor &hv) {
		hv(goodStates);
		hv(badStates);
		hv(grayStates);
		hv(successThresholds);
	}
	void destruct();
	NAMED_CLASS
};

bool Explorer::advance(GarbageCollectionToken tok)
{
	LibVEX_gc(tok);

	printf("%d gray, %d good, %d bad.\n", grayStates->size(), goodStates->size(), badStates->size());
	if (grayStates->size() == 0 ||
	    (goodStates->size() >= 30 &&
	     badStates->size() >= 10))
		return false;

	ExplorationState *basis = grayStates->pop_first();
	VexGcRoot basis_keeper((void **)&basis, "basis_keeper");

	/* Has the state already crashed? */
	if (basis->ms->crashed()) {
		printf("%p: bad\n", basis);
		badStates->push(basis);
		return true;
	}

	/* Check for threads hitting their thresholds. */
	bool good = true;
	if (!basis->ms->exitted) {
		for (unsigned x = 0;
		     good && x < basis->ms->threads->size();
		     x++) {
			Thread<unsigned long> *thr = basis->ms->threads->index(x);
			if (thr->nrAccesses < (*successThresholds)[thr->tid]) {
				good = false;
			} else {
				thr->cannot_make_progress = true;
			}
		}
	}

	if (good) {
		printf("%p: good\n", basis);
		goodStates->push(basis);
		return true;
	}

	/* Check for no-progress-possible condition */
	bool stopped = true;
	for (unsigned x = 0; stopped && x < basis->ms->threads->size(); x++) {
		Thread<unsigned long> *thr = basis->ms->threads->index(x);
		if (thr->runnable())
			stopped = false;
	}
	if (stopped) {
		printf("%p: indifferent\n", basis);
		return true;
	}

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
			VexPtr<LogWriter<unsigned long> > basis_history(basis->history);
			i.runToFailure(thr->tid, basis_history, tok, 10000);
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
		VexPtr<LogWriter<unsigned long> > newGray_history(newGray->history);
		if (r.full) {
			printf("%p: run %d to %ld\n", newGray, tid._tid(), r.value + thr->nrAccesses);
			i.runToAccessLoggingEvents(tid, r.value + 1, tok, newGray_history);
		} else {
			printf("%p: run %d to failure from %ld\n", newGray, tid._tid(), thr->nrAccesses);
			i.runToFailure(tid, newGray_history, tok, 10000);
		}

		grayStates->push(newGray);
	}

	delete first_racing_access;

	return true;
}

class CommunicationGraph {
public:
	class Edge {
	public:
		MemoryAccess<unsigned long> *load;
		unsigned load_idx;
		MemoryAccess<unsigned long> *store;
		unsigned store_idx;
		Edge(MemoryAccess<unsigned long> *_load, unsigned _load_idx, MemoryAccess<unsigned long >*_store,
		     unsigned _store_idx)
			: load(_load),
			  load_idx(_load_idx),
			  store(_store),
			  store_idx(_store_idx)
		{
		}
	};
	std::vector<Edge> content;
	void addEdge(MemoryAccess<unsigned long> *load, unsigned load_idx, MemoryAccess<unsigned long> *store, unsigned store_idx)
	{
		content.push_back(Edge(load, load_idx, store, store_idx));
	}
	CommunicationGraph(MemoryTrace<unsigned long> *mt);
	void dump() const;
};

CommunicationGraph::CommunicationGraph(MemoryTrace<unsigned long> *mt)
{
	for (unsigned loadInd = 0; loadInd < mt->size(); loadInd++) {
		MemoryAccessLoad<unsigned long> *load = dynamic_cast<MemoryAccessLoad<unsigned long> *>((*mt)[loadInd]);
		if (!load)
			continue;
		for (int storeInd = loadInd - 1; storeInd >= 0; storeInd--) {
			MemoryAccessStore<unsigned long> *store = dynamic_cast<MemoryAccessStore<unsigned long> *>((*mt)[storeInd]);
			if (!store || store->addr != load->addr)
				continue;
			addEdge(load, loadInd, store, storeInd);
			break;
		}
	}
}

void CommunicationGraph::dump() const
{
	for (unsigned x = 0; x < content.size(); x++)
		printf("%s:%d -> %s:%d\n", content[x].store->name(), content[x].store_idx,
		       content[x].load->name(), content[x].load_idx);
}

int
main(int argc, char *argv[])
{
	init_sli();

	LogReaderPtr ptr;

	VexPtr<LogReader<unsigned long> > lf(LogFile::open(argv[1], &ptr));
	if (!lf)
		err(1, "opening %s", argv[1]);

	VexPtr<MachineState<unsigned long> > ms_base(MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr, ALLOW_GC));

	VexPtr<gc_map<ThreadId, unsigned long> >thresholds
		(new gc_map<ThreadId, unsigned long>);

	{
		MachineState<unsigned long> *a = ms_base->dupeSelf();
		Interpreter<unsigned long> i(a);
		i.replayLogfile(lf, ptr, ALLOW_GC);
		for (unsigned x = 0; x < a->threads->size(); x++) {
			Thread<unsigned long> *thr = a->threads->index(x);
			(*thresholds)[thr->tid] = thr->nrAccesses * 2;
			//thresholds[thr->tid] = 10;
			printf("Thread %d threshold %ld\n", thr->tid._tid(),
			       thr->nrAccesses * 2);
		}
	}

	VexPtr<Explorer> e(new Explorer(thresholds, ExplorationState::init(ms_base)));
	VexGcRoot e_base((void **)&e, "e_base");

	while (e->advance(ALLOW_GC))
		;

	printf("Good states:\n");
	for (unsigned x = 0; x < e->goodStates->size(); x++) {
		printf("State %d\n", x);
		VexPtr<LogReader<unsigned long> > history(e->goodStates->index(x)->history);
	        VexPtr<MemoryTrace<unsigned long> > mt(
			MemoryTrace<unsigned long>::get(ms_base,
							history,
							MemLog<unsigned long>::startPtr(),
							ALLOW_GC));
		CommunicationGraph ct(mt);
		ct.dump();
	}

	printf("Bad states:\n");
	for (unsigned x = 0; x < e->badStates->size(); x++) {
		printf("State %d\n", x);
		VexPtr<LogReader<unsigned long> > history(e->badStates->index(x)->history);
                VexPtr<MemoryTrace<unsigned long> > mt(
			MemoryTrace<unsigned long>::get(ms_base,
							history,
							MemLog<unsigned long>::startPtr(),
							ALLOW_GC));
		CommunicationGraph ct(mt);
		ct.dump();
	}

	return 0;
}
