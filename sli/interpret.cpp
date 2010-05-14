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
	MachineState *ms;
	MemLog *history;
	static ExplorationState *init(MachineState *ms);
	ExplorationState *dupeSelf() const;
};

DECLARE_VEX_TYPE(ExplorationState)
DEFINE_VEX_TYPE_NO_DESTRUCT(ExplorationState, {visit(ths->ms);visit(ths->history);});

ExplorationState *ExplorationState::init(MachineState *ms)
{
	ExplorationState *es = LibVEX_Alloc_ExplorationState();
	es->ms = ms;
	es->history = MemLog::emptyMemlog();
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
	LibvexVector<ExplorationState> *whiteStates;
	LibvexVector<ExplorationState> *grayStates;
	unsigned successThreshold;

	static Explorer *init(unsigned, ExplorationState *initState);

	bool advance();
};

DECLARE_VEX_TYPE(Explorer);
DEFINE_VEX_TYPE_NO_DESTRUCT(Explorer, {visit(ths->whiteStates);visit(ths->grayStates);});

Explorer *Explorer::init(unsigned threshold, ExplorationState *initState)
{
	Explorer *e = LibVEX_Alloc_Explorer();
	memset(e, 0, sizeof(*e));
	e->whiteStates = LibvexVector<ExplorationState>::empty();
	e->grayStates = LibvexVector<ExplorationState>::empty();
	e->grayStates->push(initState);
	e->successThreshold = threshold;
	return e;
}

bool Explorer::advance()
{
	if (grayStates->size() == 0)
		return false;

	ExplorationState *basis = grayStates->pop_first();
	VexGcRoot basis_keeper((void **)&basis);

	MemTracePool thread_traces(basis->ms);
	std::map<ThreadId, Maybe<unsigned> > *first_racing_access =
		thread_traces.firstRacingAccessMap();

	bool noProgress = true;
	for (std::map<ThreadId, Maybe<unsigned> >::iterator it = first_racing_access->begin();
	     it != first_racing_access->end();
	     it++) {
		ThreadId tid = it->first;
		Maybe<unsigned> r = it->second;
		Thread *thr = basis->ms->findThread(tid);
		if (thr->cannot_make_progress) {
			printf("Thread %d cannot make progress\n", tid._tid());
			continue;
		}
		noProgress = false;
		ExplorationState *newGray = basis->dupeSelf();
		VexGcRoot grayKeeper((void **)&newGray);
		Interpreter i(newGray->ms);
		if (r.full) {
			printf("Thread %d races at %d\n", tid._tid(), r.value);
			i.runToAccessLoggingEvents(tid, r.value + 1, newGray->history);
		} else {
			printf("Thread %d doesn't race\n", tid._tid());
			i.runToFailure(tid, newGray->history, 10000);
		}
		if (newGray->ms->nrAccesses > successThreshold || newGray->ms->crashed())
			whiteStates->push(newGray);
		else
			grayStates->push(newGray);
	}

	if (noProgress)
		whiteStates->push(basis);

	delete first_racing_access;

	return true;
}

class CommunicationGraph {
public:
	class Edge {
	public:
		MemoryAccess *load;
		MemoryAccess *store;
		Edge(MemoryAccess *_load, MemoryAccess *_store)
			: load(_load),
			  store(_store)
		{
		}
	};
	std::vector<Edge> content;
	void addEdge(MemoryAccess *load, MemoryAccess *store)
	{
		content.push_back(Edge(load, store));
	}
	CommunicationGraph(MemoryTrace *mt);
	void dump() const;
};

CommunicationGraph::CommunicationGraph(MemoryTrace *mt)
{
	for (unsigned loadInd = 0; loadInd < mt->size(); loadInd++) {
		MemoryAccessLoad *load = dynamic_cast<MemoryAccessLoad *>((*mt)[loadInd]);
		if (!load)
			continue;
		for (int storeInd = loadInd - 1; storeInd >= 0; storeInd--) {
			MemoryAccessStore *store = dynamic_cast<MemoryAccessStore *>((*mt)[storeInd]);
			if (!store || store->addr != load->addr)
				continue;
			addEdge(load, store);
			break;
		}
	}
}

void CommunicationGraph::dump() const
{
	for (unsigned x = 0; x < content.size(); x++)
		printf("%s -> %s\n", content[x].store->name(), content[x].load->name());
}

/* force some functions to be included even when they're not needed,
   so that they're available for calling from the debugger. */
static void force_linkage() __attribute__((unused, used));
static void
force_linkage()
{
	gdb_machine_state(NULL);
}

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
	VexGcRoot((void **)&ms_base);

	unsigned long threshold = 50;
#if 0
	{
		MachineState *a = ms_base->dupeSelf();
		Interpreter i(a);
		i.replayLogfile(lf, ptr);
		threshold = a->nrAccesses * 2;
	}
#endif

	Explorer *e = Explorer::init(threshold, ExplorationState::init(ms_base));
	VexGcRoot e_base((void **)&e);

	while (e->advance())
		printf("Advancing...\n");

	for (unsigned x = 0; x < e->whiteStates->size(); x++) {
		printf("State %d, crashed %d\n", x, e->whiteStates->index(x)->ms->crashed());
		MemoryTrace mt(*e->whiteStates->index(x)->history,
			       MemLog::startPtr());
		CommunicationGraph ct(&mt);
		ct.dump();
	}
	return 0;
}
