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

	static Explorer *init(ExplorationState *initState);

	bool advance();
};

DECLARE_VEX_TYPE(Explorer);
DEFINE_VEX_TYPE_NO_DESTRUCT(Explorer, {visit(ths->whiteStates);visit(ths->grayStates);});

Explorer *Explorer::init(ExplorationState *initState)
{
	Explorer *e = LibVEX_Alloc_Explorer();
	memset(e, 0, sizeof(*e));
	e->whiteStates = LibvexVector<ExplorationState>::empty();
	e->grayStates = LibvexVector<ExplorationState>::empty();
	e->grayStates->push(initState);
	return e;
}

bool Explorer::advance()
{
	if (grayStates->size() == 0)
		return false;

	ExplorationState *basis = grayStates->pop();

	MemTracePool thread_traces(basis->ms);
	std::map<ThreadId, Maybe<unsigned> > *first_racing_access =
		thread_traces.firstRacingAccessMap();

	for (std::map<ThreadId, Maybe<unsigned> >::iterator it = first_racing_access->begin();
	     it != first_racing_access->end();
	     it++) {
		ThreadId tid = it->first;
		Maybe<unsigned> r = it->second;
		ExplorationState *newGray = basis->dupeSelf();
		Interpreter i(newGray->ms);
		if (r.full) {
			printf("Thread %d races at %d\n", tid._tid(), r.value);
			grayStates->push(newGray);
			i.runToAccessLoggingEvents(tid, r.value + 1, newGray->history);
		} else {
			printf("Thread %d doesn't race\n", tid._tid());
			/* This is as far as we can push this state,
			 * so it's white and needs no further
			 * exploration. */
			whiteStates->push(newGray);
			i.runToFailure(tid, newGray->history);
		}
	}

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
		for (unsigned storeInd = 0; storeInd < loadInd; storeInd++) {
			MemoryAccessStore *store = dynamic_cast<MemoryAccessStore *>((*mt)[storeInd]);
			if (!store || store->tid == load->tid || store->addr != load->addr)
				continue;
			addEdge(load, store);
		}
	}
}

void CommunicationGraph::dump() const
{
	for (unsigned x = 0; x < content.size(); x++)
		printf("%s -> %s\n", content[x].store->name(), content[x].load->name());
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
	Explorer *e = Explorer::init(ExplorationState::init(ms_base));
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
