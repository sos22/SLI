#include "sli.h"

MemTracePool::MemTracePool(MachineState<unsigned long> *base_state)
  : content()
{
	unsigned x;
	for (x = 0; x < base_state->threads->size(); x++) {
		ThreadId tid = base_state->threads->index(x)->tid;
		MachineState<unsigned long> *ms = base_state->dupeSelf();
		Interpreter<unsigned long> i(ms);
		MemoryTrace *v;
		i.getThreadMemoryTrace(tid, &v, 10000);
		content[tid] = v;
	}
}

std::map<ThreadId, Maybe<unsigned> > *MemTracePool::firstRacingAccessMap()
{
	std::map<ThreadId, Maybe<unsigned> > *work = new std::map<ThreadId, Maybe<unsigned> >();
	for (contentT::iterator outerIt = content.begin();
	     outerIt != content.end();
	     outerIt++) {
		ThreadId tid = outerIt->first;
		MemoryTrace *v = outerIt->second;
		assert(v);
		unsigned mem_index;
		for (mem_index = 0; mem_index < v->size(); mem_index++) {
			MemoryAccess *ma = (*v)[mem_index];
			for (contentT::iterator innerIt = content.begin();
			     innerIt != content.end();
			     innerIt++) {
				ThreadId other_tid = innerIt->first;
				if (other_tid == tid)
					continue;
				MemoryTrace *other_v = innerIt->second;
				for (unsigned other_access = 0;
				     other_access < other_v->size();
				     other_access++) {
					MemoryAccess *other_ma = (*other_v)[other_access];
					if (other_ma->addr + other_ma->size <= ma->addr ||
					    other_ma->addr >= ma->addr + ma->size)
						continue;
					if (other_ma->isLoad() && ma->isLoad())
						continue;
					/* This is the one */
					goto found_race;
				}
			}
		}
		(*work)[tid] = Maybe<unsigned>();
		continue;

	found_race:
		(*work)[tid] = Maybe<unsigned>(mem_index);
		continue;
	}

	return work;
}
