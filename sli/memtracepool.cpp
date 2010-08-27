#include "sli.h"

template <typename ait>
MemTracePool<ait>::MemTracePool(MachineState<ait> *base_state, ThreadId ignoredThread,
				GarbageCollectionToken token)
  : content()
{
	MemTracePool<ait> *t = this;
	VexGcRoot thisroot((void **)&t, "thisroot");
	unsigned x;
	for (x = 0; x < base_state->threads->size(); x++) {
		ThreadId tid = base_state->threads->index(x)->tid;
		if (tid == ignoredThread)
			continue;
		MachineState<ait> *ms = base_state->dupeSelf();
		Interpreter<ait> i(ms);
		MemoryTrace<ait> *v;
		i.getThreadMemoryTrace(tid, &v, 1000000, token);
		content[tid] = v;
	}
}

template <typename ait>
std::map<ThreadId, Maybe<unsigned> > *MemTracePool<ait>::firstRacingAccessMap()
{
	std::map<ThreadId, Maybe<unsigned> > *work = new std::map<ThreadId, Maybe<unsigned> >();
	for (class contentT::iterator outerIt = content.begin();
	     outerIt != content.end();
	     outerIt++) {
		ThreadId tid = outerIt->first;
		MemoryTrace<ait> *v = outerIt->second;
		assert(v);
		unsigned mem_index;
		for (mem_index = 0; mem_index < v->size(); mem_index++) {
			MemoryAccess<ait> *ma = (*v)[mem_index];
			for (class contentT::iterator innerIt = content.begin();
			     innerIt != content.end();
			     innerIt++) {
				ThreadId other_tid = innerIt->first;
				if (other_tid == tid)
					continue;
				MemoryTrace<ait> *other_v = innerIt->second;
				for (unsigned other_access = 0;
				     other_access < other_v->size();
				     other_access++) {
					MemoryAccess<ait> *other_ma = (*other_v)[other_access];
					if (force(other_ma->addr + mkConst<ait>(other_ma->size) <= ma->addr ||
						  other_ma->addr >= ma->addr + mkConst<ait>(ma->size)) )
						continue;
					if (other_ma->isLoad() && ma->isLoad())
						continue;
					/* This is the one */
					printf("Race on %lx, tids %d %d\n", force(other_ma->addr),
					       tid._tid(), other_tid._tid());
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

template <typename t>
void MemTracePool<t>::visit(HeapVisitor &hv) const
{
	for (class contentT::const_iterator outerIt = content.begin();
	     outerIt != content.end();
	     outerIt++)
		hv(outerIt->second);
}

#define MK_MEMTRACE_POOL(t)						\
  template MemTracePool<t>::MemTracePool(MachineState<t> *, ThreadId, GarbageCollectionToken); \
	template std::map<ThreadId, Maybe<unsigned> > *MemTracePool<t>::firstRacingAccessMap();	\
	template void MemTracePool<t>::visit(HeapVisitor &hv) const
