#include "sli.h"

template <typename ait> MemTracePool<ait> *
MemTracePool<ait>::get(VexPtr<MachineState> &base_state,
		       ThreadId ignoredThread,
		       GarbageCollectionToken token)
{
	VexPtr<MemTracePool<ait> > t(new MemTracePool<ait>());
	t.get()->content = new contentT();
	unsigned x;
	for (x = 0; x < base_state->threads->size(); x++) {
		ThreadId tid = base_state->threads->index(x)->tid;
		if (tid == ignoredThread)
			continue;
		MachineState *ms = base_state->dupeSelf();
		Interpreter i(ms);
		MemoryTrace<ait> *v;
		try {
			i.getThreadMemoryTrace(tid, &v, 100000, token);
		} catch (SliException) {
			/* Hackety hackety hack: if we get an
			   exception during replay, just stop the
			   trace. */
		}
		assert_gc_allocated(v);
		(*t->content)[tid] = v;
	}
	return t;
}

template <typename ait>
gc_map<ThreadId, Maybe<unsigned> > *MemTracePool<ait>::firstRacingAccessMap()
{
	gc_map<ThreadId, Maybe<unsigned> > *work = new gc_map<ThreadId, Maybe<unsigned> >();
	for (class contentT::iterator outerIt = content->begin();
	     outerIt != content->end();
	     outerIt++) {
		ThreadId tid = outerIt.key();
		MemoryTrace<ait> *v = outerIt.value();
		assert(v);
		unsigned mem_index;
		for (mem_index = 0; mem_index < v->size(); mem_index++) {
			MemoryAccess<ait> *ma = (*v)[mem_index];
			for (class contentT::iterator innerIt = content->begin();
			     innerIt != content->end();
			     innerIt++) {
				ThreadId other_tid = innerIt.key();
				if (other_tid == tid)
					continue;
				MemoryTrace<ait> *other_v = innerIt.value();
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
void MemTracePool<t>::visit(HeapVisitor &hv)
{
	hv(content);
}

#define MK_MEMTRACE_POOL(t)						\
	template MemTracePool<t> *MemTracePool<t>::get(VexPtr<MachineState> &, \
						       ThreadId,	\
						       GarbageCollectionToken); \
	template gc_map<ThreadId, Maybe<unsigned> > *MemTracePool<t>::firstRacingAccessMap(); \
	template void MemTracePool<t>::visit(HeapVisitor &hv)
