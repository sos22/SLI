#include "sli.h"

MemTracePool *
MemTracePool::get(VexPtr<MachineState> &base_state,
		  ThreadId ignoredThread,
		  GarbageCollectionToken token)
{
	VexPtr<MemTracePool> t(new MemTracePool());
	t.get()->content = new contentT();
	unsigned x;
	for (x = 0; x < base_state->threads->size(); x++) {
		ThreadId tid = base_state->threads->index(x)->tid;
		if (tid == ignoredThread)
			continue;
		MachineState *ms = base_state->dupeSelf();
		Interpreter i(ms);
		MemoryTrace *v;
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

gc_map<ThreadId, Maybe<unsigned> > *MemTracePool::firstRacingAccessMap()
{
	gc_map<ThreadId, Maybe<unsigned> > *work = new gc_map<ThreadId, Maybe<unsigned> >();
	for (class contentT::iterator outerIt = content->begin();
	     outerIt != content->end();
	     outerIt++) {
		ThreadId tid = outerIt.key();
		MemoryTrace *v = outerIt.value();
		assert(v);
		unsigned mem_index;
		for (mem_index = 0; mem_index < v->size(); mem_index++) {
			MemoryAccess *ma = (*v)[mem_index];
			for (class contentT::iterator innerIt = content->begin();
			     innerIt != content->end();
			     innerIt++) {
				ThreadId other_tid = innerIt.key();
				if (other_tid == tid)
					continue;
				MemoryTrace *other_v = innerIt.value();
				for (unsigned other_access = 0;
				     other_access < other_v->size();
				     other_access++) {
					MemoryAccess *other_ma = (*other_v)[other_access];
					if (force(other_ma->addr + mkConst<unsigned long>(other_ma->size) <= ma->addr ||
						  other_ma->addr >= ma->addr + mkConst<unsigned long>(ma->size)) )
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

void MemTracePool::visit(HeapVisitor &hv)
{
	hv(content);
}

#define MK_MEMTRACE_POOL(t)
