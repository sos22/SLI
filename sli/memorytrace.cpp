#include "sli.h"

class MemTraceMaker : public EventRecorder {
	MemoryTrace *mt;
public:
	MemTraceMaker(MemoryTrace *_mt)
		: mt(_mt)
	{
	}
	void record(Thread *thr, ThreadEvent *evt);
	void visit(HeapVisitor &hv) { hv(mt); }
	void destruct() {}
	NAMED_CLASS
};
void
MemTraceMaker::record(Thread *thr, ThreadEvent *evt)
{
	if (const LoadEvent *le = dynamic_cast<const LoadEvent *>(evt)) {
		if (address_is_interesting(thr->tid, le->addr)) {
			MemoryAccess *ma = new MemoryAccessLoad(*le);
			assert_gc_allocated(ma);
			mt->push_back(ma);
		}
	} else if (const StoreEvent *se = dynamic_cast<const StoreEvent *>(evt)) {
		if (address_is_interesting(thr->tid, se->addr)) {
			MemoryAccess *ma = new MemoryAccessStore(*se);
			assert_gc_allocated(ma);
			mt->push_back(ma);
		}
	}
}
MemoryTrace *
MemoryTrace::get(VexPtr<MachineState> &ms,
		 VexPtr<LogReader> &lf,
		 LogReaderPtr ptr,
		 GarbageCollectionToken t)
{
	VexPtr<MemoryTrace> work(new MemoryTrace);
	VexPtr<MemTraceMaker> mtm(new MemTraceMaker(work));
	Interpreter i(ms->dupeSelf());
	VexPtr<LogWriter> dummy(NULL);
	VexPtr<EventRecorder> mtm2(mtm);
	i.replayLogfile(lf, ptr, t, NULL, dummy, mtm2);
	return work;
}

void MemoryTrace::dump() const
{
	for (std::vector<MemoryAccess*>::const_iterator it = content.begin();
	     it != content.end();
	     it++)
		(*it)->dump();
}

#define MK_MEMTRACE(t)
