#include "sli.h"

template <typename ait>
class MemTraceMaker : public EventRecorder {
	MemoryTrace<ait> *mt;
public:
	MemTraceMaker(MemoryTrace<ait> *_mt)
		: mt(_mt)
	{
	}
	void record(Thread *thr, ThreadEvent *evt);
	void visit(HeapVisitor &hv) { hv(mt); }
	void destruct() {}
	NAMED_CLASS
};
template <typename ait> void
MemTraceMaker<ait>::record(Thread *thr, ThreadEvent *evt)
{
	if (const LoadEvent<ait> *le = dynamic_cast<const LoadEvent<ait> *>(evt)) {
		if (address_is_interesting(thr->tid, force(le->addr))) {
			MemoryAccess<ait> *ma = new MemoryAccessLoad<ait>(*le);
			assert_gc_allocated(ma);
			mt->push_back(ma);
		}
	} else if (const StoreEvent<ait> *se = dynamic_cast<const StoreEvent<ait> *>(evt)) {
		if (address_is_interesting(thr->tid, force(se->addr))) {
			MemoryAccess<ait> *ma = new MemoryAccessStore<ait>(*se);
			assert_gc_allocated(ma);
			mt->push_back(ma);
		}
	}
}
template <typename ait> MemoryTrace<ait> *
MemoryTrace<ait>::get(VexPtr<MachineState> &ms,
		      VexPtr<LogReader> &lf,
		      LogReaderPtr ptr,
		      GarbageCollectionToken t)
{
	VexPtr<MemoryTrace<ait> > work(new MemoryTrace<ait>);
	VexPtr<MemTraceMaker<ait> > mtm(new MemTraceMaker<ait>(work));
	Interpreter i(ms->dupeSelf());
	VexPtr<LogWriter<ait> > dummy(NULL);
	VexPtr<EventRecorder> mtm2(mtm);
	i.replayLogfile(lf, ptr, t, NULL, dummy, mtm2);
	return work;
}

template <typename ait>
void MemoryTrace<ait>::dump() const
{
	for (class std::vector<MemoryAccess<ait> *>::const_iterator it = content.begin();
	     it != content.end();
	     it++)
		(*it)->dump();
}

#define MK_MEMTRACE(t)							\
	template MemoryTrace<t>::MemoryTrace();				\
	template MemoryTrace<t> *MemoryTrace<t>::get(VexPtr<MachineState>&, \
						     VexPtr<LogReader > &, \
						     LogReaderPtr,	\
						     GarbageCollectionToken); \
	template void MemoryTrace<t>::dump() const
