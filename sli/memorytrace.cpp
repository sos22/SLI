#include "sli.h"

template <typename ait>
class MemTraceMaker : public EventRecorder<ait> {
	MemoryTrace<ait> *mt;
public:
	MemTraceMaker(MemoryTrace<ait> *_mt)
		: mt(_mt)
	{
	}
	void record(Thread<ait> *thr, ThreadEvent<ait> *evt);
	void visit(HeapVisitor &hv) { hv(mt); }
	void destruct() {}
	NAMED_CLASS
};
template <typename ait> void
MemTraceMaker<ait>::record(Thread<ait> *thr, ThreadEvent<ait> *evt)
{
	if (const LoadEvent<ait> *le = dynamic_cast<const LoadEvent<ait> *>(evt)) {
		MemoryAccess<ait> *ma = new MemoryAccessLoad<ait>(*le);
		assert_gc_allocated(ma);
		mt->push_back(ma);
	} else if (const StoreEvent<ait> *se = dynamic_cast<const StoreEvent<ait> *>(evt)) {
		MemoryAccess<ait> *ma = new MemoryAccessStore<ait>(*se);
		assert_gc_allocated(ma);
		mt->push_back(ma);
	}
}
template <typename ait> MemoryTrace<ait> *
MemoryTrace<ait>::get(VexPtr<MachineState<ait> > &ms,
		      VexPtr<LogReader<ait> > &lf,
		      LogReaderPtr ptr,
		      GarbageCollectionToken t)
{
	VexPtr<MemoryTrace<ait> > work(new MemoryTrace<ait>);
	VexPtr<MemTraceMaker<ait> > mtm(new MemTraceMaker<ait>(work));
	Interpreter<ait> i(ms->dupeSelf());
	VexPtr<LogWriter<ait> > dummy(NULL);
	VexPtr<EventRecorder<ait> > mtm2(mtm);
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
	template MemoryTrace<t> *MemoryTrace<t>::get(VexPtr<MachineState<t> >&, \
						     VexPtr<LogReader<t> > &, \
						     LogReaderPtr,	\
						     GarbageCollectionToken); \
	template void MemoryTrace<t>::dump() const
