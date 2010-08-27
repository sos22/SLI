#include "sli.h"

template <typename ait>
class MemTraceMaker : public EventRecorder<ait>,
		      public GarbageCollected<MemTraceMaker<ait> > {
	MemoryTrace<ait> *mt;
public:
	MemTraceMaker(MemoryTrace<ait> *_mt)
		: mt(_mt)
	{
	}
	void record(Thread<ait> *thr, ThreadEvent<ait> *evt);
	void visit(HeapVisitor &hv) const { hv(mt); }
	void destruct() {}
	NAMED_CLASS
};
template <typename ait> void
MemTraceMaker<ait>::record(Thread<ait> *thr, ThreadEvent<ait> *evt)
{
	if (const LoadEvent<ait> *le = dynamic_cast<const LoadEvent<ait> *>(evt)) {
		mt->push_back(new MemoryAccessLoad<ait>(*le));
	} else if (const StoreEvent<ait> *se = dynamic_cast<const StoreEvent<ait> *>(evt)) {
		mt->push_back(new MemoryAccessStore<ait>(*se));
	}
}
template <typename ait>
MemoryTrace<ait>::MemoryTrace(const MachineState<ait> *ms,
			      LogReader<ait> *lf,
			      LogReaderPtr ptr,
			      GarbageCollectionToken t)
{
	MemTraceMaker<ait> *mtm = new MemTraceMaker<ait>(this);
	VexGcRoot mtmroot((void **)&mtm, "mtmroot");
	Interpreter<ait> i(ms->dupeSelf());
	i.replayLogfile(lf, ptr, t, NULL, NULL, mtm);
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
	template MemoryTrace<t>::MemoryTrace(const MachineState<t> *,	\
					     LogReader<t> *,		\
					     LogReaderPtr,		\
					     GarbageCollectionToken);	\
	template void MemoryTrace<t>::dump() const
