#include "sli.h"

template <typename ait>
MemoryTrace<ait>::MemoryTrace()
	: content()
{  
}

template <typename ait>
class MemTraceMaker : public EventRecorder<ait> {
	MemoryTrace<ait> *mt;
public:
	MemTraceMaker(MemoryTrace<ait> *_mt)
		: mt(_mt)
	{
	}
	void record(Thread<ait> *thr, const ThreadEvent<ait> *evt);
};
template <typename ait> void
MemTraceMaker<ait>::record(Thread<ait> *thr, const ThreadEvent<ait> *evt)
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
			      LogReaderPtr ptr)
{
	MemTraceMaker<ait> mtm(this);
	Interpreter<ait> i(ms->dupeSelf());
	i.replayLogfile(lf, ptr, NULL, NULL, &mtm);
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
					     LogReaderPtr);		\
	template void MemoryTrace<t>::dump() const
