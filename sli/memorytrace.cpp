#include "sli.h"

template <typename ait>
MemoryTrace<ait>::MemoryTrace()
	: content()
{  
}

template <typename ait>
MemoryTrace<ait>::MemoryTrace(const LogReader<ait> &lf, LogReaderPtr s)
	: content()
{
	while (LogRecord<ait> *lr = lf.read(s, &s)) {
		if (LogRecordLoad<ait> *lrm = dynamic_cast<LogRecordLoad<ait> *>(lr))
		        push_back(new MemoryAccessLoad<ait>(*lrm));
		else if (LogRecordStore<ait> *lrs = dynamic_cast<LogRecordStore<ait> *>(lr))
		        push_back(new MemoryAccessStore<ait>(*lrs));
	}
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
	template MemoryTrace<t>::MemoryTrace(const LogReader<t> &lf,	\
					     LogReaderPtr s);		\
	template void MemoryTrace<t>::dump() const
