#include "sli.h"

MemoryTrace::MemoryTrace()
	: content()
{  
}

MemoryTrace::MemoryTrace(const LogReader &lf, LogReader::ptr s)
	: content()
{
	while (LogRecord *lr = lf.read(s, &s)) {
		if (LogRecordLoad *lrm = dynamic_cast<LogRecordLoad *>(lr))
			push_back(new MemoryAccessLoad(*lrm));
		else if (LogRecordStore *lrs = dynamic_cast<LogRecordStore *>(lr))
			push_back(new MemoryAccessStore(*lrs));
		delete lr;
	}
}

void MemoryTrace::dump() const
{
	for (std::vector<MemoryAccess *>::const_iterator it = content.begin();
	     it != content.end();
	     it++)
		(*it)->dump();
}
