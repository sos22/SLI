#include "sli.h"

InterpretResult MemLog::recordEvent(Thread *thr, MachineState *ms, ThreadEvent *evt)
{
	CasEvent *ce = dynamic_cast<CasEvent *>(evt);
	InterpretResult res;

	if (ce) {
		LogRecord *lr1, *lr2;
		res = ce->fake(thr, ms, &lr1, &lr2);
		appendRecord(lr1);
		if (lr2)
			appendRecord(lr2);
	} else {
		LogRecord *lr;
		res = evt->fake(thr, ms, &lr);
		appendRecord(lr);
	}
	return res;
}

void MemLog::appendRecord(LogRecord *lr)
{
	content.push_back(lr);
}

MemLog::~MemLog()
{
	unsigned x;
	for (x = 0; x < content.size(); x++)
		delete content[x];
}

LogRecord *MemLog::read(ptr startPtr, ptr *outPtr) const
{
	unsigned o = unwrapPtr(startPtr);
	if (o >= content.size())
		return NULL;
	*outPtr = mkPtr(o + 1);
	return content[o];
}

void MemLog::dump() const
{
	unsigned x;
	for (x = 0; x < content.size(); x++) {
		printf("%d: %s\n", x, content[x]->name());
	}
}
