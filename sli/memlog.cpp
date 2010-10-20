#include "sli.h"

InterpretResult LogWriter::recordEvent(Thread *thr, MachineState *ms, ThreadEvent *evt)
{
	CasEvent *ce = dynamic_cast<CasEvent *>(evt);
	InterpretResult res;

	if (ce) {
		LogRecord *lr1, *lr2;
		res = ce->fake(ms, &lr1, &lr2);
		if (lr1)
			append(lr1, evt->when.idx);
		if (lr2)
			append(lr2, evt->when.idx);
	} else {
		LogRecord *lr;
		res = evt->fake(ms, &lr);
		if (lr)
			append(lr, evt->when.idx);
	}
	return res;
}

void MemLog::append(LogRecord *lr, unsigned long ignore)
{
	content->push_back(lr);
}

LogRecord *MemLog::read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const
{
	unsigned o = unwrapPtr(startPtr);
	if (o < offset) {
		assert(parent);
		return parent->read(startPtr, outPtr);
	}
	*outPtr = mkPtr(o + 1);
	if (o - offset >= content->size())
		return NULL;
	return (*content)[o - offset];
}

void MemLog::dump() const
{
	unsigned x;
	if (parent)
		parent->dump();
	for (x = 0; x < content->size(); x++) {
		printf("%d: %s\n", x + offset, (*content)[x]->name());
	}
}

void MemLog::destruct()
{
	delete content;
}

void destroy_memlog(void *_ctxt)
{
	MemLog *ctxt = (MemLog *)_ctxt;
	ctxt->destruct();
}

void MemLog::visit(HeapVisitor &hv)
{
	hv(parent);
	for (unsigned x = 0; x < content->size(); x++)
		hv((*content)[x]);
	hv(writer);
}

MemLog *MemLog::emptyMemlog()
{
	return new MemLog();
}

MemLog *MemLog::dupeSelf() const
{
	MemLog *w = emptyMemlog();
	w->parent = this;
	w->offset = offset + content->size();
	return w;
}

MemLog::MemLog()
{
	parent = NULL;
	offset = 0;
	content = new std::vector<LogRecord *>();
	writer = new Writer(this);
}

#define MK_MEM_LOG(t)
