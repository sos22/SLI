#include "sli.h"

InterpretResult LogWriter::recordEvent(Thread<unsigned long> *thr, MachineState<unsigned long> *ms, ThreadEvent<unsigned long> *evt)
{
	CasEvent<unsigned long> *ce = dynamic_cast<CasEvent<unsigned long> *>(evt);
	InterpretResult res;

	if (ce) {
		LogRecord *lr1, *lr2;
		res = ce->fake(thr, ms, &lr1, &lr2);
		append(*lr1);
		if (lr2)
			append(*lr2);
	} else {
		LogRecord *lr;
		res = evt->fake(thr, ms, &lr);
		if (lr)
			append(*lr);
	}
	return res;
}

void MemLog::append(const LogRecord &lr)
{
	content->push_back(lr.dupe());
}

LogRecord *MemLog::read(ptr startPtr, ptr *outPtr) const
{
	unsigned o = unwrapPtr(startPtr);
	if (o < offset) {
		assert(parent);
		return parent->read(startPtr, outPtr);
	}
	*outPtr = mkPtr(o + 1);
	if (o - offset >= content->size())
		return NULL;
	return (*content)[o - offset]->dupe();
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
	unsigned x;
	for (x = 0; x < content->size(); x++)
		delete (*content)[x];
	delete content;
}

static void destroy_memlog(void *_ctxt)
{
	MemLog *ctxt = (MemLog *)_ctxt;
	ctxt->destruct();
}

void MemLog::visit(HeapVisitor &hv) const
{
	hv(parent);
}

static void visit_memlog(const void *_ctxt, HeapVisitor &hv)
{
	const MemLog *ctxt = (const MemLog *)_ctxt;
	ctxt->visit(hv);
}

MemLog *MemLog::emptyMemlog()
{
	static const VexAllocType vat = {
	nbytes: sizeof(MemLog),
	gc_visit: visit_memlog,
	destruct: destroy_memlog,
	name: "MemLog"
	};

	void *buf = (void *)__LibVEX_Alloc(&vat);
	MemLog *work = new (buf) MemLog();
	work->content = new std::vector<LogRecord *>();
	return work;
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
}


void MemLog::forceVtable()
{
	abort();
}
