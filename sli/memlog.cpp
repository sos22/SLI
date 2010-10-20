#include "sli.h"

template <typename ait>
InterpretResult LogWriter<ait>::recordEvent(Thread *thr, MachineState *ms, ThreadEvent *evt)
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

template <typename ait>
void MemLog<ait>::append(LogRecord *lr, unsigned long ignore)
{
	content->push_back(lr);
}

template <typename ait>
LogRecord *MemLog<ait>::read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const
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

template <typename ait>
void MemLog<ait>::dump() const
{
	unsigned x;
	if (parent)
		parent->dump();
	for (x = 0; x < content->size(); x++) {
		printf("%d: %s\n", x + offset, (*content)[x]->name());
	}
}

template <typename ait>
void MemLog<ait>::destruct()
{
	delete content;
}

template <typename ait>
void destroy_memlog(void *_ctxt)
{
	MemLog<ait> *ctxt = (MemLog<ait> *)_ctxt;
	ctxt->destruct();
}

template <typename ait>
void MemLog<ait>::visit(HeapVisitor &hv)
{
	hv(parent);
	for (unsigned x = 0; x < content->size(); x++)
		hv((*content)[x]);
	hv(writer);
}

template <typename ait>
static void visit_memlog(const void *_ctxt, HeapVisitor &hv)
{
	const MemLog<ait> *ctxt = (const MemLog<ait> *)_ctxt;
	ctxt->visit(hv);
}

template <typename ait>
MemLog<ait> *MemLog<ait>::emptyMemlog()
{
	return new MemLog<ait>();
}

template <typename ait>
MemLog<ait> *MemLog<ait>::dupeSelf() const
{
	MemLog<ait> *w = emptyMemlog();
	w->parent = this;
	w->offset = offset + content->size();
	return w;
}

template <typename ait>
MemLog<ait>::MemLog()
{
	parent = NULL;
	offset = 0;
	content = new std::vector<LogRecord *>();
	writer = new Writer(this);
}

#define MK_MEM_LOG(t)						       \
	template MemLog<t> *MemLog<t>::dupeSelf() const;	       \
	template MemLog<t>::MemLog();				       \
	template MemLog<t> *MemLog<t>::emptyMemlog();		       \
	template void MemLog<t>::append(LogRecord *lr, unsigned long)
