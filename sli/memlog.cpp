#include "sli.h"

template <typename ait>
InterpretResult LogWriter<ait>::recordEvent(Thread<ait> *thr, MachineState<ait> *ms, ThreadEvent<ait> *evt)
{
	CasEvent<ait> *ce = dynamic_cast<CasEvent<ait> *>(evt);
	InterpretResult res;

	if (ce) {
		LogRecord<ait> *lr1, *lr2;
		res = ce->fake(ms, &lr1, &lr2);
		append(*lr1);
		if (lr2)
			append(*lr2);
	} else {
		LogRecord<ait> *lr;
		res = evt->fake(ms, &lr);
		if (lr)
			append(*lr);
	}
	return res;
}

template <typename ait>
void MemLog<ait>::append(const LogRecord<ait> &lr)
{
	content->push_back(lr.dupe());
}

template <typename ait>
LogRecord<ait> *MemLog<ait>::read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const
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
	unsigned x;
	for (x = 0; x < content->size(); x++)
		delete (*content)[x];
	delete content;
}

template <typename ait>
void destroy_memlog(void *_ctxt)
{
	MemLog<ait> *ctxt = (MemLog<ait> *)_ctxt;
	ctxt->destruct();
}

template <typename ait>
void MemLog<ait>::visit(HeapVisitor &hv) const
{
	hv(parent);
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
	void *buf = (void *)allocator.alloc();
	MemLog<ait> *work = new (buf) MemLog<ait>();
	work->content = new std::vector<LogRecord<ait> *>();
	return work;
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
}


template <typename ait>
void MemLog<ait>::forceVtable()
{
	abort();
}

template <typename ait> VexAllocTypeWrapper<MemLog<ait>, visit_object<MemLog<ait> >, destroy_memlog<ait> > MemLog<ait>::allocator;

#define MK_MEM_LOG(t)						\
	template MemLog<t> *MemLog<t>::dupeSelf() const;	\
	template VexAllocTypeWrapper<MemLog<t>, visit_object<MemLog<t> >, destroy_memlog<t> > MemLog<t>::allocator
