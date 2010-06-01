#include "sli.h"

MemoryChunk<unsigned long> *MemoryChunk<unsigned long>::allocate()
{
	void *r = LibVEX_Alloc_Bytes(sizeof(MemoryChunk<unsigned long>));
	memset(r, 0, sizeof(MemoryChunk<unsigned long>));
	return new (r) MemoryChunk<unsigned long>();
}

MemoryChunk<unsigned long> *MemoryChunk<unsigned long>::dupeSelf() const
{
	MemoryChunk<unsigned long> *r = (MemoryChunk<unsigned long> *)LibVEX_Alloc_Bytes(sizeof(MemoryChunk<unsigned long>));
	memcpy(r, this, sizeof(*r));
	return r;
}

void MemoryChunk<unsigned long>::write(EventTimestamp when, unsigned offset, const unsigned long *source, unsigned nr_bytes,
				       unsigned long sa)
{
	assert(offset < size);
	assert(offset + nr_bytes <= size);
	for (unsigned x = 0; x < nr_bytes; x++)
		content[offset + x] = source[x];
}

EventTimestamp MemoryChunk<unsigned long>::read(unsigned offset, unsigned long *dest, unsigned nr_bytes,
						unsigned long *storeAddr) const
{
	if (storeAddr)
		*storeAddr = 0xbeeffeed;
	assert(offset < size);
	assert(offset + nr_bytes <= size);
	for (unsigned x = 0; x < nr_bytes; x++)
		dest[x] = content[offset + x];
	return EventTimestamp();
}

template <>
MemoryChunk<abstract_interpret_value> *MemoryChunk<unsigned long>::abstract() const
{
	MemoryChunk<abstract_interpret_value> *work =
		MemoryChunk<abstract_interpret_value>::allocator.alloc();
	work->headLookaside = NULL;
	work->underlying = this;
	work->base = base;
	return work;
}

MemoryChunk<abstract_interpret_value> *MemoryChunk<abstract_interpret_value>::allocate()
{
	void *r = allocator.alloc();
	memset(r, 0, sizeof(MemoryChunk<abstract_interpret_value>));
	return new (r) MemoryChunk<abstract_interpret_value>();
}

MemoryChunk<abstract_interpret_value> *MemoryChunk<abstract_interpret_value>::dupeSelf() const
{
	MemoryChunk<abstract_interpret_value> *r = allocator.alloc();
	memcpy(r, this, sizeof(*r));
	return r;
}

EventTimestamp MemoryChunk<abstract_interpret_value>::read(unsigned offset,
							   abstract_interpret_value *dest,
							   unsigned nr_bytes,
							   abstract_interpret_value *storeAddr) const
{
	EventTimestamp when;
	if (storeAddr)
		*storeAddr = mkConst<abstract_interpret_value>(0);
	for (unsigned x = 0; x < nr_bytes; x++) {
		bool done = false;
		for (const MCLookasideEntry *mce = headLookaside;
		     !done && mce;
		     mce = mce->next) {
			if (mce->offset <= offset + x &&
			    mce->offset + mce->size > offset + x) {
				dest[x] = mce->content[offset + x - mce->offset];
				if (storeAddr) {
					*storeAddr = mce->storeAddr +
						mkConst<abstract_interpret_value>(offset + x - mce->offset);
					storeAddr = NULL;
				}
				when = mce->when;
				done = true;
			}
		}
		if (!done) {
			unsigned long b;
			underlying->read(offset + x, &b, 1);
			dest[x] = import_ait<unsigned long, abstract_interpret_value>(b,
										      ImportOriginInitialMemory::get(1, base + offset + x));
		}
	}
	return when;
}

void MemoryChunk<abstract_interpret_value>::write(EventTimestamp when,
						  unsigned offset,
						  const abstract_interpret_value *source,
						  unsigned nr_bytes,
						  abstract_interpret_value sa)
{
	MCLookasideEntry *newmcl =
		(MCLookasideEntry *)LibVEX_Alloc_Sized(&mcl_allocator,
						       sizeof(MCLookasideEntry) + sizeof(abstract_interpret_value) * nr_bytes);
	newmcl->next = headLookaside;
	newmcl->offset = offset;
	newmcl->size = nr_bytes;
	newmcl->when = when;
	newmcl->storeAddr = sa;
	for (unsigned x = 0; x < nr_bytes; x++)
		newmcl->content[x] = source[x];
	headLookaside = newmcl;
}

const VexAllocTypeWrapper<MemoryChunk<abstract_interpret_value> > MemoryChunk<abstract_interpret_value>::allocator;

static void visit_mcl_lookaside(const void *_ctxt, HeapVisitor &hv)
{
	const class MemoryChunk<abstract_interpret_value>::MCLookasideEntry *mcl =
		(const class MemoryChunk<abstract_interpret_value>::MCLookasideEntry *)_ctxt;
	for (unsigned x = 0; x < mcl->size; x++)
		visit_aiv(mcl->content[x], hv);
	visit_aiv(mcl->storeAddr, hv);
	hv(mcl->next);
}

const VexAllocType MemoryChunk<abstract_interpret_value>::mcl_allocator =
{ -1, visit_mcl_lookaside, NULL, "mcl_lookaside" };
