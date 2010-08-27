#include <bitset>
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
	MemoryChunk<abstract_interpret_value> *work = new MemoryChunk<abstract_interpret_value>();
	work->headLookaside = NULL;
	work->underlying = this;
	work->base = base;
	return work;
}

MemoryChunk<abstract_interpret_value> *MemoryChunk<abstract_interpret_value>::allocate()
{
	return new MemoryChunk<abstract_interpret_value>();
}

MemoryChunk<abstract_interpret_value> *MemoryChunk<abstract_interpret_value>::dupeSelf() const
{
	MemoryChunk<abstract_interpret_value> *r = new MemoryChunk<abstract_interpret_value>();
	lookasideChainFrozen = true;
	memcpy(r, this, sizeof(*r));
	return r;
}

EventTimestamp MemoryChunk<abstract_interpret_value>::read(unsigned offset,
							   abstract_interpret_value *dest,
							   unsigned nr_bytes,
							   abstract_interpret_value *storeAddr) const
{
	EventTimestamp when;
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
			dest[x] = mkConst<abstract_interpret_value>(b);
		}
	}
	return when;
}

void
MemoryChunk<abstract_interpret_value>::compact_lookaside_chain(void)
{
	MCLookasideEntry *oldHead;
	MCLookasideEntry *newHead;
	MCLookasideEntry **newTailp;
	std::bitset<size> seen;

	newHead = NULL;
	newTailp = &newHead;
	oldHead = headLookaside;

	while (oldHead) {
		bool useful = false;
		for (unsigned x = 0; x < oldHead->size; x++) {
			if (!seen.test(x + oldHead->offset))
				useful = true;
			seen.set(x + oldHead->offset);
		}
		if (useful) {
			if (lookasideChainFrozen) {
				*newTailp = oldHead->dupeSelf();
			} else {
				*newTailp = oldHead;
			}
			newTailp = &(*newTailp)->next;
		}
		oldHead = oldHead->next;
	}

	*newTailp = NULL;
	headLookaside = newHead;
	lookasideChainFrozen = false;
}


MemoryChunk<abstract_interpret_value>::MCLookasideEntry *
MemoryChunk<abstract_interpret_value>::MCLookasideEntry::dupeSelf() const
{
	MCLookasideEntry *newmcl =
		(MCLookasideEntry *)LibVEX_Alloc_Sized(&mcl_allocator,
						       sizeof(MCLookasideEntry) + sizeof(abstract_interpret_value) * size);
	*newmcl = *this;
	memcpy(newmcl->content, content, size * sizeof(content[0]));
	return newmcl;
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
	for (unsigned x = 0; x < nr_bytes; x++) {
		sanity_check_ait(source[x]);
		newmcl->content[x] = source[x];
	}
	headLookaside = newmcl;

	if (++write_counter % 256 == 0)
		compact_lookaside_chain();
}

static void visit_mcl_lookaside(const void *_ctxt, HeapVisitor &hv)
{
	const class MemoryChunk<abstract_interpret_value>::MCLookasideEntry *mcl =
		(const class MemoryChunk<abstract_interpret_value>::MCLookasideEntry *)_ctxt;
	for (unsigned x = 0; x < mcl->size; x++)
		visit_aiv(mcl->content[x], hv);
	visit_aiv(mcl->storeAddr, hv);
	hv(mcl->next);
}

VexAllocType MemoryChunk<abstract_interpret_value>::mcl_allocator =
{ -1, visit_mcl_lookaside, NULL, "mcl_lookaside" };
