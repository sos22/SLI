#include <bitset>
#include "sli.h"

unsigned MemoryChunk<unsigned long>::serial_start = 0xbeeffeed;

MemoryChunk<unsigned long> *MemoryChunk<unsigned long>::allocate()
{
	MemoryChunk<unsigned long> *mc = new MemoryChunk<unsigned long>();
	mc->serial = serial_start++;
	return mc;
}

MemoryChunk<unsigned long> *MemoryChunk<unsigned long>::dupeSelf() const
{
	MemoryChunk<unsigned long> *r = new MemoryChunk<unsigned long>();
	sanity_check();
	memcpy(r, this, sizeof(*r));
	r->sanity_check();
	return r;
}

void MemoryChunk<unsigned long>::write(EventTimestamp when, unsigned offset, const unsigned long *source, unsigned nr_bytes,
				       unsigned long sa)
{
	assert(!frozen);
	assert(offset < size);
	assert(offset + nr_bytes <= size);
	for (unsigned x = 0; x < nr_bytes; x++) {
		checksum -= content[offset + x];
		checksum += source[x];
		content[offset + x] = source[x];
	}
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
	sanity_check();
	work->headLookaside = NULL;
	work->underlying = this;
	work->base = base;
	work->underlying_checksum = checksum;
	work->underlying_serial = serial;
	this->frozen = true;
	return work;
}

void
MemoryChunk<unsigned long>::sanity_check(void) const
{
	unsigned long desired_csum;
	unsigned x;
	desired_csum = 0;
	for (x = 0; x < size; x++)
		desired_csum += content[x];
	assert(desired_csum == checksum);
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
			if (underlying)
				underlying->read(offset + x, &b, 1);
			else
				b = 0;
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

void
MemoryChunk<abstract_interpret_value>::sanity_check(void) const
{
	if (underlying) {
		assert(underlying_checksum == underlying->checksum);
		assert(underlying_serial == underlying->serial);
	}
}

static void visit_mcl_lookaside(void *_ctxt, HeapVisitor &hv)
{
	class MemoryChunk<abstract_interpret_value>::MCLookasideEntry *mcl =
		(class MemoryChunk<abstract_interpret_value>::MCLookasideEntry *)_ctxt;
	for (unsigned x = 0; x < mcl->size; x++)
		visit_aiv(mcl->content[x], hv);
	visit_aiv(mcl->storeAddr, hv);
	hv(mcl->next);
}

VexAllocType MemoryChunk<abstract_interpret_value>::mcl_allocator =
{ -1, NULL, visit_mcl_lookaside, NULL, "mcl_lookaside" };
