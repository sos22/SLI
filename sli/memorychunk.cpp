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

void
MemoryChunk<unsigned long>::sanity_check(void) const
{
#ifndef NDEBUG
	unsigned long desired_csum;
	unsigned x;
	desired_csum = 0;
	for (x = 0; x < size; x++)
		desired_csum += content[x];
	assert(desired_csum == checksum);
#endif
}

