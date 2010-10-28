#include <bitset>
#include "sli.h"

unsigned MemoryChunk::serial_start = 0xbeeffeed;

MemoryChunk *MemoryChunk::allocate()
{
	MemoryChunk *mc = new MemoryChunk();
	mc->serial = serial_start++;
	return mc;
}

MemoryChunk *MemoryChunk::dupeSelf() const
{
	MemoryChunk *r = new MemoryChunk();
	memcpy(r, this, sizeof(*r));
	return r;
}

void MemoryChunk::write(unsigned offset, const unsigned long *source, unsigned nr_bytes,
			unsigned long sa)
{
	assert(!frozen);
	assert(offset < size);
	assert(offset + nr_bytes <= size);
	for (unsigned x = 0; x < nr_bytes; x++) {
		content[offset + x] = source[x];
	}
}

void MemoryChunk::read(unsigned offset, unsigned long *dest, unsigned nr_bytes,
		       unsigned long *storeAddr) const
{
	if (storeAddr)
		*storeAddr = 0xbeeffeed;
	assert(offset < size);
	assert(offset + nr_bytes <= size);
	for (unsigned x = 0; x < nr_bytes; x++)
		dest[x] = content[offset + x];
}
