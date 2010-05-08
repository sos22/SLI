#include "sli.h"

MemoryChunk *MemoryChunk::allocate()
{
	MemoryChunk *r = (MemoryChunk *)LibVEX_Alloc_Bytes(sizeof(MemoryChunk));
	memset(r, 0, sizeof(*r));
	return r;
}


void MemoryChunk::write(unsigned offset, const void *source, unsigned nr_bytes)
{
	assert(offset < size);
	assert(offset + nr_bytes <= size);
	memcpy(content + offset, source, nr_bytes);
}

void MemoryChunk::read(unsigned offset, void *dest, unsigned nr_bytes) const
{
	assert(offset < size);
	assert(offset + nr_bytes <= size);
	memcpy(dest, content + offset, nr_bytes);
}

