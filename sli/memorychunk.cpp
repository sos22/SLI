#include "sli.h"

template <typename ait>
MemoryChunk<ait> *MemoryChunk<ait>::allocate()
{
	void *r = LibVEX_Alloc_Bytes(sizeof(MemoryChunk<ait>));
	memset(r, 0, sizeof(MemoryChunk<ait>));
	return new (r) MemoryChunk<ait>();
}

template <typename ait>
MemoryChunk<ait> *MemoryChunk<ait>::dupeSelf() const
{
	MemoryChunk<ait> *r = (MemoryChunk<ait> *)LibVEX_Alloc_Bytes(sizeof(MemoryChunk<ait>));
	memcpy(r, this, sizeof(*r));
	return r;
}

template <typename ait>
void MemoryChunk<ait>::write(unsigned offset, const ait *source, unsigned nr_bytes)
{
	assert(offset < size);
	assert(offset + nr_bytes <= size);
	for (unsigned x = 0; x < nr_bytes; x++)
		content[offset + x] = force(source[x]);
}

template <typename ait>
void MemoryChunk<ait>::read(unsigned offset, ait *dest, unsigned nr_bytes) const
{
	assert(offset < size);
	assert(offset + nr_bytes <= size);
	for (unsigned x = 0; x < nr_bytes; x++)
		dest[x] = import_ait<unsigned long, ait>(content[offset + x]);
}

template <typename ait> template <typename new_type>
MemoryChunk<new_type> *MemoryChunk<ait>::abstract() const
{
	MemoryChunk<new_type> *work =
		new (LibVEX_Alloc_Bytes(sizeof(MemoryChunk<new_type>)))
		MemoryChunk<new_type>();
	for (unsigned x = 0; x < size; x++)
		work->content[x] = content[x];
	return work;
}

#define MK_MEMORYCHUNK(t)
