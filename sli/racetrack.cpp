/* Race tracking store. */
#include "sli.h"

MemoryChunk<racetrack_value> *
MemoryChunk<racetrack_value>::dupeSelf() const
{
	MemoryChunk<racetrack_value> *mc = MemoryChunk<racetrack_value>::allocate();

	*mc = *this;

	return mc;
}

EventTimestamp
MemoryChunk<racetrack_value>::read(unsigned offset, racetrack_value *dest, unsigned nr_bytes,
				   racetrack_value *sa) const
{
	assert(offset < size);
	assert(offset + nr_bytes <= size);
	for (unsigned x = 0; x < nr_bytes; x++)
		dest[x] = mkConst<racetrack_value>(content[x + offset]);
	if (sa)
		*sa = 0;
	return EventTimestamp();
}

void MemoryChunk<racetrack_value>::write(EventTimestamp when, unsigned offset, const racetrack_value *source, unsigned nr_bytes,
					 racetrack_value sa)
{
	assert(offset < size);
	assert(offset + nr_bytes <= size);
	for (unsigned x = 0; x < nr_bytes; x++)
		content[offset + x] = force(source[x]);
}

template <>
MemoryChunk<racetrack_value> *MemoryChunk<unsigned long>::abstract() const
{
	MemoryChunk<racetrack_value> *rv = MemoryChunk<racetrack_value>::allocate();
	racetrack_value buf[size];
	unsigned x;

	for (x = 0; x < size; x++)
		buf[x] = mkConst<racetrack_value>(content[x]);
	rv->write(EventTimestamp(), 0, buf, size, mkConst<racetrack_value>(0));
	return rv;
}
