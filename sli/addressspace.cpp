#include <sys/mman.h>
#include <stdlib.h>
#include <string.h>

#include "sli.h"

#define PAGE_MASK (~4095)

void
AddressSpace::allocateMemory(unsigned long _start, unsigned long _size,
			     VAMap::Protection prot, VAMap::AllocFlags flags)
{
	unsigned long start = _start;
	unsigned long size = _size;
	assert(!(start & ~PAGE_MASK));
	assert(!(size & ~PAGE_MASK));

	vamap->unmap(start, size);
	while (size != 0) {
		MemoryChunk *chunk = new MemoryChunk();
		PhysicalAddress pa = pmap->introduce(chunk);
		vamap->addTranslation(start, pa, prot, flags);
		start += MemoryChunk::size;
		size -= MemoryChunk::size;
	}
}

bool
AddressSpace::copyToClient(unsigned long start, unsigned size,
			   const void *contents)
{
	unsigned long *buf = (unsigned long *)malloc(sizeof(unsigned long) * size);
	bool fault;

	for (unsigned x = 0; x < size; x++)
		buf[x] = ((unsigned char *)contents)[x];
	fault = false;
	try {
		writeMemory(start, size, buf);
	} catch (BadMemoryException &e) {
		fault = true;
	}
	free(buf);
	return fault;
}

void
AddressSpace::writeMemory(unsigned long _start, unsigned size,
			  const unsigned long *contents)
{
	unsigned long start = _start;
	unsigned off = 0;

	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			unsigned long mc_start;
			unsigned to_copy_this_time;
			MemoryChunk *mc = pmap->lookup(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time > mc->size - mc_start)
				to_copy_this_time = mc->size - mc_start;
			mc->write(mc_start, contents, to_copy_this_time);

			start += to_copy_this_time;
			size -= to_copy_this_time;
			off += to_copy_this_time;
			contents = contents + to_copy_this_time;
		} else {
			throw BadMemoryException(true, _start, size);
		}
	}
}

void AddressSpace::readMemory(unsigned long _start, unsigned size,
			      unsigned long *contents)
{
	unsigned long start = _start;
	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			unsigned long mc_start;
			unsigned to_copy_this_time;
			const MemoryChunk *mc = pmap->lookupConst(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time > mc->size - mc_start)
				to_copy_this_time = mc->size - mc_start;
			mc->read(mc_start, contents, to_copy_this_time);

			start += to_copy_this_time;
			size -= to_copy_this_time;
			contents = contents + to_copy_this_time;
		} else {
			throw BadMemoryException(false, _start, size);
		}
	}
}

bool AddressSpace::isReadable(unsigned long _start)
{
	unsigned long start = _start;
	PhysicalAddress pa;
	VAMap::Protection prot(0);
	if (!vamap->translate(start, &pa, &prot))
		return false;
	if (!prot.readable)
		return false;
	return true;
}

AddressSpace *AddressSpace::initialAddressSpace()
{
	AddressSpace *work = new AddressSpace();
	work->pmap = PMap::empty();
	work->vamap = VAMap::empty();
	return work;	
}

void AddressSpace::visit(HeapVisitor &hv)
{
	hv(pmap);
	vamap->visit(vamap, hv, pmap);
}
