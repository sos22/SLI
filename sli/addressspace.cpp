#include <sys/mman.h>
#include <stdlib.h>
#include <string.h>

#include "sli.h"

#define PAGE_MASK (~4095)

DECLARE_VEX_TYPE(AddressSpace)
DEFINE_VEX_TYPE_NO_DESTRUCT(AddressSpace, {ths->visit(visit);});

void AddressSpace::allocateMemory(unsigned long start, unsigned long size,
				  VAMap::Protection prot, VAMap::AllocFlags flags)
{
	assert(!(start & ~PAGE_MASK));
	assert(!(size & ~PAGE_MASK));

	vamap->unmap(start, size);
	while (size != 0) {
		MemoryChunk *chunk = MemoryChunk::allocate();
		PhysicalAddress pa = pmap->introduce(chunk);
		vamap->addTranslation(start, pa, prot, flags);
		start += MemoryChunk::size;
		size -= MemoryChunk::size;
	}
}

void AddressSpace::releaseMemory(unsigned long start, unsigned long size)
{
	vamap->unmap(start, size);
}

void AddressSpace::protectMemory(unsigned long start, unsigned long size,
				 VAMap::Protection prot)
{
	vamap->protect(start, size, prot);
}

void AddressSpace::writeMemory(unsigned long start, unsigned size,
			       const void *contents, bool ignore_protection,
			       const Thread *thr)
{
	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if (!ignore_protection && !prot.writable)
				throw BadMemoryException(true, start, size);
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
			contents = (const void *)((unsigned long)contents + to_copy_this_time);
		} else if (thr && extendStack(start, thr->regs.rsp())) {
			continue;
		} else {
			throw BadMemoryException(true, start, size);
		}
	}
}

void AddressSpace::readMemory(unsigned long start, unsigned size,
			      void *contents, bool ignore_protection,
			      const Thread *thr)
{
	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if (!ignore_protection && !prot.readable)
				throw BadMemoryException(false, start, size);
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
			contents = (void *)((unsigned long)contents + to_copy_this_time);
		} else if (thr && extendStack(start, thr->regs.rsp())) {
			/* This is what Linux does, but it doesn't
			   make a great deal of sense: any time you
			   hit this the program will definitely have
			   accessed uninitialised stack memory, so
			   it's definitely not a good thing. */
			printf("Huh? Extended stack for a read?\n");
			continue;
		} else {
			throw BadMemoryException(false, start, size);
		}
	}
}

bool AddressSpace::isAccessible(unsigned long start, unsigned size,
				bool isWrite, const Thread *thr)
{
	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if ((!isWrite && !prot.readable) ||
			    ( isWrite && !prot.writable))
				return false;
			unsigned long mc_start;
			unsigned to_copy_this_time;
			MemoryChunk *mc = pmap->lookup(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time >
			    mc_start + mc->size - start)
				to_copy_this_time = mc_start + mc->size - start;

			start += to_copy_this_time;
			size -= to_copy_this_time;
		} else if (extendStack(start, thr->regs.rsp())) {
			continue;
		} else {
			return false;
		}
	}
	return true;
}

unsigned long AddressSpace::setBrk(unsigned long newBrk)
{
	unsigned long newBrkMap = (newBrk + 4095) & PAGE_MASK;

	if (newBrk != 0) {
		if (newBrkMap > brkMapPtr)
			allocateMemory(brkMapPtr, newBrkMap - brkMapPtr, VAMap::Protection(true, true, false));
		else
			releaseMemory(newBrkMap, brkMapPtr - newBrkMap);
		brkptr = newBrk;
		brkMapPtr = newBrkMap;
	}

	return brkptr;
}

AddressSpace *AddressSpace::initialAddressSpace(unsigned long initialBrk)
{
       AddressSpace *work;

       assert(!(initialBrk & ~PAGE_MASK));
       work = LibVEX_Alloc_AddressSpace();
       memset(work, 0, sizeof(*work));
       work->brkptr = initialBrk;
       work->brkMapPtr = initialBrk + 4096;
       work->pmap = PMap::empty();
       work->vamap = VAMap::empty(work->pmap);
       return work;	
}

AddressSpace *AddressSpace::dupeSelf() const
{
       AddressSpace *work = LibVEX_Alloc_AddressSpace();
       *work = *this;
       work->pmap = pmap->dupeSelf();
       work->vamap = vamap->dupeSelf(work->pmap);
       return work;
}

void AddressSpace::visit(HeapVisitor &hv) const
{
	hv(vamap);
	hv(pmap);
}

bool AddressSpace::extendStack(unsigned long ptr, unsigned long rsp)
{
	if (ptr + 65536 + 32 * sizeof(unsigned long) < rsp)
		return false;

	unsigned long va;
	VAMap::Protection prot(0);
	VAMap::AllocFlags flags(false);
	if (!vamap->findNextMapping(ptr, &va, NULL, &prot, &flags))
		return false;
	if (!flags.expandsDown)
		return false;

	allocateMemory(ptr & PAGE_MASK, va, prot, flags);
	return true;
}

void AddressSpace::sanityCheck() const
{
	vamap->sanityCheck();
}

void AddressSpace::dumpBrkPtr(LogWriter *lw) const
{
	lw->append(LogRecordInitialBrk(ThreadId(0), brkptr));
}

void AddressSpace::dumpSnapshot(LogWriter *lw) const
{
	unsigned long last_va;
	unsigned long next_va;
	PhysicalAddress pa;
	VAMap::Protection prot(0);
	VAMap::AllocFlags alf(false);
	last_va = 0;
	while (vamap->findNextMapping(last_va, &next_va, &pa, &prot, &alf)) {
		lw->append(LogRecordAllocateMemory(ThreadId(0),
						   next_va,
						   MemoryChunk::size,
						   (unsigned long)prot,
						   (unsigned long)alf));
		unsigned long off;
		MemoryChunk *mc = pmap->lookup(pa, &off);
		assert(off == 0);
		void *buf = malloc(MemoryChunk::size);
		mc->read(0, buf, MemoryChunk::size);
		lw->append(LogRecordMemory(ThreadId(0),
					   MemoryChunk::size,
					   next_va,
					   buf));
		last_va = next_va + MemoryChunk::size;
	}
}
