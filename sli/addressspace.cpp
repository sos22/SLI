#include <sys/mman.h>
#include <stdlib.h>
#include <string.h>

#include "sli.h"

void AddressSpace::releaseMemory(unsigned long start, unsigned long size)
{
	unsigned long end = start + size;
	AddressSpaceEntry *ase, **pprev;

	pprev = &head;
	for (ase = *pprev; ase; ase = *pprev) {
		/* Skip ASEs which don't intersect the target
		 * region. */
		if (ase->end <= start || end <= ase->start) {
			pprev = &ase->next;
			continue;
		}

		/* If the start of the target is in the middle of the
		   ASE, split the ASE so that next time around the ASE
		   start will be exactly the target start. */
		if (start > ase->start) {
			ase->splitAt(start);
			pprev = &ase->next;
			continue;
		}

		/* Likewise for the end */
		if (end < ase->end) {
			ase->splitAt(end);
			continue;
		}

		/* ASE is now entirely contained in target.  Cull
		 * it */
		assert(ase->start >= start);
		assert(ase->end <= end);
		*pprev = ase->next;
		delete ase;
	}
}

void AddressSpace::allocateMemory(unsigned long start, unsigned long size,
				  AddressSpace::Protection prot)
{
	/* Trim any existing overlapping ases */
	releaseMemory(start, size);

	AddressSpace::AddressSpaceEntry *newAse =
		new AddressSpace::AddressSpaceEntry(start, start + size,
						    prot, malloc(size));
	memset(newAse->content, 0, size);

	newAse->next = head;
	head = newAse;
}

AddressSpace::AddressSpaceEntry *AddressSpace::findAseForPointer(unsigned long ptr)
{
	AddressSpace::AddressSpaceEntry *ase;
	for (ase = head;
	     ase && (ase->end <= ptr || ase->start > ptr);
	     ase = ase->next)
		;
	return ase;
}

/* Split the ASE at addr, such that addr is the first byte in an ASE
   all of its own. */
void AddressSpace::AddressSpaceEntry::splitAt(unsigned long addr)
{
	assert(addr >= start);
	assert(addr <= end);
	if (addr == start || addr == end)
		return;

	AddressSpaceEntry *newAse =
		new AddressSpaceEntry(addr,
				      end,
				      prot,
				      malloc(end - addr));
	memcpy(newAse->content,
	       (const void *)((unsigned long)content + addr - start),
	       end - addr);
	newAse->next = next;
	end = addr;
	next = newAse;
	content = realloc(content, end - start);
}

void AddressSpace::protectMemory(unsigned long start, unsigned long size, Protection prot)
{
	unsigned long end = start + size;
	assert(end >= start);

	while (start != end) {
		AddressSpaceEntry *ase = findAseForPointer(start);
		assert(ase);

		/* This ASE is entirely contained within the target
		   zone.  Update its protection and advance the start
		   of the zone. */
		if (ase->start == start && ase->end <= end) {
			ase->prot = prot;
			start = ase->end;
			continue;
		}
		if (ase->start == start) {
			ase->splitAt(end);
		} else {
			ase->splitAt(start);
		}
	}
		

}

void AddressSpace::writeMemory(unsigned long start, unsigned size, const void *contents,
			       bool ignore_protection)
{
	unsigned long end = start + size;

	assert(end >= start);
	while (start < end) {
		AddressSpace::AddressSpaceEntry *const ase = findAseForPointer(start);
		if (!ase ||
		    (!ignore_protection && !ase->prot.writable))
			throw BadMemoryException(true, start, size);
		unsigned long to_copy;
		if (end > ase->end)
			to_copy = ase->end - start;
		else
			to_copy = end - start;
		memcpy((void *)((unsigned long)ase->content + start - ase->start),
		       contents,
		       to_copy);
		contents = (void *)((unsigned long)contents + to_copy);
		start += to_copy;
		size -= to_copy;
	}
}

void AddressSpace::readMemory(unsigned long start, unsigned size, void *contents,
			      bool ignore_protection)
{
	unsigned long end = start + size;

	assert(end >= start);
	while (start < end) {
		AddressSpace::AddressSpaceEntry *const ase = findAseForPointer(start);
		if (!ase ||
		    (!ignore_protection && !ase->prot.readable))
			throw BadMemoryException(false, start, size);
		unsigned long to_copy;
		if (end > ase->end)
			to_copy = ase->end - start;
		else
			to_copy = end - start;
		memcpy(contents,
		       (void *)((unsigned long)ase->content + start - ase->start),
		       to_copy);
		contents = (void *)((unsigned long)contents + to_copy);
		start += to_copy;
		size -= to_copy;
	}
}

void AddressSpace::populateMemory(const LogRecordMemory &rec)
{
	writeMemory(rec.start, rec.size, rec.contents, true);
}

const void *AddressSpace::getRawPointerUnsafe(unsigned long ptr)
{
	AddressSpace::AddressSpaceEntry *ase;

	ase = findAseForPointer(ptr);
	if (!ase)
		return NULL;
	return (const void *)((unsigned long)ase->content + ptr - ase->start);
}

unsigned long AddressSpace::setBrk(unsigned long newBrk)
{
	if (newBrk != 0) {
		if (newBrk > brkptr)
			allocateMemory(brkptr, newBrk - brkptr, Protection(true, true, false));
		else
			releaseMemory(newBrk, brkptr - newBrk);
		brkptr = newBrk;
	}
	
	return brkptr;
}

AddressSpace::Protection::Protection(unsigned prot)
{
	readable = writable = executable = false;
	if (prot & PROT_READ)
		readable = true;
	if (prot & PROT_WRITE)
		writable = true;
	if (prot & PROT_EXEC)
		executable = true;
}
