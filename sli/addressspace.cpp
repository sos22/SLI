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
				  AddressSpace::Protection prot,
				  AllocFlags flags)
{
	/* Trim any existing overlapping ases */
	releaseMemory(start, size);

	AddressSpace::AddressSpaceEntry *newAse =
		new AddressSpace::AddressSpaceEntry(start, start + size,
						    prot, malloc(size),
						    flags);
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
				      malloc(end - addr),
				      flags);
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

bool AddressSpace::expandStack(const Thread &thr, unsigned long ptr)
{
	/* Matches kernel stack expansion logic. */
	if (ptr + 65536 + 32 * sizeof(unsigned long) < thr.regs.regs.guest_RSP)
		return false;

	AddressSpaceEntry *currentAse, *bestAse;
	/* Find the lowest ASE above the faulting address */
	currentAse = head;
	bestAse = NULL;
	for (currentAse = head; currentAse; currentAse = currentAse->next) {
		if (currentAse->end <= ptr)
			continue;
		if (!bestAse ||
		    currentAse->start < bestAse->start)
			bestAse = currentAse;
	}
	if (!bestAse)
		return false;
	assert(bestAse->end > ptr);
	/* Shouldn't try to expand stack if we already have a mapping
	   for the relevant region. */
	assert(bestAse->start > ptr);

	if (!bestAse->flags.expandsDown)
		return false;

	ptr &= ~4095;
	bestAse->content = realloc(bestAse->content,
				   bestAse->end - ptr);
	memmove((void *)((unsigned long)bestAse->content + bestAse->start - ptr),
		bestAse->content,
		bestAse->end - bestAse->start);
	memset(bestAse->content, 0, bestAse->start - ptr);
	bestAse->start = ptr;
	return true;
}

void AddressSpace::writeMemory(unsigned long start, unsigned size,
			       const void *contents, bool ignore_protection,
			       const Thread *thr)
{
	unsigned long end = start + size;

	assert(end >= start);
	while (start < end) {
		AddressSpace::AddressSpaceEntry *const ase = findAseForPointer(start);
		if (!ase && thr && expandStack(*thr, start))
			continue;
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

void AddressSpace::readMemory(unsigned long start, unsigned size,
			      void *contents, bool ignore_protection,
			      const Thread *thr)
{
	unsigned long end = start + size;

	assert(end >= start);
	while (start < end) {
		AddressSpace::AddressSpaceEntry *const ase = findAseForPointer(start);
		if (!ase && thr && expandStack(*thr, start))
			continue;
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

AddressSpace::AllocFlags::AllocFlags(unsigned flags)
{
	expandsDown = false;
	if (flags & MAP_GROWSDOWN) {
		printf("Create a stack segment.\n");
		expandsDown = true;
	}
}

const AddressSpace::AllocFlags AddressSpace::defaultFlags(false);
