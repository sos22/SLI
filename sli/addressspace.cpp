#include <sys/mman.h>
#include <stdlib.h>
#include <string.h>

#include "sli.h"

void AddressSpace::allocateMemory(unsigned long start, unsigned long size,
				  AddressSpace::Protection prot)
{
	AddressSpace::AddressSpaceEntry *ase, **pprev, *newAse;
	unsigned long end = start + size;

	/* Trim any existing overlapping ases */
	pprev = &head;
	ase = *pprev;
	while (ase) {
		if (end >= ase->end) {
			if (start >= ase->end) {
				pprev = &ase->next;
			} else if (start > ase->start) {
				ase->end = start;
				pprev = &ase->next;
			} else {
				*pprev = ase->next;
				delete ase;
			}
		} else if (end > ase->start) {
			if (start <= ase->start) {
				pprev = &ase->next;
				ase->start = end;
			} else {
				newAse = new AddressSpace::AddressSpaceEntry(end, ase->end, ase->prot,
									     malloc(newAse->end - newAse->start));
				memcpy(newAse->content,
				       (const void *)((unsigned long)ase->content + newAse->start - ase->start),
				       newAse->end - newAse->start);
				ase->end = start;
				newAse->next = ase->next;
				ase->next = newAse;
				pprev = &newAse->next;
			}
		} else {
			pprev = &ase->next;
		}
		ase = *pprev;
	}

	newAse = new AddressSpace::AddressSpaceEntry(start, end, prot, malloc(size));
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
	if (newBrk == 0)
		return brkptr;
	abort();
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
