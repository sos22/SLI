#include <stdlib.h>
#include <string.h>

#include "sli.h"

void AddressSpace::allocateMemory(const LogRecordAllocateMemory &rec)
{
	AddressSpace::AddressSpaceEntry *ase, **pprev, *newAse;

	unsigned long start = rec.start;
	unsigned long end = rec.start + rec.size;

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
				newAse = new AddressSpace::AddressSpaceEntry;
				newAse->start = end;
				newAse->end = ase->end;
				newAse->content = malloc(newAse->end - newAse->start);
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

	newAse = new AddressSpace::AddressSpaceEntry;
	newAse->start = start;
	newAse->end = end;
	newAse->content = malloc(rec.size);
	memset(newAse->content, 0x52, rec.size);

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

void AddressSpace::writeMemory(unsigned long start, unsigned size, const void *contents)
{
	unsigned long end = start + size;

	assert(end >= start);
	while (start < end) {
		AddressSpace::AddressSpaceEntry *const ase = findAseForPointer(start);
		if (!ase)
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

void AddressSpace::readMemory(unsigned long start, unsigned size, void *contents)
{
	unsigned long end = start + size;

	assert(end >= start);
	while (start < end) {
		AddressSpace::AddressSpaceEntry *const ase = findAseForPointer(start);
		if (!ase)
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
	writeMemory(rec.client_address, rec.size, rec.contents);
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
