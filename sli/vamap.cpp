#include <sys/mman.h>

#include "sli.h"

DECLARE_VEX_TYPE(VAMap)
DEFINE_VEX_TYPE_NO_DESTRUCT(VAMap, {ths->visit(visit);});

VAMap::Protection::Protection(unsigned prot)
{
	readable = writable = executable = false;
	if (prot & PROT_READ)
		readable = true;
	if (prot & PROT_WRITE)
		writable = true;
	if (prot & PROT_EXEC)
		executable = true;
}

VAMap::AllocFlags::AllocFlags(unsigned flags)
{
       expandsDown = false;
       if (flags & MAP_GROWSDOWN) {
               printf("Create a stack segment.\n");
               expandsDown = true;
       }
 }

const VAMap::AllocFlags VAMap::defaultFlags(false);

static void visit_vme(const void *_ctxt, HeapVisitor &hv)
{
	const VAMap::VAMapEntry *ctxt = (const VAMap::VAMapEntry *)_ctxt;
	hv(ctxt->next);
}

VAMap::VAMapEntry *VAMap::VAMapEntry::alloc(unsigned long va,
					    PhysicalAddress pa,
					    Protection prot,
					    AllocFlags alf)
{
       /* The macros don't cope well with :s in type names, so do it
	* by hand. */
       static VexAllocType vme_type = {
       nbytes: sizeof(VAMapEntry),
       gc_visit: visit_vme,
       destruct: NULL,
       name: "VAMap::VAMapEntry"
       };

       VAMapEntry *work = (VAMapEntry *)__LibVEX_Alloc(&vme_type,
						       __FILE__,
						       __LINE__);
       work->next = NULL;
       work->addr = va;
       work->pa = pa;
       work->prot = prot;
       work->alf = alf;
       return work;
}

bool VAMap::translate(unsigned long va,
		      PhysicalAddress *pa,
		      Protection *prot,
		      AllocFlags *alf)
{
	memset(pa, 0, sizeof(*pa));
	VAMapEntry *vme;
	unsigned long mask = ~(MemoryChunk::size - 1);
	for (vme = head; vme; vme = vme->next)
		if ( (vme->addr & mask) == (va & mask) )
			break;
	if (!vme)
		return false;
	if (pa)
		*pa = vme->pa + (va & ~mask);
	if (prot)
		*prot = vme->prot;
	if (alf)
		*alf = vme->alf;
	return true;
}

bool VAMap::findNextMapping(unsigned long from,
			    unsigned long *va,
			    PhysicalAddress *pa,
			    Protection *prot,
			    AllocFlags *alf)
{
	VAMapEntry *vme, *bestVme;

	bestVme = NULL;
	vme = head;
	while (vme) {
		if (vme->addr >= from &&
		    (!bestVme || vme->addr < bestVme->addr))
			bestVme = vme;
		vme = vme->next;
	}
	if (!vme)
		return false;
	if (va)
		*va = vme->addr;
	if (pa)
		*pa = vme->pa;
	if (prot)
		*prot = vme->prot;
	if (alf)
		*alf = vme->alf;
	return true;
}

void VAMap::addTranslation(unsigned long va,
			   PhysicalAddress pa,
			   Protection prot,
			   AllocFlags alf)
{
	VAMapEntry *vme = VAMapEntry::alloc(va, pa, prot, alf);
	vme->next = head;
	head = vme;
}

bool VAMap::protect(unsigned long va, unsigned long size, Protection prot)
{
	unsigned long mask = ~(MemoryChunk::size - 1);
	va &= mask;
	unsigned long end = va + size;
	unsigned long va2 = va;
	while (end != va2) {
		VAMapEntry *vme;
		for (vme = head; vme; vme = vme->next)
			if ( (vme->addr & mask) == va2 )
				break;
		if (!vme)
			return false;
		va2 += MemoryChunk::size;
	}

	while (end != va) {
		VAMapEntry *vme;
		for (vme = head; vme; vme = vme->next)
			if ( (vme->addr & mask) == va )
				break;
		assert(vme);
		vme->prot = prot;
		va += MemoryChunk::size;
	}
	return true;
}

void VAMap::unmap(unsigned long start, unsigned long size)
{
	unsigned long end = start + size;

	assert(!(start & (MemoryChunk::size - 1)));
	assert(!(end & (MemoryChunk::size - 1)));
	while (start != end) {
		VAMapEntry **pprev = &head;
		VAMapEntry *vme = *pprev;
		while (vme->addr != start) {
			pprev = &vme->next;
			vme = *pprev;
		}
		if (vme)
			*pprev = vme->next;
		start += MemoryChunk::size;
	}
}

VAMap *VAMap::empty()
{
	VAMap *work = LibVEX_Alloc_VAMap();

	memset(work, 0, sizeof(*work));

	return work;
}

void VAMap::visit(HeapVisitor &hv) const
{
	hv(head);
}
