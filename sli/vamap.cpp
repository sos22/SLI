#include <sys/mman.h>

#include "sli.h"

/* Distance in chunks */
#define dchunk(start, end) (((end) - (start))/MemoryChunk::size)

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

void VAMap::VAMapEntry::visit(PMap *pmap, HeapVisitor &hv)
{
	unsigned x;
	hv(this);
	if (prev)
		prev->visit(pmap, hv);
	if (succ)
		succ->visit(pmap, hv);
	hv(pa);
	for (x = 0; x < dchunk(start, end); x++)
	    pmap->visitPA(pa[x], hv);
}

VAMap::VAMapEntry *VAMap::VAMapEntry::alloc(unsigned long start,
					    unsigned long end,
					    PhysicalAddress *pa,
					    Protection prot,
					    AllocFlags alf)
{
       /* The macros don't cope well with :s in type names, so do it
	* by hand. */
       static VexAllocType vme_type = {
       nbytes: sizeof(VAMapEntry),
       gc_visit: NULL,
       destruct: NULL,
       name: "VAMap::VAMapEntry"
       };

       VAMapEntry *work = (VAMapEntry *)__LibVEX_Alloc(&vme_type,
						       __FILE__,
						       __LINE__);
       memset(work, 0, sizeof(*work));
       work->start = start;
       work->end = end;
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
	VAMapEntry *vme;
	vme = root;
	while (vme) {
		if (va >= vme->start && va < vme->end)
			break;
		else if (va < vme->start)
			vme = vme->prev;
		else if (va >= vme->end)
			vme = vme->succ;
		else
			abort();
	}
	if (!vme)
		return false;
	if (pa)
		*pa = vme->pa[(va - vme->start) / MemoryChunk::size] +
			((va - vme->start) % MemoryChunk::size);
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
	vme = root;
	while (vme) {
		if (vme->end <= from) {
			vme = vme->succ;
			continue;
		}
		if (from >= vme->start) {
			/* Found one which overlaps the target address
			 * -> that's definitely the best bet. */
			bestVme = vme;
			break;
		}
		if (bestVme) {
			assert(bestVme->start > from);
			assert(bestVme->start > vme->start);
		}
		bestVme = vme;
		vme = vme->prev;
	}
	if (!bestVme)
		return false;
	if (va)
		*va = bestVme->start;
	if (pa) {
		if (from >= bestVme->start)
			*pa = bestVme->pa[(from - bestVme->start)/MemoryChunk::size];
		else
			*pa = bestVme->pa[0];
	}
	if (prot)
		*prot = bestVme->prot;
	if (alf)
		*alf = bestVme->alf;
	return true;
}

void VAMap::addTranslation(unsigned long start,
			   PhysicalAddress pa,
			   Protection prot,
			   AllocFlags alf)
{
	VAMapEntry *vme;
	VAMapEntry *newVme;
	unsigned long end = start + MemoryChunk::size;

	if (!root) {
		PhysicalAddress *newPas =
			(PhysicalAddress *)LibVEX_Alloc_Bytes(sizeof(PhysicalAddress));
		*newPas = pa;
		root = VAMapEntry::alloc(start, end, newPas, prot, alf);
		return;
	}

	vme = root;
	while (1) {
		/* Don't allow overlaps */
		assert(end <= vme->start || start >= vme->end);

		/* Try to merge with an existing node. */
		if (prot == vme->prot && alf == vme->alf) {
			if (end == vme->start) {
				vme->pa = (PhysicalAddress *)LibVEX_realloc(vme->pa,
									    sizeof(vme->pa[0]) *
									    dchunk(start, vme->end));
				memmove(vme->pa + dchunk(start, vme->start) * sizeof(vme->pa[0]),
					vme->pa,
					sizeof(vme->pa[0]) * dchunk(start, vme->end));
				vme->pa[0] = pa;
				vme->start = start;
				return;
			}
			if (start == vme->end) {
				vme->pa = (PhysicalAddress *)LibVEX_realloc(vme->pa,
									    sizeof(vme->pa[0]) *
									    dchunk(vme->start, end));
				vme->pa[dchunk(vme->start, vme->end)] = pa;
				vme->end = end;
				return;
			}
		}

		/* Merge failed.  Either insert here or walk to
		 * children. */
		if (start < vme->start) {
			if (vme->prev) {
				vme = vme->prev;
			} else {
				PhysicalAddress *newPas =
					(PhysicalAddress *)LibVEX_Alloc_Bytes(sizeof(PhysicalAddress));
				*newPas = pa;
				newVme = VAMapEntry::alloc(start, end, newPas, prot, alf);
				vme->prev = newVme;
				return;
			}
		} else {
			assert(start >= vme->end);
			if (vme->succ) {
				vme = vme->succ;
			} else {
				PhysicalAddress *newPas =
					(PhysicalAddress *)LibVEX_Alloc_Bytes(sizeof(PhysicalAddress));
				*newPas = pa;
				newVme = VAMapEntry::alloc(start, end, newPas, prot, alf);
				vme->succ = newVme;
				return;
			}
		}
	}
}

bool VAMap::protect(unsigned long start, unsigned long size, Protection prot)
{
	VAMapEntry *vme;
	unsigned long end = start + size;

	vme = root;
	while (1) {
		if (!vme)
			return false;
		if (end <= vme->start) {
			vme = vme->prev;
		} else if (start >= vme->end) {
			vme = vme->succ;
		} else if (start < vme->start) {
			if (!protect(start, vme->start - start, prot))
				return false;
			return protect(vme->start, end - vme->start, prot);
		} else if (end > vme->end) {
			if (!protect(start, vme->end - start, prot))
				return false;
			return protect(vme->end, end - vme->end, prot);
		} else if (start != vme->start) {
			vme->split(start);
		} else if (end != vme->end) {
			vme->split(end);
		} else {
			vme->prot = prot;
			return true;
		}
	}
}

void VAMap::unmap(unsigned long start, unsigned long size)
{
	VAMapEntry *vme;
	unsigned long end = start + size;
	VAMapEntry **pprev;

	pprev = &root;
	vme = root;
	while (1) {
		if (!vme)
			return;
		if (end <= vme->start) {
			pprev = &vme->prev;
			vme = vme->prev;
		} else if (start >= vme->end) {
			pprev = &vme->succ;
			vme = vme->succ;
		} else if (start < vme->start) {
			unmap(start, vme->start - start);
			unmap(vme->start, end - vme->start);
			return;
		} else if (end > vme->end) {
			unmap(start, vme->end - start);
			unmap(vme->end, end - vme->end);
		} else if (start != vme->start) {
			vme->split(start);
		} else if (end != vme->end) {
			vme->split(end);
		} else {
			*pprev = NULL;
			return;
		}
	}

}

VAMap *VAMap::empty(PMap *pmap)
{
	VAMap *work = LibVEX_Alloc_VAMap();

	memset(work, 0, sizeof(*work));
	work->pmap = pmap;
	return work;
}

void VAMap::visit(HeapVisitor &hv) const
{
	hv(pmap);
	root->visit(pmap, hv);
}

void VAMap::VAMapEntry::split(unsigned long at)
{
	assert(at >= start);
	assert(at <= end);
	if (at == start || at == end)
		return;
	VAMapEntry *newVme;
	if (!prev) {
		newVme = alloc(start, at, pa, prot, alf);
		start = at;
		pa = (PhysicalAddress *)LibVEX_Alloc_Bytes(sizeof(pa[0]) * dchunk(start, end));
		memcpy(pa,
		       newVme->pa + dchunk(newVme->start, newVme->end),
		       sizeof(pa[0]) * dchunk(start, end));
		newVme->pa =
			(PhysicalAddress *)LibVEX_realloc(newVme->pa,
							  sizeof(pa[0]) * dchunk(newVme->start, newVme->end));
		prev = newVme;
	} else {
		PhysicalAddress *newPas = (PhysicalAddress *)LibVEX_Alloc_Bytes(sizeof(pa[0]) * dchunk(at, end));
		memcpy(newPas,
		       pa + dchunk(start, at),
		       sizeof(pa[0]) * dchunk(at, end));
		newVme = alloc(at, end, newPas, prot, alf);
		end = at;
		newVme->succ = succ;
		succ = newVme;
		pa = (PhysicalAddress *)LibVEX_realloc(pa, sizeof(pa[0]) * dchunk(start, end));
	}
}
