#include "sli.h"

DECLARE_VEX_TYPE(PMap)
DEFINE_VEX_TYPE_NO_DESTRUCT(PMap, {ths->visit(visit);});

/* The PME is dead, and so is the matchinh memory chunk.  Unhook
   ourselves from the list. */
static void destruct_pme(void *_ctxt)
{
	PMap::PMapEntry *ctxt = (PMap::PMapEntry *)_ctxt;
	*ctxt->pprev = ctxt->next;
	if (ctxt->next)
		ctxt->next->pprev = ctxt->pprev;
}

PMap::PMapEntry *PMap::PMapEntry::alloc(PhysicalAddress pa,
					MemoryChunk *mc,
					bool readonly)
{
       /* The macros don't cope well with :s in type names, so do it
	* by hand. */
       static VexAllocType pme_type = {
       nbytes: sizeof(PMapEntry),
       gc_visit: NULL,
       destruct: destruct_pme,
       name: "PMap::PMapEntry"
       };

       PMapEntry *work = (PMapEntry *)__LibVEX_Alloc(&pme_type);
       work->pa = pa;
       work->mc = mc;
       work->readonly = readonly;
       work->next = NULL;
       work->pprev = NULL;
       return work;
}

PMap::PMapEntry *PMap::findPme(PhysicalAddress pa, unsigned h) const
{
	PMapEntry *pme;
	for (pme = heads[h];
	     pme != NULL && (pa < pme->pa ||
			     pa >= pme->pa + MemoryChunk::size);
	     pme = pme->next)
		;
	if (!pme)
		return NULL;
	if (pme != heads[h]) {
		/* Pull-to-front */
		*pme->pprev = pme->next;
		if (pme->next)
			pme->next->pprev = pme->pprev;
		pme->next = heads[h];
		pme->pprev = &heads[h];
		if (heads[h])
			heads[h]->pprev = &pme->next;
		heads[h] = pme;
	}
	return pme;
}

MemoryChunk *PMap::lookup(PhysicalAddress pa, unsigned long *mc_start)
{
	unsigned h = paHash(pa);
	PMapEntry *pme = findPme(pa, h);
	if (pme) {
		if (pme->readonly) {
			pme->mc = pme->mc->dupeSelf();
			pme->readonly = false;
		}
		*mc_start = pa - pme->pa;
		return pme->mc;
	} else if (!parent) {
		return NULL;
	} else {
		const MemoryChunk *parent_mc = parent->lookupConst(pa, mc_start, false);
		if (!parent_mc)
			return NULL;

		PMapEntry *newPme;
		newPme = PMapEntry::alloc(pa - *mc_start, parent_mc->dupeSelf(), false);
		newPme->next = heads[h];
		newPme->pprev = &heads[h];
		if (newPme->next)
			newPme->next->pprev = &newPme->next;
		heads[h] = newPme;

		return newPme->mc;
	}
}

const MemoryChunk *PMap::lookupConst(PhysicalAddress pa, unsigned long *mc_start,
				     bool pull_up) const
{
	unsigned h = paHash(pa);
	PMapEntry *pme = findPme(pa, h);
	if (pme) {
		*mc_start = pa - pme->pa;
		return pme->mc;
	} else if (parent) {
		const MemoryChunk *parent_mc = parent->lookupConst(pa, mc_start, false);
		if (pull_up) {
			PMapEntry *newPme;
			newPme = PMapEntry::alloc(pa - *mc_start, const_cast<MemoryChunk *>(parent_mc), true);
			newPme->next = heads[h];
			newPme->pprev = &heads[h];
			if (newPme->next)
				newPme->next->pprev = &newPme->next;
			heads[h] = newPme;
		}
		return parent_mc;
	} else {
		return NULL;
	}
}

PhysicalAddress PMap::introduce(MemoryChunk *mc)
{
	PhysicalAddress pa = nextPa;
	nextPa = nextPa + MemoryChunk::size;
	PMapEntry *pme = PMapEntry::alloc(pa, mc, false);
	unsigned h = paHash(pa);
	pme->next = heads[h];
	pme->pprev = &heads[h];
	if (pme->next)
		pme->next->pprev = &pme->next;
	heads[h] = pme;
	return pa;
}

PMap *PMap::empty()
{
	PMap *work = LibVEX_Alloc_PMap();

	memset(work, 0, sizeof(*work));

	work->nextPa._pa = 0xbeef0000;
	return work;	
}

PMap *PMap::dupeSelf(void) const
{
	PMap *work = empty();

	work->nextPa = nextPa;
	work->parent = this;
	return work;
}

unsigned PMap::paHash(PhysicalAddress pa)
{
	return (pa._pa / MemoryChunk::size) % nrHashBuckets;
}

void PMap::visitPA(PhysicalAddress pa, HeapVisitor &hv) const
{
	unsigned h = paHash(pa);
	PMapEntry *pme;
	for (pme = heads[h];
	     pme != NULL && (pa < pme->pa ||
			     pa >= pme->pa + MemoryChunk::size);
	     pme = pme->next)
		;
	if (!pme) {
		assert(parent);
		parent->visitPA(pa, hv);
	} else {
		hv(pme);
		hv(pme->mc);
	}
}

void PMap::visit(HeapVisitor &hv) const
{
	hv(parent);
}
