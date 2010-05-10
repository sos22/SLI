#include "sli.h"

DECLARE_VEX_TYPE(PMap)
DEFINE_VEX_TYPE(PMap);

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
					MemoryChunk *mc)
{
       /* The macros don't cope well with :s in type names, so do it
	* by hand. */
       static VexAllocType pme_type = {
       nbytes: sizeof(PMapEntry),
       gc_visit: NULL,
       destruct: destruct_pme,
       name: "PMap::PMapEntry"
       };

       PMapEntry *work = (PMapEntry *)__LibVEX_Alloc(&pme_type,
						     __FILE__,
						     __LINE__);
       work->pa = pa;
       work->mc = mc;
       work->next = NULL;
       work->pprev = NULL;
       return work;
}

MemoryChunk *PMap::lookup(PhysicalAddress pa, unsigned long *mc_start)
{
	unsigned h = paHash(pa);
	PMapEntry *pme;
	for (pme = heads[h];
	     pme != NULL && (pa < pme->pa ||
			     pa >= pme->pa + MemoryChunk::size);
	     pme = pme->next)
		;
	if (pme) {
		*mc_start = pa - pme->pa;
		return pme->mc;
	}
	if (!parent)
		return NULL;

	const MemoryChunk *parent_mc = parent->lookupConst(pa, mc_start);
	if (!parent_mc)
		return NULL;

	PMapEntry *newPme;
	newPme = PMapEntry::alloc(pa - *mc_start, parent_mc->dupeSelf());
	newPme->next = heads[h];
	newPme->pprev = &heads[h];
	if (newPme->next)
		newPme->next->pprev = &newPme->next;
	heads[h] = newPme;

	return newPme->mc;
}

const MemoryChunk *PMap::lookupConst(PhysicalAddress pa, unsigned long *mc_start) const
{
	unsigned h = paHash(pa);
	const PMapEntry *pme;
	for (pme = heads[h];
	     pme != NULL && (pa < pme->pa ||
			     pa >= pme->pa + MemoryChunk::size);
	     pme = pme->next)
		;
	if (!pme) {
		if (parent)
			return parent->lookupConst(pa, mc_start);
		else
			return NULL;
	}
	*mc_start = pa - pme->pa;
	return pme->mc;
}

PhysicalAddress PMap::introduce(MemoryChunk *mc)
{
	PhysicalAddress pa = nextPa;
	nextPa = nextPa + MemoryChunk::size;
	PMapEntry *pme = PMapEntry::alloc(pa, mc);
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

void PMap::visit(HeapVisitor &hv)
{
	hv(parent);
}
