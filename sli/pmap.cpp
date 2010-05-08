#include "sli.h"

DECLARE_VEX_TYPE(PMap)
DEFINE_VEX_TYPE_NO_DESTRUCT(PMap, {ths->visit(visit);});

static void visit_pme(const void *_ctxt, HeapVisitor &hv)
{
	const PMap::PMapEntry *ctxt = (const PMap::PMapEntry *)_ctxt;
	hv(ctxt->next);
	hv(ctxt->mc);
}

PMap::PMapEntry *PMap::PMapEntry::alloc(PhysicalAddress pa,
					MemoryChunk *mc)
{
       /* The macros don't cope well with :s in type names, so do it
	* by hand. */
       static VexAllocType pme_type = {
       nbytes: sizeof(PMapEntry),
       gc_visit: visit_pme,
       destruct: NULL,
       name: "PMap::PMapEntry"
       };

       PMapEntry *work = (PMapEntry *)__LibVEX_Alloc(&pme_type,
						     __FILE__,
						     __LINE__);
       work->pa = pa;
       work->mc = mc;
       work->next = NULL;
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
	if (!pme)
		return NULL;
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
	heads[h] = pme;
	return pa;
}

PMap *PMap::empty()
{
	PMap *work = LibVEX_Alloc_PMap();

	memset(work, 0, sizeof(*work));

	return work;	
}

void PMap::visit(HeapVisitor &hv) const
{
	unsigned x;
	for (x = 0; x < nrHashBuckets; x++)
		hv(heads[x]);
}

unsigned PMap::paHash(PhysicalAddress pa)
{
	return (pa._pa / MemoryChunk::size) % nrHashBuckets;
}
