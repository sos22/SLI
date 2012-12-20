#include "sli.h"

#ifndef TRACE_PMAP
#define TRACE_PMAP 0
#endif

static bool
operator<(const PhysicalAddress &a, const PhysicalAddress &b)
{
	return a._pa < b._pa;
}
static bool
operator>=(const PhysicalAddress &a, const PhysicalAddress &b)
{
	return a._pa >= b._pa;
}
static PhysicalAddress
operator+(const PhysicalAddress &a, unsigned long x)
{
	PhysicalAddress r;
	r._pa = a._pa + x;
	return r;
}
static unsigned long
operator-(const PhysicalAddress &a, const PhysicalAddress &b)
{
	return a._pa - b._pa;
}

PMapEntry *PMapEntry::alloc(PhysicalAddress pa,
			    MemoryChunk *mc)
{
	PMapEntry *work = new PMapEntry();
	work->pa = pa;
	work->mc = mc;
	work->next = NULL;
	work->pprev = NULL;
	return work;
}

PMapEntry *PMap::findPme(PhysicalAddress pa, unsigned h) const
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
		*mc_start = pa - pme->pa;
#if TRACE_PMAP
		printf("%p: %lx -> %p\n", this, pa._pa, pme->mc);
#endif
		return pme->mc;
	} else
		return NULL;
}

const MemoryChunk *PMap::lookupConst(PhysicalAddress pa, unsigned long *mc_start) const
{
	unsigned h = paHash(pa);
	PMapEntry *pme = findPme(pa, h);
	if (pme) {
		*mc_start = pa - pme->pa;
#if TRACE_PMAP
		printf("%p: %lx const -> %p\n", this, pa._pa, pme->mc);
#endif
		return pme->mc;
	} else
		return NULL;
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
#if TRACE_PMAP
	printf("%p: alloc %lx for %p\n", this, pa._pa, mc);
#endif
	return pa;
}

PMap *PMap::empty()
{
	PMap *work = new PMap();
	work->nextPa._pa = 0xbeef0000;
	return work;	
}

unsigned PMap::paHash(PhysicalAddress pa)
{
	return (pa._pa / MemoryChunk::size) % nrHashBuckets;
}

void PMap::visitPA(PhysicalAddress pa, HeapVisitor &hv)
{
	unsigned h = paHash(pa);

	/* Double indirection because the hv() might want to relocate
	   it. */
	PMapEntry **pme;
	
	pme = &heads[h];
	while (*pme) {
		if ( pa >= (*pme)->pa &&
		     pa < (*pme)->pa + MemoryChunk::size ) {
			hv(*pme);
			return;
		}
		pme = &(*pme)->next;
	}
	abort();
}

void
PMapEntry::relocate(PMapEntry *target, size_t sz)
{
	assert(sz >= sizeof(*this));
	if (target->next)
		target->next->pprev = &target->next;
	*target->pprev = target;
	memset(this, 0x67, sizeof(*this));
}

void
PMap::relocate(PMap *target, size_t sz)
{
	assert(sz >= sizeof(*this));
	/* The pmap head pointers are slightly weak, in the sense that
	   just being in the pmap isn't enough to keep them live (for
	   which you need an external reference from a vamap).  That
	   means that we need to manually fix them up if the GC
	   relocates us. */

	/* We've just been duplicated from *this to *target.  Fix up
	 * target's linked lists to be valid.  This will break this's
	 * linked lists, but that's okay, because they'll never be
	 * referenced again. */
	for (unsigned x = 0; x < nrHashBuckets; x++)
		if (target->heads[x])
			target->heads[x]->pprev = &target->heads[x];			
	memset(heads, 0x66, sizeof(heads));
}
