#include "sli.h"

#ifndef TRACE_PMAP
#define TRACE_PMAP 0
#endif

template <typename ait>
PMapEntry<ait> *PMapEntry<ait>::alloc(PhysicalAddress pa,
				      MemoryChunk<ait> *mc,
				      bool readonly)
{
	PMapEntry<ait> *work = new PMapEntry<ait>();
	work->pa = pa;
	work->mc = mc;
	work->readonly = readonly;
	work->next = NULL;
	work->pprev = NULL;
	return work;
}

template <typename ait>
PMapEntry<ait> *PMap<ait>::findPme(PhysicalAddress pa, unsigned h) const
{
	PMapEntry<ait> *pme;
	for (pme = heads[h];
	     pme != NULL && (pa < pme->pa ||
			     pa >= pme->pa + MemoryChunk<ait>::size);
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

template <typename ait>
MemoryChunk<ait> *PMap<ait>::lookup(PhysicalAddress pa, unsigned long *mc_start)
{
	unsigned h = paHash(pa);
	PMapEntry<ait> *pme = findPme(pa, h);
	if (pme) {
		if (pme->readonly) {
#if TRACE_PMAP
			printf("%p: COW %p for %lx\n", this, pme->mc,
			       pa._pa);
#endif
			pme->mc = pme->mc->dupeSelf();
			pme->readonly = false;
		}
		*mc_start = pa - pme->pa;
#if TRACE_PMAP
		printf("%p: %lx -> %p\n", this, pa._pa, pme->mc);
#endif
		return pme->mc;
	} else if (!parent) {
		return NULL;
	} else {
		const MemoryChunk<ait> *parent_mc = parent->lookupConst(pa, mc_start, false);
		if (!parent_mc)
			return NULL;

		PMapEntry<ait> *newPme;
		newPme = PMapEntry<ait>::alloc(pa - *mc_start, parent_mc->dupeSelf(), false);
		newPme->next = heads[h];
		newPme->pprev = &heads[h];
		if (newPme->next)
			newPme->next->pprev = &newPme->next;
		heads[h] = newPme;

#if TRACE_PMAP
		printf("%p: pull up non-const %lx -> %p from %p\n", this,
		       pa._pa, newPme->mc, parent_mc);
#endif
		return newPme->mc;
	}
}

template <typename ait>
const MemoryChunk<ait> *PMap<ait>::lookupConst(PhysicalAddress pa, unsigned long *mc_start,
					       bool pull_up) const
{
	unsigned h = paHash(pa);
	PMapEntry<ait> *pme = findPme(pa, h);
	if (pme) {
		*mc_start = pa - pme->pa;
#if TRACE_PMAP
		printf("%p: %lx const -> %p\n", this, pa._pa, pme->mc);
#endif
		return pme->mc;
	} else if (parent) {
		const MemoryChunk<ait> *parent_mc = parent->lookupConst(pa, mc_start, false);
		if (pull_up) {
			PMapEntry<ait> *newPme;
			newPme = PMapEntry<ait>::alloc(pa - *mc_start, const_cast<MemoryChunk<ait> *>(parent_mc), true);
			newPme->next = heads[h];
			newPme->pprev = &heads[h];
			if (newPme->next)
				newPme->next->pprev = &newPme->next;
			heads[h] = newPme;
#if TRACE_PMAP
			printf("%p: pull up const %lx -> %p\n", this,
			       pa._pa, parent_mc);
#endif
		}
		return parent_mc;
	} else {
		return NULL;
	}
}

template <typename ait>
PhysicalAddress PMap<ait>::introduce(MemoryChunk<ait> *mc)
{
	PhysicalAddress pa = nextPa;
	mc->base = pa;
	nextPa = nextPa + MemoryChunk<ait>::size;
	PMapEntry<ait> *pme = PMapEntry<ait>::alloc(pa, mc, false);
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

template <typename ait>
PMap<ait> *PMap<ait>::empty()
{
	PMap<ait> *work = allocator.alloc();

	memset(work, 0, sizeof(*work));
	new (work) PMap<ait> ();

	work->nextPa._pa = 0xbeef0000;
	return work;	
}

template <typename ait>
PMap<ait> *PMap<ait>::dupeSelf(void) const
{
	PMap<ait> *work = empty();
	
	work->nextPa = nextPa;
	work->parent = this;
	return work;
}

template <typename ait>
unsigned PMap<ait>::paHash(PhysicalAddress pa)
{
	return (pa._pa / MemoryChunk<ait>::size) % nrHashBuckets;
}

template <typename ait>
void PMap<ait>::visitPA(PhysicalAddress pa, HeapVisitor &hv) const
{
	unsigned h = paHash(pa);
	PMapEntry<ait> *pme;
	for (pme = heads[h];
	     pme != NULL && (pa < pme->pa ||
			     pa >= pme->pa + MemoryChunk<ait>::size);
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

template <typename ait>
void PMap<ait>::visit(HeapVisitor &hv) const
{
	hv(parent);
}

template <typename ait> template <typename new_type>
PMap<new_type> *PMap<ait>::abstract() const
{
	PMap<new_type> *work =
		new (PMap<new_type>::allocator.alloc()) PMap<new_type>();
	work->nextPa = nextPa;
	if (parent)
		work->parent = parent->abstract<new_type>();
	else
		work->parent = NULL;
	for (unsigned x = 0; x < nrHashBuckets; x++) {
		PMapEntry<new_type> **p = &work->heads[x];
		for (PMapEntry<ait> *src = heads[x];
		     src;
		     src = src->next) {
			PMapEntry<new_type> *d;
			d = PMapEntry<new_type>::alloc(src->pa,
						       src->mc->abstract<new_type>(),
						       src->readonly);
			d->pprev = p;
			*p = d;
			p = &d->next;
		}
	}
	return work;
}

template <typename ait> VexAllocTypeWrapper<PMap<ait> > PMap<ait>::allocator;

#define MK_PMAP(t)							\
	template MemoryChunk<t> *PMap<t>::lookup(PhysicalAddress pa,	\
						 unsigned long *mc_start); \
	template const MemoryChunk<t> *PMap<t>::lookupConst(PhysicalAddress pa, \
							    unsigned long *mc_start, \
							    bool pull_up) const; \
	template PhysicalAddress PMap<t>::introduce(MemoryChunk<t> *mc); \
	template PMap<t> *PMap<t>::empty();				\
	template PMap<t> *PMap<t>::dupeSelf() const;			\
	template void PMap<t>::visitPA(PhysicalAddress pa,		\
				       HeapVisitor &hv) const;		\
	template void PMap<t>::visit(HeapVisitor &hv) const

