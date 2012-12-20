#include <sys/mman.h>

#include "sli.h"

#define TRACE_VAMAP_LOOKUP 1
#define TRACE_VAMAP_CHANGE 2
#define TRACE_VAMAP_CHANGE_DETAILS 4

#ifndef TRACE_VAMAP
#define TRACE_VAMAP 0
#endif

/* Distance in chunks */
#define dchunk(start, end) (((end) - (start))/MEMORY_CHUNK_SIZE)

void VAMap::VAMapEntry::visit(VAMapEntry *&ref, PMap *pmap, HeapVisitor &hv)
{
	unsigned x;
	hv(ref);
	if (ref->prev)
		ref->prev->visit(ref->prev, pmap, hv);
	if (ref->succ)
		ref->succ->visit(ref->succ, pmap, hv);
	hv(ref->pa);
	for (x = 0; x < dchunk(ref->start, ref->end); x++) {
		assert(ref->pa[x]._pa != 0);
		pmap->visitPA(ref->pa[x], hv);
	}
}

/* The macros don't cope well with :s in type names, so do it by
 * hand. */
static VexAllocType vme_type = {
nbytes: sizeof(VAMap::VAMapEntry),
relocate: NULL,
gc_visit: NULL,
destruct: NULL,
name: "VAMap::VAMapEntry"
};

VAMap::VAMapEntry *VAMap::VAMapEntry::alloc(unsigned long start,
					    unsigned long end,
					    PhysicalAddress *pa)
{
	VAMapEntry *work = (VAMapEntry *)__LibVEX_Alloc(&main_heap, &vme_type);
	memset(work, 0, sizeof(*work));
	work->start = start;
	work->end = end;
	work->pa = pa;
	return work;
}

VAMap::VAMapEntry *VAMap::VAMapEntry::dupeSelf() const
{
	VAMapEntry *work = (VAMapEntry *)__LibVEX_Alloc(&main_heap, &vme_type);
	*work = *this;
	if (prev)
		work->prev = prev->dupeSelf();
	if (succ)
		work->succ = succ->dupeSelf();
	work->pa =
		(PhysicalAddress *)LibVEX_Alloc_Bytes(sizeof(PhysicalAddress) * dchunk(start, end));
	memcpy(work->pa, pa, sizeof(PhysicalAddress) * dchunk(start, end));
	return work;
}

bool VAMap::translate(unsigned long va,
		      PhysicalAddress *pa) const
{
#if TRACE_VAMAP & TRACE_VAMAP_LOOKUP
	printf("%p: Translate %lx\n", this, va);
#endif
	if (parent)
		return parent->translate(va, pa);
	if (!root)
		return false;
	/* Splay the target node to the root of the tree */
	while (1) {
		if (va >= root->start && va < root->end)
			break;

		if (va < root->start) {
			if (!root->prev)
				return false;
			if (va < root->prev->start) {
				if (!root->prev->prev)
					return false;
				/* This isn't quite the normal splay
				   table zig-zig rule, but seems to
				   work a bit better for these access
				   patterns. */
				VAMapEntry *r = root;
				VAMapEntry *rp = r->prev;
				VAMapEntry *rpp = rp->prev;
				VAMapEntry *rpps = rpp->succ;
				root = rpp;
				rpp->succ = r;
				rp->prev = rpps;
			} else if (va < root->prev->end) {
				VAMapEntry *r = root;
				VAMapEntry *rp = r->prev;
				VAMapEntry *rps = rp->succ;
				root = rp;
				rp->succ = r;
				r->prev = rps;
			} else {
				if (!root->prev->succ)
					return false;
				VAMapEntry *r = root;
				VAMapEntry *rp = r->prev;
				VAMapEntry *rps = rp->succ;
				VAMapEntry *rpsp = rps->prev;
				VAMapEntry *rpss = rps->succ;
				root = rps;
				rps->prev = rp;
				rps->succ = r;
				rp->succ = rpsp;
				r->prev = rpss;
			}
		} else {
			assert(va >= root->end);
			if (!root->succ)
				return false;
			if (va < root->succ->start) {
				if (!root->succ->prev)
					return false;
				VAMapEntry *r = root;
				VAMapEntry *rs = r->succ;
				VAMapEntry *rsp = rs->prev;
				VAMapEntry *rspp = rsp->prev;
				VAMapEntry *rsps = rsp->succ;
				root = rsp;
				rsp->prev = r;
				rsp->succ = rs;
				r->succ = rspp;
				rs->prev = rsps;
			} else if (va < root->succ->end) {
				VAMapEntry *r = root;
				VAMapEntry *rs = r->succ;
				VAMapEntry *rsp = rs->prev;
				root = rs;
				rs->prev = r;
				r->succ = rsp;
			} else {
				if (!root->succ->succ)
					return false;
				VAMapEntry *r = root;
				VAMapEntry *rs = r->succ;
				VAMapEntry *rsp = rs->prev;
				VAMapEntry *rss = rs->succ;
				VAMapEntry *rssp = rss->prev;
				root = rss;
				rss->prev = rs;
				rs->prev = r;
				rs->succ = rssp;
				r->succ = rsp;
			}
		}
	}

#if TRACE_VAMAP & TRACE_VAMAP_LOOKUP
	printf("%p, Translates to %lx\n", this,
	       root->pa[(va - root->start) / MEMORY_CHUNK_SIZE]._pa);
#endif
	if (pa) {
		*pa = root->pa[(va - root->start) / MEMORY_CHUNK_SIZE] +
			((va - root->start) % MEMORY_CHUNK_SIZE);
		assert(pa->_pa != 0);
	}
	return true;
}

void VAMap::forceCOW()
{
	if (parent) {
		root = parent->root->dupeSelf();
		parent = NULL;
	}
}

void VAMap::addTranslation(unsigned long start,
			   PhysicalAddress pa)
{
#if TRACE_VAMAP & TRACE_VAMAP_CHANGE
	printf("%p: Add translation %lx -> %lx\n", this, start, pa._pa);
#endif
	forceCOW();

	VAMapEntry *vme;
	VAMapEntry *newVme;
	unsigned long end = start + MEMORY_CHUNK_SIZE;

	if (!root) {
#if TRACE_VAMAP & TRACE_VAMAP_CHANGE_DETAILS
		printf("%p, new root\n", this);
#endif
		PhysicalAddress *newPas =
			(PhysicalAddress *)LibVEX_Alloc_Bytes(sizeof(PhysicalAddress));
		*newPas = pa;
		root = VAMapEntry::alloc(start, end, newPas);
		return;
	}

	vme = root;
	while (1) {
		/* Don't allow overlaps */
		assert(end <= vme->start || start >= vme->end);

		/* Try to merge with an existing node. */
		if (end == vme->start) {
#if TRACE_VAMAP & TRACE_VAMAP_CHANGE_DETAILS
			printf("%p, merge before with %lx:%lx\n", this,
			       vme->start, vme->end);
#endif
			vme->pa = (PhysicalAddress *)LibVEX_realloc(&main_heap,
								    vme->pa,
								    sizeof(vme->pa[0]) *
								    dchunk(start, vme->end));
			memmove(vme->pa + dchunk(start, vme->start),
				vme->pa,
				sizeof(vme->pa[0]) * dchunk(vme->start, vme->end));
			vme->pa[0] = pa;
			vme->start = start;
			return;
		}
		if (start == vme->end) {
#if TRACE_VAMAP & TRACE_VAMAP_CHANGE_DETAILS
			printf("%p, merge after with %lx:%lx\n", this,
			       vme->start, vme->end);
#endif
			vme->pa = (PhysicalAddress *)LibVEX_realloc(&main_heap,
								    vme->pa,
								    sizeof(vme->pa[0]) *
								    dchunk(vme->start, end));
			vme->pa[dchunk(vme->start, vme->end)] = pa;
			vme->end = end;
			return;
		}

		/* Merge failed.  Either insert here or walk to
		 * children. */
		if (start < vme->start) {
			if (vme->prev) {
				vme = vme->prev;
			} else {
#if TRACE_VAMAP & TRACE_VAMAP_CHANGE_DETAILS
				printf("%p, new before %lx:%lx\n", this,
				       vme->start, vme->end);
#endif
				PhysicalAddress *newPas =
					(PhysicalAddress *)LibVEX_Alloc_Bytes(sizeof(PhysicalAddress));
				*newPas = pa;
				newVme = VAMapEntry::alloc(start, end, newPas);
				vme->prev = newVme;
				return;
			}
		} else {
			assert(start >= vme->end);
			if (vme->succ) {
				vme = vme->succ;
			} else {
#if TRACE_VAMAP & TRACE_VAMAP_CHANGE_DETAILS
				printf("%p, new after %lx:%lx\n", this,
				       vme->start, vme->end);
#endif
				PhysicalAddress *newPas =
					(PhysicalAddress *)LibVEX_Alloc_Bytes(sizeof(PhysicalAddress));
				*newPas = pa;
				newVme = VAMapEntry::alloc(start, end, newPas);
				vme->succ = newVme;
				return;
			}
		}
	}
}

VAMap *VAMap::empty()
{
	return new VAMap();
}

void VAMap::visit(HeapVisitor &hv)
{
	hv(parent);
}

void VAMap::visit(VAMap *&ref, HeapVisitor &hv, PMap *pmap)
{
	hv(ref);
	if (ref->root) {
		assert(!ref->parent);
		ref->root->visit(ref->root, pmap, hv);
	}
	if (ref->parent) {
		assert(!ref->root);
		ref->parent->visit(ref->parent, hv, pmap);
	}
}

void VAMap::VAMapEntry::split(unsigned long at)
{
	assert(at >= start);
	assert(at <= end);
	if (at == start || at == end)
		return;
	VAMapEntry *newVme;
	if (!prev) {
		newVme = alloc(start, at, pa);
		start = at;
		pa = (PhysicalAddress *)LibVEX_Alloc_Bytes(sizeof(pa[0]) * dchunk(start, end));
		memcpy(pa,
		       newVme->pa + dchunk(newVme->start, newVme->end),
		       sizeof(pa[0]) * dchunk(start, end));
		newVme->pa =
			(PhysicalAddress *)LibVEX_realloc(&main_heap,
							  newVme->pa,
							  sizeof(pa[0]) * dchunk(newVme->start, newVme->end));
		prev = newVme;
	} else {
		PhysicalAddress *newPas =
			(PhysicalAddress *)LibVEX_Alloc_Bytes(sizeof(pa[0]) * dchunk(at, end));
		memcpy(newPas,
		       pa + dchunk(start, at),
		       sizeof(pa[0]) * dchunk(at, end));
		newVme = alloc(at, end, newPas);
		end = at;
		newVme->succ = succ;
		succ = newVme;
		pa = (PhysicalAddress *)LibVEX_realloc(&main_heap, pa, sizeof(pa[0]) * dchunk(start, end));
	}
}

