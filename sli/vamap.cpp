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

VAMap::Protection::operator unsigned long() const
{
	return (readable ? PROT_READ : 0) |
		(writable ? PROT_WRITE : 0) |
		(executable ? PROT_EXEC : 0);
}

VAMap::AllocFlags::AllocFlags(unsigned flags)
{
       expandsDown = false;
       if (flags & MAP_GROWSDOWN) {
               expandsDown = true;
       }
}

VAMap::AllocFlags::operator unsigned long() const
{
	return expandsDown ? (MAP_GROWSDOWN|MAP_STACK) : 0;
}

const VAMap::AllocFlags VAMap::defaultFlags(false);

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
					    PhysicalAddress *pa,
					    Protection prot,
					    AllocFlags alf)
{
	VAMapEntry *work = (VAMapEntry *)__LibVEX_Alloc(&main_heap, &vme_type);
	memset(work, 0, sizeof(*work));
	work->start = start;
	work->end = end;
	work->pa = pa;
	work->prot = prot;
	work->alf = alf;
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
		      PhysicalAddress *pa,
		      Protection *prot,
		      AllocFlags *alf) const
{
#if TRACE_VAMAP & TRACE_VAMAP_LOOKUP
	printf("%p: Translate %lx\n", this, va);
#endif
	if (parent)
		return parent->translate(va, pa, prot, alf);
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
	if (prot)
		*prot = root->prot;
	if (alf)
		*alf = root->alf;
	return true;
}

bool VAMap::findNextMapping(unsigned long from,
			    unsigned long *va,
			    PhysicalAddress *pa,
			    Protection *prot,
			    AllocFlags *alf) const
{
	if (parent)
		return parent->findNextMapping(from, va, pa, prot, alf);

	const VAMapEntry *vme, *bestVme;

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
	if (va) {
		if (from >= bestVme->start)
			*va = from;
		else
			*va = bestVme->start;
	}
	if (pa) {
		if (from >= bestVme->start)
			*pa = bestVme->pa[(from - bestVme->start)/MEMORY_CHUNK_SIZE];
		else
			*pa = bestVme->pa[0];
	}
	if (prot)
		*prot = bestVme->prot;
	if (alf)
		*alf = bestVme->alf;
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
			   PhysicalAddress pa,
			   Protection prot,
			   AllocFlags alf)
{
#if TRACE_VAMAP & TRACE_VAMAP_CHANGE
	printf("%p: Add translation %lx -> %lx (%d,%d,%d,%d)\n", this, start, pa._pa,
	       prot.readable, prot.writable, prot.executable,
	       alf.expandsDown);
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
				newVme = VAMapEntry::alloc(start, end, newPas, prot, alf);
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
				newVme = VAMapEntry::alloc(start, end, newPas, prot, alf);
				vme->succ = newVme;
				return;
			}
		}
	}
}

bool VAMap::protect(unsigned long start, unsigned long size, Protection prot)
{
	forceCOW();

	VAMapEntry *vme;
	unsigned long end = start + size;

#if TRACE_VAMAP & TRACE_VAMAP_CHANGE
	printf("%p: Protect %lx:%lx -> %d.%d.%d\n", this, start, end,
	       prot.readable, prot.writable, prot.executable);
#endif

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

/* Restructure the tree such that the smallest item is at the root,
   and then return a pointer to that item. */
VAMap::VAMapEntry *VAMap::VAMapEntry::promoteSmallest()
{
	/* If we have no predecessor then we don't need to do
	 * anything. */
	if (!prev)
		return this;

	/* Otherwise, recurse */
	VAMapEntry *tmp;
	tmp = prev->promoteSmallest();
	assert(!tmp->prev);
	prev = tmp->succ;
	tmp->succ = this;
	return tmp;
}

void VAMap::unmap(unsigned long start, unsigned long size)
{
	forceCOW();

	VAMapEntry *vme;
	unsigned long end = start + size;
	VAMapEntry **pprev;

#if TRACE_VAMAP & TRACE_VAMAP_CHANGE
	printf("%p: Unmap %lx:%lx\n", this, start, end);
#endif
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
			unsigned long s = vme->start;
			unmap(start, s - start);
			unmap(s, end - s);
			return;
		} else if (end > vme->end) {
			unsigned long e = vme->end;
			unmap(start, e - start);
			unmap(e, end - e);
			return;
		} else if (start != vme->start) {
#if TRACE_VAMAP & TRACE_VAMP_CHANGE_DETAILS
			printf("%p, split %lx:%lx at %lx\n",
			       this, vme->start, vme->end, start);
#endif
			vme->split(start);
		} else if (end != vme->end) {
#if TRACE_VAMAP & TRACE_VAMP_CHANGE_DETAILS
			printf("%p, split %lx:%lx at %lx\n",
			       this, vme->start, vme->end, end);
#endif
			vme->split(end);
		} else {
			/* This node of the tree must be killed.
			   Promote one of our children to the right
			   place. */

#if TRACE_VAMAP & TRACE_VAMP_CHANGE_DETAILS
			printf("%p, kill %lx:%lx\n",
			       this, vme->start, vme->end);
#endif
			/* Easy cases: no children or only one child,
			   so just promote the other one. */
			if (!vme->prev) {
#if TRACE_VAMAP & TRACE_VAMP_CHANGE_DETAILS
				printf("%p, promote successor\n",
				       this);
#endif
				*pprev = vme->succ;
				return;
			}
			if (!vme->succ) {
#if TRACE_VAMAP & TRACE_VAMP_CHANGE_DETAILS
				printf("%p, promote predecessor\n",
				       this);
#endif
				*pprev = vme->prev;
				return;
			}

			/* Otherwise, need to go and find a descendent
			   to promote. */
			VAMapEntry *newSucc;
			newSucc = vme->succ->promoteSmallest();
#if TRACE_VAMAP & TRACE_VAMP_CHANGE_DETAILS
			printf("%p, promote %p\n",
			       this, newSucc);
#endif
			assert(!newSucc->prev);
			newSucc->prev = vme->prev;
			*vme = *newSucc;
			return;
		}
	}

}

VAMap *VAMap::empty()
{
	return new VAMap();
}

VAMap *VAMap::dupeSelf()
{
	VAMap *work = empty();
	if (parent)
		work->parent = parent;
	else
		work->parent = this;
	work->last_malloc_list_entry = last_malloc_list_entry;
	return work;
}

void VAMap::visit(HeapVisitor &hv)
{
	hv(last_malloc_list_entry);
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
		newVme = alloc(start, at, pa, prot, alf);
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
		newVme = alloc(at, end, newPas, prot, alf);
		end = at;
		newVme->succ = succ;
		succ = newVme;
		pa = (PhysicalAddress *)LibVEX_realloc(&main_heap, pa, sizeof(pa[0]) * dchunk(start, end));
	}
}

void
VAMap::malloced_block(unsigned long start, unsigned long size)
{
	malloc_cntr++;
	last_malloc_list_entry = new malloc_list_entry(start, size, malloc_cntr, last_malloc_list_entry);
}

void
VAMap::freed_block(unsigned long start)
{
	malloc_cntr++;
	last_malloc_list_entry = new malloc_list_entry(start, malloc_cntr, last_malloc_list_entry);
}

void
HandleMallocFree(Thread *thr, AddressSpace *as)
{
	if (thr->regs.rip() == MALLOC_ADDRESS) {
		thr->malloc_return = as->fetch<unsigned long>(thr->regs.rsp(), thr);
		thr->malloc_size = thr->regs.get_reg(REGISTER_IDX(RDI));
	} else if (thr->regs.rip() == thr->malloc_return) {
		as->vamap->malloced_block(thr->regs.get_reg(REGISTER_IDX(RAX)),
					  thr->malloc_size);
		thr->malloc_return = 0;
	} else if (thr->regs.rip() == FREE_ADDRESS) {
		as->vamap->freed_block(thr->regs.get_reg(REGISTER_IDX(RDI)));
	}
}

unsigned long
VAMap::findMallocForAddr(unsigned long addr)
{
	for (malloc_list_entry *mle = last_malloc_list_entry;
	     mle;
	     mle = mle->prev) {
		if (!mle->isFree &&
		    mle->start <= addr &&
		    addr < mle->start + mle->size)
			return mle->name;
	}
	return 0;
}

unsigned long
VAMap::mallocKeyToDeathTime(unsigned long key)
{
	unsigned long address;
	malloc_list_entry *mle;
	unsigned long res;

	for (mle = last_malloc_list_entry;
	     mle;
	     mle = mle->prev) {
		if (!mle->isFree &&
		    mle->name == key) {
			address = mle->start;
			break;
		}
	}
	if (!mle)
		return malloc_cntr + 1;
	res = malloc_cntr + 1;
	for (mle = last_malloc_list_entry;
	     mle;
	     mle = mle->prev) {
		if (mle->isFree) {
			if (mle->start == address)
				res = mle->name;
		} else {
			if (mle->name == key)
				break;
		}
	}
	return res;
}

