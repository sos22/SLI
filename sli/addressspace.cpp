#include <sys/mman.h>
#include <stdlib.h>
#include <string.h>

#include "sli.h"

#define PAGE_MASK (~4095)

void
AddressSpace::allocateMemory(unsigned long _start, unsigned long _size,
			     VAMap::Protection prot, VAMap::AllocFlags flags)
{
	unsigned long start = _start;
	unsigned long size = _size;
	assert(!(start & ~PAGE_MASK));
	assert(!(size & ~PAGE_MASK));

	vamap->unmap(start, size);
	while (size != 0) {
		MemoryChunk *chunk = MemoryChunk::allocate();
		PhysicalAddress pa = pmap->introduce(chunk);
		vamap->addTranslation(start, pa, prot, flags);
		start += MemoryChunk::size;
		size -= MemoryChunk::size;
	}
}

void
AddressSpace::releaseMemory(unsigned long start, unsigned long size)
{
	vamap->unmap(start, size);
}

void
AddressSpace::protectMemory(unsigned long start, unsigned long size,
			    VAMap::Protection prot)
{
	vamap->protect(start, size, prot);
}

bool
AddressSpace::copyToClient(unsigned long start, unsigned size,
			   const void *contents)
{
	unsigned long *buf = (unsigned long *)malloc(sizeof(unsigned long) * size);
	bool fault;

	for (unsigned x = 0; x < size; x++)
		buf[x] = ((unsigned char *)contents)[x];
	fault = false;
	try {
		writeMemory(start, size, buf, false, NULL);
	} catch (BadMemoryException &e) {
		fault = true;
	}
	free(buf);
	return fault;
}

bool
AddressSpace::copyFromClient(unsigned long start, unsigned size, void *dest)
{
	unsigned long *buf = (unsigned long *)calloc(sizeof(unsigned long), size);
	bool fault;

	fault = false;
	try {
		readMemory(start, size, buf, false, NULL, NULL);
	} catch (BadMemoryException &e) {
		fault = true;
	}
	if (!fault) {
		for (unsigned x = 0; x < size; x++) {
			((unsigned char *)dest)[x] = buf[x];
		}
	}
	free(buf);
	return fault;
}

void
AddressSpace::writeMemory(unsigned long _start, unsigned size,
			  const unsigned long *contents, bool ignore_protection,
			  Thread *thr)
{
	unsigned long start = _start;
	unsigned off = 0;

	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if (!ignore_protection && !prot.writable)
				throw BadMemoryException(true, _start, size);
			unsigned long mc_start;
			unsigned to_copy_this_time;
			MemoryChunk *mc = pmap->lookup(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time > mc->size - mc_start)
				to_copy_this_time = mc->size - mc_start;
			mc->write(mc_start, contents, to_copy_this_time,
				  _start + off);

			start += to_copy_this_time;
			size -= to_copy_this_time;
			off += to_copy_this_time;
			contents = contents + to_copy_this_time;
		} else if (thr && extendStack(start, thr->regs.rsp())) {
			continue;
		} else {
			throw BadMemoryException(true, _start, size);
		}
	}
}

expression_result
AddressSpace::load(unsigned long start, unsigned size,
		   bool ignore_protection,
		   Thread *thr)
{
	unsigned long b[16];
	unsigned long storeAddr;
	memset(b, 0, sizeof(unsigned long) * size);
	for (unsigned x = 0; x < size; x++)
		new (&b[x]) unsigned long();
	readMemory(start, size, b, ignore_protection, thr, &storeAddr);
	expression_result res;
	res.lo = 0ul;
	res.hi = 0ul;
	switch(size) {
	case 16:
		res.hi = b[8] +
			(b[9] << 8ul) +
			(b[10] << 16ul) +
			(b[11] << 24ul) +
			(b[12] << 32ul) +
			(b[13] << 40ul) +
			(b[14] << 48ul) +
			(b[15] << 56ul);
		/* Fall through */
	case 8:
		res.lo = res.lo +
			(b[7] << 56ul) +
			(b[6] << 48ul) +
			(b[5] << 40ul) +
			(b[4] << 32ul);
		/* Fall through */
	case 4:
		res.lo = res.lo +
			(b[3] << 24ul) +
			(b[2] << 16ul);
		/* Fall through */
	case 2:
		res.lo = res.lo + (b[1] << 8ul);
		/* Fall through */
	case 1:
		res.lo = res.lo + b[0];
		break;
	default:
		abort();
	}

	return res;
}

void
AddressSpace::store(unsigned long start, unsigned size,
		    const expression_result &val, bool ignore_protection,
		    Thread *thr)
{
	unsigned long b[16];
	switch (size) {
	case 16:
		b[15] = (val.hi >> 56ul) & 0xfful;
		b[14] = (val.hi >> 48ul) & 0xfful;
		b[13] = (val.hi >> 40ul) & 0xfful;
		b[12] = (val.hi >> 32ul) & 0xfful;
		b[11] = (val.hi >> 24ul) & 0xfful;
		b[10] = (val.hi >> 16ul) & 0xfful;
		b[9] = (val.hi >> 8ul) & 0xfful;
		b[8] = val.hi & 0xfful;
	case 8:
		b[7] = (val.lo >> 56ul) & 0xfful;
		b[6] = (val.lo >> 48ul) & 0xfful;
		b[5] = (val.lo >> 40ul) & 0xfful;
		b[4] = (val.lo >> 32ul) & 0xfful;
	case 4:
		b[3] = (val.lo >> 24ul) & 0xfful;
		b[2] = (val.lo >> 16ul) & 0xfful;
	case 2:
		b[1] = (val.lo >> 8ul) & 0xfful;
	case 1:
		b[0] = val.lo & 0xfful;
		break;
	default:
		abort();
	}
	writeMemory(start, size, b, ignore_protection, thr);
}

template <typename t> const t
AddressSpace::fetch(unsigned long start, Thread *thr)
{
	unsigned long *res;

	res = (unsigned long *)malloc(sizeof(unsigned long) * sizeof(t));
	readMemory(start, sizeof(t), res, false, thr);
	t tt;
	for (unsigned x = 0; x < sizeof(t); x++)
		((unsigned char *)&tt)[x] = res[x];
	free(res);
	return tt;
}

void AddressSpace::readMemory(unsigned long _start, unsigned size,
			      unsigned long *contents, bool ignore_protection,
			      Thread *thr,
			      unsigned long *storeAddr)
{
	unsigned long start = _start;
	if (storeAddr)
		*storeAddr = start;
	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if (!ignore_protection && !prot.readable)
				throw BadMemoryException(false, _start, size);
			unsigned long mc_start;
			unsigned to_copy_this_time;
			const MemoryChunk *mc = pmap->lookupConst(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time > mc->size - mc_start)
				to_copy_this_time = mc->size - mc_start;
			mc->read(mc_start, contents, to_copy_this_time,
				 storeAddr);

			start += to_copy_this_time;
			size -= to_copy_this_time;
			contents = contents + to_copy_this_time;
		} else if (thr && extendStack(start, thr->regs.rsp())) {
			/* This is what Linux does, but it doesn't
			   make a great deal of sense: any time you
			   hit this the program will definitely have
			   accessed uninitialised stack memory, so
			   it's definitely not a good thing. */
			printf("Huh? Extended stack for a read?\n");
			continue;
		} else {
			throw BadMemoryException(false, _start, size);
		}
	}
}

bool AddressSpace::isAccessible(unsigned long _start, unsigned size,
				     bool isWrite, Thread *thr)
{
	unsigned long start = _start;
	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if ((!isWrite && !prot.readable) ||
			    ( isWrite && !prot.writable))
				return false;
			unsigned long mc_start;
			unsigned to_copy_this_time;
			const MemoryChunk *mc = pmap->lookupConst(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time >
			    mc_start + mc->size - start)
				to_copy_this_time = mc_start + mc->size - start;

			start += to_copy_this_time;
			size -= to_copy_this_time;
		} else if (thr && extendStack(start, thr->regs.rsp())) {
			continue;
		} else {
			return false;
		}
	}
	return true;
}

unsigned long AddressSpace::setBrk(unsigned long _newBrk)
{
	unsigned long newBrk = _newBrk;
	unsigned long newBrkMap = (newBrk + 4095) & PAGE_MASK;

	if (newBrk != 0) {
		if (newBrkMap > brkMapPtr)
			allocateMemory(brkMapPtr, newBrkMap - brkMapPtr, VAMap::Protection(true, true, false));
		else
			releaseMemory(newBrkMap, brkMapPtr - newBrkMap);
		brkptr = newBrk;
		brkMapPtr = newBrkMap;
	}

	return brkptr;
}

AddressSpace *AddressSpace::initialAddressSpace(unsigned long _initialBrk)
{
	unsigned long initialBrk = _initialBrk;
	AddressSpace *work = new AddressSpace();
	work->brkptr = initialBrk;
	work->brkMapPtr = initialBrk /*+ 4096*/;
	work->pmap = PMap::empty();
	work->vamap = VAMap::empty();
	return work;	
}

AddressSpace *AddressSpace::dupeSelf() const
{
	AddressSpace *work = new AddressSpace();
	*work = *this;
	work->pmap = pmap->dupeSelf();
	work->vamap = vamap->dupeSelf();
	memset(work->trans_hash, 0, sizeof(work->trans_hash));
	return work;
}

void AddressSpace::visit(HeapVisitor &hv)
{
	hv(pmap);
	vamap->visit(vamap, hv, pmap);
	for (unsigned x = 0; x < nr_trans_hash_slots; x++)
		hv(trans_hash[x]);
}

bool AddressSpace::extendStack(unsigned long ptr, unsigned long rsp)
{
	if (ptr + 65536 + 32 * sizeof(unsigned long) < rsp)
		return false;

	unsigned long va;
	VAMap::Protection prot(0);
	VAMap::AllocFlags flags(false);
	if (!vamap->findNextMapping(ptr, &va, NULL, &prot, &flags))
		return false;
	if (!flags.expandsDown)
		return false;

	printf("Extending stack from %lx to %lx\n", ptr, va);
	ptr &= PAGE_MASK;
	allocateMemory(ptr, va - ptr, prot, flags);
	return true;
}

void AddressSpace::dumpBrkPtr(LogWriter *lw) const
{
	lw->append(new LogRecordInitialBrk(ThreadId(0), brkptr));
}

void AddressSpace::dumpSnapshot(LogWriter *lw) const
{
	unsigned long end_of_last_block = 0;

	while (1) {
		unsigned long start_va;
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		VAMap::AllocFlags alf(false);

		if (!vamap->findNextMapping(end_of_last_block, &start_va, &pa, &prot, &alf))
			return;

		/* Do this in two steps.  First, dump all the allocate
		   records, and then go back and do the populate ones.
		   This makes it easier to merge adjacent
		   allocations. */
		unsigned long end_va = start_va;
		while (1) {
			unsigned long next_va;
			VAMap::Protection prot2(0);
			VAMap::AllocFlags alf2(false);
			if (!vamap->findNextMapping(end_va + 4096, &next_va, &pa, &prot2, &alf2))
				break;
			if (next_va != end_va + 4096 || prot != prot2 || alf != alf2)
				break;
			end_va = next_va;
		}

		end_va += 4096;

		lw->append(new LogRecordAllocateMemory(ThreadId(0),
						       start_va,
						       end_va - start_va,
						       (unsigned long)prot,
						       (unsigned long)alf));

		/* Now do the contents of the block */

		/* We cheat just a little bit and only bother dumping
		   stuff which can be read or executed.  In principle,
		   other bits of address space could be relevant,
		   because someone might mprotect() them to be
		   readable, but that's rather unlikely.  This allows
		   us to avoid dumping reserved areas of address
		   space, which can be hundreds of megabytes of data
		   in some cases. */
		if (prot.readable || prot.executable) {
			unsigned long cursor_va;
			for (cursor_va = start_va; cursor_va < end_va; cursor_va += 4096) {
				bool r;
				PhysicalAddress pa;
				r = vamap->translate(cursor_va, &pa);
				assert(r);
				unsigned long off;
				const MemoryChunk *mc = pmap->lookupConst(pa, &off);
				assert(off == 0);
				unsigned long *buf = (unsigned long *)calloc(MemoryChunk::size, sizeof(unsigned long));
				mc->read(0, buf, MemoryChunk::size);
				lw->append(new LogRecordMemory(ThreadId(0),
							       MemoryChunk::size,
							       cursor_va,
							       buf));
			}
		}

		end_of_last_block = end_va;
	}
}

char *
AddressSpace::readString(unsigned long start, Thread *thr)
{
	char *buf;
	unsigned offset;
	unsigned buf_size;

	buf_size = 64;
	buf = (char *)malloc(buf_size);
	offset = 0;
	while (1) {
		unsigned long b;
		readMemory(start + offset, 1, &b, false, thr);
		buf[offset] = b;
		if (!buf[offset])
			break;
		offset++;
		if (offset >= buf_size) {
			buf_size *= 2;
			buf = (char *)realloc(buf, buf_size);
		}
	}
	return buf;
}

static unsigned long
rip_hash(unsigned long rip, unsigned nr_trans_hash_slots)
{
	unsigned long hash = 0;
	while (rip) {
		hash ^= rip % nr_trans_hash_slots;
		rip /= nr_trans_hash_slots;
	}
	return hash;
}

void
AddressSpace::relocate(AddressSpace *target, size_t)
{
	for (unsigned x = 0; x < nr_trans_hash_slots; x++)
		if (target->trans_hash[x])
			target->trans_hash[x]->pprev = &target->trans_hash[x];
	memset(trans_hash, 0x99, sizeof(trans_hash));
}

WeakRef<IRSB> *
AddressSpace::searchDecodeCache(unsigned long rip)
{
	unsigned long hash = rip_hash(rip, nr_trans_hash_slots);
	trans_hash_entry **pprev, *n;

	pprev = &trans_hash[hash];
	if (trans_hash[hash])
		assert(trans_hash[hash]->pprev == &trans_hash[hash]);
	while (1) {
		n = *pprev;
		if (!n)
			break;
		if (n->next)
			assert(n->next->pprev == &n->next);
		assert(*n->pprev == n);
		assert(rip_hash(n->rip, nr_trans_hash_slots) == hash);
		if (n->rip == rip) {
			/* Pull-to-front hash chaining */
			if (trans_hash[hash] != n) {
				if (n->next)
					n->next->pprev = n->pprev;
				*n->pprev = n->next;

				trans_hash[hash]->pprev = &n->next;
				n->next = trans_hash[hash];
				n->pprev = &trans_hash[hash];
				trans_hash[hash] = n;
				assert(trans_hash[hash]->pprev == &trans_hash[hash]);
			}
			if (n->next)
				assert(n->next->pprev == &n->next);
			assert(*n->pprev == n);
			return n->irsb;
		}

		if (!n->irsb->get()) {
			/* Target has been garbage collected.  Unhook
			   ourselves from the list.  We'll get garbage
			   collected ourselves on the next cycle. */
			if (n->next)
				n->next->pprev = n->pprev;
			*n->pprev = n->next;
		}

		pprev = &n->next;
	}

	n = new trans_hash_entry(rip);
	n->next = trans_hash[hash];
	if (trans_hash[hash])
		trans_hash[hash]->pprev = &n->next;
	n->pprev = &trans_hash[hash];
	trans_hash[hash] = n;

	return n->irsb;
}

#define MK_ADDRESS_SPACE(t)
