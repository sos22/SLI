#include <sys/mman.h>
#include <stdlib.h>
#include <string.h>

#include "sli.h"

#define PAGE_MASK (~4095)

template <typename ait>
void AddressSpace<ait>::allocateMemory(ait _start, ait _size,
				       VAMap::Protection prot, VAMap::AllocFlags flags)
{
	unsigned long start = force(_start);
	unsigned long size = force(_size);
	assert(!(start & ~PAGE_MASK));
	assert(!(size & ~PAGE_MASK));

	vamap->unmap(start, size);
	while (size != 0) {
		MemoryChunk<ait> *chunk = MemoryChunk<ait>::allocate();
		PhysicalAddress pa = pmap->introduce(chunk);
		vamap->addTranslation(start, pa, prot, flags);
		start += MemoryChunk<ait>::size;
		size -= MemoryChunk<ait>::size;
	}
}

template <typename ait>
void AddressSpace<ait>::releaseMemory(ait start, ait size)
{
	vamap->unmap(force(start), force(size));
}

template <typename ait>
void AddressSpace<ait>::protectMemory(ait start, ait size,
				      VAMap::Protection prot)
{
	vamap->protect(force(start), force(size), prot);
}

template <typename ait>
void AddressSpace<ait>::writeMemory(EventTimestamp when, ait _start, unsigned size,
				    const ait *contents, bool ignore_protection,
				    const Thread<ait> *thr)
{
	unsigned long start = force(_start);
	unsigned off = 0;
	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if (!ignore_protection && !prot.writable)
				throw BadMemoryException<ait>(true, _start, size);
			unsigned long mc_start;
			unsigned to_copy_this_time;
			MemoryChunk<ait> *mc = pmap->lookup(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time > mc->size - mc_start)
				to_copy_this_time = mc->size - mc_start;
			mc->write(when, mc_start, contents, to_copy_this_time,
				  _start + mkConst<ait>(off));

			start += to_copy_this_time;
			size -= to_copy_this_time;
			off += to_copy_this_time;
			contents = contents + to_copy_this_time;
		} else if (thr && extendStack(start, force(thr->regs.rsp()))) {
			continue;
		} else {
			throw BadMemoryException<ait>(true, _start, size);
		}
	}
}

template <typename ait>
expression_result<ait> AddressSpace<ait>::load(EventTimestamp when,
					       ait start, unsigned size,
					       bool ignore_protection,
					       const Thread<ait> *thr)
{
	ait b[16];
	ait storeAddr;
	memset(b, 0, sizeof(ait) * size);
	for (unsigned x = 0; x < size; x++)
		new (&b[x]) ait();
	EventTimestamp sto = readMemory(start, size, b, ignore_protection, thr, &storeAddr);
	expression_result<ait> res;
	res.hi = mkConst<ait>(0);
	res.lo = mkConst<ait>(0);
	switch(size) {
	case 16:
		res.hi = b[8] +
			(b[9] << mkConst<ait>(8)) +
			(b[10] << mkConst<ait>(16)) +
			(b[11] << mkConst<ait>(24)) +
			(b[12] << mkConst<ait>(32)) +
			(b[13] << mkConst<ait>(40)) +
			(b[14] << mkConst<ait>(48)) +
			(b[15] << mkConst<ait>(56));
		/* Fall through */
	case 8:
		res.lo = res.lo +
			(b[7] << mkConst<ait>(56)) +
			(b[6] << mkConst<ait>(48)) +
			(b[5] << mkConst<ait>(40)) +
			(b[4] << mkConst<ait>(32));
		/* Fall through */
	case 4:
		res.lo = res.lo +
			(b[3] << mkConst<ait>(24)) +
			(b[2] << mkConst<ait>(16));
		/* Fall through */
	case 2:
		res.lo = res.lo + (b[1] << mkConst<ait>(8));
		/* Fall through */
	case 1:
		res.lo = res.lo + b[0];
		break;
	default:
		abort();
	}

	/* We cheat slightly and assume that you don't race on stack
	   accesses.  This isn't *entirely* valid, but it makes things
	   so much easier that it's worth it. */
	if (!is_stack(start) &&
	    (!thr ||
	     force(start) < force(thr->regs.rsp()) - 1000000 ||
	     force(start) > force(thr->regs.rsp()) + 1000000)) {
		res.lo = load_ait<ait>(res.lo, start, when, sto, storeAddr);
		if (size > 8)
			res.hi = load_ait<ait>(res.hi, start, when, sto, storeAddr);
	}
	return res;
}

template <typename ait>
void AddressSpace<ait>::store(EventTimestamp when, ait start, unsigned size,
			      const expression_result<ait> &val, bool ignore_protection,
			      const Thread<ait> *thr)
{
	ait b[16];
	switch (size) {
	case 16:
		b[15] = (val.hi >> mkConst<ait>(56)) & mkConst<ait>(0xff);
		b[14] = (val.hi >> mkConst<ait>(48)) & mkConst<ait>(0xff);
		b[13] = (val.hi >> mkConst<ait>(40)) & mkConst<ait>(0xff);
		b[12] = (val.hi >> mkConst<ait>(32)) & mkConst<ait>(0xff);
		b[11] = (val.hi >> mkConst<ait>(24)) & mkConst<ait>(0xff);
		b[10] = (val.hi >> mkConst<ait>(16)) & mkConst<ait>(0xff);
		b[9] = (val.hi >> mkConst<ait>(8)) & mkConst<ait>(0xff);
		b[8] = val.hi & mkConst<ait>(0xff);
	case 8:
		b[7] = (val.lo >> mkConst<ait>(56)) & mkConst<ait>(0xff);
		b[6] = (val.lo >> mkConst<ait>(48)) & mkConst<ait>(0xff);
		b[5] = (val.lo >> mkConst<ait>(40)) & mkConst<ait>(0xff);
		b[4] = (val.lo >> mkConst<ait>(32)) & mkConst<ait>(0xff);
	case 4:
		b[3] = (val.lo >> mkConst<ait>(24)) & mkConst<ait>(0xff);
		b[2] = (val.lo >> mkConst<ait>(16)) & mkConst<ait>(0xff);
	case 2:
		b[1] = (val.lo >> mkConst<ait>(8)) & mkConst<ait>(0xff);
	case 1:
		b[0] = val.lo & mkConst<ait>(0xff);
		break;
	default:
		abort();
	}
	writeMemory(when, start, size, b, ignore_protection, thr);
}

template <typename ait>
EventTimestamp AddressSpace<ait>::readMemory(ait _start, unsigned size,
					     ait *contents, bool ignore_protection,
					     const Thread<ait> *thr,
					     ait *storeAddr)
{
	EventTimestamp when;
	unsigned long start = force(_start);
	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if (!ignore_protection && !prot.readable)
				throw BadMemoryException<ait>(false, _start, size);
			unsigned long mc_start;
			unsigned to_copy_this_time;
			const MemoryChunk<ait> *mc = pmap->lookupConst(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time > mc->size - mc_start)
				to_copy_this_time = mc->size - mc_start;
			when = mc->read(mc_start, contents, to_copy_this_time,
					storeAddr);

			start += to_copy_this_time;
			size -= to_copy_this_time;
			contents = contents + to_copy_this_time;
		} else if (thr && extendStack(start, force(thr->regs.rsp()))) {
			/* This is what Linux does, but it doesn't
			   make a great deal of sense: any time you
			   hit this the program will definitely have
			   accessed uninitialised stack memory, so
			   it's definitely not a good thing. */
			printf("Huh? Extended stack for a read?\n");
			continue;
		} else {
			throw BadMemoryException<ait>(false, _start, size);
		}
	}
	return when;
}

template <typename ait>
bool AddressSpace<ait>::isAccessible(ait _start, unsigned size,
				     bool isWrite, const Thread<ait> *thr)
{
	unsigned long start = force(_start);
	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if ((!isWrite && !prot.readable) ||
			    ( isWrite && !prot.writable))
				return false;
			unsigned long mc_start;
			unsigned to_copy_this_time;
			const MemoryChunk<ait> *mc = pmap->lookupConst(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time >
			    mc_start + mc->size - start)
				to_copy_this_time = mc_start + mc->size - start;

			start += to_copy_this_time;
			size -= to_copy_this_time;
		} else if (extendStack(start, force(thr->regs.rsp()))) {
			continue;
		} else {
			return false;
		}
	}
	return true;
}

template <typename ait>
unsigned long AddressSpace<ait>::setBrk(ait _newBrk)
{
	unsigned long newBrk = force(_newBrk);
	unsigned long newBrkMap = (newBrk + 4095) & PAGE_MASK;

	if (newBrk != 0) {
		if (newBrkMap > brkMapPtr)
			allocateMemory(mkConst<ait>(brkMapPtr), mkConst<ait>(newBrkMap - brkMapPtr), VAMap::Protection(true, true, false));
		else
			releaseMemory(mkConst<ait>(newBrkMap), mkConst<ait>(brkMapPtr - newBrkMap));
		brkptr = newBrk;
		brkMapPtr = newBrkMap;
	}

	return brkptr;
}

template <typename ait>
AddressSpace<ait> *AddressSpace<ait>::initialAddressSpace(ait _initialBrk)
{
	unsigned long initialBrk = force(_initialBrk);
	AddressSpace<ait> *work = allocator.alloc();
	memset(work, 0, sizeof(*work));
	work->brkptr = initialBrk;
	work->brkMapPtr = initialBrk + 4096;
	work->pmap = PMap<ait>::empty();
	work->vamap = VAMap::empty();
	return work;	
}

template <typename ait>
AddressSpace<ait> *AddressSpace<ait>::dupeSelf() const
{
	AddressSpace<ait> *work = allocator.alloc();
	*work = *this;
	work->pmap = pmap->dupeSelf();
	work->vamap = vamap->dupeSelf();
	return work;
}

template <typename ait>
void AddressSpace<ait>::visit(HeapVisitor &hv) const
{
	hv(vamap);
	hv(pmap);
	vamap->visit(hv, pmap);
}

template <typename ait>
bool AddressSpace<ait>::extendStack(unsigned long ptr, unsigned long rsp)
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

	allocateMemory(mkConst<ait>(ptr & PAGE_MASK), mkConst<ait>(va), prot, flags);
	return true;
}

template <typename ait>
void AddressSpace<ait>::sanityCheck() const
{
	vamap->sanityCheck();
}

template <typename ait>
void AddressSpace<ait>::dumpBrkPtr(LogWriter<ait> *lw) const
{
	lw->append(LogRecordInitialBrk<ait>(ThreadId(0), mkConst<ait>(brkptr)),
		   0);
}

template <typename ait>
void AddressSpace<ait>::dumpSnapshot(LogWriter<ait> *lw) const
{
	unsigned long last_va;
	unsigned long next_va;
	PhysicalAddress pa;
	VAMap::Protection prot(0);
	VAMap::AllocFlags alf(false);
	last_va = 0;
	while (vamap->findNextMapping(last_va, &next_va, &pa, &prot, &alf)) {
		lw->append(LogRecordAllocateMemory<ait>(ThreadId(0),
							mkConst<ait>(next_va),
							mkConst<ait>(MemoryChunk<ait>::size),
							(unsigned long)prot,
							(unsigned long)alf),
			   0);
		unsigned long off;
		const MemoryChunk<ait> *mc = pmap->lookupConst(pa, &off);
		assert(off == 0);
		ait *buf = (ait *)calloc(MemoryChunk<ait>::size, sizeof(ait));
		mc->read(0, buf, MemoryChunk<ait>::size);
		lw->append(LogRecordMemory<ait>(ThreadId(0),
						MemoryChunk<ait>::size,
						mkConst<ait>(next_va),
						buf),
			   0);
		last_va = next_va + MemoryChunk<ait>::size;
	}
}

template <typename ait> template <typename new_type>
AddressSpace<new_type> *AddressSpace<ait>::abstract() const
{
	AddressSpace<new_type> *work = new (AddressSpace<new_type>::allocator.alloc()) AddressSpace<new_type>();

	work->brkptr = brkptr;
	work->brkMapPtr = brkMapPtr;
	work->vamap = vamap->dupeSelf();
	work->pmap = pmap->abstract<new_type>();
	return work;
}

template <typename ait> VexAllocTypeWrapper<AddressSpace<ait> > AddressSpace<ait>::allocator;

#define MK_ADDRESS_SPACE(t)						\
	template VexAllocTypeWrapper<AddressSpace<t> > AddressSpace<t>::allocator;
