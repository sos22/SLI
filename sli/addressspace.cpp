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
		MemoryChunk *chunk = MemoryChunk::allocate();
		PhysicalAddress pa = pmap->introduce(chunk);
		vamap->addTranslation(start, pa, prot, flags);
		start += MemoryChunk::size;
		size -= MemoryChunk::size;
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
void AddressSpace<ait>::writeMemory(ait _start, unsigned size,
				    const void *contents, bool ignore_protection,
				    const Thread<ait> *thr)
{
	unsigned long start = force(_start);
	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if (!ignore_protection && !prot.writable)
				throw BadMemoryException<ait>(true, _start, size);
			unsigned long mc_start;
			unsigned to_copy_this_time;
			MemoryChunk *mc = pmap->lookup(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time > mc->size - mc_start)
				to_copy_this_time = mc->size - mc_start;
			mc->write(mc_start, contents, to_copy_this_time);

			start += to_copy_this_time;
			size -= to_copy_this_time;
			contents = (const void *)((unsigned long)contents + to_copy_this_time);
		} else if (thr && extendStack(start, force(thr->regs.rsp()))) {
			continue;
		} else {
			throw BadMemoryException<ait>(true, _start, size);
		}
	}
}

template <typename ait>
expression_result<ait> AddressSpace<ait>::load(ReplayTimestamp when,
					       ait start, unsigned size,
					       bool ignore_protection,
					       const Thread<ait> *thr)
{
	unsigned long b[2];
	memset(b, 0, sizeof(b));
	readMemory(start, size, b, ignore_protection, thr);
	expression_result<ait> res;
	res.lo = load_ait<unsigned long, ait>(b[0], start, when);
	res.hi = load_ait<unsigned long, ait>(b[1], start + mkConst<ait>(8), when);
	return res;
}

template <typename ait>
void AddressSpace<ait>::store(ait start, unsigned size, expression_result<ait> val,
			      bool ignore_protection,
			      const Thread<ait> *thr)
{
	expression_result<unsigned long> concrete;
	val.abstract(&concrete);
	unsigned long b[2];
	b[0] = concrete.lo;
	b[1] = concrete.hi;
	writeMemory(start, size, b, ignore_protection, thr);
}

template <typename ait>
void AddressSpace<ait>::readMemory(ait _start, unsigned size,
				   void *contents, bool ignore_protection,
				   const Thread<ait> *thr)
{
	unsigned long start = force(_start);
	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if (!ignore_protection && !prot.readable)
				throw BadMemoryException<ait>(false, _start, size);
			unsigned long mc_start;
			unsigned to_copy_this_time;
			const MemoryChunk *mc = pmap->lookupConst(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time > mc->size - mc_start)
				to_copy_this_time = mc->size - mc_start;
			mc->read(mc_start, contents, to_copy_this_time);

			start += to_copy_this_time;
			size -= to_copy_this_time;
			contents = (void *)((unsigned long)contents + to_copy_this_time);
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
			const MemoryChunk *mc = pmap->lookupConst(pa, &mc_start);
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
	work->pmap = PMap::empty();
	work->vamap = VAMap::empty(work->pmap);
	return work;	
}

template <typename ait>
AddressSpace<ait> *AddressSpace<ait>::dupeSelf() const
{
	AddressSpace<ait> *work = allocator.alloc();
	*work = *this;
	work->pmap = pmap->dupeSelf();
	work->vamap = vamap->dupeSelf(work->pmap);
	return work;
}

template <typename ait>
void AddressSpace<ait>::visit(HeapVisitor &hv) const
{
	hv(vamap);
	hv(pmap);
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
	lw->append(LogRecordInitialBrk<ait>(ThreadId(0), mkConst<ait>(brkptr)));
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
							mkConst<ait>(MemoryChunk::size),
							(unsigned long)prot,
							(unsigned long)alf));
		unsigned long off;
		const MemoryChunk *mc = pmap->lookupConst(pa, &off);
		assert(off == 0);
		void *buf = malloc(MemoryChunk::size);
		mc->read(0, buf, MemoryChunk::size);
		lw->append(LogRecordMemory<ait>(ThreadId(0),
						MemoryChunk::size,
						mkConst<ait>(next_va),
						buf));
		last_va = next_va + MemoryChunk::size;
	}
}

template <typename ait> template <typename new_type>
AddressSpace<new_type> *AddressSpace<ait>::abstract() const
{
	return (AddressSpace<new_type> *)dupeSelf();
}

template <typename ait> VexAllocTypeWrapper<AddressSpace<ait> > AddressSpace<ait>::allocator;

#define MK_ADDRESS_SPACE(t)						\
	template VexAllocTypeWrapper<AddressSpace<t> > AddressSpace<t>::allocator;
