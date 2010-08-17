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

	findInterestingFunctions();
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
	if (thr)
		checkFreeList(_start, _start + mkConst<ait>(size), thr->tid, EventTimestamp::invalid);
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
	for (unsigned x = 0; x < size; x++)
		sanity_check_ait(b[x]);
	expression_result<ait> res;
	res.lo = mkConst<ait>(0);
	res.hi = mkConst<ait>(0);
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
	bool irrelevant;
#if 0
	irrelevant = (is_stack(start) ||
		      (thr &&
		       force(start) > force(thr->regs.rsp()) - 1000000 &&
		       force(start) < force(thr->regs.rsp()) + 1000000));
#else
	irrelevant = force(start) != 0x601080 && force(start) != 0x4221010;
#endif
	if (!irrelevant) {
		if (size <= 8) {
			res.lo = load_ait<ait>(res.lo, start, when, sto, storeAddr, size);
		} else {
			res.lo = load_ait<ait>(res.lo, start, when, sto, storeAddr, 8);
			res.hi = load_ait<ait>(res.hi, start, when, sto, storeAddr, 8);
		}
	}
	return res;
}

template <typename ait>
void AddressSpace<ait>::store(EventTimestamp when, ait start, unsigned size,
			      const expression_result<ait> &val, bool ignore_protection,
			      const Thread<ait> *thr)
{
	ait b[16];
	sanity_check_ait(val.hi);
	sanity_check_ait(val.lo);
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
	for (unsigned x = 0; x < size; x++)
		sanity_check_ait(b[x]);
	writeMemory(when, start, size, b, ignore_protection, thr);
}

template <typename ait> template <typename t> const t
AddressSpace<ait>::fetch(unsigned long start, Thread<ait> *thr)
{
	ait *res;

	res = (ait *)malloc(sizeof(ait) * sizeof(t));
	readMemory(mkConst<ait>(start), sizeof(t), res, thr);
	t tt;
	for (unsigned x = 0; x < sizeof(t); x++)
		((unsigned char *)&tt)[x] = force(res[x]);
	free(res);
	return tt;
}

template <typename ait>
EventTimestamp AddressSpace<ait>::readMemory(ait _start, unsigned size,
					     ait *contents, bool ignore_protection,
					     const Thread<ait> *thr,
					     ait *storeAddr)
{
	EventTimestamp when;
	unsigned long start = force(_start);
	if (thr)
		checkFreeList(_start, _start + mkConst<ait>(size), thr->tid, EventTimestamp::invalid);
	if (storeAddr)
		*storeAddr = mkConst<ait>(start);
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

template <typename ait> bool
AddressSpace<ait>::isOnFreeList(ait start, ait end,
				ThreadId asking,
				EventTimestamp *when,
				ait *free_addr) const
{
	class AddressSpace<ait>::freed_memory_t::const_iterator it;

	for (it = freed_memory.begin();
	     it != freed_memory.end();
	     it++) {
		if (it->when.tid != asking && force(it->start < end) &&
		    force(it->end > start)) {
			if (when)
				*when = it->when;
			if (free_addr)
				*free_addr = it->start;
			return true;
		}
	}
	return false;
}

template <typename ait> void
AddressSpace<ait>::checkFreeList(ait start, ait end,
				 ThreadId asking, EventTimestamp now)
{
	EventTimestamp when;
	if (isOnFreeList(start, end, asking, &when))
		throw UseOfFreeMemoryException(now, force(start), when);
}

template <typename ait>
bool AddressSpace<ait>::isAccessible(ait _start, unsigned size,
				     bool isWrite, const Thread<ait> *thr)
{
	unsigned long start = force(_start);
	if (isOnFreeList(_start, _start + mkConst<ait>(size), thr->tid))
		return false;
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
	AddressSpace<ait> *work = new AddressSpace<ait>();
	work->brkptr = initialBrk;
	work->brkMapPtr = initialBrk + 4096;
	work->pmap = PMap<ait>::empty();
	work->vamap = VAMap::empty();
	return work;	
}

template <typename ait>
AddressSpace<ait> *AddressSpace<ait>::dupeSelf() const
{
	AddressSpace<ait> *work = new AddressSpace<ait>();
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
	visit_aiv(client_free, hv);
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

	printf("Extending stack from %lx to %lx\n", ptr, va);
	ptr &= PAGE_MASK;
	allocateMemory(mkConst<ait>(ptr), mkConst<ait>(va - ptr), prot, flags);
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
	lw->append(new LogRecordInitialBrk<ait>(ThreadId(0), mkConst<ait>(brkptr)),
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
		lw->append(new LogRecordAllocateMemory<ait>(ThreadId(0),
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
		lw->append(new LogRecordMemory<ait>(ThreadId(0),
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
	AddressSpace<new_type> *work = new AddressSpace<new_type>();

	work->brkptr = brkptr;
	work->brkMapPtr = brkMapPtr;
	work->vamap = vamap->dupeSelf();
	work->pmap = pmap->abstract<new_type>();
	work->client_free = mkConst<new_type>(force(client_free));
	return work;
}

/* Valgrind handles vsyscalls in a slightly weird way, and we have to
   emulate that here. */
#define STRING(x) #x
#define STRING2(x) STRING(x)
asm (
"redirect_vtime:\n"
"        movq $" STRING2(__NR_time) ", %rax\n"
"        syscall\n"
"        ret\n"
"redirect_vgettimeofday:\n"
"        movq $" STRING2(__NR_gettimeofday) ", %rax\n"
"        syscall\n"
"        ret\n"
"redirect_end:\n"
	);
extern unsigned char redirect_vtime[];
extern unsigned char redirect_vgettimeofday[];
extern unsigned char redirect_end[];

template <typename ait> void
AddressSpace<ait>::writeLiteralMemory(unsigned long start,
				      unsigned size,
				      const unsigned char *content)
{
	ait *c = (ait *)malloc(sizeof(ait) * size);
	for (unsigned x = 0; x < size; x++)
		c[x] = mkConst<ait>(content[x]);
	writeMemory(EventTimestamp::invalid, mkConst<ait>(start),
		    size, c, true, NULL);
	free(c);
}

template <typename ait> void
AddressSpace<ait>::addVsyscalls()
{
	allocateMemory(mkConst<ait>(0xFFFFFFFFFF600000),
		       mkConst<ait>(0x1000),
		       VAMap::Protection(true, false, true),
		       VAMap::AllocFlags(false));
	writeLiteralMemory(0xFFFFFFFFFF600000,
			   redirect_end - redirect_vgettimeofday,
			   redirect_vgettimeofday);
	writeLiteralMemory(0xFFFFFFFFFF600400,
			   redirect_vgettimeofday - redirect_vtime,
			   redirect_vtime);
}

template <typename ait> char *
AddressSpace<ait>::readString(ait start, Thread<ait> *thr)
{
	char *buf;
	unsigned offset;
	unsigned buf_size;

	buf_size = 64;
	buf = (char *)malloc(buf_size);
	offset = 0;
	while (1) {
		ait b;
		readMemory(start + mkConst<ait>(offset), 1, &b, false, thr);
		buf[offset] = force(b);
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

template <typename ait> int
compare_ait_buffer_char_buffer(const ait *buffer,
			       const char *bytes,
			       size_t s)
{
	for (unsigned x = 0; x < s; x++) {
		unsigned long b = force(buffer[x]);
		unsigned long b2 = ((unsigned char *)bytes)[x];
		if (b < b2)
			return -1;
		else if (b > b2)
			return 1;
	}
	return 0;
}

template <typename ait> void
AddressSpace<ait>::findInterestingFunctions(const VAMap::VAMapEntry *it)
{
	ait buf[4096];

	/* Try to spot malloc, free, realloc.  Hideous hack. */
	if (it->end - it->start != 0x168000) {
		/* Wrong size -> not libc. */
		return;
	}
	readMemory(mkConst<ait>(it->start + 0x7a230),
		   293,
		   buf,
		   false,
		   NULL);
	if (compare_ait_buffer_char_buffer<ait>(
		    buf,
		    "\x48\x8b\x05\x21\x1d\x2f\x00\x53\x49\x89\xf8\x48\x8b\x00\x48\x85\xc0\x74\x0d\x48\x8b\x74\x24\x08\x49\x89\xc3\x5b\x41\xff\xe3\x90\x48\x85\xff\x74\x6d\x48\x8b\x47\xf8\x48\x8d\x4f\xf0\xa8\x02\x75\x67\xa8\x04\x48\x8d\x1d\x96\x37\x2f\x00\x74\x0a\x48\x81\xe1\x00\x00\x00\xfc\x48\x8b\x19\xbe\x01\x00\x00\x00\x31\xc0\x83\x3d\xc4\x6d\x2f\x00\x00\x74\x0c\xf0\x0f\xb1\x33\x0f\x85\xb6\x3d\x00\x00\xeb\x09\x0f\xb1\x33\x0f\x85\xab\x3d\x00\x00\x4c\x89\xc6\x48\x89\xdf\xe8\x5a\xf6\xff\xff\x83\x3d\x9b\x6d\x2f\x00\x00\x74\x0b\xf0\xff\x0b\x0f\x85\xa9\x3d\x00\x00\xeb\x08\xff\x0b\x0f\x85\x9f\x3d\x00\x00\x5b\xc3\x0f\x1f\x40\x00\x8b\x15\xf6\x3f\x2f\x00\x85\xd2\x75\x2e\x48\x3b\x05\xd7\x3f\x2f\x00\x76\x25\x48\x3d\x00\x00\x00\x02\x77\x1d\x48\x89\xc2\x48\x83\xe2\xf8\x48\x8d\x04\x12\x48\x89\x15\xbb\x3f\x2f\x00\x48\x89\x05\xa4\x3f\x2f\x00\xeb\x09\x66\x90\x48\x89\xc2\x48\x83\xe2\xf8\x49\x8b\x40\xf0\x48\x89\xcf\x48\x29\xc7\x48\x8d\x34\x02\x8b\x05\xad\x3f\x2f\x00\x48\x89\xf2\x48\x09\xfa\x83\xe8\x01\x48\x85\xc2\x75\x14\x5b\x83\x2d\x87\x3f\x2f\x00\x01\x48\x29\x35\x98\x3f\x2f\x00\xe9\x23\x86\x06\x00\x5b\x8b\x3d\xa0\x1d\x2f\x00\x48\x8d\x51\x10\x48\x8d\x35\xc9\x21\x0c\x00\xe9\xdc\xd8\xff\xff\x66",
		    293)) {
		printf("free() mismatch -> not libc\n");
		return;
	}
//	this->client_free = mkConst<ait>(it->start + 0x7a230);
}

template <typename ait> void
AddressSpace<ait>::findInterestingFunctions()
{
	for (VAMap::iterator it = vamap->begin();
	     it != vamap->end();
	     it++) {
		if (!it->prot.readable || !it->prot.executable)
			continue;

		findInterestingFunctions(&*it);
	}

	fflush(NULL);
}

template <typename ait> void
AddressSpace<ait>::client_freed(EventTimestamp when, ait ptr)
{
	if (force(ptr == mkConst<ait>(0)))
		return;

	expression_result<ait> chk = load(when, ptr - mkConst<ait>(8), 8);
	client_freed_entry<ait> cf;

	cf.start = ptr;
	cf.end = ptr + chk.lo;
	cf.when = when;
	printf("client_free(%lx, %lx)\n", force(cf.start), force(cf.end));
	freed_memory.push_back(cf);
}

#define MK_ADDRESS_SPACE(t)
