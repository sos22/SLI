#include <sys/mman.h>
#include <stdlib.h>
#include <string.h>

#include "sli.h"

#define PAGE_MASK (~4095)

void
AddressSpace::allocateMemory(unsigned long _start, unsigned long _size,
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

	findInterestingFunctions();
}

void
AddressSpace::releaseMemory(unsigned long start, unsigned long size)
{
	vamap->unmap(force(start), force(size));
}

void
AddressSpace::protectMemory(unsigned long start, unsigned long size,
			    VAMap::Protection prot)
{
	vamap->protect(force(start), force(size), prot);
}

bool
AddressSpace::copyToClient(EventTimestamp when, unsigned long start, unsigned size,
			   const void *contents)
{
	unsigned long *buf = (unsigned long *)malloc(sizeof(unsigned long) * size);
	bool fault;

	for (unsigned x = 0; x < size; x++)
		buf[x] = mkConst<unsigned long>( ((unsigned char *)contents)[x] );
	fault = false;
	try {
		writeMemory(when, start, size, buf, false, NULL);
	} catch (BadMemoryException<unsigned long> &e) {
		fault = true;
	}
	free(buf);
	return fault;
}

bool
AddressSpace::copyFromClient(EventTimestamp when, unsigned long start, unsigned size,
			     void *dest)
{
	unsigned long *buf = (unsigned long *)calloc(sizeof(unsigned long), size);
	bool fault;

	fault = false;
	try {
		readMemory(start, size, buf, false, NULL, NULL);
	} catch (BadMemoryException<unsigned long> &e) {
		fault = true;
	}
	if (!fault) {
		for (unsigned x = 0; x < size; x++) {
			((unsigned char *)dest)[x] = force(buf[x]);
		}
	}
	free(buf);
	return fault;
}

void
AddressSpace::writeMemory(EventTimestamp when, unsigned long _start, unsigned size,
			  const unsigned long *contents, bool ignore_protection,
			  Thread<unsigned long> *thr)
{
	unsigned long start = force(_start);
	unsigned off = 0;
	if (thr) {
		checkFreeList(_start, _start + mkConst<unsigned long>(size), thr->tid, EventTimestamp::invalid);
		if (start == 0x456e9e0)
			printf("Thread %d writes %d to %lx\n", thr->tid._tid(),
			       size, start);
	}

	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if (!ignore_protection && !prot.writable)
				throw BadMemoryException<unsigned long>(true, _start, size);
			unsigned long mc_start;
			unsigned to_copy_this_time;
			MemoryChunk *mc = pmap->lookup(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time > mc->size - mc_start)
				to_copy_this_time = mc->size - mc_start;
			mc->write(when, mc_start, contents, to_copy_this_time,
				  _start + mkConst<unsigned long>(off));

			start += to_copy_this_time;
			size -= to_copy_this_time;
			off += to_copy_this_time;
			contents = contents + to_copy_this_time;
		} else if (thr && extendStack(start, force(thr->regs.rsp()))) {
			continue;
		} else {
			throw BadMemoryException<unsigned long>(true, _start, size);
		}
	}
}

expression_result<unsigned long>
AddressSpace::load(EventTimestamp when,
		   unsigned long start, unsigned size,
		   bool ignore_protection,
		   Thread<unsigned long> *thr)
{
	unsigned long b[16];
	unsigned long storeAddr;
	memset(b, 0, sizeof(unsigned long) * size);
	for (unsigned x = 0; x < size; x++)
		new (&b[x]) unsigned long();
	EventTimestamp sto = readMemory(start, size, b, ignore_protection, thr, &storeAddr);
	expression_result<unsigned long> res;
	res.lo = mkConst<unsigned long>(0);
	res.hi = mkConst<unsigned long>(0);
	switch(size) {
	case 16:
		res.hi = b[8] +
			(b[9] << mkConst<unsigned long>(8)) +
			(b[10] << mkConst<unsigned long>(16)) +
			(b[11] << mkConst<unsigned long>(24)) +
			(b[12] << mkConst<unsigned long>(32)) +
			(b[13] << mkConst<unsigned long>(40)) +
			(b[14] << mkConst<unsigned long>(48)) +
			(b[15] << mkConst<unsigned long>(56));
		/* Fall through */
	case 8:
		res.lo = res.lo +
			(b[7] << mkConst<unsigned long>(56)) +
			(b[6] << mkConst<unsigned long>(48)) +
			(b[5] << mkConst<unsigned long>(40)) +
			(b[4] << mkConst<unsigned long>(32));
		/* Fall through */
	case 4:
		res.lo = res.lo +
			(b[3] << mkConst<unsigned long>(24)) +
			(b[2] << mkConst<unsigned long>(16));
		/* Fall through */
	case 2:
		res.lo = res.lo + (b[1] << mkConst<unsigned long>(8));
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
#if 1
	irrelevant = (is_stack(start) ||
		      (thr &&
		       force(start) > force(thr->regs.rsp()) - 1000000 &&
		       force(start) < force(thr->regs.rsp()) + 1000000));
#else
	irrelevant = force(start) != 0x601080 && force(start) != 0x4221010;
#endif
	if (!irrelevant || 1) {
		if (size <= 8) {
			res.lo = load_ait<unsigned long>(res.lo, start, when, sto, storeAddr, size);
		} else {
			res.lo = load_ait<unsigned long>(res.lo, start, when, sto, storeAddr, 8);
			res.hi = load_ait<unsigned long>(res.hi, start, when, sto, storeAddr, 8);
		}
	}
	return res;
}

void
AddressSpace::store(EventTimestamp when, unsigned long start, unsigned size,
		    const expression_result<unsigned long> &val, bool ignore_protection,
		    Thread<unsigned long> *thr)
{
	unsigned long b[16];
	sanity_check_ait(val.hi);
	sanity_check_ait(val.lo);
	switch (size) {
	case 16:
		b[15] = (val.hi >> mkConst<unsigned long>(56)) & mkConst<unsigned long>(0xff);
		b[14] = (val.hi >> mkConst<unsigned long>(48)) & mkConst<unsigned long>(0xff);
		b[13] = (val.hi >> mkConst<unsigned long>(40)) & mkConst<unsigned long>(0xff);
		b[12] = (val.hi >> mkConst<unsigned long>(32)) & mkConst<unsigned long>(0xff);
		b[11] = (val.hi >> mkConst<unsigned long>(24)) & mkConst<unsigned long>(0xff);
		b[10] = (val.hi >> mkConst<unsigned long>(16)) & mkConst<unsigned long>(0xff);
		b[9] = (val.hi >> mkConst<unsigned long>(8)) & mkConst<unsigned long>(0xff);
		b[8] = val.hi & mkConst<unsigned long>(0xff);
	case 8:
		b[7] = (val.lo >> mkConst<unsigned long>(56)) & mkConst<unsigned long>(0xff);
		b[6] = (val.lo >> mkConst<unsigned long>(48)) & mkConst<unsigned long>(0xff);
		b[5] = (val.lo >> mkConst<unsigned long>(40)) & mkConst<unsigned long>(0xff);
		b[4] = (val.lo >> mkConst<unsigned long>(32)) & mkConst<unsigned long>(0xff);
	case 4:
		b[3] = (val.lo >> mkConst<unsigned long>(24)) & mkConst<unsigned long>(0xff);
		b[2] = (val.lo >> mkConst<unsigned long>(16)) & mkConst<unsigned long>(0xff);
	case 2:
		b[1] = (val.lo >> mkConst<unsigned long>(8)) & mkConst<unsigned long>(0xff);
	case 1:
		b[0] = val.lo & mkConst<unsigned long>(0xff);
		break;
	default:
		abort();
	}
	for (unsigned x = 0; x < size; x++)
		sanity_check_ait(b[x]);
	writeMemory(when, start, size, b, ignore_protection, thr);
}

template <typename t> const t
AddressSpace::fetch(unsigned long start, Thread<unsigned long> *thr)
{
	unsigned long *res;

	res = (unsigned long *)malloc(sizeof(unsigned long) * sizeof(t));
	readMemory(mkConst<unsigned long>(start), sizeof(t), res, false, thr);
	t tt;
	for (unsigned x = 0; x < sizeof(t); x++)
		((unsigned char *)&tt)[x] = force(res[x]);
	free(res);
	return tt;
}

EventTimestamp AddressSpace::readMemory(unsigned long _start, unsigned size,
					unsigned long *contents, bool ignore_protection,
					Thread<unsigned long> *thr,
					unsigned long *storeAddr)
{
	EventTimestamp when;
	unsigned long start = force(_start);
	if (thr)
		checkFreeList(_start, _start + mkConst<unsigned long>(size), thr->tid, EventTimestamp::invalid);
	if (storeAddr)
		*storeAddr = mkConst<unsigned long>(start);
	while (size != 0) {
		PhysicalAddress pa;
		VAMap::Protection prot(0);
		if (vamap->translate(start, &pa, &prot)) {
			if (!ignore_protection && !prot.readable)
				throw BadMemoryException<unsigned long>(false, _start, size);
			unsigned long mc_start;
			unsigned to_copy_this_time;
			const MemoryChunk *mc = pmap->lookupConst(pa, &mc_start);
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
			throw BadMemoryException<unsigned long>(false, _start, size);
		}
	}
	return when;
}

bool
AddressSpace::isOnFreeList(unsigned long start, unsigned long end,
				ThreadId asking,
				EventTimestamp *when,
				unsigned long *free_addr) const
{
	AddressSpace::freed_memory_t::const_iterator it;

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

void
AddressSpace::checkFreeList(unsigned long start, unsigned long end,
				 ThreadId asking, EventTimestamp now)
{
	EventTimestamp when;
	if (isOnFreeList(start, end, asking, &when))
		throw UseOfFreeMemoryException(now, force(start), when);
}

bool AddressSpace::isAccessible(unsigned long _start, unsigned size,
				     bool isWrite, Thread<unsigned long> *thr)
{
	unsigned long start = force(_start);
	if (thr && isOnFreeList(_start, _start + mkConst<unsigned long>(size), thr->tid))
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
			const MemoryChunk *mc = pmap->lookupConst(pa, &mc_start);
			assert(mc);
			to_copy_this_time = size;
			if (to_copy_this_time >
			    mc_start + mc->size - start)
				to_copy_this_time = mc_start + mc->size - start;

			start += to_copy_this_time;
			size -= to_copy_this_time;
		} else if (thr && extendStack(start, force(thr->regs.rsp()))) {
			continue;
		} else {
			return false;
		}
	}
	return true;
}

unsigned long AddressSpace::setBrk(unsigned long _newBrk)
{
	unsigned long newBrk = force(_newBrk);
	unsigned long newBrkMap = (newBrk + 4095) & PAGE_MASK;

	if (newBrk != 0) {
		if (newBrkMap > brkMapPtr)
			allocateMemory(mkConst<unsigned long>(brkMapPtr), mkConst<unsigned long>(newBrkMap - brkMapPtr), VAMap::Protection(true, true, false));
		else
			releaseMemory(mkConst<unsigned long>(newBrkMap), mkConst<unsigned long>(brkMapPtr - newBrkMap));
		brkptr = newBrk;
		brkMapPtr = newBrkMap;
	}

	return brkptr;
}

AddressSpace *AddressSpace::initialAddressSpace(unsigned long _initialBrk)
{
	unsigned long initialBrk = force(_initialBrk);
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
	visit_aiv(client_free, hv);
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
	allocateMemory(mkConst<unsigned long>(ptr), mkConst<unsigned long>(va - ptr), prot, flags);
	return true;
}

void AddressSpace::sanityCheck() const
{
	vamap->sanityCheck();
}

void AddressSpace::dumpBrkPtr(LogWriter<unsigned long> *lw) const
{
	lw->append(new LogRecordInitialBrk<unsigned long>(ThreadId(0), mkConst<unsigned long>(brkptr)),
		   0);
}

void AddressSpace::dumpSnapshot(LogWriter<unsigned long> *lw) const
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

		lw->append(new LogRecordAllocateMemory<unsigned long>(ThreadId(0),
							    mkConst<unsigned long>(start_va),
							    mkConst<unsigned long>(end_va - start_va),
							    (unsigned long)prot,
							    (unsigned long)alf),
			   0);

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
				lw->append(new LogRecordMemory<unsigned long>(ThreadId(0),
								    MemoryChunk::size,
								    mkConst<unsigned long>(cursor_va),
								    buf),
					   0);
			}
		}

		end_of_last_block = end_va;
	}
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

void
AddressSpace::writeLiteralMemory(unsigned long start,
				      unsigned size,
				      const unsigned char *content)
{
	unsigned long *c = (unsigned long *)malloc(sizeof(unsigned long) * size);
	for (unsigned x = 0; x < size; x++)
		c[x] = mkConst<unsigned long>(content[x]);
	writeMemory(EventTimestamp::invalid, mkConst<unsigned long>(start),
		    size, c, true, NULL);
	free(c);
}

void
AddressSpace::addVsyscalls()
{
#if 0
	allocateMemory(mkConst<unsigned long>(0xFFFFFFFFFF600000),
		       mkConst<unsigned long>(0x1000),
		       VAMap::Protection(true, false, true),
		       VAMap::AllocFlags(false));
	writeLiteralMemory(0xFFFFFFFFFF600000,
			   redirect_end - redirect_vgettimeofday,
			   redirect_vgettimeofday);
	writeLiteralMemory(0xFFFFFFFFFF600400,
			   redirect_vgettimeofday - redirect_vtime,
			   redirect_vtime);
#endif
}

char *
AddressSpace::readString(unsigned long start, Thread<unsigned long> *thr)
{
	char *buf;
	unsigned offset;
	unsigned buf_size;

	buf_size = 64;
	buf = (char *)malloc(buf_size);
	offset = 0;
	while (1) {
		unsigned long b;
		readMemory(start + mkConst<unsigned long>(offset), 1, &b, false, thr);
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

int
compare_ait_buffer_char_buffer(const unsigned long *buffer,
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

void
AddressSpace::findInterestingFunctions(const VAMap::VAMapEntry *it)
{
	unsigned long buf[4096];

	/* Try to spot malloc, free, realloc.  Hideous hack. */
	if (it->end - it->start != 0x168000) {
		/* Wrong size -> not libc. */
		return;
	}
	readMemory(mkConst<unsigned long>(it->start + 0x7a230),
		   293,
		   buf,
		   false,
		   NULL);
	if (compare_ait_buffer_char_buffer(
		    buf,
		    "\x48\x8b\x05\x21\x1d\x2f\x00\x53\x49\x89\xf8\x48\x8b\x00\x48\x85\xc0\x74\x0d\x48\x8b\x74\x24\x08\x49\x89\xc3\x5b\x41\xff\xe3\x90\x48\x85\xff\x74\x6d\x48\x8b\x47\xf8\x48\x8d\x4f\xf0\xa8\x02\x75\x67\xa8\x04\x48\x8d\x1d\x96\x37\x2f\x00\x74\x0a\x48\x81\xe1\x00\x00\x00\xfc\x48\x8b\x19\xbe\x01\x00\x00\x00\x31\xc0\x83\x3d\xc4\x6d\x2f\x00\x00\x74\x0c\xf0\x0f\xb1\x33\x0f\x85\xb6\x3d\x00\x00\xeb\x09\x0f\xb1\x33\x0f\x85\xab\x3d\x00\x00\x4c\x89\xc6\x48\x89\xdf\xe8\x5a\xf6\xff\xff\x83\x3d\x9b\x6d\x2f\x00\x00\x74\x0b\xf0\xff\x0b\x0f\x85\xa9\x3d\x00\x00\xeb\x08\xff\x0b\x0f\x85\x9f\x3d\x00\x00\x5b\xc3\x0f\x1f\x40\x00\x8b\x15\xf6\x3f\x2f\x00\x85\xd2\x75\x2e\x48\x3b\x05\xd7\x3f\x2f\x00\x76\x25\x48\x3d\x00\x00\x00\x02\x77\x1d\x48\x89\xc2\x48\x83\xe2\xf8\x48\x8d\x04\x12\x48\x89\x15\xbb\x3f\x2f\x00\x48\x89\x05\xa4\x3f\x2f\x00\xeb\x09\x66\x90\x48\x89\xc2\x48\x83\xe2\xf8\x49\x8b\x40\xf0\x48\x89\xcf\x48\x29\xc7\x48\x8d\x34\x02\x8b\x05\xad\x3f\x2f\x00\x48\x89\xf2\x48\x09\xfa\x83\xe8\x01\x48\x85\xc2\x75\x14\x5b\x83\x2d\x87\x3f\x2f\x00\x01\x48\x29\x35\x98\x3f\x2f\x00\xe9\x23\x86\x06\x00\x5b\x8b\x3d\xa0\x1d\x2f\x00\x48\x8d\x51\x10\x48\x8d\x35\xc9\x21\x0c\x00\xe9\xdc\xd8\xff\xff\x66",
		    293)) {
		printf("free() mismatch -> not libc\n");
		return;
	}
//	this->client_free = mkConst<unsigned long>(it->start + 0x7a230);
}

void
AddressSpace::findInterestingFunctions()
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

void
AddressSpace::client_freed(EventTimestamp when, unsigned long ptr)
{
	if (force(ptr == mkConst<unsigned long>(0)))
		return;

	expression_result<unsigned long> chk = load(when, ptr - mkConst<unsigned long>(8), 8);
	client_freed_entry<unsigned long> cf;

	cf.start = ptr;
	cf.end = ptr + chk.lo;
	cf.when = when;
	printf("client_free(%lx, %lx)\n", force(cf.start), force(cf.end));
	freed_memory.push_back(cf);
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

#if 0
void
AddressSpace::sanityCheckDecodeCache() const
{
	trans_hash_entry *n;

	for (unsigned x = 0;
	     x < nr_trans_hash_slots;
	     x++) {
		if (!trans_hash[x])
			continue;
		assert(trans_hash[x]->pprev == &trans_hash[x]);
		n = trans_hash[x];
		while (n) {
			assert(rip_hash(n->rip, nr_trans_hash_slots) == x);
			if (n->next)
				assert(n->next->pprev == &n->next);
			n = n->next;
		}
	}
}
#endif

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

	sanityCheckDecodeCache();

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
			sanityCheckDecodeCache();
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

	sanityCheckDecodeCache();
	return n->irsb;
}

#define MK_ADDRESS_SPACE(t)
