#include <stdio.h>
#include "sli.h"

class VAPMap {
public:
	static VexAllocTypeWrapper<VAPMap> allocator;
	VAMap *vamap;
	PMap<unsigned long> *pmap;
	void visit(HeapVisitor &hv) const {
		hv(vamap);
		hv(pmap);
		vamap->visit(hv, pmap);
	}
	void destruct() {}
	NAMED_CLASS
};
VexAllocTypeWrapper<VAPMap> VAPMap::allocator;

int
main()
{
	vexInitHeap();

	PMap<unsigned long> *pmap = PMap<unsigned long>::empty();
	VAMap *vamap = VAMap::empty();

	printf("Check that translating bad addresses gives back false\n");
	assert(!vamap->translate(0));
	assert(!vamap->translate(0xf001));
	assert(!vamap->translate(~0));
	assert(!vamap->translate(~0ul));

	MemoryChunk<unsigned long> *mc1 = MemoryChunk<unsigned long>::allocate();
	PhysicalAddress pa1 = pmap->introduce(mc1);
	printf("Introduce a mapping and check that it comes back\n");
	vamap->addTranslation(0x10000, pa1,
			      VAMap::Protection(true, true, false),
			      VAMap::AllocFlags(false));
	bool r;
	r = vamap->translate(0x10000);
	assert(r);
	PhysicalAddress pa2;
	r = vamap->translate(0x10000, &pa2);
	assert(r);
	assert(pa2 == pa1);
	r = vamap->translate(0x10005, &pa2);
	assert(r);
	assert(pa2 == pa1 + 5);
	VAMap::Protection prot(0);
	r = vamap->translate(0x10000, NULL, &prot);
	assert(r);
	assert(prot.readable);
	assert(prot.writable);
	assert(!prot.executable);
	VAMap::AllocFlags alf(false);
	r = vamap->translate(0x10000, NULL, NULL, &alf);
	assert(r);
	assert(!alf.expandsDown);

	printf("Check that bad mappings are still bad\n");
	r = vamap->translate(0);
	assert(!r);
	r = vamap->translate(0x11000);
	assert(!r);
	r = vamap->translate(0xffff);
	assert(!r);

	printf("Introduce another mapping and check that they stay separate.\n");
	MemoryChunk<unsigned long> *mc2 = MemoryChunk<unsigned long>::allocate();
	pa2 = pmap->introduce(mc2);
	vamap->addTranslation(0x11000, pa2,
			      VAMap::Protection(true, false, true),
			      VAMap::AllocFlags(true));
	PhysicalAddress pa3;
	r = vamap->translate(0x10000,
			     &pa3,
			     &prot,
			     &alf);
	assert(r);
	assert(pa3 == pa1);
	assert(prot == VAMap::Protection(true, true, false));
	assert(alf == VAMap::AllocFlags(false));

	r = vamap->translate(0x11000,
			     &pa3,
			     &prot,
			     &alf);
	assert(r);
	assert(pa3 == pa2);
	assert(prot == VAMap::Protection(true, false, true));
	assert(alf == VAMap::AllocFlags(true));

	printf("Try unmapping something\n");
	vamap->unmap(0x11000, 0x1000);
	r = vamap->translate(0x11000);
	assert(!r);
	r = vamap->translate(0x10000,
			     &pa3,
			     &prot,
			     &alf);
	assert(r);
	assert(pa3 == pa1);
	assert(prot == VAMap::Protection(true, true, false));
	assert(alf == VAMap::AllocFlags(false));

	printf("mprotect()\n");
	r = vamap->protect(0x10000, 0x1000, VAMap::Protection(false, false, true));
	assert(r);
	r = vamap->translate(0x10000,
			     &pa3,
			     &prot,
			     &alf);
	assert(r);
	assert(pa3 == pa1);
	assert(prot == VAMap::Protection(false, false, true));
	assert(alf == VAMap::AllocFlags(false));

	printf("mprotect() bad\n");
	r = vamap->protect(0x11000, 0x1000, VAMap::Protection(false, false, true));
	assert(!r);

	unsigned long va;
	printf("findNextMapping\n");
	r = vamap->findNextMapping(0x5000, &va, &pa3, &prot, &alf);
	assert(r);
	assert(va == 0x10000);
	assert(pa3 == pa1);
	assert(prot == VAMap::Protection(false, false, true));
	assert(alf == VAMap::AllocFlags(false));

	printf("Check GC behaviour: VAMap keeps physical addresses live\n");
	VAPMap *vap = VAPMap::allocator.alloc();
	vap->vamap = vamap;
	vap->pmap = pmap;
	VexGcRoot vgc((void **)&vap, "test vamap");
	
	LibVEX_gc(ALLOW_GC);

	unsigned long o;

	printf("Keep PA1 live...\n");
	assert(pmap->lookup(pa1, &o));
	printf("Let PA2 die...\n");
	assert(!pmap->lookup(pa2, &o));

	printf("Introduce 0x70000->0x75000...\n");
	unsigned x;
	PhysicalAddress block1Pa[5];
	MemoryChunk<unsigned long> *block1Mc[5];
	for (x = 0; x < 5; x++) {
		block1Mc[x] = MemoryChunk<unsigned long>::allocate();
		block1Pa[x] = pmap->introduce(block1Mc[x]);
		vamap->addTranslation(0x70000 + x * 0x1000,
				      block1Pa[x],
				      VAMap::Protection(true, false, true),
				      VAMap::AllocFlags(false));
	}
	for (x = 0; x < 5; x++) {
		r = vamap->translate(0x70000 + x * 0x1000, &pa3);
		assert(r);
		assert(pa3 == block1Pa[x]);
	}
	printf("...protect last few pages away...\n");
	vamap->protect(0x72000, 0x1000, VAMap::Protection(false, false, false));
	vamap->protect(0x73000, 0x1000, VAMap::Protection(false, false, false));
	vamap->protect(0x74000, 0x1000, VAMap::Protection(false, false, false));
	for (x = 0; x < 5; x++) {
		r = vamap->translate(0x70000 + x * 0x1000, &pa3);
		assert(pa3 == block1Pa[x]);
	}
	printf("...unmap tail...\n");
	vamap->unmap(0x72000, 0x3000);
	for (x = 0; x < 2; x++) {
		r = vamap->translate(0x70000 + x * 0x1000, &pa3);
		assert(r);
		assert(pa3 == block1Pa[x]);
	}
	for (; x < 5; x++) {
		r = vamap->translate(0x70000 + x * 0x1000);
		assert(!r);
	}
	printf("...reallocate last few pages...\n");
	for (x = 3; x < 5; x++) {
		block1Mc[x] = MemoryChunk<unsigned long>::allocate();
		block1Pa[x] = pmap->introduce(block1Mc[x]);
		vamap->addTranslation(0x70000 + x * 0x1000,
				      block1Pa[x],
				      VAMap::Protection(true, true, false),
				      VAMap::AllocFlags(false));
	}
	printf("...check results\n");
	r = vamap->translate(0x70000, &pa3);
	assert(r && pa3 == block1Pa[0]);
	r = vamap->translate(0x71000, &pa3);
	assert(r && pa3 == block1Pa[1]);
	r = vamap->translate(0x72000);
	assert(!r);
	r = vamap->translate(0x73000, &pa3);
	assert(r && pa3 == block1Pa[3]);
	r = vamap->translate(0x74000, &pa3);
	assert(r && pa3 == block1Pa[4]);

	return 0;
}
