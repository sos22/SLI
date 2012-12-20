#include <stdio.h>
#include "sli.h"

class VAPMap : public GarbageCollected<VAPMap> {
public:
	VAMap *vamap;
	PMap *pmap;
	void visit(HeapVisitor &hv) {
		hv(pmap);
		vamap->visit(vamap, hv, pmap);
	}
	NAMED_CLASS
};

int
main()
{
	vexInitHeap();

	PMap *pmap = PMap::empty();
	VAMap *vamap = VAMap::empty();

	printf("Check that translating bad addresses gives back false\n");
	assert(!vamap->translate(0));
	assert(!vamap->translate(0xf001));
	assert(!vamap->translate(~0));
	assert(!vamap->translate(~0ul));

	MemoryChunk *mc1 = new MemoryChunk();
	PhysicalAddress pa1 = pmap->introduce(mc1);
	printf("Introduce a mapping and check that it comes back\n");
	vamap->addTranslation(0x10000, pa1);
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
	r = vamap->translate(0x10000, NULL);
	assert(r);
	r = vamap->translate(0x10000, NULL);
	assert(r);

	printf("Check that bad mappings are still bad\n");
	r = vamap->translate(0);
	assert(!r);
	r = vamap->translate(0x11000);
	assert(!r);
	r = vamap->translate(0xffff);
	assert(!r);

	printf("Introduce another mapping and check that they stay separate.\n");
	MemoryChunk *mc2 = new MemoryChunk();
	pa2 = pmap->introduce(mc2);
	vamap->addTranslation(0x11000, pa2);
	PhysicalAddress pa3;
	r = vamap->translate(0x10000, &pa3);
	assert(r);
	assert(pa3 == pa1);

	r = vamap->translate(0x11000, &pa3);
	assert(r);
	assert(pa3 == pa2);

	printf("Try unmapping something\n");
	vamap->unmap(0x11000, 0x1000);
	r = vamap->translate(0x11000);
	assert(!r);
	r = vamap->translate(0x10000, &pa3);
	assert(r);
	assert(pa3 == pa1);

	assert(r);
	r = vamap->translate(0x10000, &pa3);
	assert(r);
	assert(pa3 == pa1);

	printf("Check GC behaviour: VAMap keeps physical addresses live\n");
	VexPtr<VAPMap> vap(new VAPMap());
	vap->vamap = vamap;
	vap->pmap = pmap;
	
	LibVEX_gc(ALLOW_GC);

	pmap = vap->pmap;
	vamap = vap->vamap;

	unsigned long o;

	printf("Keep PA1 live...\n");
	assert(pmap->lookup(pa1, &o));
	printf("Let PA2 die...\n");
	assert(!pmap->lookup(pa2, &o));

	printf("Introduce 0x70000->0x75000...\n");
	unsigned x;
	PhysicalAddress block1Pa[5];
	MemoryChunk *block1Mc[5];
	for (x = 0; x < 5; x++) {
		block1Mc[x] = new MemoryChunk();
		block1Pa[x] = pmap->introduce(block1Mc[x]);
		vamap->addTranslation(0x70000 + x * 0x1000,
				      block1Pa[x]);
	}
	for (x = 0; x < 5; x++) {
		r = vamap->translate(0x70000 + x * 0x1000, &pa3);
		assert(r);
		assert(pa3 == block1Pa[x]);
	}
	printf("...protect last few pages away...\n");
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
		block1Mc[x] = new MemoryChunk();
		block1Pa[x] = pmap->introduce(block1Mc[x]);
		vamap->addTranslation(0x70000 + x * 0x1000,
				      block1Pa[x]);
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
