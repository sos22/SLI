#include <stdio.h>
#include "sli.h"

int
main()
{
	vexInitHeap();

	PMap *pmap = PMap::empty();
	VAMap *vamap = VAMap::empty(pmap);

	printf("Check that translating bad addresses gives back false\n");
	assert(!vamap->translate(0));
	assert(!vamap->translate(0xf001));
	assert(!vamap->translate(~0));
	assert(!vamap->translate(~0ul));

	MemoryChunk *mc1 = MemoryChunk::allocate();
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
	MemoryChunk *mc2 = MemoryChunk::allocate();
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
	VexGcRoot vgc((void **)&vamap);

	LibVEX_gc();

	unsigned long o;

	printf("Keep PA1 live...\n");
	assert(pmap->lookup(pa1, &o));
	printf("Let PA2 die...\n");
	assert(!pmap->lookup(pa2, &o));
}
