#include <assert.h>
#include <stdio.h>

#include "sli.h"
#include "libvex_alloc.h"
#include "main_util.h"

struct keeper {
	PhysicalAddress pa1;
	PhysicalAddress pa2;
	PMap<unsigned long> *pmap;
};

DECLARE_VEX_TYPE(keeper);
DEFINE_VEX_TYPE_NO_DESTRUCT(keeper, {
		ths->pmap->visitPA(ths->pa1, visit);
		ths->pmap->visitPA(ths->pa2, visit);
	});

int
main()
{
	vexInitHeap();

	PMap<unsigned long> *pmap1 = PMap<unsigned long>::empty();

	MemoryChunk<unsigned long> *mc1;

	printf("Lookup in an empty map -> NULL\n");
	unsigned long off1;
	mc1 = pmap1->lookup(PhysicalAddress(), &off1);
	assert(mc1 == NULL);

	mc1 = MemoryChunk<unsigned long>::allocate();
	PhysicalAddress pa1;

	printf("Introduce a memory chunk and make sure we can get it back again.\n");
	pa1 = pmap1->introduce(mc1);
	printf("pa1 %lx\n", pa1._pa);
	MemoryChunk<unsigned long> *mc2 = pmap1->lookup(pa1, &off1);
	assert(mc1 == mc2);
	assert(off1 == 0);
	printf("Check that offsets work.\n");
	mc2 = pmap1->lookup(pa1 + 10, &off1);
	assert(mc1 == mc2);
	assert(off1 == 10);
	printf("Make sure that looking up a bad address returns NULL.\n");
	mc2 = pmap1->lookup(pa1 + MemoryChunk<unsigned long>::size, &off1);
	assert(mc2 == NULL);

	printf("Introduce a second chunk and make sure that they stay separate.\n");
	mc2 = MemoryChunk<unsigned long>::allocate();
	PhysicalAddress pa2 = pmap1->introduce(mc2);
	printf("pa2 %lx\n", pa2._pa);
	assert(pa2 != pa1);
	MemoryChunk<unsigned long> *mc3;
	mc3 = pmap1->lookup(pa1, &off1);
	assert(mc3 == mc1);
	mc3 = pmap1->lookup(pa2, &off1);
	assert(mc3 == mc2);
	
	printf("GC behaviour.  There are no external references, so a GC cycle should cause the pmap to empty itself.\n");
	vexRegisterGCRoot((void **)&pmap1, "testpmap");
	LibVEX_gc();

	mc1 = pmap1->lookup(pa1, &off1);
	assert(mc1 == NULL);
	mc2 = pmap1->lookup(pa2, &off1);
	assert(mc2 == NULL);

	printf("Now check that it's possible to hold references to the chunks\n");
	mc1 = MemoryChunk<unsigned long>::allocate();
	mc2 = MemoryChunk<unsigned long>::allocate();
	pa1 = pmap1->introduce(mc1);
	pa2 = pmap1->introduce(mc2);

	keeper *k = LibVEX_Alloc_keeper();
	k->pa1 = pa1;
	k->pa2 = pa2;
	k->pmap = pmap1;

	vexRegisterGCRoot((void **)&k, "testpmap2");
	LibVEX_gc();

	mc3 = pmap1->lookup(pa1, &off1);
	assert(mc3 == mc1);
	mc3 = pmap1->lookup(pa2, &off1);
	assert(mc3 == mc2);

	printf("Unregister the keeper and check that everything drops away\n");
	vexUnregisterGCRoot((void **)&k);
	LibVEX_gc();
	mc3 = pmap1->lookup(pa1, &off1);
	assert(mc3 == NULL);
	mc3 = pmap1->lookup(pa2, &off1);
	assert(mc3 == NULL);

	printf("State forking...\n");
	mc1 = MemoryChunk<unsigned long>::allocate();
	unsigned long b[12];
	for (unsigned x = 0; x < 12; x++)
		b[x] = "Hello world"[x];
	mc1->write(EventTimestamp::invalid, 0, b, 11);
	pa1 = pmap1->introduce(mc1);
	PMap<unsigned long> *pmap2 = pmap1->dupeSelf();
	PMap<unsigned long> *pmap3 = pmap1->dupeSelf();

	printf("Check forked state can see parent's MCs\n");
	const MemoryChunk<unsigned long> *cmc = pmap2->lookupConst(pa1, &off1);
	assert(cmc == mc1);
	cmc = pmap3->lookupConst(pa1, &off1);
	assert(cmc == mc1);

	printf("Check forked state can update own MCs.\n");
	mc2 = pmap2->lookup(pa1, &off1);
	unsigned long b2[7];
	for (unsigned x = 0; x < 7; x++)
		b2[x] = "goodbye"[x];
	mc2->write(EventTimestamp::invalid, 0, b2, 7);
	unsigned long buf[11];
	mc2->read(0, buf, 7);
	unsigned char b3[11];
	for (unsigned x = 0; x < 7; x++)
		b3[x] = buf[x];
	assert(!memcmp(b3, "goodbye", 7));

	printf("Check forked state can't update parent or sibling MCs\n");
	mc3 = pmap1->lookup(pa1, &off1);

	mc3->read(0, buf, 11);
	for (unsigned x = 0; x < 11; x++)
		b3[x] = buf[x];
	assert(!memcmp(b3, "Hello world", 11));

	cmc = pmap3->lookup(pa1, &off1);
	cmc->read(0, buf, 11);
	for (unsigned x = 0; x < 11; x++)
		b3[x] = buf[x];
	assert(!memcmp(b3, "Hello world", 11));
	return 0;
}
