#include <assert.h>
#include <stdio.h>

#include "sli.h"
#include "libvex_alloc.h"
#include "main_util.h"

struct keeper {
	PhysicalAddress pa1;
	PhysicalAddress pa2;
	PMap *pmap;
};

DECLARE_VEX_TYPE(keeper);
DEFINE_VEX_TYPE_NO_DESTRUCT(keeper, {
		visit(ths->pmap);
		ths->pmap->visitPA(ths->pa1, visit);
		ths->pmap->visitPA(ths->pa2, visit);
	});

int
main()
{
	vexInitHeap();

	PMap *pmap1 = PMap::empty();

	MemoryChunk *mc1;

	printf("Lookup in an empty map -> NULL\n");
	unsigned long off1;
	mc1 = pmap1->lookup(PhysicalAddress(), &off1);
	assert(mc1 == NULL);

	mc1 = MemoryChunk::allocate();
	PhysicalAddress pa1;

	printf("Introduce a memory chunk and make sure we can get it back again.\n");
	pa1 = pmap1->introduce(mc1);
	printf("pa1 %lx\n", pa1._pa);
	MemoryChunk *mc2 = pmap1->lookup(pa1, &off1);
	assert(mc1 == mc2);
	assert(off1 == 0);
	printf("Check that offsets work.\n");
	mc2 = pmap1->lookup(pa1 + 10, &off1);
	assert(mc1 == mc2);
	assert(off1 == 10);
	printf("Make sure that looking up a bad address returns NULL.\n");
	mc2 = pmap1->lookup(pa1 + MemoryChunk::size, &off1);
	assert(mc2 == NULL);

	printf("Introduce a second chunk and make sure that they stay separate.\n");
	mc2 = MemoryChunk::allocate();
	PhysicalAddress pa2 = pmap1->introduce(mc2);
	printf("pa2 %lx\n", pa2._pa);
	assert(pa2 != pa1);
	MemoryChunk *mc3;
	mc3 = pmap1->lookup(pa1, &off1);
	assert(mc3 == mc1);
	mc3 = pmap1->lookup(pa2, &off1);
	assert(mc3 == mc2);
	
	printf("GC behaviour.  There are no external references, so a GC cycle should cause the pmap to empty itself.\n");
	vexRegisterGCRoot(&main_heap, (void **)&pmap1, "testpmap");
	LibVEX_gc(&main_heap, ALLOW_GC);

	mc1 = pmap1->lookup(pa1, &off1);
	assert(mc1 == NULL);
	mc2 = pmap1->lookup(pa2, &off1);
	assert(mc2 == NULL);

	printf("Now check that it's possible to hold references to the chunks\n");
	mc1 = MemoryChunk::allocate();
	mc2 = MemoryChunk::allocate();
	unsigned mc1_serial = mc1->serial;
	unsigned mc2_serial = mc2->serial;
	pa1 = pmap1->introduce(mc1);
	pa2 = pmap1->introduce(mc2);

	keeper *k = LibVEX_Alloc_keeper();
	k->pa1 = pa1;
	k->pa2 = pa2;
	k->pmap = pmap1;

	vexRegisterGCRoot(&main_heap, (void **)&k, "testpmap2");
	LibVEX_gc(&main_heap, ALLOW_GC);

	pmap1 = k->pmap;

	mc3 = pmap1->lookup(pa1, &off1);
	assert(mc3->serial == mc1_serial);
	mc3 = pmap1->lookup(pa2, &off1);
	assert(mc3->serial == mc2_serial);

	printf("Unregister the keeper and check that everything drops away\n");
	vexUnregisterGCRoot(&main_heap, (void **)&k);
	LibVEX_gc(&main_heap, ALLOW_GC);
	mc3 = pmap1->lookup(pa1, &off1);
	assert(mc3 == NULL);
	mc3 = pmap1->lookup(pa2, &off1);
	assert(mc3 == NULL);

	printf("State forking...\n");
	mc1 = MemoryChunk::allocate();
	unsigned long b[12];
	for (unsigned x = 0; x < 12; x++)
		b[x] = "Hello world"[x];
	mc1->write(0, b, 11, 0);
	pa1 = pmap1->introduce(mc1);
	PMap *pmap2 = pmap1->dupeSelf();
	PMap *pmap3 = pmap1->dupeSelf();

	printf("Check forked state can see parent's MCs\n");
	const MemoryChunk *cmc = pmap2->lookupConst(pa1, &off1);
	assert(cmc == mc1);
	cmc = pmap3->lookupConst(pa1, &off1);
	assert(cmc == mc1);

	printf("Check forked state can update own MCs.\n");
	mc2 = pmap2->lookup(pa1, &off1);
	unsigned long b2[7];
	for (unsigned x = 0; x < 7; x++)
		b2[x] = "goodbye"[x];
	mc2->write(0, b2, 7, 0);
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
