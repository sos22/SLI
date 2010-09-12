/* Simple memory allocator and garbage collector. */

/* Why not use malloc() for this?  Historically, it was supposed to
   run in Valgrind, which means you have an extremely limited CRT,
   which doesn't include a full malloc() implementation, so we had to
   build our own.  So why not switch over now?  Because this is,
   despite being extremely simple, also extremely fast (multiple
   orders of magnitude better than glibc malloc/free()).  The trick is
   that there usually aren't very many GC roots, and they won't
   usually cover very many things in the heap, so the GC pass is very
   cheap, and we can cover it out of the much simpler allocator. */

/* The heap sanity checks are expensive enough that we're better off
   leaving them off even during normal debug runs. */
//#define NDEBUG

/* How often should we perform a garbage collection, measured in calls
   to vexSetAllocModeTEMP_and_clear, which roughly corresponds to
   client basic blocks. */
#define GC_PERIOD 100000

/* If we're given an opportunity to garbage collect and the heap is
   bigger than this then we always take it. */
#define GC_MAX_SIZE 5000000000ul

/* How far are we willing to recur during the heap walking phase of a
 * GC sweep?  If we hit this limit then we start pushing stuff off
 * to a std::vector<> to deal with later. */
#define MAX_RECURSION_DEPTH 1000

#include <sys/mman.h>
#include <err.h>
#include <stdio.h>
#include <string.h>
#include <vector>

#include "libvex_basictypes.h"
#include "libvex.h"
#include "libvex_alloc.h"

#include "main_globals.h"
#include "main_util.h"

#define DBG(...) do {} while (0)
//#define DBG printf

void dump_heap_usage(void);

struct arena;

#define ALLOCATION_HEADER_MAGIC 0x11223344aa987654ul

struct allocation_header {
	VexAllocType *type;
	unsigned long magic;
	unsigned long _size;
	struct allocation_header *redirection;

	unsigned long size() const { return _size & ~1ul; }

	bool mark() const { return _size & 1; }
	void set_mark() { _size |= 1; }
	void clear_mark() { _size &= ~1ul; }

	unsigned char content[0];
};

struct arena {
	struct arena *next;
	unsigned long bytes_used;
	unsigned long size; /* Including header */
	unsigned char content[0];
};

/* Make the arena allocations be precisely 2MB. */
#define ARENA_CONTENT_SIZE ((2ul << 20) - sizeof(struct arena))

static struct allocation_header *raw_alloc(VexAllocType *t, unsigned long size);

#define NR_GC_ROOTS 128
static unsigned nr_gc_roots;
static void **gc_roots[NR_GC_ROOTS];
static const char *gc_root_names[NR_GC_ROOTS];
static struct arena *head_arena;
static struct arena *current_arena;
static VexAllocType *headType;
struct wr_core *headVisitedWeakRef;
static unsigned long heap_used;

static void *
header_to_alloc(struct allocation_header *ah)
{
	return ah->content;
}

static struct allocation_header *
alloc_to_header(const void *x)
{
	return (struct allocation_header *)x - 1;
}

static struct arena *
new_arena(size_t content_size)
{
	struct arena *r;

	content_size += sizeof(struct arena);
	content_size = (content_size + 4095) & ~4095;

	r = (struct arena *)mmap(NULL, content_size, PROT_READ|PROT_WRITE,
				 MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
	if (r == MAP_FAILED)
		err(1, "mmap() for %'zd bytes", content_size);
	r->size = content_size;
	r->next = head_arena;
	head_arena = r;

	heap_used += content_size;

	return r;
}

class GcVisitor : public HeapVisitor {
public:
	std::vector<struct allocation_header *> deferredVisit;
	unsigned depth;
	void visit(void *&ptr);
};

void
GcVisitor::visit(void *&what)
{
	struct allocation_header *what_header;

	if (!what)
		return;
	assert_gc_allocated(what);

	what_header = alloc_to_header(what);

	DBG("Visit %p\n", what);
	if (!what_header->redirection) {
		struct allocation_header *redir;
		redir = raw_alloc(what_header->type, what_header->size() - sizeof(struct allocation_header));
		what_header->redirection = redir;

		memcpy(redir->content, what_header->content, what_header->size() - sizeof(struct allocation_header));
		if (what_header->type->relocate)
			what_header->type->relocate(what, redir->content, what_header->size() - sizeof(*what_header));

		/* Do this even in NDEBUG mode: using something from
		   the old generation when you should be using the new
		   one is an easy bug to introduce (e.g. when writing
		   destructors), and tends to have pretty subtle
		   effects, so make it honkingly obvious. */
		memset(what, 0x93, what_header->size() - sizeof(*what_header));

		DBG("Redirect %p:%p to %p\n", what, (void *)((unsigned long)what + what_header->size()), header_to_alloc(redir));
		what = header_to_alloc(redir);
		assert(what != NULL);
		if (redir->type->gc_visit) {
			if (depth >= MAX_RECURSION_DEPTH) {
				deferredVisit.push_back(redir);
			} else {
				depth++;
				redir->type->gc_visit(what, *this);
				depth--;
			}
		}

		DBG("Done visit of %p\n", what);
	} else {
		assert(!((unsigned long)what_header->redirection & 0x8000000000000000ul));
		assert((unsigned long)header_to_alloc(what_header->redirection) != 0x93939393939393ab);
		assert(what_header->redirection->type == what_header->type);
		what = header_to_alloc(what_header->redirection);
		assert(what != NULL);
		assert_gc_allocated(what);
		DBG("Already visited; redirect to %p\n", what);
		assert((unsigned long)what != 0x93939393939393ab);
	}
}

void
LibVEX_free(const void *_ptr)
{
	assert_gc_allocated(_ptr);

	struct allocation_header *ah = alloc_to_header(_ptr);

	/* We support one special case, which is just rewinding the
	   allocation pointer if you allocate something and then
	   immediately free it. */
	if (current_arena &&
	    (unsigned long)ah + ah->size() == (unsigned long)current_arena->content + current_arena->bytes_used) {
		assert(current_arena->bytes_used >= ah->size());
		current_arena->bytes_used -= ah->size();
		/* memset to zero, for the benefit of whoever uses
		   this bit of memory after us. */
		memset(ah, 0, ah->size());
	}		
}

void
LibVEX_gc(GarbageCollectionToken t)
{
	struct arena *old_arena;
	struct arena *next_old;
	GcVisitor gc;

	LibVEX_alloc_sanity_check();

	printf("Major GC starts\n");

	gc.depth = 0;

	/* Zap the old redirection pointers */
	for (struct arena *a = head_arena; a; a = a->next) {
		unsigned offset;
		struct allocation_header *ah;
		for (offset = 0; offset < a->bytes_used; offset += ah->size()) {
			ah = (struct allocation_header *)(a->content + offset);
			ah->redirection = NULL;
		}
	}

	/* Swizzle out the old arena */
	old_arena = head_arena;
	head_arena = NULL;
	current_arena = NULL;
	heap_used = 0;

	/* Any allocations made from this point onwards will
	   automatically go to the new generation. */

	assert(headVisitedWeakRef == NULL);

	/* Do the copy phase */
	for (unsigned x = 0; x < nr_gc_roots; x++)
		gc.visit(*gc_roots[x]);
	while (!gc.deferredVisit.empty()) {
		struct allocation_header *ah;
		ah = gc.deferredVisit.back();
		gc.deferredVisit.pop_back();
		assert(ah->type);
		assert(ah->type->gc_visit);
		ah->type->gc_visit(header_to_alloc(ah), gc);
	}

	/* Hack: the expression internment table still points at the
	   old generation.  Fix it up. */
	fixup_expression_table();

	LibVEX_alloc_sanity_check();

	/* Handle weak references.  They're strung together in the
	   global list automatically during the visit pass. */
	for (struct wr_core *weak = headVisitedWeakRef;
	     weak != NULL;
	     weak = weak->next) {
		assert(weak->content);
		struct allocation_header *ah =
			alloc_to_header(weak->content);
		assert(ah);
		/* If the target was visited during the copy phase,
		   it'll have a redirection.  Otherwise, it's garbage.
		   Update the content of the reference
		   appropriately. */
		if (ah->redirection)
			weak->content = header_to_alloc(ah->redirection);
		else
			weak->content = NULL;
	}
	headVisitedWeakRef = NULL;

	/* Run destructors and release memory */
	while (old_arena) {
		unsigned offset;
		struct allocation_header *ah;

		for (offset = 0; offset < old_arena->bytes_used; offset += ah->size()) {
			ah = (struct allocation_header *)(&old_arena->content[offset]);
			if (ah->redirection) {
				/* This one is still alive, so don't
				   run its destructor.  The underlying
				   memory will be released, though,
				   because it's in the old
				   generation. */
				continue;
			}
			assert(ah->type);
			DBG("Release %p\n", header_to_alloc(ah));
			if (ah->type->destruct)
				ah->type->destruct(header_to_alloc(ah));
		}
		next_old = old_arena->next;
		DBG("Release %p:%p\n", old_arena, (void *)((unsigned long)old_arena + old_arena->size));
		munmap(old_arena, old_arena->size);
		old_arena = next_old;
	}
	LibVEX_alloc_sanity_check();

	printf("Major GC finished; %ld bytes in heap\n", heap_used);

	if (heap_used >= GC_MAX_SIZE) {
		/* We're pretty much boned at this point: every
		   vexSetAllocModeTEMP_and_clear will trigger a full
		   GC, and performance will go through the floor. */
		extern void dbg_break(const char *msg, ...);
		dbg_break("Heap is enormous (%ld bytes) after a full garbage collect!\n",
			  heap_used);
	}
}

void vexSetAllocModeTEMP_and_clear(GarbageCollectionToken t)
{
	static unsigned counter;
	if (counter++ % GC_PERIOD == 0 ||
	    heap_used >= GC_MAX_SIZE)
		LibVEX_gc(t);
}

static struct allocation_header *
raw_alloc(VexAllocType *t, unsigned long size)
{
	struct arena *a;

	LibVEX_alloc_sanity_check();

	size += sizeof(struct allocation_header);
	size = (size + 31) & ~31;
	if (size > ARENA_CONTENT_SIZE) {
		/* Allocate a dedicated arena for this very large
		 * allocation. */
		a = new_arena(size);
	} else {
		a = current_arena;
		if (!a || a->bytes_used + size > ARENA_CONTENT_SIZE) {
			a = new_arena(ARENA_CONTENT_SIZE);
			current_arena = a;
		}
	}

	struct allocation_header *res;
	res = (struct allocation_header *)(a->content + a->bytes_used);
	a->bytes_used += size;
	res->_size = size;
	res->type = t;

	/* We set the newly-allocated block to redirect to itself, so
	   that if we somehow ``discover'' an object in the new
	   generation during the visit pass we don't allocate another
	   object and redirect the redirection to that.  That
	   (discovery of new generation) shouldn't normally happen,
	   but can sometimes if e.g. you register a root twice, or
	   just visit a single pointer twice in a single visit()
	   method.  It's easy to handle, and the bugs you get if you
	   don't handle it are annoyingly subtle, so just do it. */
	res->redirection = res;

	res->magic = ALLOCATION_HEADER_MAGIC;

	LibVEX_alloc_sanity_check();

	return res;
}

static void *
alloc_bytes(VexAllocType *type, unsigned long size)
{
	struct allocation_header *ah = raw_alloc(type, size);
	return header_to_alloc(ah);
}

static VexAllocType byte_alloc_type = { -1, NULL, NULL, NULL, "<bytes>" };
void *
__LibVEX_Alloc_Bytes(unsigned long nbytes, struct libvex_allocation_site *site)
{
	return alloc_bytes(&byte_alloc_type, nbytes);
}

void *
LibVEX_Alloc_Sized(VexAllocType *t, unsigned long nbytes)
{
	return alloc_bytes(t, nbytes);
}

struct libvex_alloc_type *
__LibVEX_Alloc(VexAllocType *t)
{
	return (struct libvex_alloc_type *)alloc_bytes(t, t->nbytes);
}

void *
LibVEX_realloc(void *ptr, unsigned long new_size)
{
	assert_gc_allocated(ptr);
	struct allocation_header *ah = alloc_to_header(ptr);
	void *newptr;

	if (new_size <= ah->size() - sizeof(*ah))
		return ptr;

	/* The *2 is because if you've had to grow it once you're
	   likely to have to do so again, and we want to grow the
	   actual allocation as few times as possible. */
	newptr = alloc_bytes(ah->type, new_size * 2);
	memcpy(newptr, ptr, ah->size() - sizeof(*ah));
	return newptr;
}

void
vexRegisterGCRoot(void **w, const char *name)
{
	vassert(nr_gc_roots < NR_GC_ROOTS);
	gc_roots[nr_gc_roots] = w;
	gc_root_names[nr_gc_roots] = name;
	nr_gc_roots++;
}

void
vexUnregisterGCRoot(void **w)
{
	unsigned x;
	if (*w)
		assert_gc_allocated(*w);
	for (x = 0; x < nr_gc_roots; x++) {
		if (gc_roots[x] == w) {
			memmove(gc_roots + x, gc_roots + x + 1, (nr_gc_roots - x - 1) * sizeof(gc_roots[0]));
			memmove(gc_root_names, gc_root_names + x + 1, (nr_gc_roots - x - 1) * sizeof(gc_root_names[0]));
			nr_gc_roots--;
			return;
		}
	}
	vpanic("Unregistering a GC root which was never registered.");
}

class HeapUsageVisitor : public HeapVisitor {
public:
	unsigned long heap_used;
	unsigned nr_allocations;
	void visit(void *&ptr);
	void account_one_allocation(allocation_header *hdr);
};

void
HeapUsageVisitor::account_one_allocation(allocation_header *hdr)
{
	VexAllocType *t = hdr->type;
	if (!t->total_allocated) {
		t->next = headType;
		if (!t->name)
			t->name = t->get_name(hdr + 1);
		headType = t;
	}
	t->total_allocated += hdr->size();
	t->nr_allocated++;
	this->heap_used += hdr->size();
	this->nr_allocations++;
}

void HeapUsageVisitor::visit(void *&ptr)
{
	if (!ptr)
		return;
	allocation_header *hdr = alloc_to_header(ptr);
	VexAllocType *t = hdr->type;
	
	if (hdr->mark())
		return;
	account_one_allocation(hdr);
	hdr->set_mark();
	if (t->gc_visit)
		t->gc_visit(ptr, *this);
}

void
dump_heap_usage(void)
{
	VexAllocType *cursor;
	for (cursor = headType; cursor; cursor = cursor->next) {
		cursor->total_allocated = 0;
		cursor->nr_allocated = 0;
	}
	headType = NULL;

	for (struct arena *a = head_arena; a; a = a->next) {
		unsigned offset;
		struct allocation_header *ah;
		for (offset = 0; offset < a->bytes_used; offset += ah->size()) {
			ah = (struct allocation_header *)(a->content + offset);
			ah->clear_mark();
		}
	}

	HeapUsageVisitor visitor;
	visitor.heap_used = 0;
	visitor.nr_allocations = 0;

	for (unsigned x = 0; x < nr_gc_roots; x++)
		visitor.visit(*gc_roots[x]);

	printf("Live:\n");
	for (cursor = headType; cursor; cursor = cursor->next)
		printf("%8ld\t%8d\t%s\n", cursor->total_allocated, cursor->nr_allocated, cursor->name);
	printf("%8ld\t%8d\ttotal\n", visitor.heap_used, visitor.nr_allocations);
	visitor.heap_used = 0;
	visitor.nr_allocations = 0;

	for (cursor = headType; cursor; cursor = cursor->next) {
		cursor->total_allocated = 0;
		cursor->nr_allocated = 0;
	}
	headType = NULL;
	
	for (struct arena *a = head_arena; a; a = a->next) {
		unsigned offset;
		struct allocation_header *ah;
		for (offset = 0; offset < a->bytes_used; offset += ah->size()) {
			ah = (struct allocation_header *)(a->content + offset);
			if (!ah->mark())
				visitor.account_one_allocation(ah);
		}
	}

	printf("\nDragging:\n");
	for (cursor = headType; cursor; cursor = cursor->next)
		printf("%8ld\t%8d\t%s\n", cursor->total_allocated, cursor->nr_allocated, cursor->name);
	printf("%8ld\t%8d\ttotal\n", visitor.heap_used, visitor.nr_allocations);

	for (struct arena *a = head_arena; a; a = a->next) {
		unsigned offset;
		struct allocation_header *ah;
		for (offset = 0; offset < a->bytes_used; offset += ah->size()) {
			ah = (struct allocation_header *)(a->content + offset);
			ah->clear_mark();
		}
	}

	headVisitedWeakRef = NULL;
}

void
vexInitHeap(void)
{
}


static void
visit_ptr_array(void *ths, HeapVisitor &visitor)
{
	struct allocation_header *ah = alloc_to_header(ths);
	void **payload = (void **)ths;
	unsigned x;
	for (x = 0; x < (ah->size() - sizeof(*ah)) / sizeof(void *); x++)
		visitor(payload[x]);
}
static VexAllocType ptr_array_type = { -1, NULL, visit_ptr_array, NULL, "<array>" };
struct libvex_alloc_type *
__LibVEX_Alloc_Ptr_Array(unsigned long len)
{
	struct allocation_header *ah;
	void **res;
	unsigned x;

	res = (void **)alloc_bytes(&ptr_array_type, sizeof(void *) * len);
	ah = alloc_to_header(res);
	for (x = 0; x < (ah->size() - sizeof(*ah)) / sizeof(void *); x++)
		res[x] = NULL;
	return (struct libvex_alloc_type *)res;
}


void __visit_vector(void *_ctxt, HeapVisitor &hv)
{
	LibvexVector<void *> *ctxt = (LibvexVector<void *>*)_ctxt;
	unsigned x;
	for (x = 0; x < ctxt->sz; x++)
		hv(ctxt->items[x]);
}
VexAllocType LibvexVectorType = {
nbytes: sizeof(LibvexVector<void *>),
relocate: NULL,
gc_visit: __visit_vector,
destruct: NULL,
name: "LibvexVector"
};


static void
sanity_check_arena(struct arena *a)
{
	unsigned offset;
	struct allocation_header *ah;

	assert(a->size >= ARENA_CONTENT_SIZE + sizeof(struct arena));
	assert(a->bytes_used <= a->size);
	for (offset = 0; offset < a->bytes_used; offset += ah->size()) {
		ah = (struct allocation_header *)(&a->content[offset]);
		assert(ah->magic == ALLOCATION_HEADER_MAGIC);
		assert(ah->type != NULL);
		assert(ah->size() <= a->size - offset);
		assert(!ah->mark());
		assert(ah->redirection == ah || ah->redirection == NULL);
	}
}

void
_LibVEX_alloc_sanity_check()
{
	struct arena *fast, *slow;
	bool found_current;

	slow = fast = head_arena;
	found_current = false;
	while (1) {
		if (fast == current_arena)
			found_current = true;
		if (!fast)
			break;
		sanity_check_arena(fast);
		fast = fast->next;
		if (fast == current_arena)
			found_current = true;
		if (!fast)
			break;
		sanity_check_arena(fast);
		fast = fast->next;
		slow = slow->next;
		assert(fast != slow);
	}
	assert(found_current);
}

void
LibVEX_alloc_sanity_check()
{
#ifndef NDEBUG
	static int counter;

	if (counter++ % 10000000 != 0)
		return;

	_LibVEX_alloc_sanity_check();
#endif
}

void
assert_gc_allocated(const void *ptr)
{
#ifndef NDEBUG
	struct allocation_header *ah = alloc_to_header(ptr);
	assert(ah->magic == ALLOCATION_HEADER_MAGIC);
#endif
}
