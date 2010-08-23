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
#define NDEBUG
#include <valgrind/memcheck.h>
#include <sys/mman.h>
#include <stdio.h>
#include <string.h>

#include "libvex_basictypes.h"
#include "libvex.h"
#include "libvex_alloc.h"

#include "main_globals.h"
#include "main_util.h"

void dump_heap_usage(void);

#undef VALGRIND_MAKE_MEM_NOACCESS
#undef VALGRIND_MAKE_MEM_UNDEFINED
#undef VALGRIND_CHECK_MEM_IS_DEFINED
#define VALGRIND_MAKE_MEM_NOACCESS(x, y)
#define VALGRIND_MAKE_MEM_UNDEFINED(x, y)
#define VALGRIND_CHECK_MEM_IS_DEFINED(x, y)

/* The main arena. */
#define N_TEMPORARY_BYTES (2ul<<30)
static char *temporary;
static unsigned long heap_used;

static VexAllocType *headType;

/* Each allocation in the arena is prefixed by an allocation header. */
struct alloc_header {
  VexAllocType *type; /* Or NULL for free blocks */
  unsigned long size; /* Includes header */
  unsigned long flags;
#define ALLOC_FLAG_GC_MARK 1
#define ALLOC_FLAG_HAS_WEAK_TABLE 2
#define ALLOC_FLAG_WEAK_TABLE_MASK (~(3ul))
  struct libvex_allocation_site *site;
};

struct weak_table {
  unsigned nr_refs;
  void **inlineRef;
  void ***outlineRefs;
  void registerRef(void **);
  void unregisterRef(void **);
  void ownerDied();
};

static alloc_header *alloc_header_terminator;

static void visit_ptr_array(const void *ths, HeapVisitor &visitor);
static VexAllocType byte_alloc_type = { -1, 0, 0, "<bytes>" };
static VexAllocType ptr_array_type = { -1, visit_ptr_array, NULL, "<array>" };
static VexAllocType weak_table_type = { -1, 0, 0, "<weaktable>" };

#define NR_GC_ROOTS 128
static unsigned nr_gc_roots;
static void **gc_roots[NR_GC_ROOTS];
static const char *gc_root_names[NR_GC_ROOTS];

/* A pointer to an allocation somewhere in the heap which is likely to
   be a reasonable place to start looking when performing
   allocations. */
static struct alloc_header *allocation_cursor;

static void *alloc_bytes(VexAllocType *type, unsigned long size);

static void *
header_to_alloc(struct alloc_header *ah)
{
  return ah + 1;
}

static struct alloc_header *
alloc_to_header(const void *x)
{
  return (struct alloc_header *)x - 1;
}

static struct alloc_header *
first_alloc_header(void)
{
  return (struct alloc_header *)temporary;
}

static struct alloc_header *
next_alloc_header(struct alloc_header *h)
{
  assert(h->size != 0);
  return (struct alloc_header *)((unsigned long)h + h->size);
}

static weak_table *
header_to_weak_table(alloc_header *h)
{
  weak_table *w;
  if (!(h->flags & ALLOC_FLAG_HAS_WEAK_TABLE)) {
    w = (weak_table *)alloc_bytes(&weak_table_type, sizeof(weak_table));
    w->nr_refs = 0;
    w->outlineRefs = NULL;
    unsigned long off = (unsigned long)w - (unsigned long)temporary;
    assert(!(off & ~ALLOC_FLAG_WEAK_TABLE_MASK));
    h->flags &= ~ALLOC_FLAG_WEAK_TABLE_MASK;
    h->flags |= off | ALLOC_FLAG_HAS_WEAK_TABLE;
  }
  return (weak_table *)((unsigned long)temporary +
			(h->flags & ALLOC_FLAG_WEAK_TABLE_MASK));
}

class GcVisitor : public HeapVisitor {
public:
  void visitWeakTable(weak_table *w);
  void visit(const void *ptr);
};

void
GcVisitor::visit(const void *what)
{
  struct alloc_header *what_header;

  if (!what)
    return;
  what_header = alloc_to_header(what);
  vassert(what_header->type != NULL); /* Shouldn't be visiting free memory... */
  if (what_header->flags & ALLOC_FLAG_GC_MARK)
    return;
  if (what_header->flags & ALLOC_FLAG_HAS_WEAK_TABLE)
    visitWeakTable(header_to_weak_table(what_header));
  what_header->flags |= ALLOC_FLAG_GC_MARK;
  if (what_header->type->gc_visit)
    what_header->type->gc_visit(what, *this);
}

void
GcVisitor::visitWeakTable(weak_table *w)
{
  visit(w);
  if (w->outlineRefs) {
    /* Visit the table itself, but not the things referenced from
       it. */
    visit(w->outlineRefs);
  }
}

static void
poison(void *start, unsigned long nr_bytes, unsigned pattern)
{
#ifndef NDEBUG
  unsigned long x;
  for (x = 0; x < nr_bytes / 4; x++)
    ((unsigned *)start)[x] = pattern;
#endif
}

static void
release_weak_table(alloc_header *h)
{
  weak_table *w = header_to_weak_table(h);
  w->ownerDied();
  if (w->outlineRefs)
    LibVEX_free(w->outlineRefs);
  LibVEX_free(w);
  h->flags &= ~ALLOC_FLAG_HAS_WEAK_TABLE;
}

void
LibVEX_free(const void *_ptr)
{
  void *ptr = (void *)_ptr;
  struct alloc_header *h = alloc_to_header(ptr);
  struct alloc_header *n;

  LibVEX_alloc_sanity_check();
  heap_used -= h->size;

  if (h->flags & ALLOC_FLAG_HAS_WEAK_TABLE)
    release_weak_table(h);
  if (h->type->destruct)
    h->type->destruct(ptr);
  if (h->site)
    h->site->nr_bytes -= h->size;

  poison(h + 1, h->size - sizeof(*h), 0xa9b8c7d6);
  h->type = NULL;
  VALGRIND_MAKE_MEM_NOACCESS(h + 1, h->size - sizeof(*h));

  n = next_alloc_header(h);
  while (n != alloc_header_terminator &&
	 !n->type) {
    if (allocation_cursor == n)
      allocation_cursor = h;
    h->size += n->size;
    poison(n, sizeof(*n), 0xa9b8c7d6);
    VALGRIND_MAKE_MEM_NOACCESS(n, sizeof(*n));
    n = next_alloc_header(h);
  }
  LibVEX_alloc_sanity_check();
}

void
LibVEX_gc(void)
{
  unsigned x;
  struct alloc_header *h;
  struct alloc_header *p;
  struct alloc_header *n;
  GcVisitor gc;

  LibVEX_alloc_sanity_check();

  for (h = first_alloc_header(); h != alloc_header_terminator; h = next_alloc_header(h))
    h->flags &= ~ ALLOC_FLAG_GC_MARK;
  for (x = 0; x < nr_gc_roots; x++)
    gc.visit(*gc_roots[x]);

  heap_used = 0;
  h = first_alloc_header();
  p = NULL;
  while (h != alloc_header_terminator) {
    n = next_alloc_header(h);
    if (h->type) {
      if (h->flags & ALLOC_FLAG_GC_MARK) {
	heap_used += h->size;
      } else if (h->type != &weak_table_type) {
	/* We're going to free off this block.  Weak table allocations
	   are released when their owner goes away, and not before. */

	if (h->flags & ALLOC_FLAG_HAS_WEAK_TABLE)
	  release_weak_table(h);
	if (h->type->destruct)
	  h->type->destruct(header_to_alloc(h));
	if (h->site)
	  h->site->nr_bytes -= h->size;
	poison(h + 1, h->size - sizeof(*h), 0xa1b2c3d4);
	h->type = NULL;
	VALGRIND_MAKE_MEM_NOACCESS(h + 1, h->size - sizeof(*h));
	if (p && !p->type) {
	  if (h == allocation_cursor)
	    allocation_cursor = p;
	  p->size += h->size;
	  VALGRIND_MAKE_MEM_NOACCESS(h, sizeof(*h));
	  if (n != alloc_header_terminator && !n->type) {
	    p->size += n->size;
	    VALGRIND_MAKE_MEM_NOACCESS(n, sizeof(*n));
	    if (n == allocation_cursor)
	      allocation_cursor = p;
	  }
	  n = next_alloc_header(p);
	  h = p;
	} else if (n != alloc_header_terminator && !n->type) {
	  if (n == allocation_cursor)
	    allocation_cursor = h;
	  h->size += n->size;
	  VALGRIND_MAKE_MEM_NOACCESS(n, sizeof(*n));
	  n = next_alloc_header(h);
	}
      }
    } else {
      while (n != alloc_header_terminator && !n->type) {
	h->size += n->size;
	VALGRIND_MAKE_MEM_NOACCESS(n, sizeof(*n));
	n = next_alloc_header(h);
      }
    }

    p = h;
    h = n;
  }

  LibVEX_alloc_sanity_check();
}

void vexSetAllocModeTEMP_and_clear ( void )
{
  if (heap_used > N_TEMPORARY_BYTES / 2)
    LibVEX_gc();
}


static void
visit_ptr_array(const void *ths, HeapVisitor &visitor)
{
  struct alloc_header *ah = alloc_to_header(ths);
  void **payload = (void **)(ah + 1);
  unsigned x;
  for (x = 0; x < (ah->size - sizeof(*ah)) / sizeof(void *); x++)
    visitor.visit(payload[x]);
}

static void *
alloc_bytes(VexAllocType *type, unsigned long size)
{
  struct alloc_header *cursor;
  struct alloc_header *next;
  unsigned long old_size;
  void *res;

  size += sizeof(struct alloc_header);
  size = (size + 15) & ~15;

  /* First-fit policy.  Search starts from the allocation cursor, and
     then if that fails we try again from the beginning. */
  for (cursor = allocation_cursor;
       cursor != alloc_header_terminator;
       cursor = next) {
    assert(cursor >= first_alloc_header());
    assert(cursor < alloc_header_terminator);
    next = next_alloc_header(cursor);
    assert(next <= alloc_header_terminator);
    if (!cursor->type) {
      while (next != alloc_header_terminator && !next->type && cursor->size < size) {
	assert(next < alloc_header_terminator);
	assert(next >= first_alloc_header());
	assert(next->size != 0);
	cursor->size += next->size;
	poison(next, sizeof(*next), 0xa1b2c3d4);
	VALGRIND_MAKE_MEM_NOACCESS(next, sizeof(*next));
	next = next_alloc_header(cursor);
      }
      if (cursor->size >= size)
	break;
    }
  }
  if (cursor == alloc_header_terminator) {
    for (cursor = first_alloc_header();
	 cursor != allocation_cursor;
	 cursor = next_alloc_header(cursor)) {
      assert(cursor >= first_alloc_header());
      assert(cursor < alloc_header_terminator);
      next = next_alloc_header(cursor);
      assert(next <= alloc_header_terminator);
      if (!cursor->type) {
	while (next != alloc_header_terminator && !next->type && cursor->size < size) {
	  assert(next < alloc_header_terminator);
	  assert(next >= first_alloc_header());
	  assert(next->size != 0);
	  cursor->size += next->size;
	  poison(next, sizeof(*next), 0xa1b2c3d4);
	  VALGRIND_MAKE_MEM_NOACCESS(next, sizeof(*next));
	  if (next == allocation_cursor)
	    allocation_cursor = next_alloc_header(cursor);
	  next = next_alloc_header(cursor);
	}
	if (cursor->size >= size)
	  break;
      }
    }
    if (cursor == allocation_cursor) {
      dump_heap_usage();
      vpanic("VEX temporary storage exhausted.\n"
	     "Increase N_TEMPORARY_BYTES and recompile.");
    }
  }

  /* Consider splitting the block */
  if (cursor->size >= size + 32ul) {
    /* Do split. */
    old_size = cursor->size;
    cursor->size = size;
    vassert(cursor->size != 0);
    next = next_alloc_header(cursor);
    VALGRIND_MAKE_MEM_UNDEFINED(next, sizeof(*next));
    vassert(next != alloc_header_terminator);
    next->type = NULL;
    next->size = old_size - size;
    vassert(next->size != 0);
    next->flags = 0;
    next->site = NULL;
  }

  cursor->type = type;
  res = header_to_alloc(cursor);
  VALGRIND_MAKE_MEM_UNDEFINED(res, cursor->size - sizeof(*cursor));
  poison(res, size - sizeof(struct alloc_header), 0xaabbccdd);
  VALGRIND_MAKE_MEM_UNDEFINED(res, cursor->size - sizeof(*cursor));

  heap_used += cursor->size;

  allocation_cursor = next_alloc_header(cursor);

  return res;
}

/* Exported to library client. */
void *
__LibVEX_Alloc_Bytes(unsigned long nbytes, struct libvex_allocation_site *site)
{
  void *res = alloc_bytes(&byte_alloc_type, nbytes);
  struct alloc_header *ah = alloc_to_header(res);
  ah->site = site;
  site->nr_bytes += ah->size;
  return res;
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
  struct alloc_header *ah = alloc_to_header(ptr);
  struct alloc_header *next;
  unsigned long old_size;
  void *newptr;

  LibVEX_alloc_sanity_check();
  new_size += sizeof(struct alloc_header);
  new_size = (new_size + 15) & ~15;

  VALGRIND_CHECK_MEM_IS_DEFINED(ah, sizeof(*ah));

  /* Can only resize byte allocations */
  vassert(ah->type == &byte_alloc_type || ah->type == &weak_table_type);

  if (ah->site)
    ah->site->nr_bytes -= ah->size;

  /* Enlarge if possible */
  while (new_size > ah->size) {
    next = next_alloc_header(ah);
    if (next == alloc_header_terminator || next->type)
      break;
    if (next == allocation_cursor)
      allocation_cursor = ah;
    ah->size += next->size;
    heap_used += next->size;
    poison(next, next->size, 0xaabbccdd);
    VALGRIND_MAKE_MEM_UNDEFINED((void *)((unsigned long)(ah + 1) + ah->size - sizeof(*ah) - next->size),
				next->size);
    next = next_alloc_header(ah);
  }

  /* Trim it down again */
  if (new_size < ah->size - 32) {
    old_size = ah->size;
    ah->size = new_size;
    next = next_alloc_header(ah);
    VALGRIND_MAKE_MEM_UNDEFINED(next, sizeof(*next));
    next->type = NULL;
    next->size = old_size - new_size;
    next->flags = 0;
    next->site = NULL;
    heap_used -= old_size - new_size;
    poison(next + 1, next->size - sizeof(*next), 0xa1b2c3d4);
    VALGRIND_MAKE_MEM_NOACCESS(next + 1, next->size - sizeof(*next));
  }

  /* Good enough? */
  if (new_size <= ah->size) {
    LibVEX_alloc_sanity_check();
    if (ah->site)
      ah->site->nr_bytes += ah->size;
    return ptr;
  }

  /* Failed to resize: allocate a new block.  This is expensive, and
     tends to cause heap fragmentation, so if we have to do it then we
     double the requested allocation so as to make future realloc()s
     cheaper. */
  newptr = alloc_bytes(ah->type, new_size * 2);
  if (new_size < ah->size)
    memcpy(newptr, ptr, new_size);
  else
    memcpy(newptr, ptr, ah->size);
  LibVEX_free(ptr);

  LibVEX_alloc_sanity_check();

  ah = alloc_to_header(newptr);
  if (ah->site)
    ah->site->nr_bytes += ah->size;

  return newptr;
}

struct libvex_alloc_type *
__LibVEX_Alloc_Ptr_Array(unsigned long len)
{
  struct alloc_header *ah;
  void **res;
  unsigned x;

  res = (void **)alloc_bytes(&ptr_array_type, sizeof(void *) * len);
  ah = alloc_to_header(res);
  for (x = 0; x < (ah->size - sizeof(*ah)) / sizeof(void *); x++)
    res[x] = NULL;
  return (struct libvex_alloc_type *)res;
}

void vexAllocSanityCheck ( void )
{
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

class DumpHeapVisitor : public HeapVisitor {
public:
  unsigned depth;
  virtual void visit(const void *ptr);
  DumpHeapVisitor() : depth(0) {};
  ~DumpHeapVisitor() { vassert(depth == 0); }
};

void
DumpHeapVisitor::visit(const void *what)
{
    if (!what)
      return;
    struct alloc_header *ah = alloc_to_header(what);
    if (!ah->type || (ah->flags & ALLOC_FLAG_GC_MARK))
      return;
    ah->flags |= ALLOC_FLAG_GC_MARK;
    vex_printf("%d %p %s\n", depth, what, ah->type->name ?: ah->type->get_name(what));
    depth++;
    if (ah->type && ah->type->gc_visit)
      ah->type->gc_visit(what, *this);
    depth--;
}

void
dump_heap(void)
{
  unsigned x;
  struct alloc_header *h;
  DumpHeapVisitor visitor;

  for (h = first_alloc_header(); h != alloc_header_terminator; h = next_alloc_header(h))
    h->flags &= ~ ALLOC_FLAG_GC_MARK;
  for (x = 0; x < nr_gc_roots; x++) {
    vex_printf("Root %d:\n", x);
    visitor.visit(*gc_roots[x]);
  }

  for (h = first_alloc_header(); h != alloc_header_terminator; h = next_alloc_header(h)) {
    if (!h->type || (h->flags & ALLOC_FLAG_GC_MARK))
      continue;
    vex_printf("Unattached but allocated:\n");
    visitor.visit(h + 1);
  }
}

class HeapUsageVisitor : public HeapVisitor {
public:
  unsigned long heap_used;
  unsigned nr_allocations;
  void visit(const void *ptr);
  void account_one_allocation(alloc_header *hdr);
};

void
HeapUsageVisitor::account_one_allocation(alloc_header *hdr)
{
  VexAllocType *t = hdr->type;
  if (!t->total_allocated) {
    t->next = headType;
    if (!t->name)
      t->name = t->get_name(hdr + 1);
    headType = t;
  }
  t->total_allocated += hdr->size;
  t->nr_allocated++;
  this->heap_used += hdr->size;
  this->nr_allocations++;
}

void HeapUsageVisitor::visit(const void *ptr)
{
  if (!ptr)
    return;
  alloc_header *hdr = alloc_to_header(ptr);
  VexAllocType *t = hdr->type;
  
  if (!hdr->type || (hdr->flags & ALLOC_FLAG_GC_MARK))
    return;
  account_one_allocation(hdr);
  hdr->flags |= ALLOC_FLAG_GC_MARK;
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

  HeapUsageVisitor visitor;
  visitor.heap_used = 0;
  visitor.nr_allocations = 0;
  alloc_header *h;
  for (h = first_alloc_header(); h != alloc_header_terminator; h = next_alloc_header(h))
    h->flags &= ~ ALLOC_FLAG_GC_MARK;
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
  for (h = first_alloc_header(); h != alloc_header_terminator; h = next_alloc_header(h)) {
    if (!h->type || (h->flags & ALLOC_FLAG_GC_MARK))
      continue;
    visitor.account_one_allocation(h);
  }

  printf("\nDragging:\n");
  for (cursor = headType; cursor; cursor = cursor->next)
    printf("%8ld\t%8d\t%s\n", cursor->total_allocated, cursor->nr_allocated, cursor->name);
  printf("%8ld\t%8d\ttotal\n", visitor.heap_used, visitor.nr_allocations);

  printf("\nByte allocation sites:\n");
  for (h = first_alloc_header(); h != alloc_header_terminator; h = next_alloc_header(h)) {
    if (!h->site || h->site->flags)
      continue;
    printf("%8ld\t\t%s:%d\n", h->site->nr_bytes, h->site->file, h->site->line);
    h->site->flags = 1;
  }
  for (h = first_alloc_header(); h != alloc_header_terminator; h = next_alloc_header(h)) {
    if (!h->site)
      continue;
    h->site->flags = 0;
  }
}

void
dump_heap_pattern(void)
{
  FILE *f = fopen("heap_pattern.dat", "w");
  for (alloc_header *h = first_alloc_header(); h != alloc_header_terminator; h = next_alloc_header(h)) {
    if (h->type && !h->type->name)
      h->type->name = h->type->get_name(h + 1);
    fprintf(f, "%p %80s %ld\n", h, h->type ? h->type->name : "<free>", h->size);
  }
  fclose(f);
}

void
LibVEX_ShowAllocStats(void)
{
  printf("<no allocation stats collected>\n");
}

void
vexSetAllocMode(VexAllocMode)
{
}


void
vexInitHeap(void)
{
  static bool done_init;
  struct alloc_header *entire_arena_hdr;

  vassert(!done_init);
  temporary = (char *)mmap(NULL, N_TEMPORARY_BYTES, PROT_READ|PROT_WRITE,
			   MAP_PRIVATE|MAP_ANONYMOUS, -1, 0);
  alloc_header_terminator = (alloc_header *)(temporary + N_TEMPORARY_BYTES);
  poison(temporary, N_TEMPORARY_BYTES, 0xa1b2c3d4);
  entire_arena_hdr = first_alloc_header();
  entire_arena_hdr->type = NULL;
  entire_arena_hdr->size = N_TEMPORARY_BYTES;
  entire_arena_hdr->flags = 0;
  entire_arena_hdr->site = NULL;
  allocation_cursor = entire_arena_hdr;
  done_init = true;
}


void __visit_vector(const void *_ctxt, HeapVisitor &hv)
{
  LibvexVector<void *> *ctxt = (LibvexVector<void *>*)_ctxt;
  unsigned x;
  for (x = 0; x < ctxt->sz; x++)
    hv(ctxt->items[x]);
}

VexAllocType LibvexVectorType = {
 nbytes: sizeof(LibvexVector<void *>),
 gc_visit: __visit_vector,
 destruct: NULL,
 name: "LibvexVector"
};


void registerWeakRef(const void *object, void **ref)
{
  alloc_header *ah = alloc_to_header(object);
  weak_table *w = header_to_weak_table(ah);
  w->registerRef(ref);
}

void unregisterWeakRef(const void *object, void **ref)
{
  alloc_header *ah = alloc_to_header(object);
  weak_table *w = header_to_weak_table(ah);
  w->unregisterRef(ref);
}

void
weak_table::registerRef(void **ref)
{
  if (nr_refs == 0) {
    inlineRef = ref;
  } else {
    if (outlineRefs)
      outlineRefs = (void ***)LibVEX_realloc(outlineRefs, sizeof(void **) * nr_refs);
    else
      outlineRefs = (void ***)alloc_bytes(&weak_table_type, sizeof(void **) * nr_refs);
    outlineRefs[nr_refs - 1] = ref;
  }
  nr_refs++;
}

void
weak_table::unregisterRef(void **ref)
{
  nr_refs--;
  if (!nr_refs)
    return;
  if (inlineRef == ref) {
    inlineRef = outlineRefs[0];
    memmove(outlineRefs, outlineRefs + 1, (nr_refs - 1) * sizeof(void **));
  } else {
    unsigned x;
    for (x = 0; x < nr_refs; x++) {
      if (outlineRefs[x] == ref) {
	memmove(outlineRefs + x, outlineRefs + x + 1, (nr_refs - x - 1) * sizeof(void **));
	break;
      }
    }
    assert(x != nr_refs);
  }
}

void
weak_table::ownerDied()
{
  if (nr_refs == 0)
    return;
  *inlineRef = NULL;
  if (outlineRefs) {
    for (unsigned x = 1; x < nr_refs; x++)
      *(outlineRefs[x-1]) = NULL;
    LibVEX_free(outlineRefs);
    outlineRefs = NULL;
  }
  nr_refs = 0;
}

/* Occasionally useful for dealing with heap corruption bugs, but too
   expensive to be on by default, even in debug builds. */
#if 0
static void
sanity_check_alloc_header(const alloc_header *h)
{
  assert(h >= first_alloc_header());
  assert(h < alloc_header_terminator);
  assert(h->size >= sizeof(*h));
  if (!(h->flags & ALLOC_FLAG_HAS_WEAK_TABLE))
    assert(!(h->flags & ALLOC_FLAG_WEAK_TABLE_MASK));
  if (h->type) {
    assert(h->type->name || h->type->get_name);
  } else {
    const unsigned *p = (const unsigned *)header_to_alloc((alloc_header *)h);
    for (unsigned x = 0; x < (h->size - sizeof(*h)) / sizeof(unsigned); x++)
      assert(p[x] == 0xa1b2c3d4 || p[x] == 0xa9b8c7d6);
  }
}

static unsigned nr_sanity_checks;
static unsigned sanity_threshold = 2383010;
void
LibVEX_alloc_sanity_check(void)
{
  bool found_cursor = false;
  nr_sanity_checks++;
  /* Magic number is 2383357 */
  if (nr_sanity_checks < sanity_threshold)
    return;

  for (alloc_header *h = first_alloc_header();
       h != alloc_header_terminator;
       h = next_alloc_header(h)) {
    if (h == allocation_cursor)
      found_cursor = true;
    sanity_check_alloc_header(h);
  }
  assert(found_cursor);
  printf("Sanity passed.\n");
}
#else
void
LibVEX_alloc_sanity_check(void)
{
}
#endif

bool
LibVEX_is_gc_address(const void *what)
{
  return what >= temporary && what < temporary + N_TEMPORARY_BYTES;
}
