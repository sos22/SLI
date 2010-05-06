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
#include <stdio.h>
#include <string.h>

#include "libvex_basictypes.h"
#include "libvex.h"
#include "libvex_alloc.h"

#include "main_globals.h"
#include "main_util.h"

/* The main arena. */
#define N_TEMPORARY_BYTES 1000000000
static char temporary[N_TEMPORARY_BYTES] __attribute__((aligned(8)));
static unsigned heap_used;

/* Each allocation in the arena is prefixed by an allocation header. */
struct alloc_header {
  const VexAllocType *type; /* Or NULL for free blocks */
  unsigned size; /* Includes header */
  unsigned flags;
#define ALLOC_FLAG_GC_MARK 1
  const char *file;
  unsigned line;
};

#define NR_GC_ROOTS 128
static unsigned nr_gc_roots;
static void **gc_roots[NR_GC_ROOTS];

/* A pointer to an allocation somewhere in the heap which is likely to
   be a reasonable place to start looking when performing
   allocations. */
static struct alloc_header *allocation_cursor;

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
  struct alloc_header *maybe = (struct alloc_header *)((unsigned long)h + h->size);
  if ( (unsigned long)maybe >= (unsigned long)temporary + N_TEMPORARY_BYTES )
    return NULL;
  return maybe;
}

class GcVisitor : public HeapVisitor {
public:
   virtual void visit(const void *ptr);
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
  what_header->flags |= ALLOC_FLAG_GC_MARK;
  if (what_header->type->gc_visit)
    what_header->type->gc_visit(what, *this);
}

static void
poison(void *start, unsigned nr_bytes, unsigned pattern)
{
#ifndef NDEBUG
  unsigned x;
  for (x = 0; x < nr_bytes / 4; x++)
    ((unsigned *)start)[x] = pattern;
#endif
}

static void
do_gc(void)
{
  unsigned x;
  struct alloc_header *h;
  struct alloc_header *p;
  struct alloc_header *n;
  GcVisitor gc;

  for (h = first_alloc_header(); h; h = next_alloc_header(h))
    h->flags &= ~ ALLOC_FLAG_GC_MARK;
  for (x = 0; x < nr_gc_roots; x++)
    gc.visit(*gc_roots[x]);

  heap_used = 0;
  h = first_alloc_header();
  p = NULL;
  while (h) {
    n = next_alloc_header(h);
    if (h->type) {
      if (h->flags & ALLOC_FLAG_GC_MARK) {
	heap_used += h->size;
      } else {
	/* We're going to free off this block. */
	if (h->type->destruct)
	  h->type->destruct(header_to_alloc(h));
	h->type = NULL;
	poison(h + 1, h->size - sizeof(*h), 0xa1b2c3d4);
	if (p && !p->type) {
	  if (h == allocation_cursor)
	    allocation_cursor = p;
	  p->size += h->size;
	  if (n && !n->type) {
	    p->size += n->size;
	  }
	  n = next_alloc_header(p);
	  h = p;
	} else if (n && !n->type) {
	  if (n == allocation_cursor)
	    allocation_cursor = h;
	  h->size += n->size;
	  n = next_alloc_header(h);
	}
      }
    }

    p = h;
    h = n;
  }
}

void vexSetAllocModeTEMP_and_clear ( void )
{
  if (heap_used > N_TEMPORARY_BYTES / 2)
    do_gc();
}


static VexAllocType byte_alloc_type = { -1, 0, 0, "<bytes>" };

static void
visit_ptr_array(const void *ths, HeapVisitor &visitor)
{
  struct alloc_header *ah = alloc_to_header(ths);
  void **payload = (void **)(ah + 1);
  unsigned x;
  for (x = 0; x < (ah->size - sizeof(*ah)) / sizeof(void *); x++)
    visitor.visit(payload[x]);
}

static VexAllocType ptr_array_type = { -1, visit_ptr_array, NULL, "<array>" };


static void *
alloc_bytes(const VexAllocType *type, unsigned size, const char *file, unsigned line)
{
  struct alloc_header *cursor;
  struct alloc_header *next;
  unsigned old_size;
  void *res;

  size += sizeof(struct alloc_header);
  size = (size + 15) & ~15;

  /* First-fit policy.  Search starts from the allocation cursor, and
     then if that fails we try again from the beginning. */
  for (cursor = allocation_cursor;
       cursor != NULL;
       cursor = next_alloc_header(cursor)) {
    vassert(!(cursor->flags & ~ALLOC_FLAG_GC_MARK));
    if (!cursor->type && cursor->size >= size)
      break;
  }
  if (!cursor) {
    for (cursor = first_alloc_header();
	 cursor != allocation_cursor;
	 cursor = next_alloc_header(cursor)) {
      vassert(!(cursor->flags & ~ALLOC_FLAG_GC_MARK));
      if (!cursor->type && cursor->size >= size)
	break;
    }
    if (cursor == allocation_cursor)
      vpanic("VEX temporary storage exhausted.\n"
	     "Increase N_TEMPORARY_BYTES and recompile.");
  }

  /* Consider splitting the block */
  if (cursor->size >= size + 32) {
    /* Do split. */
    old_size = cursor->size;
    cursor->size = size;
    vassert(cursor->size != 0);
    next = next_alloc_header(cursor);
    vassert(next != NULL);
    next->type = NULL;
    next->size = old_size - size;
    vassert(next->size != 0);
    next->flags = 0;
  }

  cursor->type = type;
  cursor->file = file;
  cursor->line = line;
  res = header_to_alloc(cursor);
  poison(res, size - sizeof(struct alloc_header), 0xaabbccdd);

  heap_used += cursor->size;

  allocation_cursor = next_alloc_header(cursor);

  return res;
}

/* Exported to library client. */
void *
__LibVEX_Alloc_Bytes(Int nbytes, const char *file, unsigned line)
{
  return alloc_bytes(&byte_alloc_type, nbytes, file, line);
}

struct libvex_alloc_type *
__LibVEX_Alloc(const VexAllocType *t, const char *file, unsigned line)
{
  return (struct libvex_alloc_type *)alloc_bytes(t, t->nbytes, file, line);
}

void *
LibVEX_realloc(void *ptr, unsigned new_size)
{
  struct alloc_header *ah = alloc_to_header(ptr);
  struct alloc_header *next;
  unsigned old_size;
  void *newptr;

  new_size += sizeof(struct alloc_header);
  new_size = (new_size + 15) & ~15;

  /* Can only resize byte allocations */
  vassert(ah->type == &byte_alloc_type);

  /* Enlarge if possible */
  while (new_size > ah->size) {
    next = next_alloc_header(ah);
    if (!next || next->type)
      break;
    ah->size += next->size;
    heap_used += next->size;
  }

  /* Trim it down again */
  if (new_size < ah->size - 32) {
    old_size = ah->size;
    ah->size = new_size;
    next = next_alloc_header(ah);
    next->type = NULL;
    next->size = old_size - new_size;
    next->flags = 0;
    heap_used -= old_size - new_size;
  }

  /* Good enough? */
  if (new_size <= ah->size)
    return ptr;

  /* Failed to resize: allocate a new block */
  newptr = __LibVEX_Alloc_Bytes(new_size, ah->file, ah->line);
  if (new_size < ah->size)
    memcpy(newptr, ptr, new_size);
  else
    memcpy(newptr, ptr, ah->size);

  ah->type = NULL;
  heap_used -= ah->size;

  return newptr;
}

struct libvex_alloc_type *
__LibVEX_Alloc_Ptr_Array(unsigned len, const char *file, unsigned line)
{
  struct alloc_header *ah;
  void **res;
  unsigned x;

  res = (void **)alloc_bytes(&ptr_array_type, sizeof(void *) * len, file, line);
  ah = alloc_to_header(res);
  for (x = 0; x < (ah->size - sizeof(*ah)) / sizeof(void *); x++)
    res[x] = NULL;
  return (struct libvex_alloc_type *)res;
}

void vexAllocSanityCheck ( void )
{
}

void
vexRegisterGCRoot(void **w)
{
  vassert(nr_gc_roots < NR_GC_ROOTS);
  gc_roots[nr_gc_roots] = w;
  nr_gc_roots++;
}

static void
my_memmove(void *dest, const void *src, unsigned n)
{
  int x;

  if (dest < src) {
    for (x = 0; x < (int)n; x++) {
      ((char *)dest)[x] = ((const char *)src)[x];
    }
  } else {
    for (x = n - 1; x >= 0; x++)
      ((char *)dest)[x] = ((const char *)src)[x];
  }
}

void
vexUnregisterGCRoot(void **w)
{
  unsigned x;
  for (x = 0; x < nr_gc_roots; x++) {
    if (gc_roots[x] == w) {
      my_memmove(gc_roots + x, gc_roots + x + 1, (nr_gc_roots - x - 1) * sizeof(gc_roots[0]));
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
    vex_printf("%d %p %s %s:%d\n", depth, what, ah->type->name, ah->file, ah->line);
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

  for (h = first_alloc_header(); h; h = next_alloc_header(h))
    h->flags &= ~ ALLOC_FLAG_GC_MARK;
  for (x = 0; x < nr_gc_roots; x++) {
    vex_printf("Root %d:\n", x);
    visitor.visit(*gc_roots[x]);
  }

  for (h = first_alloc_header(); h; h = next_alloc_header(h)) {
    if (!h->type || (h->flags & ALLOC_FLAG_GC_MARK))
      continue;
    vex_printf("Unattached but allocated:\n");
    visitor.visit(h + 1);
  }
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
  entire_arena_hdr = first_alloc_header();
  entire_arena_hdr->type = NULL;
  entire_arena_hdr->size = N_TEMPORARY_BYTES;
  entire_arena_hdr->flags = 0;
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

