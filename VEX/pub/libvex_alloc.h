#ifndef __LIBVEX_ALLOC_H
#define __LIBVEX_ALLOC_H

#include <assert.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include <set>

/* A GC token doesn't actually do anything, it's just there to make it
   more obvious which functions can perform GC sweeps. */
class GarbageCollectionToken {
  GarbageCollectionToken() {}
public:
  static GarbageCollectionToken GarbageCollectionAllowed() { return GarbageCollectionToken(); }
};

#define ALLOW_GC GarbageCollectionToken::GarbageCollectionAllowed()

class __GcCallback;

#define NR_GC_ROOTS (65536*8)
class Heap {
public:
	unsigned nr_gc_roots;
	void **gc_roots[NR_GC_ROOTS];
	struct arena *head_arena;
	struct arena *current_arena;
	struct _VexAllocType *headType;
	struct wr_core *headVisitedWeakRef;
	unsigned long heap_used;
	bool redirection_tags_set;
	std::set<__GcCallback *> callbacks;
};

extern Heap main_heap;

template <typename t, Heap *heap> class GarbageCollected;

class HeapVisitor {
public:
	virtual void visit(void *&ptr) = 0;
	template <typename t> void operator()(t *&p) {
		if (p) {
			void *p2 = (void *)p;
			visit(p2);
			p = (t *)p2;
			assert(p);
		}
	}
};

class __GcCallback {
	Heap *h;
protected:
	__GcCallback(Heap *_h)
		: h(_h)
	{
		h->callbacks.insert(this);
	}
	~__GcCallback()
	{
		h->callbacks.erase(this);
	}
	virtual void runGc(HeapVisitor &hv) = 0;
public:
	void operator()(HeapVisitor &hv) { runGc(hv); }
};

template <Heap *heap = &main_heap>
class GcCallback : public __GcCallback {
protected:
	GcCallback() : __GcCallback(heap) {}
};

/* Allocate in Vex's temporary allocation area.  Be careful with this.
   You can only call it inside an instrumentation or optimisation
   callback that you have previously specified in a call to
   LibVEX_Translate.  The storage allocated will only stay alive until
   translation of the current basic block is complete.
 */
typedef
   struct _VexAllocType {
      unsigned long nbytes;
      void (*relocate)(void *, void *, size_t s);
      void (*gc_visit)(void *, HeapVisitor &);
      void (*destruct)(void *);
      const char *name;
      const char *(*get_name)(const void *);
      unsigned long total_allocated;
      unsigned nr_allocated;
      struct _VexAllocType *next;
   }
   VexAllocType;

struct libvex_allocation_site {
	unsigned long nr_bytes;
	const char *file;
	unsigned line;
	unsigned flags;
};

struct libvex_alloc_type;

void assert_gc_allocated(const void *ptr);
extern struct libvex_alloc_type *__LibVEX_Alloc(Heap *h, VexAllocType *t);
extern struct libvex_alloc_type *__LibVEX_Alloc_Ptr_Array(Heap *h, unsigned long len);
extern void _LibVEX_free(Heap *h, const void *_ptr);
template <typename t, Heap *h> void
__LibVEX_free(const GarbageCollected<t, h> *, void *ptr)
{
	_LibVEX_free(h, ptr);
}
#define LibVEX_free(x) __LibVEX_free((x), (x))

extern void *__LibVEX_Alloc_Bytes(Heap *h,
				  unsigned long nbytes,
				  struct libvex_allocation_site *las);
#define LibVEX_Alloc_Bytes(_n)						\
	({								\
		static libvex_allocation_site __las = {0, __FILE__,	\
						       __LINE__};	\
		__LibVEX_Alloc_Bytes(&main_heap, (_n), &__las);		\
	})
extern size_t __LibVEX_Alloc_Size(const void *ptr);

extern void *LibVEX_Alloc_Sized(Heap *h, VexAllocType *t, unsigned long size);
extern void *LibVEX_realloc(Heap *h, void *base, unsigned long new_size);

void vexRegisterGCRoot(Heap *h, void **);
void vexUnregisterGCRoot(Heap *h, void **);
void vexInitHeap(void);
void LibVEX_gc(GarbageCollectionToken t);
void LibVEX_maybe_gc(GarbageCollectionToken t);

template <Heap *heap>
class VexGcRoot {
	void **root;
public:
	void init(void **x)
	{
		root = x;
		vexRegisterGCRoot(heap, x);
	}
	VexGcRoot(void **x, const char *)
	{
		init(x);
	}
	void destruct()
	{
		vexUnregisterGCRoot(heap, root);
	}
	~VexGcRoot()
	{
		destruct();
	}
};

template <typename underlying>
void visit_object(void *_ctxt, HeapVisitor &hv)
{
	underlying *ctxt = (underlying *)_ctxt;
	/* hackety hackety hack: don't visit if we've not been
	 * constructed (no vtable pointer) */
	if (*(unsigned long *)_ctxt)
		ctxt->visit(hv);
}

template <typename underlying>
void destruct_object(void *_ctxt)
{
	underlying *ctxt = (underlying *)_ctxt;
	/* Like visit_object(), don't destruct if we've not been
	   constructed. */
	if (*(unsigned long *)_ctxt)
		ctxt->destruct();
}

template <typename underlying>
void relocate_object(void *_ctxt, void *target, size_t sz)
{
	underlying *ctxt = (underlying *)_ctxt;
	if (*(unsigned long *)_ctxt)
		ctxt->relocate((underlying *)target, sz);
}

template <typename underlying>
const char *get_name(const void *_ctxt)
{
	const underlying *ctxt = (const underlying *)_ctxt;
	return ctxt->cls_name();
}

#define NAMED_CLASS static const char *cls_name() { return __PRETTY_FUNCTION__ + 19; }

template <typename t, Heap *_heap = &main_heap>
class GarbageCollected {
protected:
	virtual ~GarbageCollected() {}
public:
	static VexAllocType type;
	static Heap *const heap;
	static void *operator new(size_t s)
	{
		void *res = LibVEX_Alloc_Sized(_heap, &type, s);
		memset(res, 0, s);
		return res;
	}
	static void operator delete(void *)
	{
		abort();
	}
	virtual void visit(HeapVisitor &hv) = 0;
	virtual void relocate(t *, size_t) { }

	/* Because you can't call someone else's virtual destructor... */
	void destruct() { this->~GarbageCollected(); }
};
template <typename t, Heap *heap> VexAllocType GarbageCollected<t,heap>::type = {-1, relocate_object<t>, visit_object<t>, destruct_object<t>, NULL, get_name<t> };
template <typename t, Heap *_heap> Heap *const GarbageCollected<t,_heap>::heap = _heap;

template <typename p, Heap *heap = &main_heap>
class VexPtr {
	p *content;
	VexGcRoot<heap> root;
public:
	VexPtr() : content(NULL), root((void **)&content, "VexPtr") {}
	VexPtr(p *_content) : content(_content), root((void **)&content, "VexPtr") {}
	VexPtr(const VexPtr<p,heap> &c) : content(c.content), root((void **)&content, "VexPtr") {}
	const VexPtr<p,heap> &operator=(const VexPtr<p,heap> &x) { content = x.content; return *this; }
	const VexPtr<p,heap> &operator=(p *x) { content = x; return *this; }
	p &operator*() const { return *content; }
	p *operator->() const { return content; }
	operator p*() const { return content; }
	p *&get() { return content; }
	p * const &get() const { return content; }
	void set(p *x) { content = x; }
	void relocate(VexPtr<p, heap> *to) {
		root.destruct();
		to->root.init((void **)&to->content);
	}
};

template <typename t, Heap *heap> class WeakRef;

struct wr_core {
	template <typename t, Heap *heap> friend class WeakRef;
public:
	struct wr_core *next;
	void *content;

	wr_core() : next(), content() {}
};

template <typename t, Heap *heap>
class WeakRef : public GarbageCollected<WeakRef<t,heap>, heap > {
	wr_core core;
public:
	WeakRef() : core() {}
	void set(t *newTarg) { assert((unsigned long)newTarg != 0x93939393939393b3); core.content = (void *)newTarg; }
	t *get() { return (t *)core.content; }

	void visit(HeapVisitor &) {
		if (core.content) {
			assert(core.content != (void *)0x93939393939393b3);
			core.next = heap->headVisitedWeakRef;
			heap->headVisitedWeakRef = &core;
		}
	}
	void destruct() {}
	NAMED_CLASS
};

void LibVEX_alloc_sanity_check(Heap *h);
char *vex_asprintf(const char *fmt, ...) __attribute__((__format__ (__printf__, 1, 2)));
char *vex_vasprintf(const char *fmt, va_list args);

static inline char *my_asprintf(const char *fmt, ...) __attribute__((__format__ (__printf__, 1, 2)));
static inline char *my_asprintf(const char *fmt, ...)
{
	va_list args;
	char *r;
	va_start(args, fmt);
	int x = vasprintf(&r, fmt, args);
	(void)x;
	va_end(args);
	return r;
}

#endif /* !__LIBVEX_ALLOC_H */
