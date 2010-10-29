#ifndef __LIBVEX_ALLOC_H
#define __LIBVEX_ALLOC_H

#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* A GC token doesn't actually do anything, it's just there to make it
   more obvious which functions can perform GC sweeps. */
class GarbageCollectionToken {
  GarbageCollectionToken() {}
public:
  static GarbageCollectionToken GarbageCollectionAllowed() { return GarbageCollectionToken(); }
};

#define ALLOW_GC GarbageCollectionToken::GarbageCollectionAllowed()

#define NR_GC_ROOTS 128
class Heap {
public:
	unsigned nr_gc_roots;
	void **gc_roots[NR_GC_ROOTS];
	const char *gc_root_names[NR_GC_ROOTS];
	struct arena *head_arena;
	struct arena *current_arena;
	struct _VexAllocType *headType;
	struct wr_core *headVisitedWeakRef;
	unsigned long heap_used;
};

extern Heap main_heap;


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

#define DEFINE_VEX_TYPE(t) VexAllocType __vex_type_ ## t = { sizeof(t), NULL, NULL, NULL, #t }
#define __DEFINE_VEX_TYPE_NO_DESTRUCT(__t, __visit)			\
  VexAllocType __vex_type_ ## __t = {				        \
    sizeof(__t),							\
    NULL,							        \
    (void (*)(void *, HeapVisitor &visit))__visit,			\
    NULL,								\
    # __t								\
  }
#define DEFINE_VEX_TYPE_NO_DESTRUCT(__t, __visit)			\
	static void __visit_ ## __t(__t *ths, HeapVisitor &visit)	\
       __visit								\
  __DEFINE_VEX_TYPE_NO_DESTRUCT(__t, __visit_ ## __t)

#define DECLARE_VEX_TYPE(t)						\
  extern VexAllocType __vex_type_ ## t;					\
  static inline t *LibVEX_Alloc_ ## t(void)				\
  {									\
    return (t *)__LibVEX_Alloc(&__vex_type_ ## t);			\
  }									\
  static inline t **LibVEX_Alloc_Array_ ## t(unsigned nr)		\
  {									\
    return (t **)__LibVEX_Alloc_Ptr_Array(nr);				\
  }

struct libvex_alloc_type;

void assert_gc_allocated(const void *ptr);
extern struct libvex_alloc_type *__LibVEX_Alloc(VexAllocType *t);
extern struct libvex_alloc_type *__LibVEX_Alloc_Ptr_Array(unsigned long len);
extern void LibVEX_free(const void *_ptr);
extern void *__LibVEX_Alloc_Bytes(unsigned long nbytes,
				  struct libvex_allocation_site *las);
#define LibVEX_Alloc_Bytes(_n)						\
	({								\
		static libvex_allocation_site __las = {0, __FILE__,	\
						       __LINE__};	\
		__LibVEX_Alloc_Bytes(_n, &__las);			\
	})

extern void *LibVEX_Alloc_Sized(VexAllocType *t, unsigned long size);
extern void *LibVEX_realloc(void *base, unsigned long new_size);

void vexRegisterGCRoot(void **, const char *name);
void vexUnregisterGCRoot(void **);
void vexInitHeap(void);
void LibVEX_gc(GarbageCollectionToken t);
void LibVEX_maybe_gc(GarbageCollectionToken t);
void libvex_redirect(void *what, void *to);

class VexGcRoot {
	void **root;
public:
	VexGcRoot(void **x, const char *name) :
		root(x)
	{
		vexRegisterGCRoot(x, name);
	}
	~VexGcRoot()
	{
		vexUnregisterGCRoot(root);
	}
};

template <typename t>
class VexGcVisitor {
	t **owner;
	VexGcRoot root;
	static VexAllocType type;
public:
	VexGcVisitor(t *x, const char *name) : root((void **)&owner, name)
	{
		owner = (t **)__LibVEX_Alloc(&type);
		*owner = x;
	}
};

template <typename t>
void visit_vex_gc_visitor(void *_ctxt, HeapVisitor &hv)
{
	t **ctxt = (t **)_ctxt;
	if (*ctxt)
		(*ctxt)->visit(hv);
}

template <typename t> VexAllocType VexGcVisitor<t>::type = {
	sizeof(t *),
	NULL,
	visit_vex_gc_visitor<t>,
	NULL,
	"vex_gc_visitor"
};

extern VexAllocType LibvexVectorType;

template <typename content>
class LibvexVector {
	friend void __visit_vector(void *_ctxt, HeapVisitor &hv);
	unsigned sz;
	unsigned maxSz;
	content **items;

	/* DNI */
	LibvexVector();
	~LibvexVector();
public:
	unsigned size() const { return sz; }
	content *index(unsigned idx) {
		if (idx >= sz)
			abort();
		return items[idx];
	}
	void set(unsigned idx, content *x) {
		assert(idx < sz);
		items[idx] = x;
	}
	void push(content *v) {
		sz++;
		if (sz > maxSz) {
			items = (content **)realloc(items, sizeof(content *) * sz);
			maxSz = sz;
		}
		items[sz-1] = v;
	}
	content *pop() {
		assert(sz != 0);
		sz--;
		return items[sz];
	}
	content *pop_first() {
		assert(sz != 0);
		content *r = items[0];
		sz--;
		memmove(items, items + 1, sizeof(items[0]) * sz);
		return r;
	}

	/* This gets a leading underscore because it throws away the
	   existing content of the array. */
	void _set_size(unsigned new_size) {
		free(items);
		items = (content **)malloc(sizeof(content *) * new_size);
		memset(items, 0, sizeof(content *) * new_size);
		maxSz = sz = new_size;
	}

	static LibvexVector<content> *empty() {
		struct libvex_alloc_type *t = __LibVEX_Alloc(&LibvexVectorType);
		LibvexVector<content> *t2 = (LibvexVector<content> *)t;
		memset(t2, 0, sizeof(*t2));
		return t2;
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

template <typename t>
class GarbageCollected {
	static VexAllocType type;
protected:
	static void release(const t *x) {
		LibVEX_free(x);
	}
	void libvex_install_redirect(GarbageCollected<t> *n) {
		libvex_redirect(this, n);
	}
	virtual ~GarbageCollected() {}
public:
	static void *operator new(size_t s)
	{
		void *res = LibVEX_Alloc_Sized(&type, s);
		memset(res, 0, s);
		return res;
	}
	static void operator delete(void *)
	{
		abort();
	}
	virtual void visit(HeapVisitor &hv) = 0;
	virtual void destruct() { this->~GarbageCollected(); }
	virtual void relocate(t *target, size_t sz) { }
};
template <typename t> VexAllocType GarbageCollected<t>::type = {-1, relocate_object<t>, visit_object<t>, destruct_object<t>, NULL, get_name<t> };

template <typename p>
class VexPtr {
	p *content;
	VexGcRoot root;
public:
	VexPtr() : content(NULL), root((void **)&content, "VexPtr") {}
	VexPtr(p *_content) : content(_content), root((void **)&content, "VexPtr") {}
	VexPtr(VexPtr<p> &c) : content(c.content), root((void **)&content, "VexPtr") {}
	const VexPtr<p> &operator=(VexPtr<p> &x) { content = x.content; return *this; }
	const VexPtr<p> &operator=(p *x) { content = x; return *this; }
	p &operator*() const { return *content; }
	p *operator->() const { return content; }
	operator p*() const { return content; }
	p *&get() { return content; }
	p * const &get() const { return content; }
	void set(p *x) { content = x; }
};

template <typename t> class WeakRef;

struct wr_core {
	template <typename t> friend class WeakRef;
	friend void LibVEX_gc(GarbageCollectionToken);
private:
	struct wr_core *next;
	void *content;
public:
	wr_core() : next(), content() {}
};

template <typename t>
class WeakRef : public GarbageCollected<WeakRef<t> > {
	wr_core core;
public:
	WeakRef() : core() {}
	void set(t *newTarg) { assert((unsigned long)newTarg != 0x93939393939393b3); core.content = (void *)newTarg; }
	t *get() { return (t *)core.content; }

	void visit(HeapVisitor &hv) {
		if (core.content) {
			assert(core.content != (void *)0x93939393939393b3);
			core.next = main_heap.headVisitedWeakRef;
			main_heap.headVisitedWeakRef = &core;
		}
	}
	void destruct() {}
	NAMED_CLASS
};

void LibVEX_alloc_sanity_check();

#endif /* !__LIBVEX_ALLOC_H */
