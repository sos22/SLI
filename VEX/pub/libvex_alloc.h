#ifndef __LIBVEX_ALLOC_H
#define __LIBVEX_ALLOC_H

#include <assert.h>
#include <stdlib.h>

class HeapVisitor {
public:
   virtual void visit(const void *ptr) = 0;
   void operator()(const void *p) { visit(p); }
};

/* Allocate in Vex's temporary allocation area.  Be careful with this.
   You can only call it inside an instrumentation or optimisation
   callback that you have previously specified in a call to
   LibVEX_Translate.  The storage allocated will only stay alive until
   translation of the current basic block is complete.
 */
typedef
   struct _VexAllocType {
      Int nbytes;
      void (*gc_visit)(const void *, HeapVisitor &);
      void (*destruct)(void *);
      const char *name;
      const char *(*get_name)(const void *);
      unsigned total_allocated;
      struct _VexAllocType *next;
   }
   VexAllocType;

#define DEFINE_VEX_TYPE(t) VexAllocType __vex_type_ ## t = { sizeof(t), NULL, NULL, #t }
#define __DEFINE_VEX_TYPE_NO_DESTRUCT(__t, __visit)			\
  VexAllocType __vex_type_ ## __t = {				        \
    sizeof(__t),							\
    (void (*)(const void *, HeapVisitor &visit))__visit,		\
    NULL,								\
    # __t								\
  }
#define DEFINE_VEX_TYPE_NO_DESTRUCT(__t, __visit)			\
  static void __visit_ ## __t(const __t *ths, HeapVisitor &visit)	\
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

extern struct libvex_alloc_type *__LibVEX_Alloc(VexAllocType *t);
extern struct libvex_alloc_type *__LibVEX_Alloc_Ptr_Array(unsigned len);
extern void LibVEX_free(const void *_ptr);
extern void *__LibVEX_Alloc_Bytes(Int nbytes);
#define LibVEX_Alloc_Bytes(_n) __LibVEX_Alloc_Bytes(_n)
extern void *LibVEX_Alloc_Sized(VexAllocType *t, unsigned size);
extern void *LibVEX_realloc(void *base, unsigned new_size);

void vexRegisterGCRoot(void **, const char *name);
void vexUnregisterGCRoot(void **);
void vexInitHeap(void);
void LibVEX_gc(void);

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
void visit_vex_gc_visitor(const void *_ctxt, HeapVisitor &hv)
{
	const t **ctxt = (const t **)_ctxt;
	if (*ctxt)
		(*ctxt)->visit(hv);
}

template <typename t> VexAllocType VexGcVisitor<t>::type = {
	sizeof(t *),
	visit_vex_gc_visitor<t>,
	NULL,
	"vex_gc_visitor"
};

extern VexAllocType LibvexVectorType;

template <typename content>
class LibvexVector {
	friend void __visit_vector(const void *_ctxt, HeapVisitor &hv);
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

void registerWeakRef(const void *object, void **ref);
void unregisterWeakRef(const void *object, void **ref);

template <typename t>
class WeakRef {
	t *target;
public:
	WeakRef() : target(NULL) {}
	~WeakRef() { if (target) unregisterWeakRef(target, (void **)&target); }
	void set(t *newTarg) {
		if (target) unregisterWeakRef(target, (void **)&target);
		target = newTarg;
		if (newTarg) registerWeakRef(newTarg, (void **)&target);
	}
	t *get() { return target; }
};

#endif /* !__LIBVEX_ALLOC_H */
