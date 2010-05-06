#ifndef __LIBVEX_ALLOC_H
#define __LIBVEX_ALLOC_H

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
   struct {
      Int nbytes;
      void (*gc_visit)(const void *, HeapVisitor &);
      void (*destruct)(void *);
      const char *name;
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
    return (t *)__LibVEX_Alloc(&__vex_type_ ## t, __FILE__, __LINE__);	\
  }									\
  static inline t **LibVEX_Alloc_Array_ ## t(unsigned nr)		\
  {									\
    return (t **)__LibVEX_Alloc_Ptr_Array(nr, __FILE__, __LINE__);	\
  }

struct libvex_alloc_type;

extern struct libvex_alloc_type *__LibVEX_Alloc(const VexAllocType *t,
						const char *file,
						unsigned line);
extern struct libvex_alloc_type *__LibVEX_Alloc_Ptr_Array(unsigned len,
							  const char *file,
							  unsigned line);
extern void *__LibVEX_Alloc_Bytes(Int nbytes, const char *file, unsigned line);
#define LibVEX_Alloc_Bytes(_n) __LibVEX_Alloc_Bytes((_n), __FILE__, __LINE__)

void vexRegisterGCRoot(void **);
void vexUnregisterGCRoot(void **);
void vexInitHeap(void);

class VexGcRoot {
	void **root;
public:
	VexGcRoot(void **x) :
		root(x)
	{
		vexRegisterGCRoot(x);
	}
	~VexGcRoot()
	{
		vexUnregisterGCRoot(root);
	}
};

extern VexAllocType LibvexVectorType;

template <typename content>
class LibvexVector {
	friend void __visit_vector(const void *_ctxt, HeapVisitor &hv);
	unsigned sz;
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
	void push(content *v) {
		sz++;
		items = (content **)realloc(items, sizeof(content *) * sz);
		items[sz-1] = v;
	}

	static LibvexVector<content> *empty() {
		struct libvex_alloc_type *t = __LibVEX_Alloc(&LibvexVectorType,
							     __FILE__,
							     __LINE__);
		LibvexVector<content> *t2 = (LibvexVector<content> *)t;
		memset(t2, 0, sizeof(*t2));
		return t2;							     
	}
};

#endif /* !__LIBVEX_ALLOC_H */
