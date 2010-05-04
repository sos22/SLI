#ifndef __LIBVEX_ALLOC_H
#define __LIBVEX_ALLOC_H

class HeapVisitor {
public:
   virtual void visit(const void *ptr) = 0;
   void operator()(const void *p) { visit(p); }
};

class Visitable {
public:
   void visit(HeapVisitor &) const {};
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

#define DEFINE_VEX_TYPE_VISITABLE(__t)					\
	static void __visit_ ## __t(const __t *ths, HeapVisitor &visit)	\
	{								\
		ths->visit(visit);					\
	}								\
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

#endif /* !__LIBVEX_ALLOC_H */
