/* Stuff for pickling IRExprs */
#include "sli.h"
#include <map>
#include "libvex_alloc.h"
#include "pickle.hpp"

typedef unsigned long memoSlotT;
class Pickler {
	std::map<void *, memoSlotT> memoTable;
	memoSlotT lastMemoSlot;

	void emitMemoReference(memoSlotT s);
	void emitObjectHeader(memoSlotT id, void *start);

	FILE *output;
public:
	Pickler(FILE *f) : lastMemoSlot(0), output(f) {}
	bool startObject(void *ptr);
	void finishObject();

	void emitString(const char *s);
	void raw(const void *start, const void *end);
};

class Unpickler {
	std::map<memoSlotT, void *> memoTable;
	memoSlotT lastMemoSlot;

	bool _retrieveObject(void *&ptr, memoSlotT &id, size_t &sz);

	FILE *input;
public:
	Unpickler(FILE *f) : input(f) {}
	void finishObject();
	void raw(void *start, void *end);
	template <typename t>
	bool retrieveObject(t *&ptr, memoSlotT &id, size_t &sz)
	{
		void *r = ptr;
		bool res = _retrieveObject(r, id, sz);
		ptr = (t *)r;
		return res;
	}
	template <typename t>
	bool retrieveObject(t *&ptr, memoSlotT &id)
	{
		size_t ign;
		return retrieveObject(ptr, id, ign);
	}
	void discover(void *ptr, memoSlotT id);
	char *restoreString();
};

static void
pickle(const char *c, Pickler &p)
{
	p.emitString(c);
}

static void
unpickle(const char *&c, Unpickler &p)
{
	c = p.restoreString();
}

static void pickle(IRExpr *&e, Pickler &p);
static void
pickle_null(IRExpr **&e, Pickler &p)
{
	int i;
	
	if (p.startObject(e))
		return;
	i = 0;
	while (1) {
		pickle(e[i], p);
		if (!e[i])
			break;
		i++;
	}
}
static void
pickle_counted(IRExpr **&e, Pickler &p, int nr)
{
	int i;
	if (p.startObject(e))
		return;
	for (i = 0; i < nr; i++)
		pickle(e[i], p);
}

static void
pickle(int o, Pickler &p)
{
	p.raw(&o, &o + 1);
}

static void
unpickle(int &o, Unpickler &p)
{
	p.raw(&o, &o + 1);
}

/* This should only really be used for enums, but I can't see any way
   of telling C++ about that. */
template <typename foo>
void
unpickle(foo &o, Unpickler &p)
{
	int x;
	unpickle(x, p);
	o = (foo)x;
}


static void unpickle(IRExpr *&e, Unpickler &p);
IRExpr **alloc_irexpr_array(unsigned nr);
static void
unpickle_null(IRExpr **&e, Unpickler &p)
{
	int i;
	memoSlotT id;
	size_t sz;

	if (p.retrieveObject(e, id, sz))
		return;
	e = alloc_irexpr_array(sz / sizeof(e[0]));
	p.discover(e, id);
	i = 0;
	while (1) {
		unpickle(e[i], p);
		if (!e[i])
			break;
		i++;
	}
}
static void
unpickle_counted(IRExpr **&e, Unpickler &p, int nr)
{
	int i;
	memoSlotT id;
	size_t sz;

	if (p.retrieveObject(e, id, sz))
		return;
	static libvex_allocation_site __las = {0, __FILE__, __LINE__};
	e = (IRExpr **)__LibVEX_Alloc_Bytes(&ir_heap, sz, &__las);
	p.discover(e, id);
	for (i = 0; i < nr; i++)
		unpickle(e[i], p);
}


#define __pickle_header(type, n)					\
	do {								\
		if (p.startObject(n))					\
			return;						\
	} while (0)
#define __depickle_header(type, n)					\
	do {								\
		memoSlotT id;						\
		if (p.retrieveObject(n, id)) {				\
			return;						\
		} else {						\
			n = new type();					\
			p.discover(n, id);				\
		}							\
	} while (0)

#define mk_pickle(pickle, state, header)				\
	static void							\
	pickle(IRRegArray *&arr, state &p)				\
	{								\
		header(IRRegArray, arr);				\
		pickle(arr->base, p);					\
		pickle(arr->elemTy, p);					\
		pickle(arr->nElems, p);					\
		p.finishObject();					\
	}								\
	static void							\
	pickle(IRConst *&cnst, state &p)				\
	{								\
		header(IRConst, cnst);					\
		pickle(cnst->tag, p);					\
		pickle(cnst->Ico.U64, p);				\
		p.finishObject();					\
	}								\
	static void							\
	pickle(IRCallee *&irc, state &p)				\
	{								\
		header(IRCallee, irc);					\
		pickle(irc->regparms, p);				\
		pickle(irc->name, p);					\
		/* Note that we don't restore irc->addr.  That's */     \
		/* okay, because we never actually use it. */		\
		pickle(irc->mcx_mask, p);				\
		p.finishObject();					\
	}								\
	static void							\
	pickle(IRExpr *&expr, state &p)					\
	{								\
		header(IRExpr, expr);					\
		pickle(expr->tag, p);					\
		pickle(expr->optimisationsApplied, p);			\
		switch (expr->tag) {					\
		case Iex_Binder:					\
			pickle(expr->Iex.Binder.binder, p);		\
			break;						\
		case Iex_Get:						\
			pickle(expr->Iex.Get.offset, p);		\
			pickle(expr->Iex.Get.ty, p);			\
			pickle(expr->Iex.Get.tid, p);			\
			break;						\
		case Iex_GetI:						\
			pickle(expr->Iex.GetI.descr, p);		\
			pickle(expr->Iex.GetI.ix, p);			\
			pickle(expr->Iex.GetI.bias, p);			\
			pickle(expr->Iex.GetI.tid, p);			\
			break;						\
		case Iex_RdTmp:						\
			pickle(expr->Iex.RdTmp.tmp, p);			\
			pickle(expr->Iex.RdTmp.tid, p);			\
			break;						\
		case Iex_Qop:						\
			pickle(expr->Iex.Qop.arg4, p);			\
		case Iex_Triop:						\
			pickle(expr->Iex.Qop.arg3, p);			\
		case Iex_Binop:						\
			pickle(expr->Iex.Qop.arg2, p);			\
		case Iex_Unop:						\
			pickle(expr->Iex.Qop.arg1, p);			\
			pickle(expr->Iex.Qop.op, p);			\
			break;						\
		case Iex_Load:						\
			pickle(expr->Iex.Load.isLL, p);			\
			pickle(expr->Iex.Load.end, p);			\
			pickle(expr->Iex.Load.ty, p);			\
			pickle(expr->Iex.Load.addr, p);			\
			break;						\
		case Iex_Const:						\
			pickle(expr->Iex.Const.con, p);			\
			break;						\
		case Iex_CCall:						\
			pickle(expr->Iex.CCall.cee, p);			\
			pickle(expr->Iex.CCall.retty, p);		\
			pickle ## _null(expr->Iex.CCall.args, p);	\
			break;						\
		case Iex_Mux0X:						\
			pickle(expr->Iex.Mux0X.cond, p);		\
			pickle(expr->Iex.Mux0X.expr0, p);		\
			pickle(expr->Iex.Mux0X.exprX, p);		\
			break;						\
		case Iex_Associative:					\
			pickle(expr->Iex.Associative.op, p);		\
			pickle(expr->Iex.Associative.nr_arguments, p);	\
			pickle(expr->Iex.Associative.nr_arguments_allocated, p); \
			pickle ## _counted(expr->Iex.Associative.contents, \
					   p,				\
					   expr->Iex.Associative.nr_arguments); \
			break;						\
		}							\
		p.finishObject();					\
	}
mk_pickle(pickle, Pickler, __pickle_header)
mk_pickle(unpickle, Unpickler, __depickle_header)

bool
Pickler::startObject(void *ptr)
{
	if (memoTable.count(ptr)) {
		emitMemoReference(memoTable[ptr]);
		return true;
	}
	lastMemoSlot++;
	memoSlotT s = lastMemoSlot;
	memoTable[ptr] = s;
	emitObjectHeader(s, ptr);
	return false;
}

struct backreference {
	unsigned char code;
	memoSlotT id;
} __attribute__((packed));

void
Pickler::emitMemoReference(memoSlotT s)
{
	struct backreference br;
	br.code = 1;
	br.id = s;
	fwrite(&br, sizeof(br), 1, output);
}

struct object_header {
	unsigned char code;
	memoSlotT id;
	size_t size;
} __attribute__((packed));

void
Pickler::emitObjectHeader(memoSlotT id, void *start)
{
	struct object_header oh;
	oh.code = 2;
	oh.id = id;
	oh.size = __LibVEX_Alloc_Size(start);
	fwrite(&oh, sizeof(oh), 1, output);
}

struct raw_block {
	unsigned char code;
	unsigned size;
	unsigned char content[0];
} __attribute__((packed));

void
Pickler::raw(const void *start, const void *end)
{
	struct raw_block *rb;
	size_t s = (unsigned long)end - (unsigned long)start;
	rb = (struct raw_block *)malloc(s + sizeof(*rb));
	rb->code = 3;
	rb->size = s;
	memcpy(rb->content, start, s);
	fwrite(rb, s + sizeof(*rb), 1, output);
	free(rb);
}

struct end_object {
	unsigned char code;
};

void
Pickler::finishObject()
{
	struct end_object eo;
	eo.code = 4;
	fwrite(&eo, sizeof(eo), 1, output);
}

void
Pickler::emitString(const char *start)
{
	struct raw_block *rb;
	size_t s = strlen(start);
	rb = (struct raw_block *)malloc(s + sizeof(*rb));
	rb->code = 5;
	rb->size = s;
	memcpy(rb->content, start, s);
	fwrite(rb, s + sizeof(*rb), 1, output);
	free(rb);
}

void
pickleIRExpr(IRExpr *e, FILE *f)
{
	Pickler p(f);

	pickle(e, p);
}

bool
Unpickler::_retrieveObject(void *&ptr, memoSlotT &id, size_t &sz)
{
	int c = fgetc(input);
	fread(&id, sizeof(id), 1, input);
	if (c == 1) {
		/* Backreference */
		assert(memoTable.count(id) == 1);
		ptr = memoTable[id];
		return true;
	}
	ptr = (void *)0xf001;
	/* New object */
	assert(c == 2);

	fread(&sz, sizeof(sz), 1, input);
	return false;
}

void
Unpickler::raw(void *start, void *end)
{
	int c = fgetc(input);
	assert(c == 3);
	unsigned sz;
	fread(&sz, sizeof(sz), 1, input);
	assert(sz == (unsigned long)end - (unsigned long)start);
	fread(start, 1, sz, input);
}

void
Unpickler::discover(void *ptr, memoSlotT id)
{
	assert(memoTable.count(id) == 0);
	memoTable[id] = ptr;
}

void
Unpickler::finishObject()
{
	int c = fgetc(input);
	assert(c == 4);
}

char *
Unpickler::restoreString()
{
	int c = fgetc(input);
	assert(c == 4);
	unsigned size;
	fread(&size, sizeof(size), 1, input);
	char *res = (char *)LibVEX_Alloc_Bytes(size + 1);
	fread(res, 1, size, input);
	res[size] = 0;
	return res;
}

IRExpr *
unpickleIRExpr(FILE *f)
{
	Unpickler p(f);
	IRExpr *res;

	unpickle(res, p);

	return res;
}
