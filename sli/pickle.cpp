/* Stuff for pickling IRExprs */
#include "sli.h"
#include <map>
#include "libvex_alloc.h"
#include "pickle.hpp"
#include "state_machine.hpp"

typedef unsigned long memoSlotT;
class Pickler {
	std::map<void *, memoSlotT> memoTable;
	memoSlotT lastMemoSlot;

	void emitMemoReference(memoSlotT s);
	void emitObjectHeader(memoSlotT id, void *start);

	FILE *output;
public:
	Pickler(FILE *f) : lastMemoSlot(0), output(f) {memoTable[NULL] = 0;}
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
	Unpickler(FILE *f) : input(f) {memoTable[0] = NULL;}
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
	p.finishObject();
}
static void
pickle_counted(IRExpr **&e, Pickler &p, int nr)
{
	int i;
	if (p.startObject(e))
		return;
	for (i = 0; i < nr; i++)
		pickle(e[i], p);
	p.finishObject();
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
	p.finishObject();
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
	p.finishObject();
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

#define MAGIC (unsigned long)0xaabbccddeefful
struct backreference {
	unsigned long magic;
	unsigned char code;
	memoSlotT id;
} __attribute__((packed));

void
Pickler::emitMemoReference(memoSlotT s)
{
	struct backreference br;
	br.magic = MAGIC;
	br.code = 1;
	br.id = s;
	fwrite(&br, sizeof(br), 1, output);
}

struct object_header {
	unsigned long magic;
	unsigned char code;
	memoSlotT id;
	size_t size;
} __attribute__((packed));

void
Pickler::emitObjectHeader(memoSlotT id, void *start)
{
	struct object_header oh;
	oh.magic = MAGIC;
	oh.code = 2;
	oh.id = id;
	oh.size = __LibVEX_Alloc_Size(start);
	fwrite(&oh, sizeof(oh), 1, output);
}

struct raw_block {
	unsigned long magic;
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
	rb->magic = MAGIC;
	rb->code = 3;
	rb->size = s;
	memcpy(rb->content, start, s);
	fwrite(rb, s + sizeof(*rb), 1, output);
	free(rb);
}

struct end_object {
	unsigned long magic;
	unsigned char code;
} __attribute__((packed));

void
Pickler::finishObject()
{
	struct end_object eo;
	eo.magic = MAGIC;
	eo.code = 4;
	fwrite(&eo, sizeof(eo), 1, output);
}

void
Pickler::emitString(const char *start)
{
	struct raw_block *rb;
	size_t s = strlen(start);
	rb = (struct raw_block *)malloc(s + sizeof(*rb));
	rb->magic = MAGIC;
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
	unsigned long m;
	fread(&m, sizeof(m), 1, input);
	assert(m == MAGIC);
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
	unsigned long m;
	fread(&m, sizeof(m), 1, input);
	assert(m == MAGIC);
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
	unsigned long m;
	fread(&m, sizeof(m), 1, input);
	assert(m == MAGIC);
	int c = fgetc(input);
	assert(c == 4);
}

char *
Unpickler::restoreString()
{
	unsigned long m;
	fread(&m, sizeof(m), 1, input);
	assert(m == MAGIC);
	int c = fgetc(input);
	assert(c == 5);
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

static void pickle(StateMachine *sm, Pickler &p);

enum smse_tag { SMSE_unreached, SMSE_store, SMSE_load, SMSE_copy };
static void
pickle(StateMachineSideEffect *smse, Pickler &p)
{
	smse_tag t;
	if (p.startObject(smse))
		return;
	if (dynamic_cast<StateMachineSideEffectUnreached *>(smse)) {
		t = SMSE_unreached;
		pickle(t, p);
	} else if (StateMachineSideEffectStore *smses =
		   dynamic_cast<StateMachineSideEffectStore *>(smse)) {
		t = SMSE_store;
		pickle(t, p);
		pickle(smses->addr, p);
		pickle(smses->data, p);
		pickle(smses->rip, p);
	} else if (StateMachineSideEffectLoad *smsel =
		   dynamic_cast<StateMachineSideEffectLoad *>(smse)) {
		t = SMSE_load;
		pickle(t, p);
		pickle(smsel->key, p);
		pickle(smsel->smsel_addr, p);
		pickle(smsel->rip, p);
	} else if (StateMachineSideEffectCopy *smsec =
		   dynamic_cast<StateMachineSideEffectCopy *>(smse)) {
		t = SMSE_copy;
		pickle(t, p);
		pickle(smsec->key, p);
		pickle(smsec->value, p);
	} else {
		abort();
	}
	p.finishObject();
}

static void
pickle(StateMachineEdge *sme, Pickler &p)
{
	unsigned i;

	if (p.startObject(sme))
		return;
	pickle(sme->target, p);
	i = sme->sideEffects.size();
	pickle(i, p);
	for (i = 0; i < sme->sideEffects.size(); i++)
		pickle(sme->sideEffects[i], p);
	p.finishObject();
}

enum sm_tag { SM_unreachable, SM_crash, SM_survive, SM_proxy, SM_bifurcate, SM_stub };
static void
pickle(StateMachine *sm, Pickler &p)
{
	sm_tag t;

	if (p.startObject(sm))
		return;
	pickle(sm->origin, p);
	if (dynamic_cast<StateMachineUnreached *>(sm)) {
		t = SM_unreachable;
		pickle(t, p);
	} else if (dynamic_cast<StateMachineCrash *>(sm)) {
		t = SM_crash;
		pickle(t, p);
	} else if (dynamic_cast<StateMachineNoCrash *>(sm)) {
		t = SM_survive;
		pickle(t, p);
	} else if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
		t = SM_proxy;
		pickle(t, p);
		pickle(smp->target, p);
	} else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm)) {
		t = SM_bifurcate;
		pickle(t, p);
		pickle(smb->condition, p);
		pickle(smb->trueTarget, p);
		pickle(smb->falseTarget, p);
	} else if (StateMachineStub *sms = dynamic_cast<StateMachineStub *>(sm)) {
		t = SM_stub;
		pickle(t, p);
		pickle(sms->target, p);
	} else {
		abort();
	}
	p.finishObject();
}

void
pickleStateMachine(StateMachine *sm, FILE *f)
{
	Pickler p(f);
	pickle(sm, p);
}

static void unpickle(StateMachine *&sm, Unpickler &p);

static void
unpickle(StateMachineSideEffect *&out, Unpickler &p)
{
	smse_tag t;
	memoSlotT id;
	if (p.retrieveObject(out, id))
		return;
	unpickle(t, p);
	switch (t) {
	case SMSE_unreached:
		out = StateMachineSideEffectUnreached::get();
		break;
	case SMSE_store: {
		IRExpr *addr;
		IRExpr *data;
		unsigned long rip;
		unpickle(addr, p);
		unpickle(data, p);
		unpickle(rip, p);
		out = new StateMachineSideEffectStore(addr, data, rip);
		break;
	}
	case SMSE_load: {
		Int key;
		IRExpr *addr;
		unsigned long rip;
		unpickle(key, p);
		unpickle(addr, p);
		unpickle(rip, p);
		out = new StateMachineSideEffectLoad(key, addr, rip);
		break;
	}
	case SMSE_copy: {
		Int key;
		IRExpr *value;
		unpickle(key, p);
		unpickle(value, p);
		out = new StateMachineSideEffectCopy(key, value);
		break;
	}
	}
	p.discover(out, id);
	p.finishObject();
}

static void
unpickle(StateMachineEdge *&sme, Unpickler &p)
{
	unsigned i;
	unsigned j;
	StateMachineEdge *work;
	memoSlotT id;

	if (p.retrieveObject(sme, id))
		return;
	work = new StateMachineEdge(NULL);
	p.discover(work, id);

	unpickle(work->target, p);
	unpickle(i, p);

	work->sideEffects.resize(i);
	for (j = 0; j < i; j++)
		unpickle(work->sideEffects[j], p);
	sme = work;
	p.finishObject();
}

static void
unpickle(StateMachine *&sm, Unpickler &p)
{
	memoSlotT id;
	unsigned long origin;
	sm_tag t;

	if (p.retrieveObject(sm, id))
		return;
	unpickle(origin, p);
	unpickle(t, p);
	switch (t) {
	case SM_unreachable:
		sm = StateMachineUnreached::get();
		break;
	case SM_crash:
		sm = StateMachineCrash::get();
		break;
	case SM_survive:
		sm = StateMachineNoCrash::get();
		break;
	case SM_proxy: {
		StateMachineProxy *sme = new StateMachineProxy(origin, (StateMachineEdge *)NULL);
		p.discover(sme, id);
		unpickle(sme->target, p);
		sm = sme;
		p.finishObject();
		return;
	}
	case SM_bifurcate: {
		StateMachineBifurcate *res = new StateMachineBifurcate(origin, NULL,
								       (StateMachineEdge *)NULL,
								       (StateMachineEdge *)NULL);
		p.discover(res, id);
		unpickle(res->condition, p);
		unpickle(res->trueTarget, p);
		unpickle(res->falseTarget, p);
		sm = res;
		p.finishObject();
		return;
	}
	case SM_stub: {
		IRExpr *targ;
		unpickle(targ, p);
		sm = new StateMachineStub(origin, targ);
		break;
	}
	}
	p.discover(sm, id);
	p.finishObject();
	return;
}

StateMachine *
unpickleStateMachine(FILE *f)
{
	Unpickler p(f);
	StateMachine *res;

	unpickle(res, p);

	return res;	
}
