#include <typeinfo>
#include <deque>
#include <set>

#include "sli.h"

#include "libvex_guest_offsets.h"

#include "guest_generic_bb_to_IR.h"
#include "guest_amd64_defs.h"

/* Do it this way so that we still get format argument checking even
   when a particular type of debug is disabled. */
#define DBG_DISCARD(fmt, ...) do { if (0) { printf(fmt, ## __VA_ARGS__ ); } } while (0)
#define DBG_PRINT(fmt, ...) do { printf(fmt, ## __VA_ARGS__ ); } while (0)

#define DBG_CYCLE_BREAKER(fmt, ...) DBG_DISCARD(fmt, ## __VA_ARGS__)
#define DBG_CALC_CMNS(fmt, ...) DBG_DISCARD(fmt, ## __VA_ARGS__)

/* Something which is almost like a timestamp: a bundle of TID and
   RIP.  Most of the analysis works on acyclic CFGs, for which this is
   actually sufficient to uniquely identify a dynamic instruction. */
class CrashTimestamp : public Named {
protected:
	char *mkName() const {
		char *b = my_asprintf("}%d:%lx", tid._tid(), rip);
		for (std::vector<unsigned long>::const_iterator it =
			     callStack.begin();
		     it != callStack.end();
		     it++) {
			char *b2 = my_asprintf("%lx;%s", *it, b);
			free(b);
			b = b2;
		}
		char *b2 = my_asprintf("{%s", b);
		free(b);
		return b2;
	}
public:
	void changed() { clearName(); }
	ThreadId tid; /* Which thread are we talking about */
	unsigned long rip;
	std::vector<unsigned long> callStack;
	CrashTimestamp(ThreadId _tid, unsigned long _rip,
		       const std::vector<unsigned long> &stack)
		: tid(_tid), rip(_rip), callStack(stack)
	{
	}
	CrashTimestamp() : tid(), rip(-1), callStack() {}
	CrashTimestamp(Thread<unsigned long> *thr)
		: tid(thr->tid),
		  rip(thr->regs.rip()),
		  callStack(thr->currentCallStack)
	{
	}
	void operator=(const CrashTimestamp &ts)
	{
		tid = ts.tid;
		rip = ts.rip;
		callStack = ts.callStack;
	}
	bool valid() { return tid.valid(); }
	unsigned long hash() const {
		unsigned long h = tid.hash() ^ (rip * 7);
		for (std::vector<unsigned long>::const_iterator it = callStack.begin();
		     it != callStack.end();
		     it++)
			h = h * 103 + *it;
		return h;
	}
	bool operator==(const CrashTimestamp &c) const {
		return tid == c.tid && rip == c.rip && callStack == c.callStack;
	}
	bool operator!=(const CrashTimestamp &c) const {
		return !(*this == c);
	}
	bool operator<(const CrashTimestamp &c) const {
		if (tid < c.tid)
			return true;
		if (tid > c.tid)
			return false;
		if (rip < c.rip)
			return true;
		if (rip > c.rip)
			return false;
		if (callStack.size() < c.callStack.size())
			return true;
		if (callStack.size() > c.callStack.size())
			return false;
		for (unsigned x = 0; x < callStack.size(); x++) {
			if (callStack[x] < c.callStack[x])
				return true;
			if (callStack[x] < c.callStack[x])
				return false;
		}
		return false;
	}
};

class CrashExpression;

struct concrete_store {
	unsigned long addr;
	unsigned long value;
	concrete_store(unsigned long _addr, unsigned long _value)
		: addr(_addr), value(_value)
	{
	}
	concrete_store()
		: addr(0xf001), value(0xbeef)
	{
	}
};
typedef std::vector<concrete_store> concreteStoresT;

struct abstract_store {
	CrashExpression *addr;
	CrashExpression *data;
	abstract_store(CrashExpression *_addr,
		       CrashExpression *_data)
		: addr(_addr), data(_data)
	{
	}
};
typedef std::vector<abstract_store> abstractStoresT;

class CrashExpression;

class CPMapper {
public:
	virtual CrashExpression *operator()(CrashExpression *e) = 0;
};

class CrashExpression : public GarbageCollected<CrashExpression>, public Named {
	mutable unsigned long hashval;
	mutable bool have_hash;

	static const int nr_intern_heads = 4095;
	static CrashExpression *intern_heads[nr_intern_heads];
	CrashExpression *next_intern;
	CrashExpression *prev_intern;

	CrashExpression *simplified;
	unsigned simplified_hardness;
protected:
	CrashExpression() { prev_intern = next_intern = NULL; }
	virtual void _visit(HeapVisitor &hv) = 0;
	virtual const char *_mkName() const = 0;
	char *mkName() const {
		return my_asprintf("%s", _mkName());
	}
	virtual unsigned long _hash() const = 0;
	virtual bool _eq(const CrashExpression *o) const = 0;
	virtual CrashExpression *_simplify(unsigned hardness) { return this; }
	void rehash() {
		clearName();
		if (!have_hash)
			return;
		int old_head = hashval % nr_intern_heads;
		unsigned long newhash = _hash();
		if (newhash == hashval)
			return;
		hashval = newhash;
		if (next_intern)
			next_intern->prev_intern = prev_intern;
		if (prev_intern)
			prev_intern->next_intern = next_intern;
		else
			intern_heads[old_head] = next_intern;
		int new_head = hashval % nr_intern_heads;
		next_intern = intern_heads[new_head];
		prev_intern = NULL;
		if (intern_heads[new_head])
			intern_heads[new_head]->prev_intern = this;
		intern_heads[new_head] = this;
	}

	static CrashExpression *intern(CrashExpression *what) {
		CrashExpression *cursor;
		int head = what->hash() % nr_intern_heads;
		cursor = intern_heads[head];
		while (cursor) {
			if (cursor->eq(what)) {
				if (cursor->next_intern)
					cursor->next_intern->prev_intern = cursor->prev_intern;
				if (cursor->prev_intern) {
					cursor->prev_intern->next_intern = cursor->next_intern;
				} else {
					assert(intern_heads[head] == cursor);
					intern_heads[head] = cursor->next_intern;
				}
				cursor->prev_intern = cursor->next_intern = NULL;
				what = cursor;
				break;
			}
			cursor = cursor->next_intern;
		}
		what->next_intern = intern_heads[head];
		what->prev_intern = NULL;
		if (intern_heads[head])
			intern_heads[head]->prev_intern = what;
		intern_heads[head] = what;
		return what;
	}

	~CrashExpression() {
		if (next_intern)
			next_intern->prev_intern = prev_intern;
		if (prev_intern)
			prev_intern->next_intern = next_intern;
		else
			intern_heads[hashval % nr_intern_heads] = next_intern;
		prev_intern = NULL;
		next_intern = NULL;
	}

	static void discover_relevant_address(std::set<unsigned long> &addresses,
					      unsigned long addr);

public:
	bool eq(const CrashExpression *o) const {
		if (o == this)
			return true;
		return hash() == o->hash() && _eq(o);
	}
	unsigned long hash() const {
		if (!have_hash) {
			hashval = _hash();
			have_hash = true;
		}
		return hashval;
	}
	virtual bool isConstant(unsigned long &l) { return false; }
	bool isConstant() { unsigned long ign; return isConstant(ign); }
	bool isTrue() { unsigned long r; if (isConstant(r) && r) return !!r; else return false; }
	static CrashExpression *get(IRExpr *e);
	virtual CrashExpression *map(CPMapper &m) = 0;

	void visit(HeapVisitor &hv) { hv(simplified); _visit(hv); }
	void destruct() { this->~CrashExpression(); }
	virtual unsigned complexity() const = 0;

	virtual void build_relevant_address_list(Thread<unsigned long> *thr,
						 MachineState<unsigned long> *ms,
						 std::set<unsigned long> &addresses,
						 const concreteStoresT &stores) = 0;
	virtual unsigned long eval(Thread<unsigned long> *thr,
				   MachineState<unsigned long> *ms,
				   const concreteStoresT &stores) = 0;

	CrashExpression *simplify(unsigned hardness = 1) {
		if (simplified_hardness < hardness) {
			simplified_hardness = hardness;

			/* Break possible infinite recursion */
			if (!simplified)
				simplified = this;

			simplified = _simplify(hardness);
			if (simplified->simplified_hardness < hardness) {
				simplified->simplified = simplified;
				simplified->simplified_hardness = hardness;
			}
		}
		return simplified;
	}
	virtual bool pointsAtStack() const { return false; }

	void relocate(CrashExpression *target, size_t sz)
	{
		if (target->next_intern)
			target->next_intern->prev_intern = target;
		if (target->prev_intern)
			target->prev_intern->next_intern = target;
		else
			intern_heads[target->hashval % nr_intern_heads] = target;
		memset(this, 0x73, sizeof(*this));
	}

	NAMED_CLASS
};

CrashExpression *CrashExpression::intern_heads[CrashExpression::nr_intern_heads];

void
CrashExpression::discover_relevant_address(std::set<unsigned long> &addresses,
					   unsigned long addr)
{
	addresses.insert(addr);
}

class CrashExpressionTemp : public CrashExpression {
	CrashExpressionTemp(IRTemp t) : tmp(t) {}
protected:
	const char *_mkName() const { return vex_asprintf("t%d", tmp); }
	void _visit(HeapVisitor &hv) {}

	bool _eq(const CrashExpression *o) const {
		if (const CrashExpressionTemp *t =
		    dynamic_cast<const CrashExpressionTemp *>(o))
			return t->tmp == tmp;
		else
			return false;
	}
	unsigned long _hash() const {
		return tmp;
	}
public:
	IRTemp tmp;
	static CrashExpression *get(IRTemp t) {return (new CrashExpressionTemp(t))->simplify(); }
	CrashExpression *map(CPMapper &m) { return m(this); }
	unsigned complexity() const { return 2; }

	void build_relevant_address_list(Thread<unsigned long> *thr,
					 MachineState<unsigned long> *ms,
					 std::set<unsigned long> &addresses,
					 const concreteStoresT &stores) {
		/* This can't happen, because we shouldn't be building
		   the address list until all temporaries have been
		   resolved. */
		abort();
	}

	unsigned long eval(Thread<unsigned long> *thr,
			   MachineState<unsigned long> *ms,
			   const std::vector<concrete_store> &)
	{
		return thr->temporaries[tmp].lo;
	}
};

class CrashExpressionRegister : public CrashExpression {
	CrashExpressionRegister(Int o) : offset(o) {}
protected:
	const char *_mkName() const { return vex_asprintf("r%d", offset); }
	void _visit(HeapVisitor &hv) {}
	bool _eq(const CrashExpression *o) const {
		if (const CrashExpressionRegister *t =
		    dynamic_cast<const CrashExpressionRegister *>(o))
			return t->offset == offset;
		else
			return false;
	}
	unsigned long _hash() const {
		return offset * 4657;
	}
public:
	int offset;
	static CrashExpression *get(int o) {return (new CrashExpressionRegister(o))->simplify(); }
	CrashExpression *map(CPMapper &m) { return m(this); }
	unsigned complexity() const { return 2; }
	bool pointsAtStack() const {
		return offset == OFFSET_amd64_RSP ||
			offset == OFFSET_amd64_RBP;
	}
	void build_relevant_address_list(Thread<unsigned long> *thr,
					 MachineState<unsigned long> *ms,
					 std::set<unsigned long> &addresses,
					 const concreteStoresT &stores)
	{
	}
	unsigned long eval(Thread<unsigned long> *thr,
			   MachineState<unsigned long> *ms,
			   const std::vector<concrete_store> &)

	{
		return thr->regs.get_reg(offset / 8);
	}
};

class CrashExpressionConst : public CrashExpression {
	CrashExpressionConst(unsigned long v) : value(v) {}
protected:
	const char *_mkName() const { return vex_asprintf("0x%lx", value); }
	void _visit(HeapVisitor &hv) {}
	bool _eq(const CrashExpression *o) const {
		if (const CrashExpressionConst *t =
		    dynamic_cast<const CrashExpressionConst *>(o))
			return t->value == value;
		else
			return false;
	}
	unsigned long _hash() const {
		return (value ^ 0x84182b462e9136cb) * 7681;
	}
public:
	unsigned long value;
	static CrashExpression *get(unsigned long r) {return intern(new CrashExpressionConst(r))->simplify(); }
	CrashExpression *map(CPMapper &m) { return m(this); }
	unsigned complexity() const { return 1; }
	bool isConstant(unsigned long &l) { l = value; return true; }
	void build_relevant_address_list(Thread<unsigned long> *thr,
					 MachineState<unsigned long> *ms,
					 std::set<unsigned long> &addresses,
					 const concreteStoresT &stores)
	{
	}
	unsigned long eval(Thread<unsigned long> *thr,
			   MachineState<unsigned long> *ms,
			   const std::vector<concrete_store> &)
	{
		return value;
	}
};

class CrashExpressionFailed : public CrashExpression {
	CrashExpressionFailed(char *_reason)
		: reason(_reason)
	{
	}
protected:
	char *reason;
	const char *_mkName() const { return my_asprintf("<decode_failed:%s>",
							 reason); }
	void _visit(HeapVisitor &hv) {hv(reason);}
	bool _eq(const CrashExpression *o) const {
		/* We cheat a little and consider all failed crash
		   expressions to be identical, even if they have
		   different reason strings, as this makes the
		   analysis work a lot better. */
		if (dynamic_cast<const CrashExpressionFailed *>(o))
			return true;
		else
			return false;
	}
	unsigned long _hash() const {
		return 99999;
	}
public:
	static CrashExpression *get(const char *fmt, ...)
	{
		va_list args;
		char *reason;
		va_start(args, fmt);
		va_arg(args, void *);
		reason = vex_vasprintf(fmt, args);
		va_end(args);
		return intern(new CrashExpressionFailed(reason))->simplify();
	}
	CrashExpression *map(CPMapper &m) { return m(this); }
	/* Give failed nodes a very high complexity, so that the
	   simplification eliminates them whenever possible. */
	unsigned complexity() const { return (unsigned)-1; }
	void build_relevant_address_list(Thread<unsigned long> *thr,
					 MachineState<unsigned long> *ms,
					 std::set<unsigned long> &addresses,
					 const concreteStoresT &stores)
	{
	}
	unsigned long eval(Thread<unsigned long> *thr,
			   MachineState<unsigned long> *ms,
			   const std::vector<concrete_store> &)
	{
		/* Guess wildly. */
		return 0;
	}
};

class CrashExpressionLoad : public CrashExpression {
	CrashExpressionLoad(const CrashTimestamp &_when, CrashExpression *_addr)
		: addr(_addr)
	{
		when = _when;
	}

protected:
	const char *_mkName() const { return vex_asprintf("(load %s at %s)",
							  addr->name(), when.name());
	}
	void _visit(HeapVisitor &hv) { hv(addr); }
	bool _eq(const CrashExpression *o) const {
		if (const CrashExpressionLoad *t =
		    dynamic_cast<const CrashExpressionLoad *>(o))
			return when == t->when && addr->eq(t->addr);
		else
			return false;
	}
	unsigned long _hash() const {
		return (when.hash() * 12517) ^ (addr->hash() * 27431);
	}
	CrashExpression *_simplify(unsigned hardness) {
		addr = addr->simplify(hardness);
		return this;
	}
public:
	CrashTimestamp when;
	CrashExpression *addr;
	static CrashExpression *get(const CrashTimestamp &when,
				    CrashExpression *addr)
	{
		unsigned long c;
		if (addr->isConstant(c))
			assert(c == 0 || c > 0x1000);
		return intern(new CrashExpressionLoad(when, addr))->simplify();
	}
	CrashExpression *map(CPMapper &m) {
		CrashExpression *addr2 = addr->map(m);
		if (addr2 == addr)
			return m(this);
		else
			return m(get(when, addr2));
	}
	unsigned complexity() const { return addr->complexity() + 3; }

	void build_relevant_address_list(Thread<unsigned long> *thr,
					 MachineState<unsigned long> *ms,
					 std::set<unsigned long> &addresses,
					 const concreteStoresT &stores)
	{
		addr->build_relevant_address_list(thr, ms, addresses, stores);
		if (!addr->pointsAtStack())
			discover_relevant_address(
				addresses,
				addr->eval(thr, ms, stores));
	}
	/* This doesn't really belong here, but nevermind. */
	static unsigned long fetch(unsigned long addr,
				   MachineState<unsigned long> *ms,
				   Thread<unsigned long> *thr)
	{
		unsigned long res[8];
		ms->addressSpace->readMemory(addr, 8, res, false, thr);
		unsigned long folded;
		for (unsigned x = 0; x < 8; x++)
			((unsigned char *)&folded)[x] = res[x];
		return folded;
	}
	unsigned long eval(Thread<unsigned long> *thr,
			   MachineState<unsigned long> *ms,
			   const std::vector<concrete_store> &stores)
	{
		unsigned long concrete_addr = addr->eval(thr, ms, stores);
		for (std::vector<concrete_store>::const_reverse_iterator it = stores.rbegin();
		     it != stores.rend();
		     it++) {
			if (it->addr == concrete_addr)
				return it->value;
		}
		return fetch(addr->eval(thr, ms, stores), ms, thr);
	}
};

class CrashExpressionBinop : public CrashExpression {
protected:
	virtual void __visit(HeapVisitor &hv) {}
	virtual const char *__mkName() const = 0;
	void _visit(HeapVisitor &hv) { hv(l); hv(r); __visit(hv); }
	const char *_mkName() const { return vex_asprintf("%s(%s, %s)",
							  __mkName(),
							  l->name(),
							  r->name()); }
	CrashExpressionBinop(CrashExpression *_l,
			     CrashExpression *_r)
		: l(_l), r(_r)
	{
	}
public:
	virtual CrashExpression *semiDupe(CrashExpression *l, CrashExpression *r) = 0;
	CrashExpression *l, *r;
	CrashExpression *map(CPMapper &m) {
		CrashExpression *l2 = l->map(m), *r2 = r->map(m);
		if (l2 == l && r2 == r)
			return m(this);
		else
			return m(semiDupe(l2, r2));
	}
	unsigned complexity() const { return l->complexity() + r->complexity() + 1; }
	bool pointsAtStack() const {
		return l->isConstant() && r->pointsAtStack();
	}
	void build_relevant_address_list(Thread<unsigned long> *thr,
					 MachineState<unsigned long> *ms,
					 std::set<unsigned long> &addresses,
					 const concreteStoresT &stores)
	{
		l->build_relevant_address_list(thr, ms, addresses, stores);
		r->build_relevant_address_list(thr, ms, addresses, stores);
	}
};

#define mk_binop(name, op, hashop)					\
	class CrashExpression ## name : public CrashExpressionBinop {	\
		CrashExpression ## name(CrashExpression *l,		\
					CrashExpression *r)		\
		: CrashExpressionBinop(l, r)				\
		{							\
		}							\
		unsigned long _hash() const {				\
			return l->hash() hashop r->hash();			\
		}							\
	protected:							\
	const char *__mkName() const { return #name; }			\
	CrashExpression *_simplify(unsigned hardness);			\
	bool _eq(const CrashExpression *o) const {			\
		const CrashExpression ## name *t =			\
			dynamic_cast<const CrashExpression ## name *>(o); \
		if (t)							\
			return t->l->eq(l) && t->r->eq(r);		\
		else							\
			return false;					\
	}								\
	public:								\
	static CrashExpression *get(CrashExpression *l,			\
				    CrashExpression *r) {		\
		return intern(new CrashExpression ## name(l, r))->simplify();	\
	}								\
	CrashExpression *semiDupe(CrashExpression *l, CrashExpression *r) { \
		if (l == this->l && r == this->r)			\
			return this;					\
		return get(l, r);					\
	}								\
	unsigned long eval(Thread<unsigned long> *thr,			\
			   MachineState<unsigned long> *ms,		\
			   const concreteStoresT &stores)		\
	{								\
		return l->eval(thr, ms, stores) op			\
			r->eval(thr, ms, stores);			\
	}								\
	};

#define most_binops(x)						\
	x(Add, +, +)						\
	x(Mul, *, *)						\
	x(Xor, ^, ^)						\
	x(And, &, &)						\
	x(Or, |, |)						\
	x(Shl, <<, <<)

#define all_binops(x)				\
	most_binops(x)				\
	x(Equal, * 46278 + 472389 *, ==)	\
	x(UnsignedLessThan, *4451 + 9227 *, <)

all_binops(mk_binop)

#define simplify_add_xor(name, op)					\
	CrashExpression *						\
	CrashExpression ## name::_simplify(unsigned hardness)		\
	{								\
		unsigned long lc;					\
		unsigned long rc;					\
									\
	top:								\
		l = l->simplify(hardness);				\
		r = r->simplify(hardness);				\
		if (l->complexity() > r->complexity()) {		\
			CrashExpression *t;				\
			t = l;						\
			l = r;						\
			r = t;						\
		}							\
									\
		rehash();						\
		if (l->isConstant(lc)) {				\
			if (lc == 0)					\
				return r;				\
			if (r->isConstant(rc))				\
				return CrashExpressionConst::get(lc op rc); \
			CrashExpression ## name *r2 =			\
				dynamic_cast<CrashExpression ## name *>(r); \
			if (r2 && r2->l->isConstant(rc)) {			\
				l = CrashExpressionConst::get(lc op rc); \
				r = r2->r;				\
				goto top;				\
			}						\
		}							\
									\
		CrashExpression ## name *l2 =				\
			dynamic_cast<CrashExpression ## name *>(l);	\
		if (l2) {						\
			r = semiDupe(l2->r, r);				\
			l = l2->l;					\
			goto top;					\
		}							\
		return this;						\
	}
simplify_add_xor(Xor, ^)
simplify_add_xor(Or, |)

class CrashExpressionSignedLessThan : public CrashExpressionBinop {		
	CrashExpressionSignedLessThan(CrashExpression *l,		
				      CrashExpression *r)		
		: CrashExpressionBinop(l, r)			       
	{							
	}							
	unsigned long _hash() const {				
		return l->hash() * 4451 + r->hash() * 9227;
	}
protected:							
	const char *__mkName() const { return "SignedLessThan"; }			
	CrashExpression *_simplify(unsigned hardness) {
		l = l->simplify(hardness);
		r = r->simplify(hardness);
		rehash();
		unsigned long lc, rc;
		if (l->isConstant(lc) && r->isConstant(rc)) {
			if ((long)lc < (long)rc)
				return CrashExpressionConst::get(1);
			else
				return CrashExpressionConst::get(0);
		}
		return this;
	}
	bool _eq(const CrashExpression *o) const {			
		const CrashExpressionSignedLessThan *t =			
			dynamic_cast<const CrashExpressionSignedLessThan *>(o); 
		if (t)							
			return t->l->eq(l) && t->r->eq(r);		
		else							
			return false;					
	}								
	public:								
	static CrashExpression *get(CrashExpression *l,			
				    CrashExpression *r) {		
		return intern(new CrashExpressionSignedLessThan(l, r))->simplify();	
	}								
	CrashExpression *semiDupe(CrashExpression *l, CrashExpression *r) { 
		if (l == this->l && r == this->r)			
			return this;					
		return get(l, r);					
	}								
	unsigned long eval(Thread<unsigned long> *thr,
			   MachineState<unsigned long> *ms,
			   const concreteStoresT &stores)
	{
		return (long)l->eval(thr, ms, stores) < (long)r->eval(thr, ms, stores);
	}
};

CrashExpression *
CrashExpressionAnd::_simplify(unsigned hardness)
{
	unsigned long lc;
	unsigned long rc;

top:
	l = l->simplify(hardness);
	r = r->simplify(hardness);
	if (l->complexity() > r->complexity()) {
		CrashExpression *t;
		t = l;
		l = r;
		r = t;
	}

	rehash();
	if (l->isConstant(lc)) {
		if (lc == 0)
			return l;
		if (r->isConstant(rc))
			return CrashExpressionConst::get(lc & rc);
		if (typeid(r) == typeid(this)) {
			CrashExpressionAnd *r2 =
				dynamic_cast<CrashExpressionAnd *>(r);
			if (r2->l->isConstant(rc)) {
				l = CrashExpressionConst::get(lc & rc);
				r = r2->r;
				goto top;
			}
		}
	}

	if (typeid(l) == typeid(this)) {
		CrashExpressionAnd *l2 =
			dynamic_cast<CrashExpressionAnd *>(l);

		r = semiDupe(l2->r, r);
		l = l2->l;
		goto top;
	}

	if (hardness > 1 && l->eq(r))
		return l;

	return this;
}

CrashExpression *
CrashExpressionMul::_simplify(unsigned hardness)
{
	unsigned long lc;
	unsigned long rc;
	l = l->simplify(hardness);
	r = r->simplify(hardness);
	if (l->complexity() > r->complexity()) {
		CrashExpression *t = l;
		l = r;
		r = t;
	}
	rehash();
	if (l->isConstant(lc)) {
		if (lc == 0)
			return l;
		if (lc == 1)
			return r;
		if (r->isConstant(rc))
			return CrashExpressionConst::get(lc * rc);
	}

	return this;
}

CrashExpression *
CrashExpressionShl::_simplify(unsigned hardness)
{
	unsigned long lc;
	unsigned long rc;

top:
	l = l->simplify(hardness);
	r = r->simplify(hardness);

	rehash();
	if (l->isConstant(lc)) {
		if (lc == 0)
			return l;
		if (r->isConstant(rc))
			return CrashExpressionConst::get(lc << rc);
	}

	if (r->isConstant(rc) && rc == 0)
		return l;

	if (typeid(l) == typeid(this)) {
		CrashExpressionShl *l2 = dynamic_cast<CrashExpressionShl *>(l);
		r = CrashExpressionAdd::get(l2->r, r);
		l = l2->l;
		goto top;
	}

	return this;
}

CrashExpression *
CrashExpressionUnsignedLessThan::_simplify(unsigned hardness)
{
	l = l->simplify(hardness);
	r = r->simplify(hardness);
	rehash();
	unsigned long lc, rc;
	if (l->isConstant(lc) && r->isConstant(rc)) {
		if (lc < rc)
			return CrashExpressionConst::get(1);
		else
			return CrashExpressionConst::get(0);
	}
	return this;
}

class CrashExpressionUnary : public CrashExpression {
protected:
	CrashExpressionUnary(CrashExpression *_l)
		: l(_l)
	{
	}
	virtual const char *__mkName() const = 0;
	const char *_mkName() const { return vex_asprintf("(%s %s)", __mkName(), l->name()); }
	void _visit(HeapVisitor &hv) { hv(l); }
	virtual CrashExpression *_simplify(unsigned hardness) {
		l = l->simplify(hardness);
		return this;
	}
public:
	virtual CrashExpression *semiDupe(CrashExpression *e) = 0;
	CrashExpression *l;
	CrashExpression *map(CPMapper &m) {
		CrashExpression *l2 = l->map(m);
		if (l2 == l)
			return m(this);
		else
			return m(semiDupe(l2));
	}
	unsigned complexity() const { return l->complexity() + 1; }
	void build_relevant_address_list(Thread<unsigned long> *thr,
					 MachineState<unsigned long> *ms,
					 std::set<unsigned long> &addresses,
					 const concreteStoresT &stores)
	{
		l->build_relevant_address_list(thr, ms, addresses, stores);
	}
};

#define mk_unop(name, hashop)					\
	class CrashExpression ## name : public CrashExpressionUnary {	\
		CrashExpression ## name (CrashExpression *_l)		\
		: CrashExpressionUnary(_l)				\
		{							\
		}							\
	protected:							\
	const char *__mkName() const { return #name ; }			\
	unsigned long _hash() const {					\
		return hashop l->hash();					\
	}								\
	CrashExpression *_simplify(unsigned hardness);			\
	virtual bool _eq(const CrashExpression *o) const {		\
		const CrashExpression ## name *t =			\
			dynamic_cast<const CrashExpression ## name *>(o); \
		return t && t->l->eq(l);				\
	}								\
	public:								\
	static CrashExpression *get(CrashExpression *l)			\
		{							\
			return intern(new CrashExpression ## name(l))->simplify(); \
		}							\
	CrashExpression *semiDupe(CrashExpression *e)			\
		{							\
			return get(e);					\
		}							\
	unsigned long eval(Thread<unsigned long> *thr,			\
			   MachineState<unsigned long> *ms,		\
			   const concreteStoresT &stores);		\
	};

mk_unop(Neg, -)
mk_unop(Not, 0x7f8ff8ac608cb30d ^)

/* build_relevant_address_list for BadAddr is moderately non-obvious,
   but turns out to be exactly the same as it is for every other unary
   operation.  The relevant addresses are those whose history might
   contain relevant information for producing a fix, and the address
   referenced by the argument of BadAddr has, by definition, no
   history at all.  Addresses referenced in computing the address
   might, however, contain some relevant information, and so we have
   to recur into them as we would for any other operation. */
mk_unop(BadAddr, 76348956389 *)

unsigned long
CrashExpressionNeg::eval(Thread<unsigned long> *thr, MachineState<unsigned long> *ms,
			 const concreteStoresT &stores)
{
	return -l->eval(thr, ms, stores);
}

unsigned long
CrashExpressionNot::eval(Thread<unsigned long> *thr, MachineState<unsigned long> *ms,
			 const concreteStoresT &stores)
{
	return !l->eval(thr, ms, stores);
}

unsigned long
CrashExpressionBadAddr::eval(Thread<unsigned long> *thr, MachineState<unsigned long> *ms,
			     const concreteStoresT &stores)
{
	unsigned long a = l->eval(thr, ms, stores);
	if (ms->addressSpace->isAccessible(a, 8, false, thr))
		return 0;
	else
		return 1;
}


static CrashExpression *
replaceFirstAddExpression(CrashExpression *start,
			  CrashExpression *replace_from,
			  CrashExpression *replace_to)
{
	if (start == replace_from)
		return replace_to;

	CrashExpressionAdd *a = dynamic_cast<CrashExpressionAdd *>(start);
	if (a->l == replace_from)
		return a->semiDupe(replace_to, a->r);
	if (a->r == replace_from)
		return a->semiDupe(a->l, replace_to);
	return a->semiDupe(a->l, replaceFirstAddExpression(a->r, replace_from, replace_to));
}

CrashExpression *						
CrashExpressionAdd::_simplify(unsigned hardness)			
{								
	unsigned long lc;					
	unsigned long rc;					
	
top:								
	l = l->simplify(hardness);				
	r = r->simplify(hardness);				
	if (l->complexity() > r->complexity()) {		
		CrashExpression *t;				
		t = l;						
		l = r;						
		r = t;						
	}							
	
	rehash();						

	CrashExpressionAdd *r2 =			
		dynamic_cast<CrashExpressionAdd *>(r); 
	if (l->isConstant(lc)) {				
		if (lc == 0)					
			return r;				
		if (r->isConstant(rc))				
			return CrashExpressionConst::get(lc + rc); 
		if (r2 && r2->l->isConstant(rc)) {
			l = CrashExpressionConst::get(lc + rc);
			r = r2->r;
			goto top;
		}
	}							

	if (r2 && l->complexity() > r2->l->complexity()) {
		r = get(l, r2->r);
		l = r2->l;
		goto top;				
	}						
									
	CrashExpressionAdd *l2 =				
		dynamic_cast<CrashExpressionAdd *>(l);	
	if (l2) {						
		r = semiDupe(l2->r, r);				
		l = l2->l;					
		goto top;					
	}							

	if (hardness > 5) {
		CrashExpression *nr = CrashExpressionNeg::get(r);
		CrashExpression *c =
			CrashExpressionEqual::get(l, nr)->simplify(hardness);
		if (c->isTrue())
			return CrashExpressionConst::get(0);
	}
	if (hardness > 10) {
		/* Walk the chain of expressions to the right and see
		   if we find something which can cancel with the
		   thing on the left. */
		CrashExpression *r2 = r;
		while (1) {
			CrashExpressionAdd *r2a = dynamic_cast<CrashExpressionAdd *>(r2);
			if (!r2a)
				break;
			if (CrashExpressionEqual::get(
				    l,
				    CrashExpressionNeg::get(r2))->simplify(hardness)->isTrue()) {
				return replaceFirstAddExpression(
					r, r2, r2a->l)->simplify(hardness);
			}
			if (CrashExpressionEqual::get(
				    l,
				    CrashExpressionNeg::get(r2a->l))->simplify(hardness)->isTrue()) {
				return replaceFirstAddExpression(
					r, r2, r2a->r)->simplify(hardness);
			}
			r2 = r2a->r;
		}
	}
	return this;						
}

CrashExpression *
CrashExpressionNeg::_simplify(unsigned hardness)
{
	l = l->simplify(hardness);
	rehash();
	unsigned long lc;
	if (l->isConstant(lc))
		return CrashExpressionConst::get(-lc);
	if (typeid(l) == typeid(this)) {
		CrashExpressionNeg *nn = dynamic_cast<CrashExpressionNeg *>(l);
		return nn->l;
	}
	if (CrashExpressionAdd *cea = dynamic_cast<CrashExpressionAdd *>(l))
		return CrashExpressionAdd::get(get(cea->l), get(cea->r))->simplify(hardness);
	if (CrashExpressionNeg *cn = dynamic_cast<CrashExpressionNeg *>(l))
		return cn->l;
	return this;
}

CrashExpression *
CrashExpressionNot::_simplify(unsigned hardness)
{
	l = l->simplify(hardness);
	rehash();
	unsigned long lc;
	if (l->isConstant(lc))
		return CrashExpressionConst::get(!lc);
	return this;
}

CrashExpression *
CrashExpressionBadAddr::_simplify(unsigned hardness)
{
	l = l->simplify(hardness);
	rehash();
	return this;
}

class CrashExpressionBitwiseNot  {
public:
	static CrashExpression *get(CrashExpression *l) {
		return CrashExpressionAdd::get(
			CrashExpressionNeg::get(l),
			CrashExpressionConst::get(1));
	}
};

class CrashExpressionStackPtr : public CrashExpressionUnary {
	CrashExpressionStackPtr(CrashExpression *_l)
		: CrashExpressionUnary(_l)
	{
	}
protected:
	const char *__mkName() const { return "stack"; }
	unsigned long _hash() const {
		return l->hash() + 0xf2851c4acf19336b;
	}
	CrashExpression *_simplify(unsigned hardness)
	{
		l = l->simplify(hardness);
		rehash();
		if (l->pointsAtStack())
			return l;
		if (CrashExpressionBinop *b = dynamic_cast<CrashExpressionBinop *>(l)) {
			if (b->l->isConstant())
				return b->semiDupe(b->l, get(b->r)->simplify(hardness))->simplify(hardness);
		}
		return this;
	}
	virtual bool _eq(const CrashExpression *o) const {		
		const CrashExpressionStackPtr *t =			
			dynamic_cast<const CrashExpressionStackPtr *>(o); 
		return t && t->l->eq(l);				
	}								
public:
	static CrashExpression *get(CrashExpression *l)
	{
		if (l->pointsAtStack())
			return l;
		else
			return intern(new CrashExpressionStackPtr(l))->simplify();
	}
	bool pointsAtStack() const { return true; }
	CrashExpression *semiDupe(CrashExpression *l) {
		return get(l);
	}
	unsigned long eval(Thread<unsigned long> *thr, MachineState<unsigned long> *ms,
			   const concreteStoresT &stores) {
		return l->eval(thr, ms, stores);
	}
};

class CrashExpressionWiden : public CrashExpressionUnary {
	CrashExpressionWiden(CrashExpression *_l, int _start, int _end)
		: CrashExpressionUnary(_l), start(_start), end(_end)
	{
	}
protected:
	const char *__mkName() const { return vex_asprintf("widen%d:%d", start, end); }
	bool _eq(const CrashExpression *o) const {
		const CrashExpressionWiden *t =
			dynamic_cast<const CrashExpressionWiden *>(o);
		if (t)
			return t->start == start && t->end == end && t->l->eq(l);
		else
			return false;
	}
	unsigned long _hash() const {
		return l->hash() + 0xc6c02675a5903f75;
	}
public:
	int start;
	int end;
	static CrashExpression *get(CrashExpression *l, int start, int end)
	{
		return intern(new CrashExpressionWiden(l, start, end))->simplify();
	}
	unsigned complexity() const { return l->complexity() + 1; }
	CrashExpression *semiDupe(CrashExpression *l) {
		return get(l, start, end);
	}
	unsigned long eval(Thread<unsigned long> *thr, MachineState<unsigned long> *ms,
			   const concreteStoresT &stores) {
		long a = l->eval(thr, ms, stores);
		a <<= 64 - start;
		a >>= 64 - start;
		if (end != 64)
			a &= (1 << end) - 1;
		return a;
	}
};

class CrashExpressionCondition : public CrashExpression {
	CrashExpressionCondition(CrashExpression *_a,
				 CrashExpression *_b,
				 CrashExpression *_c,
				 CrashExpression *_d,
				 CrashExpression *_e)
		: a(_a), b(_b), c(_c), d(_d), e(_e)
	{
	}
protected:
	const char *_mkName() const { return vex_asprintf("conditions(%s, %s, %s, %s, %s)",
							  a->name(),
							  b->name(),
							  c->name(),
							  d->name(),
							  e->name()); }
	void _visit(HeapVisitor &hv) {
		hv(a);
		hv(b);
		hv(c);
		hv(d);
		hv(e);
	}
	bool _eq(const CrashExpression *o) const {
		const CrashExpressionCondition *t =
			dynamic_cast<const CrashExpressionCondition *>(o);
		if (t)
			return t->a->eq(a) &&
				t->b->eq(b) &&
				t->c->eq(c) &&
				t->d->eq(d) &&
				t->e->eq(e);
		else
			return false;
	}
	unsigned long _hash() const {
		return (a->hash() * 23741) ^
			(b->hash() * 25541) ^
			(c->hash() * 26713) ^
			(d->hash() * 28547) ^
			(e->hash() * 30323);
	}
	CrashExpression *_simplify(unsigned hardness);
public:
	CrashExpression *a, *b, *c, *d, *e;
	static CrashExpression *get(CrashExpression *a,
				    CrashExpression *b,
				    CrashExpression *c,
				    CrashExpression *d,
				    CrashExpression *e)
	{
		return intern(new CrashExpressionCondition(a, b, c, d, e))->simplify();
	}
	CrashExpression *map(CPMapper &m) {
		CrashExpression *a2 = a->map(m);
		CrashExpression *b2 = b->map(m);
		CrashExpression *c2 = c->map(m);
		CrashExpression *d2 = d->map(m);
		CrashExpression *e2 = e->map(m);
		if (a2 == a && b2 == b && c2 == c && d2 == d && e2 == e)
			return m(this);
		else
			return m(get(a2, b2, c2, d2, e2));
	}
	unsigned complexity() const {
		return a->complexity() +
			b->complexity() + 
			c->complexity() + 
			d->complexity() + 
			e->complexity();
	}
	unsigned long eval(Thread<unsigned long> *thr, MachineState<unsigned long> *ms,
			   const concreteStoresT &stores)
	{
		/* If the simplifier doesn't know what to do with
		   this, we're pretty much boned. */
		abort();
	}
	void build_relevant_address_list(Thread<unsigned long> *thr,
					 MachineState<unsigned long> *ms,
					 std::set<unsigned long> &addresses,
					 const concreteStoresT &stores)
	{
		a->build_relevant_address_list(thr, ms, addresses, stores);
		b->build_relevant_address_list(thr, ms, addresses, stores);
		c->build_relevant_address_list(thr, ms, addresses, stores);
		d->build_relevant_address_list(thr, ms, addresses, stores);
		e->build_relevant_address_list(thr, ms, addresses, stores);
	}
};

class CrashExpressionRflags : public CrashExpression {
	CrashExpressionRflags(CrashExpression *_a,
			      CrashExpression *_b,
			      CrashExpression *_c,
			      CrashExpression *_d)
		: a(_a), b(_b), c(_c), d(_d)
	{
	}
protected:
	const char *_mkName() const { return vex_asprintf("rflags(%s, %s, %s, %s)",
							  a->name(),
							  b->name(),
							  c->name(),
							  d->name()); }
	void _visit(HeapVisitor &hv) {
		hv(a);
		hv(b);
		hv(c);
		hv(d);
	}
	bool _eq(const CrashExpression *o) const {
		const CrashExpressionRflags *t =
			dynamic_cast<const CrashExpressionRflags *>(o);
		if (t)
			return t->a->eq(a) &&
				t->b->eq(b) &&
				t->c->eq(c) &&
				t->d->eq(d);
		else
			return false;
	}
	unsigned long _hash() const {
		return (a->hash() * 9619) ^
			(b->hash() * 13487) ^
			(c->hash() * 17443) ^
			(d->hash() * 23189);
	}
	CrashExpression *_simplify(unsigned hardness) {
		a = a->simplify(hardness);
		b = b->simplify(hardness);
		c = c->simplify(hardness);
		d = d->simplify(hardness);
		return this;
	}
public:
	CrashExpression *a, *b, *c, *d;
	static CrashExpression *get(CrashExpression *a,
				    CrashExpression *b,
				    CrashExpression *c,
				    CrashExpression *d)
	{
		return intern(new CrashExpressionRflags(a, b, c, d))->simplify();
	}
	CrashExpression *map(CPMapper &m) {
		CrashExpression *a2 = a->map(m);
		CrashExpression *b2 = b->map(m);
		CrashExpression *c2 = c->map(m);
		CrashExpression *d2 = d->map(m);
		if (a2 == a && b2 == b && c2 == c && d2 == d)
			return m(this);
		else
			return m(get(a2, b2, c2, d2));
	}
	unsigned complexity() const {
		return a->complexity() +
			b->complexity() + 
			c->complexity() + 
			d->complexity();
	}
	unsigned long eval(Thread<unsigned long> *thr, MachineState<unsigned long> *ms,
			   const concreteStoresT &stores)
	{
		/* If the simplifier doesn't know what to do with
		   this, we're pretty much boned. */
		abort();
	}
	void build_relevant_address_list(Thread<unsigned long> *thr,
					 MachineState<unsigned long> *ms,
					 std::set<unsigned long> &addresses,
					 const concreteStoresT &stores)
	{
		a->build_relevant_address_list(thr, ms, addresses, stores);
		b->build_relevant_address_list(thr, ms, addresses, stores);
		c->build_relevant_address_list(thr, ms, addresses, stores);
		d->build_relevant_address_list(thr, ms, addresses, stores);
	}
};

class CrashExpressionMux : public CrashExpression {
	CrashExpressionMux(CrashExpression *_cond,
			   CrashExpression *_zero,
			   CrashExpression *_nzero)
		: cond(_cond), zero(_zero), nzero(_nzero)
	{
	}
protected:
	const char *_mkName() const { return vex_asprintf("mux0x(%s, %s, %s)",
							  cond->name(),
							  zero->name(),
							  nzero->name()); }
	void _visit(HeapVisitor &hv) {
		hv(cond);
		hv(zero);
		hv(nzero);
	}
	bool _eq(const CrashExpression *o) const {
		const CrashExpressionMux *t =
			dynamic_cast<const CrashExpressionMux *>(o);
		if (t)
			return t->cond->eq(cond) &&
				t->zero->eq(zero) &&
				t->nzero->eq(nzero);
		else
			return false;
	}
	unsigned long _hash() const {
		return (cond->hash() * 32203) ^
			(zero->hash() * 33889) ^
			(nzero->hash() * 35837);
	}
	CrashExpression *_simplify(unsigned hardness) {
		cond = cond->simplify(hardness);
		zero = zero->simplify(hardness);
		nzero = nzero->simplify(hardness);
		return this;
	}
public:
	CrashExpression *cond, *zero, *nzero;
	static CrashExpression *get(CrashExpression *cond,
				    CrashExpression *zero,
				    CrashExpression *nzero)
	{
		return intern(new CrashExpressionMux(cond, zero, nzero))->simplify();
	}
	CrashExpression *map(CPMapper &m) {
		CrashExpression *cond2 = cond->map(m);
		CrashExpression *zero2 = zero->map(m);
		CrashExpression *nzero2 = nzero->map(m);
		if (cond2 == cond && zero2 == zero && nzero2 == nzero)
			return m(this);
		else
			return m(get(cond2, zero2, nzero2));
	}
	unsigned complexity() const {
		return cond->complexity() +
			zero->complexity() + 
			nzero->complexity();
	}
	unsigned long eval(Thread<unsigned long> *thr, MachineState<unsigned long> *ms,
			   const concreteStoresT &stores)
	{
		if (cond->eval(thr, ms, stores) == 0)
			return zero->eval(thr, ms, stores);
		else
			return nzero->eval(thr, ms, stores);
	}
	void build_relevant_address_list(Thread<unsigned long> *thr,
					 MachineState<unsigned long> *ms,
					 std::set<unsigned long> &addresses,
					 const concreteStoresT &stores)
	{
		cond->build_relevant_address_list(thr, ms, addresses, stores);
		zero->build_relevant_address_list(thr, ms, addresses, stores);
		nzero->build_relevant_address_list(thr, ms, addresses, stores);
	}
};

class CrashExpressionNotEqual {
public:
	static CrashExpression *get(CrashExpression *l, CrashExpression *r) {
		return
			CrashExpressionAnd::get(
				CrashExpressionNot::get(
					CrashExpressionEqual::get(l, r)),
				CrashExpressionConst::get(1));
	}
};

/* A crash machine is intended to be an abstraction of a program,
   starting from a particular RIP, which attempts to capture the
   details of why it's going to crash in a particular way.  It's a
   very simple, non-Turing complete, programming language.  Programs
   are essentially DAGs.  Interior nodes indicate control-flow
   expressions.  Leaf nodes have some condition attached to them, and
   we crash if we get to that node and the condition turns out to be
   true.  Edges are annotated with sequences of stores, which tells
   you what memory stores you'll make while going down that edge.

   Major complication: all of the expressions are evaluates with
   respect to registers at the *start* of the program.

   Note that the machine is a DAG i.e. it cannot contain cycles.  This
   limits the expressivity quite a bit, but also makes it much easier
   to analyse.

   We also restrict things in that internal nodes have at most two
   successors.  If we ever need more than that then we'll have to
   factor them.

   There are also stub nodes in the graph, which just indicate that we
   don't really know what happens there yet.  That can be either
   because we've not run the analysis yet, or because we can't (e.g
   indirect branch).
*/
class CrashMachineNode : public GarbageCollected<CrashMachineNode>, public Named {
	class RewriteTmpMapper : public CPMapper {
		IRTemp tmp;
		CrashExpression *e;
	public:
		RewriteTmpMapper(IRTemp _tmp, CrashExpression *_e)
			: tmp(_tmp), e(_e)
		{
		}
		CrashExpression *operator()(CrashExpression *ce) {
			if (CrashExpressionTemp *cet =
			    dynamic_cast<CrashExpressionTemp *>(ce)) {
                               if (cet->tmp == tmp)
                                       return e;
			}
			return ce;
		}
	};
	class RewriteRegisterMapper : public CPMapper {
		Int offset;
		CrashExpression *e;
	public:
		RewriteRegisterMapper(Int _offset, CrashExpression *_e)
			: offset(_offset), e(_e)
		{
		}
		CrashExpression *operator()(CrashExpression *ce) {
			if (CrashExpressionRegister *cet =
			    dynamic_cast<CrashExpressionRegister *>(ce)) {
				if (cet->offset == offset)
                                       return e;
			}
			return ce;
		}
	};
	class ResolveLoadsMapper : public CPMapper {
		std::map<unsigned long, unsigned long> &memory;
		MachineState<unsigned long> *ms;
		concreteStoresT &stores;
	public:
		ResolveLoadsMapper(std::map<unsigned long, unsigned long> &_memory,
				   MachineState<unsigned long> *_ms,
				   concreteStoresT &_stores)
			: memory(_memory), ms(_ms), stores(_stores)
		{
		}
		CrashExpression *operator()(CrashExpression *ce) {
			CrashExpressionLoad *cel =
				dynamic_cast<CrashExpressionLoad *>(ce);
			unsigned long addr;
			CrashExpression *ce2;
			if (!cel) {
				CrashExpressionBadAddr *ceba =
					dynamic_cast<CrashExpressionBadAddr *>(ce);
				if (!ceba)
					return ce;
				if (!ceba->l->isConstant(addr)) {
					ce2 = ce->simplify(1000);
					if (ce2 != ce)
						return ce2->map(*this);
					else
						return ce;
				}
				if (ms->addressSpace->isReadable(addr, 8))
					return CrashExpressionConst::get(0);
				else
					return CrashExpressionConst::get(1);
			}
			if (!cel->addr->isConstant(addr)) {
				CrashExpression *ce2 = ce->simplify(1000);
				if (ce != ce2)
					return ce2->map(*this);
				else
					return ce;
			}
			for (concreteStoresT::reverse_iterator it = stores.rbegin();
			     it != stores.rend();
			     it++) {
				if (addr == it->addr)
					return CrashExpressionConst::get(it->value);
			}
			if (memory.count(addr) != 0)
				return CrashExpressionConst::get(memory[addr]);
			return ce;
		}
	};

protected:
	char *mkName() const {
		char *buf = my_asprintf("<%lx> ", origin_rip);
#if 0
		for (abstractStoresT::const_iterator it = stores.begin();
		     it != stores.end();
		     it++) {
			char *b2 = my_asprintf("%s*(%s) = %s;",
					       buf,
					       it->addr->name(),
					       it->data->name());
			free(buf);
			buf = b2;
		}
#endif
		char *b2;
		switch (type) {
		case CM_NODE_LEAF:
			b2 = my_asprintf("%sleaf{%s}", buf, leafCond->name());
			break;
		case CM_NODE_STUB:
			b2 = my_asprintf("%sstub", buf);
			break;
		case CM_NODE_BRANCH:
			b2 = my_asprintf("%sbranch{%s, %s, %s}",
					 buf,
					 branchCond->name(),
					 trueTarget ? trueTarget->name() : "(null)",
					 falseTarget ? falseTarget->name() : "(null)");
			break;
		default:
			abort();
		}
		free(buf);
		return b2;
	}

public:
	abstractStoresT stores;

	CrashMachineNode(unsigned long _origin_rip,
			 CrashExpression *e,
			 const abstractStoresT &_stores)
		: stores(_stores),
		  origin_rip(_origin_rip),
		  type(CM_NODE_LEAF),
		  leafCond(e)
	{
	}
	CrashMachineNode(unsigned long _origin_rip,
			 const abstractStoresT &_stores)
		: stores(_stores),
		  origin_rip(_origin_rip),
		  type(CM_NODE_STUB)
	{
	}
	CrashMachineNode(unsigned long _origin_rip,
			 CrashExpression *_branchCond,
			 CrashMachineNode *_trueTarget,
			 CrashMachineNode *_falseTarget,
			 const abstractStoresT &_stores)
		: stores(_stores),
		  origin_rip(_origin_rip),
		  type(CM_NODE_BRANCH),
		  branchCond(_branchCond),
		  trueTarget(_trueTarget),
		  falseTarget(_falseTarget)
	{
		sanity_check();
	}

	bool isStubFree() const {
		switch (type) {
		case CM_NODE_LEAF:
			return true;
		case CM_NODE_STUB:
			return false;
		case CM_NODE_BRANCH:
			if (trueTarget && !trueTarget->isStubFree())
				return false;
			if (falseTarget && !falseTarget->isStubFree())
				return false;
			return true;
		}
		abort();
	}

	void sanity_check() {
#if 0
		switch (type) {
		case CM_NODE_LEAF:
		case CM_NODE_STUB:
			return;
		case CM_NODE_BRANCH:
			assert(trueTarget || falseTarget);
			if (trueTarget) {
				trueTarget->sanity_check();
			}
			if (falseTarget) {
				falseTarget->sanity_check();
			}
			return;
		}
		abort();
#endif
	}

	/* Where was the instruction which caused us to generate this
	   node?  Mostly a debug aid, except for STUB nodes, where it
	   tells you what instruction we're a stub for. */
	unsigned long origin_rip;

	enum { CM_NODE_LEAF = 52, CM_NODE_BRANCH, CM_NODE_STUB } type;

	/* Crash condition for leaf nodes */
	CrashExpression *leafCond;

	/* Internal binary branches.  branchCond might be constant, in
	   which case only one of the targets will relevant (and the
	   other might well be NULL). */
	CrashExpression *branchCond;
	CrashMachineNode *trueTarget;
	CrashMachineNode *falseTarget;

	CrashMachineNode *map(CPMapper &m)
	{
		CrashMachineNode *res;
		abstractStoresT newStores;
		bool forceNew = false;
		for (abstractStoresT::iterator it = stores.begin();
		     it != stores.end();
		     it++) {
			CrashExpression *a = it->addr->map(m);
			CrashExpression *d = it->data->map(m);
			if (a != it->addr || d != it->data)
				forceNew = true;
			newStores.push_back(abstract_store(a, d));
		}
		switch (type) {
		case CM_NODE_LEAF: {
			CrashExpression *l = leafCond->map(m);
			if (l == leafCond && !forceNew)
				return this;
			res = new CrashMachineNode(origin_rip, l, newStores);
			break;
		}
		case CM_NODE_BRANCH: {
			CrashExpression *c = branchCond->map(m);
			CrashMachineNode *t = trueTarget ? trueTarget->map(m) : NULL;
			CrashMachineNode *f = falseTarget ? falseTarget->map(m) : NULL;
			if (c == branchCond && t == trueTarget &&
			    f == falseTarget && !forceNew)
				return this;
			res = new CrashMachineNode(origin_rip, c, t, f, newStores);
			break;
		}
		case CM_NODE_STUB: {
			if (!forceNew)
				return this;
			res = new CrashMachineNode(origin_rip, newStores);
			break;
		}
		default:
			abort();
		}
		res->sanity_check();
		return res;
	}
	CrashMachineNode *rewriteTemporary(IRTemp tmp,
					   CrashExpression *ce)
	{
		RewriteTmpMapper rtm(tmp, ce);
		return map(rtm);
	}
	CrashMachineNode *rewriteRegister(unsigned offset,
					  CrashExpression *ce)
	{
		RewriteRegisterMapper rrm(offset, ce);
		return map(rrm);
	}
	/* ms is used to resolve badAddr expressions */
	CrashMachineNode *resolveLoads(std::map<unsigned long, unsigned long> &memory,
				       MachineState<unsigned long> *ms,
				       concreteStoresT &stores);
	CrashMachineNode *resolveLoads(std::map<unsigned long, unsigned long> &memory,
				       MachineState<unsigned long> *ms)
	{
		concreteStoresT stores;
		return resolveLoads(memory, ms, stores);
	}

	bool willDefinitelyCrash()
	{
		if (type == CM_NODE_LEAF) {
			unsigned long v;
			if (leafCond->isConstant(v) && v)
				return true;
		}
		return false;
	}

	bool willDefinitelyNotCrash()
	{
		if (type == CM_NODE_LEAF) {
			unsigned long v;
			if (leafCond->isConstant(v) && !v)
				return true;
		}
		return false;
	}

	void build_relevant_address_list(Thread<unsigned long> *thr,
					 MachineState<unsigned long> *ms,
					 std::set<unsigned long> &addresses,
					 concreteStoresT &stores);

	void changed() { clearName(); }
	void visit(HeapVisitor &hv) {
		for (abstractStoresT::iterator it = stores.begin();
		     it != stores.end();
		     it++) {
			hv(it->addr);
			hv(it->data);
		}
		switch (type) {
		case CM_NODE_LEAF:
			hv(leafCond);
			break;
		case CM_NODE_BRANCH:
			hv(branchCond);
			hv(trueTarget);
			hv(falseTarget);
			break;
		case CM_NODE_STUB:
			break;
		}
	}
	NAMED_CLASS
};

class CrashMachine : public GarbageCollected<CrashMachine> {
	friend class CRAEventRecorder;

	static void visit_content_fn(std::pair<CrashMachineNode *,
				             std::set<unsigned long> > &v,
				     HeapVisitor &hv)
	{
		hv(v.first);
	}

	void calc_relevant_addresses_snapshot(Thread<unsigned long> *ts,
					      MachineState<unsigned long> *ms);
public:
	typedef gc_map<CrashTimestamp,
		       std::pair<CrashMachineNode *, std::set<unsigned long> >,
		       __default_hash_function<CrashTimestamp>,
		       __default_eq_function<CrashTimestamp>,
		       visit_content_fn> contentT;
	contentT *content;

	CrashMachine() : content(new contentT()) {}

	bool hasKey(const CrashTimestamp &ts) { return content->hasKey(ts); }
	CrashMachineNode *get(const CrashTimestamp &ts) {
		/* We know where abort() and raise() live */
		if ((ts.rip >= 0x50a6a40 && ts.rip <= 0x50a6c7a) ||
		    (ts.rip >= 0x50a4f80 && ts.rip <= 0x50a4ff7)) {
			return new CrashMachineNode(
				ts.rip,
				CrashExpressionConst::get(1),
				abstractStoresT());
		}
		return content->get(ts).first;
	}
	void set(const CrashTimestamp &ts, CrashMachineNode *cmn)
	{
		std::set<unsigned long> t;
		content->set(ts,
			     std::pair<CrashMachineNode *, std::set<unsigned long> >
			     (cmn, t));
	}

	void calculate_relevant_addresses(VexPtr<MachineState<unsigned long> > &ms,
					  VexPtr<LogReader<unsigned long> > &lr,
					  LogReaderPtr ptr,
					  GarbageCollectionToken tok);

	void visit(HeapVisitor &hv) { hv(content); }
	void destruct() { this->~CrashMachine(); }
	NAMED_CLASS
};

CrashMachineNode *
CrashMachineNode::resolveLoads(std::map<unsigned long, unsigned long> &memory,
			       MachineState<unsigned long> *ms,
			       concreteStoresT &concrete_stores)
{
	ResolveLoadsMapper rlm(memory, ms, concrete_stores);
	abstractStoresT newAbsStores;
	CrashMachineNode *res;

	unsigned sz = concrete_stores.size();
	for (abstractStoresT::iterator it = stores.begin();
	     it != stores.end();
	     it++) {
		CrashExpression *addr = it->addr->map(rlm);
		CrashExpression *data = it->data->map(rlm);
		newAbsStores.push_back(abstract_store(addr, data));
		unsigned long concreteAddr, concreteData;
		if (addr->isConstant(concreteAddr) &&
		    data->isConstant(concreteData)) {
			concrete_stores.push_back(
				concrete_store(concreteAddr, concreteData));
		}
	}
	unsigned sz2 = concrete_stores.size();

	switch (type) {
	case CM_NODE_LEAF:
		res = new CrashMachineNode(origin_rip,
					   leafCond->map(rlm), newAbsStores);
		break;
	case CM_NODE_BRANCH: {
		CrashExpression *b = branchCond->map(rlm);
		CrashMachineNode *t = NULL;
		CrashMachineNode *f = NULL;
		if (trueTarget) {
			t = trueTarget->resolveLoads(memory, ms, concrete_stores);
			assert(concrete_stores.size() == sz2);
		}
		if (falseTarget) {
			f = falseTarget->resolveLoads(memory, ms, concrete_stores);
			assert(concrete_stores.size() == sz2);
		}
		res = new CrashMachineNode(origin_rip,
					   b, t, f, newAbsStores);
		break;
	}
	case CM_NODE_STUB:
		res = new CrashMachineNode(origin_rip, newAbsStores);
		break;
	default:
		abort();
	}

	assert(concrete_stores.size() == sz2);
	(void)sz2;
	concrete_stores.resize(sz);
	return res;
}

void
CrashMachineNode::build_relevant_address_list(Thread<unsigned long> *thr,
					      MachineState<unsigned long> *ms,
					      std::set<unsigned long> &addresses,
					      concreteStoresT &concrete_stores)
{
	switch (type) {
	case CM_NODE_LEAF:
		leafCond->build_relevant_address_list(thr, ms, addresses, concrete_stores);
		return;
	case CM_NODE_BRANCH: {
		unsigned sz = concrete_stores.size();
		for (abstractStoresT::iterator it = stores.begin();
		     it != stores.end();
		     it++)
			concrete_stores.push_back(
				concrete_store(
					it->addr->eval(thr, ms, concrete_stores),
					it->data->eval(thr, ms, concrete_stores)));
		unsigned sz2 = concrete_stores.size();
		branchCond->build_relevant_address_list(thr, ms, addresses, concrete_stores);
		if (trueTarget) {
			trueTarget->build_relevant_address_list(thr, ms, addresses,
								concrete_stores);
			assert(concrete_stores.size() == sz2);
		}
		if (falseTarget) {
			falseTarget->build_relevant_address_list(thr, ms, addresses,
								 concrete_stores);
			assert(concrete_stores.size() == sz2);
		}
		(void)sz2;
		concrete_stores.resize(sz);
		return;
	}
	case CM_NODE_STUB:
		return;
	}
	abort();
}

void
CrashMachine::calc_relevant_addresses_snapshot(Thread<unsigned long> *thr,
					       MachineState<unsigned long> *ms)
{
	CrashTimestamp ts(thr->tid, thr->regs.rip(), thr->currentCallStack);
	std::pair<CrashMachineNode *, std::set<unsigned long> >
		&slot(content->get(ts));

	/* We're only interested in the results of the *last*
	   execution of this instruction */
	slot.second.clear();

	/* Do it. */
	concreteStoresT concreteStores;
	slot.first->build_relevant_address_list(thr, ms, slot.second, concreteStores);
	assert(concreteStores.size() == 0);
}

class CRAEventRecorder : public EventRecorder<unsigned long> {
protected:
	void record(Thread<unsigned long> *thr, ThreadEvent<unsigned long> *evt) {
		abort();
	}
public:
	CrashMachine *cm;
	CRAEventRecorder(CrashMachine *_cm) : cm(_cm) {}
	void record(Thread<unsigned long> *thr, ThreadEvent<unsigned long> *evt,
		    MachineState<unsigned long> *ms)
	{
		if (InstructionEvent<unsigned long> *ie =
		    dynamic_cast<InstructionEvent<unsigned long> *>(evt)) {
#if 0 /* Stop emacs getting confused by putting in a redundant { */
		{
#endif
			CrashTimestamp ts(thr);
			ts.rip = ie->rip;
			if (cm->hasKey(ts))
				cm->calc_relevant_addresses_snapshot(thr, ms);
		}
	}
	void visit(HeapVisitor &hv) { hv(cm); }
};

void
CrashMachine::calculate_relevant_addresses(VexPtr<MachineState<unsigned long> > &ms,
					   VexPtr<LogReader<unsigned long> > &lr,
					   LogReaderPtr ptr,
					   GarbageCollectionToken tok)
{
	VexPtr<EventRecorder<unsigned long> > craer(new CRAEventRecorder(this));
	Interpreter<unsigned long> i(ms->dupeSelf());
	VexPtr<LogWriter<unsigned long> > dummy(NULL);
	i.replayLogfile(lr, ptr, tok, NULL, dummy, craer);
}

CrashExpression *
CrashExpressionEqual::_simplify(unsigned hardness)
{
	unsigned long lc;
	unsigned long rc;

	l = l->simplify(hardness);
	r = r->simplify(hardness);
	if (l->complexity() > r->complexity()) {
		CrashExpression *t;
		t = l;
		l = r;
		r = t;
		rehash();
	}

	rehash();

	if (l->isConstant(lc) &&
	    r->isConstant(rc))
		return CrashExpressionConst::get(lc == rc);

	if (hardness > 1 && l->eq(r))
		return CrashExpressionConst::get(1);

	if (l->isConstant(lc)) {
		CrashExpressionAdd *ra =
			dynamic_cast<CrashExpressionAdd *>(r);
		if (ra && ra->l->isConstant(rc))
			return get(CrashExpressionConst::get(lc - rc),
				   ra->r)->simplify(hardness);
	}
	return this;
}

CrashExpression *
CrashExpressionCondition::_simplify(unsigned hardness)
{
	unsigned long cond;
	unsigned long op;

	a = a->simplify(hardness);
	b = b->simplify(hardness);
	c = c->simplify(hardness);
	d = d->simplify(hardness);
	e = e->simplify(hardness);

	rehash();

	if (!a->isConstant(cond) ||
	    !b->isConstant(op))
		return this;

	switch (cond) {
	case AMD64CondB:
		switch (op) {
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBW:
		case AMD64G_CC_OP_SUBL:
		case AMD64G_CC_OP_SUBQ:
			return CrashExpressionUnsignedLessThan::get(c, d);
		default:
			return this;
		}

	case AMD64CondZ:
		switch (op) {
		case AMD64G_CC_OP_LOGICB:
		case AMD64G_CC_OP_LOGICW:
		case AMD64G_CC_OP_LOGICL:
		case AMD64G_CC_OP_LOGICQ:
		case AMD64G_CC_OP_DECB:
		case AMD64G_CC_OP_DECW:
		case AMD64G_CC_OP_DECL:
		case AMD64G_CC_OP_DECQ:
			return CrashExpressionEqual::get(c, CrashExpressionConst::get(0))->simplify(hardness);
		case AMD64G_CC_OP_ADDB:
		case AMD64G_CC_OP_ADDW:
		case AMD64G_CC_OP_ADDL:
		case AMD64G_CC_OP_ADDQ:
			return CrashExpressionEqual::get(c, CrashExpressionNeg::get(d))->simplify(hardness);
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBW:
		case AMD64G_CC_OP_SUBL:
		case AMD64G_CC_OP_SUBQ:
			return CrashExpressionEqual::get(c, d)->simplify(hardness);
		default:
			return this;
		}

	case AMD64CondS:
		switch (op) {
		case AMD64G_CC_OP_SUBB:
		case AMD64G_CC_OP_SUBW:
		case AMD64G_CC_OP_SUBL:
		case AMD64G_CC_OP_SUBQ:
			return CrashExpressionSignedLessThan::get(c, d);
		case AMD64G_CC_OP_LOGICB:
		case AMD64G_CC_OP_LOGICW:
		case AMD64G_CC_OP_LOGICL:
		case AMD64G_CC_OP_LOGICQ:
			return CrashExpressionSignedLessThan::get(
				c,
				CrashExpressionConst::get(0));
		default:
			return this;
		}

	case AMD64CondLE:
		switch (op) {
		case AMD64G_CC_OP_LOGICB:
		case AMD64G_CC_OP_LOGICW:
		case AMD64G_CC_OP_LOGICL:
		case AMD64G_CC_OP_LOGICQ:
			return CrashExpressionOr::get(
				CrashExpressionSignedLessThan::get(
					c,
					CrashExpressionConst::get(0)),
				CrashExpressionEqual::get(
					c,
					CrashExpressionConst::get(0)));
		default:
			return this;
		}
	default:
		return this;
	}
}

CrashExpression *
CrashExpression::get(IRExpr *e)
{
	switch (e->tag) {
	case Iex_RdTmp:
		return CrashExpressionTemp::get(e->Iex.RdTmp.tmp);
	case Iex_Get:
		return CrashExpressionRegister::get(e->Iex.Get.offset);
	case Iex_Const:
		return CrashExpressionConst::get(e->Iex.Const.con->Ico.U64);
	case Iex_Binop:
		switch (e->Iex.Binop.op) {
#define do_binop(x, _1, _2)						\
			case Iop_ ## x ## 8:				\
			case Iop_ ## x ## 16:				\
			case Iop_ ## x ## 32:				\
			case Iop_ ## x ## 64:				\
				return CrashExpression ## x ::get(	\
					CrashExpression::get(e->Iex.Binop.arg1), \
					CrashExpression::get(e->Iex.Binop.arg2));
			most_binops(do_binop);
#undef do_binop

		case Iop_CasCmpNE32:
			return CrashExpressionNotEqual::get(
				CrashExpression::get(e->Iex.Binop.arg1),
				CrashExpression::get(e->Iex.Binop.arg2));

		case Iop_Sar8:
		case Iop_Sar16:
		case Iop_Sar32:
		case Iop_Sar64:
			return CrashExpressionShl::get(
				CrashExpression::get(e->Iex.Binop.arg1),
				CrashExpressionNeg::get(
					CrashExpression::get(e->Iex.Binop.arg2)));

		case Iop_Sub8:
		case Iop_Sub16:
		case Iop_Sub32:
		case Iop_Sub64:
			return CrashExpressionAdd::get(
				CrashExpression::get(e->Iex.Binop.arg1),
				CrashExpressionNeg::get(
					CrashExpression::get(e->Iex.Binop.arg2)));

		case Iop_MullS8:
		case Iop_MullS16:
		case Iop_MullS32:
		case Iop_MullS64:
			return CrashExpressionMul::get(
				CrashExpression::get(e->Iex.Binop.arg1),
				CrashExpression::get(e->Iex.Binop.arg2));

		default:
			goto failed;
		}
	case Iex_Unop:
		switch (e->Iex.Unop.op) {
		case Iop_64to1:
		case Iop_64to8:
		case Iop_64to16:
		case Iop_64to32:
		case Iop_1Uto8:                  case Iop_1Uto32:  case Iop_1Uto64:
		                case Iop_8Uto16: case Iop_8Uto32:  case Iop_8Uto64: 
		                                 case Iop_16Uto32: case Iop_16Uto64: 
		                                                   case Iop_32Uto64:
			return CrashExpression::get(e->Iex.Unop.arg);
		case Iop_32Sto64:
			return CrashExpressionWiden::get(
				CrashExpression::get(e->Iex.Unop.arg),
				32,
				64);
		case Iop_64HIto32:
			return CrashExpressionShl::get(
				CrashExpression::get(e->Iex.Unop.arg),
				CrashExpressionConst::get(-32));

		case Iop_Not8:
		case Iop_Not16:
		case Iop_Not32:
		case Iop_Not64:
			return CrashExpressionBitwiseNot::get(
				CrashExpression::get(e->Iex.Unop.arg));
		default:
			goto failed;
		}
	case Iex_CCall:
		if (!strcmp(e->Iex.CCall.cee->name, "amd64g_calculate_condition"))  {
			return CrashExpressionCondition::get(
				CrashExpression::get(e->Iex.CCall.args[0]),
				CrashExpression::get(e->Iex.CCall.args[1]),
				CrashExpression::get(e->Iex.CCall.args[2]),
				CrashExpression::get(e->Iex.CCall.args[3]),
				CrashExpression::get(e->Iex.CCall.args[4]));
		} else if (!strcmp(e->Iex.CCall.cee->name,
				   "amd64g_calculate_rflags_c")) {
			return CrashExpressionCondition::get(
				CrashExpressionConst::get(AMD64CondB),
				CrashExpression::get(e->Iex.CCall.args[0]),
				CrashExpression::get(e->Iex.CCall.args[1]),
				CrashExpression::get(e->Iex.CCall.args[2]),
				CrashExpression::get(e->Iex.CCall.args[3]));
		} else if (!strcmp(e->Iex.CCall.cee->name,
				   "amd64g_calculate_rflags_all")) {
			return CrashExpressionRflags::get(
				CrashExpression::get(e->Iex.CCall.args[0]),
				CrashExpression::get(e->Iex.CCall.args[1]),
				CrashExpression::get(e->Iex.CCall.args[2]),
				CrashExpression::get(e->Iex.CCall.args[3]));
		} else {
			goto failed;
		}
	case Iex_Mux0X:
		return CrashExpressionMux::get(
			CrashExpression::get(e->Iex.Mux0X.cond),
			CrashExpression::get(e->Iex.Mux0X.expr0),
			CrashExpression::get(e->Iex.Mux0X.exprX));
	default:
		goto failed;
	}

failed:
	printf("Failed to translate expression ");
	ppIRExpr(e);
	printf("\n");
	return CrashExpressionFailed::get("expression tag 0x%x op 0x%x",
					  e->tag,
					  e->Iex.Unop.op);
}

static CrashMachineNode *
exprToCrashReason(const CrashTimestamp &when, IRExpr *expr)
{
	return NULL;
}

static CrashMachineNode *
statementToCrashReason(const CrashTimestamp &when, IRStmt *irs)
{
	CrashMachineNode *r;

	switch (irs->tag) {
	case Ist_NoOp:
	case Ist_AbiHint:
	case Ist_MBE:
	default: /* Because I really am that lazy */
	case Ist_IMark:
		return NULL;
	case Ist_Put:
		return exprToCrashReason(when, irs->Ist.Put.data);
	case Ist_PutI:
		r = exprToCrashReason(when, irs->Ist.PutI.data);
		if (!r)
			r = exprToCrashReason(when, irs->Ist.PutI.ix);
		return r;
	case Ist_WrTmp:
		return exprToCrashReason(when, irs->Ist.WrTmp.data);
	case Ist_Store:
		r = exprToCrashReason(when, irs->Ist.Store.addr);
		if (!r)
			r = exprToCrashReason(when, irs->Ist.Store.data);
		if (!r) {
			abstractStoresT stores;
			r = new CrashMachineNode(
				when.rip,
				CrashExpressionBadAddr::get(
					CrashExpression::get(irs->Ist.Store.addr)),
				stores);
		}
		return r;
	case Ist_Dirty:
		if (irs->Ist.Dirty.details->guard) {
			r = exprToCrashReason(when, irs->Ist.Dirty.details->guard);
			if (r)
				return r;
		}
		for (unsigned x = 0;
		     irs->Ist.Dirty.details->args[x];
		     x++) {
			r = exprToCrashReason(when, irs->Ist.Dirty.details->args[x]);
			if (r)
				return r;
		}
		if (!strncmp(irs->Ist.Dirty.details->cee->name,
			     "helper_load_",
			     12)) {
			abstractStoresT stores;
			return new CrashMachineNode(
				when.rip,
				CrashExpressionBadAddr::get(
					CrashExpression::get(irs->Ist.Dirty.details->args[0])),
				stores);
		}
		return NULL;
	}
}

class ResolveLoadsMapper : public CPMapper {
public:
	CrashExpression *data;
	const std::set<CrashTimestamp> &satisfiedLoads;
	ResolveLoadsMapper(CrashExpression *_data,
			   const std::set<CrashTimestamp> &_satisfiedLoads)
		: data(_data), satisfiedLoads(_satisfiedLoads)
	{
	}
	CrashExpression *operator ()(CrashExpression *ce);
};
CrashExpression *
ResolveLoadsMapper::operator()(CrashExpression *ce)
{
	if (CrashExpressionLoad *cel =
	    dynamic_cast<CrashExpressionLoad *>(ce)) {
		if (satisfiedLoads.count(cel->when))
			return data;
	}
	return ce;
}

/* The Oracle is used when static analysis fails us (or I just
   couldn't be bothered to write it properly :)).  It basically allows
   you to make queries against the captured crash in a relatively
   structured way. */
class Oracle {
	typedef std::vector<std::pair<CrashTimestamp, bool> > traceT;
	traceT trace;
	struct memaccess {
		bool is_load;
		CrashTimestamp rip;
		unsigned long addr;
		static memaccess load(const CrashTimestamp &rip, unsigned long addr) {
			memaccess r;
			r.is_load = true;
			r.rip = rip;
			r.addr = addr;
			return r;
		}
		static memaccess store(const CrashTimestamp &rip, unsigned long addr) {
			memaccess r;
			r.is_load = false;
			r.rip = rip;
			r.addr = addr;
			return r;
		}
		memaccess()
			: is_load(0), rip(), addr(99)
		{
		}
	};
	std::vector<memaccess> memlog;
public:
	ThreadId crashingTid;
	std::set<unsigned long> interesting_addresses;
	std::set<unsigned long> constant_addresses;

	/* Note that the RIP trace is in reverse chronological order
	   i.e. it produces things which are nearest the crash
	   first! */
	class RipTraceIterator {
		friend class Oracle;
		traceT::iterator it;
		RipTraceIterator(traceT::iterator _it)
			: it(_it)
		{
		}
	public:
		const CrashTimestamp &operator*() { return it->first; }
		bool operator==(const RipTraceIterator &b) {
			return it == b.it;
		}
		bool operator!=(const RipTraceIterator &b) {
			return !(*this == b);
		}
		void operator++(int i) {
			it++;
		}
	};
	RipTraceIterator begin_rip_trace() { return RipTraceIterator(trace.begin()); }
	RipTraceIterator end_rip_trace() { return RipTraceIterator(trace.end()); }
	void addRipTrace(const CrashTimestamp &rip, bool branchTaken) {
		trace.push_back(std::pair<CrashTimestamp, bool>(rip, branchTaken));
	}

	void load_event(const CrashTimestamp &rip, unsigned long addr) {
		memlog.push_back(memaccess::load(rip, addr));
	}
	void store_event(const CrashTimestamp &rip, unsigned long addr) {
		memlog.push_back(memaccess::store(rip, addr));
	}

	/* Given a RIP, try to make a guess at what the next
	   instruction is likely to be.  Returns 0 if we don't
	   know. */
	bool successorOf(const CrashTimestamp &rip, CrashTimestamp &out) const
	{
		traceT::const_iterator it = trace.begin();
		const CrashTimestamp *succ_rip = &it->first;
		it++;
		while (it != trace.end() && it->first != rip) {
			succ_rip = &it->first;
			it++;
		}
		if (it == trace.end())
			return false;
		out = *succ_rip;
		return true;
	}

	/* Did the dynamic execution include a branch from @first to
	 * @second? */
	bool containsRipEdge(const CrashTimestamp &first, const CrashTimestamp &second) const
	{
		for (traceT::const_iterator oit = trace.begin();
		     oit + 1 != trace.end();
		     oit++) {
			if (oit->first == first &&
			    (oit+1)->first == second)
				return true;
		}
		return false;
	}

	/* Is the branch @rip taken?  Returns true if it is, and @dflt
	 * otherwise.  Also returns @dflt if @rip doesn't contain a
	 * branch. */
	bool branchTaken(const CrashTimestamp &rip, bool dflt) const {
		for (traceT::const_iterator it = trace.begin();
		     it != trace.end();
		     it++) {
			if (it->first == rip)
				return it->second;
		}
		return dflt;
	}

	void findLoadsForStore(const CrashTimestamp &store, std::set<CrashTimestamp> *loads) const;

	void collect_interesting_access_log(
		VexPtr<MachineState<unsigned long> > &ms,
		VexPtr<LogReader<unsigned long> > &lf,
		LogReaderPtr ptr,
		GarbageCollectionToken tok);

	struct address_log_entry {
		CrashTimestamp rip;
		unsigned long addr;
		unsigned long val;
		address_log_entry(const CrashTimestamp &_rip,
				  unsigned long _addr,
				  unsigned long _val)
			: addr(_addr), val(_val)
		{
			rip = _rip;
		}
	};
	std::vector<address_log_entry> address_log;
};

void
Oracle::findLoadsForStore(const CrashTimestamp &store_rip,
			  std::set<CrashTimestamp> *load_rips) const
{
	/* First, find the last instance we have of that store RIP in
	 * the mem log. */
	int idx;
	for (idx = memlog.size() - 1; idx >= 0; idx--)
		if (memlog[idx].rip == store_rip &&
		    !memlog[idx].is_load)
			break;
	if (idx < 0)
		return;
	unsigned long addr = memlog[idx].addr;
	/* Now go through and find all of the loads which were
	   satisfied by that store. */
	for (idx++; idx < (int)memlog.size(); idx++) {
		if (!memlog[idx].is_load) {
			assert(memlog[idx].rip != store_rip);
			continue;
		}
		if (memlog[idx].addr != addr)
			continue;
		load_rips->insert(memlog[idx].rip);
	}
}

class CIALEventRecorder : public EventRecorder<unsigned long> {
	Oracle *oracle; /* Note that the oracle isn't garbage
			 * collected! */
protected:
	void record(Thread<unsigned long> *thr, ThreadEvent<unsigned long> *evt);
public:
	CIALEventRecorder(Oracle *_oracle)
		: oracle(_oracle)
	{
	}
	void visit(HeapVisitor &hv) {}
};
void
CIALEventRecorder::record(Thread<unsigned long> *thr, ThreadEvent<unsigned long> *evt)
{
	StoreEvent<unsigned long> *se =
		dynamic_cast<StoreEvent<unsigned long> *>(evt);
	if (!se)
		return;
	if (oracle->interesting_addresses.count(se->addr) == 0)
		return;
	oracle->constant_addresses.erase(se->addr);
	oracle->address_log.push_back(
		Oracle::address_log_entry(
			CrashTimestamp(thr->tid, thr->regs.rip(), thr->currentCallStack),
			se->addr,
			se->data.lo));
}
void
Oracle::collect_interesting_access_log(
	VexPtr<MachineState<unsigned long> > &ms,
	VexPtr<LogReader<unsigned long> > &lf,
	LogReaderPtr ptr,
	GarbageCollectionToken tok)
{
	constant_addresses = interesting_addresses;

	/* Make bootstrapping easier by starting the log off with
	   records for the initial state of every interesting memory
	   location. */
	for (std::set<unsigned long>::iterator it = interesting_addresses.begin();
	     it != interesting_addresses.end();
	     it++)
		address_log.push_back(
			address_log_entry(
				CrashTimestamp(),
				*it,
				CrashExpressionLoad::fetch(*it, ms, NULL)));

	VexPtr<EventRecorder<unsigned long> > er(new CIALEventRecorder(this));
	Interpreter<unsigned long> i(ms);
	VexPtr<LogWriter<unsigned long> > dummy(NULL);
	i.replayLogfile(lf, ptr, tok, NULL, dummy, er);
}

static CrashMachineNode *
backtrack_crash_machine_node_for_statements(
	const CrashTimestamp &when,
	CrashMachineNode *node,
	IRStmt **statements,
	int nr_statements,
	bool ignore_branches,
	const Oracle &oracle)
{
	int i;

	assert(statements[0]->tag == Ist_IMark);
	assert(when.rip == statements[0]->Ist.IMark.addr);

	for (i = nr_statements - 1; i >= 0; i--)  {
		IRStmt *stmt = statements[i];

		switch (stmt->tag) {
		case Ist_NoOp:
		case Ist_AbiHint:
		case Ist_MBE:
			break;

		case Ist_IMark:
			assert(i == 0);
			break;

		case Ist_Put: {
			CrashExpression *d = CrashExpression::get(stmt->Ist.Put.data);
			if (stmt->Ist.Put.offset == OFFSET_amd64_RSP ||
			    stmt->Ist.Put.offset == OFFSET_amd64_RBP)
				d = CrashExpressionStackPtr::get(d);
			node = node->rewriteRegister(stmt->Ist.Put.offset, d);
			break;
		}

		case Ist_WrTmp:
			node = node->rewriteTemporary(
				stmt->Ist.WrTmp.tmp,
				CrashExpression::get(stmt->Ist.WrTmp.data));
			break;
			
		case Ist_Dirty:
			if (strncmp(stmt->Ist.Dirty.details->cee->name,
				    "helper_load_",
				    12))
				abort(); /* don't know how to deal with these */
			node = node->rewriteTemporary(
				stmt->Ist.Dirty.details->tmp,
				CrashExpressionLoad::get(
					when,
					CrashExpression::get(
						stmt->Ist.Dirty.details->args[0])));
			break;

		case Ist_Store: {
			CrashExpression *data =	CrashExpression::get(stmt->Ist.Store.data);
			CrashExpression *addr =	CrashExpression::get(stmt->Ist.Store.addr);
			std::set<CrashTimestamp> satisfiedLoads;
			oracle.findLoadsForStore(when, &satisfiedLoads);
			if (!satisfiedLoads.empty()) {
				ResolveLoadsMapper rlm(data, satisfiedLoads);
				node = node->map(rlm);
			} else {
				node->stores.insert(
					node->stores.begin(),
					abstract_store(addr, data));
			}
			break;
		}

		case Ist_Exit:
			if (!ignore_branches) {
				/* Only handle two-way branches */
				assert(!node->trueTarget);
				abstractStoresT stores;
				node->trueTarget = new CrashMachineNode(stmt->Ist.Exit.dst->Ico.U64, stores);
				node->branchCond = CrashExpression::get(stmt->Ist.Exit.guard);
			}
			break;

		case Ist_CAS:
			node = node->rewriteTemporary(
				stmt->Ist.CAS.details->oldLo,
				CrashExpressionLoad::get(
					when,
					CrashExpression::get(
						stmt->Ist.CAS.details->addr)));
			break;

		default:
			/* Dunno what to do here. */
			abort();
		}
	}

	return node;
}


/* Returns true if two CMNs are definitely equivalent, and false if
   we're not sure. */
static bool
cmns_bisimilar(CrashMachineNode *cmn1, CrashMachineNode *cmn2)
{
	if (cmn1 == cmn2)
		return true;
	if (!cmn1 || !cmn2)
		return false;
	if (cmn1->type != cmn2->type)
		return false;
	if (cmn1->stores.size() != cmn2->stores.size())
		return false;
	for (unsigned idx = 0;
	     idx < cmn1->stores.size();
	     idx++)
		if (!cmn1->stores[idx].addr->eq(cmn2->stores[idx].addr) ||
		    !cmn1->stores[idx].data->eq(cmn2->stores[idx].data))
			return false;

	switch (cmn1->type) {
	case CrashMachineNode::CM_NODE_STUB:
		return cmn1->origin_rip == cmn2->origin_rip;
	case CrashMachineNode::CM_NODE_LEAF:
		return cmn1->leafCond->eq(cmn2->leafCond);
	case CrashMachineNode::CM_NODE_BRANCH:
		return cmn1->branchCond->eq(cmn2->branchCond) &&
			cmns_bisimilar(cmn1->trueTarget,
				       cmn2->trueTarget) &&
			cmns_bisimilar(cmn1->falseTarget,
				       cmn2->falseTarget);
	}
	abort();
}

/* Aim here is to incorporate a bit of static analysis into the crash
 * machine. */
/* There are two crash machines:
 *
 * -- The dynamic one which we just derived from the captured log
 * -- The static one which we're going to try to build up
 *
 * In addition, there are also a bunch of CrashMachineNodes, which
 * provide a predicate which can be evaluated at a particular
 * instruction and tell you whether you're going to crash there.
 *
 * The static CrashMachine starts off containing just the leaf node
 * from the dynamic machine.
 *
 * We then try to translate the starting dynamic CrashMachineNode into
 * a static CrashMachineNode.
 *
 * If there's already a static CMN for that RIP, then we're done and
 * we can just return.
 *
 * If it's a branch CMN, we convert both the target branches to static
 * form and then construct a new static CMN which points at them.  We
 * then backtrack this static CMN to the start of the relevant
 * instruction, and return the result.
 *
 * If it's a stub CMN, we have to perform a forwards analysis, which
 * is more tricky.  Starting at the stub RIP, we construct a control
 * flow graph working forwards.  The CFG may intersect the existing
 * static control machine, and if it does we drop in a proxy to the
 * relevant static CMN.  It might also disappear (e.g. dynamic jump),
 * in which case we construct a fresh new constant static CMN which is
 * just true and proxy to that instead.
 *
 * The end result of this is a CFG which sometimes proxies to static
 * CMNs.  We then stooge in and break all of the cycles in some pretty
 * much arbitrary way, producing an acycilc CFG with static CMN
 * proxies.  We now walk the CFG backwards from the proxies, which
 * will be leaves, and try to turn all of the CFG nodes into
 * equivalent proxies.  These proxies can be entered into the static
 * CrashMachine.  Eventually, we should be able to convert the entire
 * CFG into a single proxy, which is then used as the static CMN in
 * place of the original stub dynamic CMN.
 *
 * The end result is that we produce a kind of static slice through
 * the program which captures all of the relevant parts of the dynamic
 * execution.  The big advantage of this over pure dynamic schemes is
 * that we can look at what the other branches are doing, and hence
 * eliminate a whole bunch of them.
 */

class CrashCFGNode : public GarbageCollected<CrashCFGNode> {
	CrashCFGNode(const CrashCFGNode &); /* DNI */
public:
	CrashCFGNode(const CrashTimestamp &_when, const CrashTimestamp &t, const CrashTimestamp &f)
	{
		when = _when;
		trueTargetRip = t;
		falseTargetRip = f;
	}
	CrashTimestamp when;

	CrashTimestamp trueTargetRip;
	bool brokeCycleTrueTarget;
	CrashCFGNode *trueTarget;

	CrashTimestamp falseTargetRip;
	bool brokeCycleFalseTarget;
	CrashCFGNode *falseTarget;

	bool dead;

	bool visitedByCycleBreaker;
	bool onCycleBreakerPath;

	CrashMachineNode *cmn;

	void visit(HeapVisitor &hv) { hv(trueTarget); hv(falseTarget); hv(cmn); }
	NAMED_CLASS
};

class CrashCFG : public GarbageCollected<CrashCFG> {
	typedef gc_map<CrashTimestamp, CrashCFGNode *,
		       __default_hash_function<CrashTimestamp>,
		       __default_eq_function<CrashTimestamp>,
		       __visit_function_heap<CrashCFGNode *> > nodeMapT;
	nodeMapT *nodeMap;

	/* Things which we need to visit, but haven't reached yet. */
	std::vector<CrashTimestamp> grey;

	std::vector<CrashTimestamp> roots;

	void build_cfg(MachineState<unsigned long> *ms, const Oracle &oracle,
		       CrashMachine *partial_cm);
		       
	void resolve_stubs();
	void break_cycles(const Oracle &oracle);
	bool break_cycles_from(CrashCFGNode *n, const Oracle &oracle);
	void calculate_cmns(MachineState<unsigned long> *ms,
			    CrashMachine *cm,
			    const Oracle &oracle);
public:
	CrashCFG()
		: nodeMap(new nodeMapT())
	{
	}

	void add_root(const CrashTimestamp &x)
	{
		roots.push_back(x);
		grey.push_back(x);
	}
	void build(MachineState<unsigned long> *ms,
		   const Oracle &footstep_log,
		   CrashMachine *partial_cm);
	CrashMachineNode *get_cmn(const CrashTimestamp &when)
	{
		return nodeMap->get(when)->cmn;
	}

	void visit(HeapVisitor &hv) { hv(nodeMap); }
	NAMED_CLASS
};


static bool
get_fallthrough_rip(IRSB *irsb, int instr_end, unsigned long *out, bool *do_pop)
{
	if (instr_end == irsb->stmts_used) {
		/* Disable special handling for calls for now, because
		   it doesn't really work all that well.  Because we
		   pick the return address for functions out of the
		   dynamic trace this is kind of equivalent to just
		   inlining all functions, provided they're only
		   called once, which is reasonably safe. */
		if (0 && irsb->jumpkind == Ijk_Call) {
			/* We pretend that functions do nothing at
			   all.  That's not entirely valid, but it's
			   kind of convenient. */
			*out =	extract_call_follower(irsb);
			/* We ignore the call, so we need to pop the
			   return address which we just pushed. */
			if (do_pop)
				*do_pop = true;
		} else if (irsb->next->tag == Iex_Const) {
			*out = irsb->next->Iex.Const.con->Ico.U64;
		} else {
			return false;
		}
	} else {
		assert(irsb->stmts[instr_end]->tag == Ist_IMark);
		*out = irsb->stmts[instr_end]->Ist.IMark.addr;
	}
	return true;
}

/* Hackety hackety hack: we ``know'' that certain RIPs are equivalent,
   because we have some idea of how the standard library is
   implemented.  In particular, we know what the system call template
   looks like. */
static void
fixup_rip(CrashTimestamp &ts)
{
	if (ts.rip == 0x00007fde5be4601a)
		ts.rip = 0x00007fde5be45fc8;
	else if (ts.rip == 0x00007faa4af5d7b8)
		ts.rip = 0x00007faa4af5d800;
}

void
CrashCFG::build_cfg(MachineState<unsigned long> *ms,
		    const Oracle &oracle,
		    CrashMachine *partial_cm)
{
	ThreadId tid = oracle.crashingTid;
	while (!grey.empty()) {
		CrashTimestamp &when = grey.back();
		if (nodeMap->hasKey(when)) {
			grey.pop_back();
			continue;
		}

		bool haveFallThrough = false;
		bool haveNonFallThrough = false;
		CrashTimestamp fallThroughTarget;
		fallThroughTarget = when;
		CrashTimestamp nonFallThroughTarget;
		nonFallThroughTarget = when;
		bool dead = false;
		if (!partial_cm->content->hasKey(when)) {
			/* We stop exploration if we get to something
			   which already has a CMN, because it can't
			   do us any good to go beyond that point, and
			   it can sometimes cause problems if e.g. it
			   causes the loop breaker to do something
			   stupid. */

			IRSB *irsb = ms->addressSpace->getIRSBForAddress(when.rip);
			int instr_end;
			for (instr_end = 1;
			     instr_end < irsb->stmts_used &&
				     irsb->stmts[instr_end]->tag != Ist_IMark;
			     instr_end++) {
				if (irsb->stmts[instr_end]->tag == Ist_Exit) {
					assert(!haveNonFallThrough);
					nonFallThroughTarget.rip =
						irsb->stmts[instr_end]->Ist.Exit.dst->Ico.U64;
					haveNonFallThrough = true;
				}
			}
			unsigned long frip = 0;
			get_fallthrough_rip(irsb, instr_end, &frip, NULL);
			if (instr_end == irsb->stmts_used &&
			    !frip) {
				if (irsb->jumpkind == Ijk_Ret &&
				    !when.callStack.empty()) {
					frip = when.callStack.back();
					fallThroughTarget.callStack.pop_back();
				} else {
					/* Cheat and grab the return
					   address out of the dynamic
					   trace, if it's
					   available. */
					CrashTimestamp n;
					if (oracle.successorOf(when, n))
						frip = n.rip;
				}
			}

			if (frip) {
				fallThroughTarget.rip = frip;
				haveFallThrough = true;
			}

			if (haveFallThrough &&
			    instr_end == irsb->stmts_used &&
			    irsb->jumpkind == Ijk_Call) {
				fallThroughTarget.callStack.push_back(extract_call_follower(irsb));
			}
			if (irsb->jumpkind == Ijk_NoDecode) {
				dead = true;
				haveFallThrough = false;
				haveFallThrough = false;
			}
		}

		fixup_rip(fallThroughTarget);
		fixup_rip(nonFallThroughTarget);

		CrashCFGNode *newNode =
			new CrashCFGNode(when, nonFallThroughTarget, fallThroughTarget);
		newNode->dead = dead;
		assert(newNode != NULL);
		nodeMap->set(when, newNode);

		grey.pop_back();

		if (haveFallThrough)
			grey.push_back(fallThroughTarget);
		if (haveNonFallThrough)
			grey.push_back(nonFallThroughTarget);
	}
}

void
CrashCFG::resolve_stubs()
{
	for (nodeMapT::iterator it = nodeMap->begin();
	     it != nodeMap->end();
	     it++) {
		CrashCFGNode *n = it.value();
		assert(n);
		if (n->trueTargetRip.valid())
			n->trueTarget = nodeMap->get(n->trueTargetRip);
		if (n->falseTargetRip.valid())
			n->falseTarget = nodeMap->get(n->falseTargetRip);
	}
}

/* This converts the CFG to a ``similar'' CFG which is definitely
 * acyclic.  It's not really valid, in any particularly useful sense,
 * but it does make all of the subsequent analysis much easier. */
/* This works by partitioning the graph into two sets, the visited one
   and the unvisited one, and maintaining the invariant that:

   -- There are no cycles contained entirely within the visited set.
   -- Any node which is reachable from a visited node will either be
      visited itself or will be reachable from the current node.

   The current node is what you'd expect for a depth-first search.

   This is very similar to Tarjan's algorithm.
*/
struct CycleBreakerState {
	CrashCFGNode *n;
	bool visitedTrueTarget;
	bool visitedFalseTarget;
	CycleBreakerState(CrashCFGNode *_n)
		: n(_n), visitedTrueTarget(false), visitedFalseTarget(false)
	{
	}
};
bool
CrashCFG::break_cycles_from(CrashCFGNode *n, const Oracle &oracle)
{
	bool succeeded = true;

	/* We use an explicit stack so as to make it easier to search
	   backwards along the current path. */
	std::vector<CycleBreakerState> stack;

	stack.push_back(CycleBreakerState(n));
	while (!stack.empty()) {
		CycleBreakerState &s(stack.back());

		assert(s.n);

		DBG_CYCLE_BREAKER("Cycle breaker %p %p %s: ", &s, s.n, s.n->when.name());
		if (s.n->visitedByCycleBreaker) {
			/* Nothing to do here: we've already visited
			   this node, and know that it doesn't
			   participate in any cycles. */
			DBG_CYCLE_BREAKER("Already visited.\n");
			stack.pop_back();
			continue;
		}

		if ( (s.visitedTrueTarget || !s.n->trueTarget) &&
		     (s.visitedFalseTarget || !s.n->falseTarget) ) {
			/* Finished this node. */
			DBG_CYCLE_BREAKER("Finished.\n");
			s.n->visitedByCycleBreaker = true;
			s.n->onCycleBreakerPath = false;
			stack.pop_back();
		} else if (s.visitedTrueTarget) {
			assert(s.n->falseTarget);
			DBG_CYCLE_BREAKER("Visited true; trying false %s.\n",
					  s.n->falseTarget->when.name());
			s.visitedFalseTarget = true;
			stack.push_back(CycleBreakerState(s.n->falseTarget));
		} else if (s.visitedFalseTarget) {
			assert(s.n->trueTarget);
			DBG_CYCLE_BREAKER("Visited false; trying true %s.\n",
					  s.n->trueTarget->when.name());
			s.visitedTrueTarget = true;
			stack.push_back(CycleBreakerState(s.n->trueTarget));
		} else if (s.n->onCycleBreakerPath) {
			/* We have a cycle.  Break it. */
			DBG_CYCLE_BREAKER("Found a cycle.\n");

			succeeded = false;

			/* This node should be on the stack in two
			   places, and the cyclic path is all of the
			   nodes between those two points.  We pick
			   break points according to some heuristics:

			   -- We try not to break edges which are
                              present in the oracle.
			   -- We prefer not to remove the only exit
			      from a node.
			   -- We prefer later edges to earlier ones

			   Those are in descending order of priority.
			*/

			bool avoid_edges_in_oracle = true;
			bool avoid_only_exit_nodes = true;

			while (avoid_edges_in_oracle ||
			       avoid_only_exit_nodes) {
				for (std::vector<CycleBreakerState>::reverse_iterator it =
					     stack.rbegin() + 1;
				     it != stack.rend();
				     it++) {
					if (it->n == s.n)
						break;
					if (it->n->trueTarget && it->n->falseTarget) {
						CrashTimestamp target;
						target = (it - 1)->n->when;
						if (avoid_edges_in_oracle &&
						    oracle.containsRipEdge(
							    s.n->when,
							    target))
							continue;

						DBG_CYCLE_BREAKER("Cycle breaker removes edge %s -> %s ",
								  it->n->when.name(),
								  target.name());
						if (it->n->trueTarget == (it - 1)->n) {
							DBG_CYCLE_BREAKER("(true %s, false was %s)\n",
									  it->n->trueTarget->when.name(),
									  it->n->falseTarget->when.name());
							it->n->trueTarget = NULL;
							it->n->brokeCycleTrueTarget = true;
						} else {
							DBG_CYCLE_BREAKER("(false %s, true was %s)\n",
									  it->n->falseTarget->when.name(),
									  it->n->trueTarget->when.name());
							it->n->falseTarget = NULL;
							it->n->brokeCycleFalseTarget = true;
						}
					
						/* Tell caller to
						   restart.  This is
						   arguable a bit of a
						   waste, because
						   quite a lot of work
						   is still valid, but
						   it makes things a
						   bit easier. */
						goto out;
					}
				}

				/* Failed.  Weaken the heuristics and
				   try again. */
				if (avoid_edges_in_oracle)
					avoid_edges_in_oracle = false;
				else
					avoid_only_exit_nodes = false;
			}

			/* Really failed.  Just break on the last
			 * possible edge. */
			CycleBreakerState &parent(stack[stack.size()-2]);
			DBG_CYCLE_BREAKER("Forced cycle breaking at %s -> %s ",
					  parent.n->when.name(),
					  s.n->when.name());
			if (parent.n->trueTarget == s.n) {
				DBG_CYCLE_BREAKER("(true)\n");
				parent.n->trueTarget = NULL;
				parent.n->brokeCycleTrueTarget = true;
			} else {
				DBG_CYCLE_BREAKER("(false %s)\n",
						  parent.n->falseTarget->when.name());
				parent.n->falseTarget = NULL;
				parent.n->brokeCycleFalseTarget = true;
			}
			goto out;
		} else {
			DBG_CYCLE_BREAKER("First visit, no cycle discovered yet: ");
			assert(!s.n->onCycleBreakerPath);
			s.n->onCycleBreakerPath = true;

			bool visitTrueTargetFirst = false;

			if (s.n->trueTarget && s.n->falseTarget) {
				/* If the partial CM has a node for
				 * this RIP, we prefer to visit the
				 * branch which it exitted on first.
				 * This helps keep the approximation
				 * as accurate as possible on the path
				 * which the program actually
				 * executed.  Otherwise, we visit the
				 * false path first, as that
				 * corresponds to the fall-through
				 * execution, and that tends to
				 * encourage the visiter to keep the
				 * simplest possible execution and
				 * avoids unnecessary partitioning. */
				visitTrueTargetFirst =
					oracle.branchTaken(n->when,
							   visitTrueTargetFirst);
			} else if (s.n->trueTarget) {
				assert(!s.n->falseTarget);
				visitTrueTargetFirst = true;
			} else {
				assert(s.n->falseTarget);
			}

			if (visitTrueTargetFirst) {
				assert(s.n->trueTarget);
				DBG_CYCLE_BREAKER("Explore true branch %s first\n", s.n->trueTarget->when.name());
				s.visitedTrueTarget = true;
				stack.push_back(CycleBreakerState(s.n->trueTarget));
			} else {
				assert(s.n->falseTarget);
				DBG_CYCLE_BREAKER("Explore false branch %s first\n", s.n->falseTarget->when.name());
				s.visitedFalseTarget = true;
				stack.push_back(CycleBreakerState(s.n->falseTarget));
			}
		}
	}

out:
	/* pop the stack */
	while (!stack.empty()) {
		CycleBreakerState &s(stack.back());
		s.n->onCycleBreakerPath = false;
		stack.pop_back();
	}
	return succeeded;
}
void
CrashCFG::break_cycles(const Oracle &oracle)
{
	/* We start enumeration from the roots, because that helps to
	   keep the important bits of the graph structure intact. */
	for (std::vector<CrashTimestamp>::iterator it = roots.begin();
	     it != roots.end();
	     it++) {
		while (!break_cycles_from(nodeMap->get(*it), oracle))
			;
	}
}

void
CrashCFG::calculate_cmns(MachineState<unsigned long> *ms,
			 CrashMachine *cm,
			 const Oracle &oracle)
{
	bool progress;
	progress = true;
	while (progress) {
		progress = false;
		for (nodeMapT::iterator it = nodeMap->begin();
		     it != nodeMap->end();
		     it++) {
			CrashCFGNode *node = it.value();
			if (node->cmn)
				continue;
			if (cm->hasKey(node->when)) {
				node->cmn = cm->get(node->when);
				progress = true;
				DBG_CALC_CMNS("%s: %s from crash machine\n", node->when.name(), node->cmn->name());
				continue;
			}

			if ((node->trueTarget && !node->trueTarget->cmn) ||
			    (node->falseTarget && !node->falseTarget->cmn))
				continue;
			/* Okay, both exits either have a CMN or don't
			 * exist.  That means we should be able to
			 * derive a CMN for this node. */
			DBG_CALC_CMNS("Calculate CMN for %s\n", node->when.name());
			progress = true;
			if (node->dead) {
				node->cmn = new CrashMachineNode(
					node->when.rip,
					CrashExpressionConst::get(1),
					abstractStoresT());
				continue;
			}

			if (!node->trueTarget && !node->falseTarget) {
				/* Don't know where we go after this
				   node, and it wasn't executed in the
				   dynamic execution -> assume it's
				   sufficiently different from the
				   captured one that we avoid the
				   crash. */
				DBG_CALC_CMNS("%s: no known successors\n", node->when.name());
				abstractStoresT stores;
				node->cmn = new CrashMachineNode(
					node->when.rip,
					CrashExpressionConst::get(0),
					stores);
				continue;
			}

			IRSB *irsb = ms->addressSpace->getIRSBForAddress(node->when.rip);
			int instr_end;
			for (instr_end = 1;
			     instr_end < irsb->stmts_used && irsb->stmts[instr_end]->tag != Ist_IMark;
			     instr_end++)
				;
			CrashMachineNode *trueTarget = NULL;
			CrashMachineNode *falseTarget = NULL;
			CrashExpression *branchCond = NULL;
			CrashMachineNode *cmn;
			bool doCallFixup = false;
			if (node->falseTarget && node->trueTarget) {
				/* We have both fall-through and
				   non-fall-through exits. */
				assert(irsb->stmts[instr_end-1]->tag == Ist_Exit);
				branchCond = CrashExpression::get(irsb->stmts[instr_end-1]->Ist.Exit.guard);
				trueTarget = node->trueTarget->cmn;
				falseTarget = node->falseTarget->cmn;

				/* We've already handled the Exit
				   statement, so don't bother with it
				   during normal backtracking. */
				instr_end--;
			} else if (node->falseTarget) {
				/* We have a false target but not a
				   true one.  That could either mean
				   that there's no branch here, or
				   that there is one and we've decided
				   to cull it to break a cycle.  If
				   there is one, ignore it during
				   backtracking. */
				if (irsb->stmts[instr_end-1]->tag == Ist_Exit)
					instr_end--;
				branchCond = CrashExpressionConst::get(0);
				falseTarget = node->falseTarget->cmn;

#if 0
				if (instr_end == irsb->stmts_used &&
				    irsb->jumpkind == Ijk_Call) {
					/* We pretty much ignore
					   calls, but we do have to do
					   enough fixup to pop the
					   return address. */
					doCallFixup = true;
				}
#endif

			} else {
				/* We have a true target but not a
				   false one.  The fall-through branch
				   must have been culled. */
				assert(node->trueTarget);
				while (irsb->stmts[instr_end-1]->tag != Ist_Exit &&
				       instr_end - 1 > 0)
					instr_end--;
				assert(instr_end > 0);
				branchCond = CrashExpressionConst::get(1);
				trueTarget = node->trueTarget->cmn;
			}

			DBG_CALC_CMNS("%s: have successors %s and %s\n",
				      node->when.name(),
				      trueTarget ? trueTarget->name() : NULL,
				      falseTarget ? falseTarget->name() : NULL);
			
			/* cmn is now valid at the exit of this
			   instruction.  Backtrack it to get the CMN
			   for the start of the instruction. */
			abstractStoresT stores;
			cmn = new CrashMachineNode(node->when.rip,
						   branchCond,
						   trueTarget,
						   falseTarget,
						   stores);
			if (doCallFixup)
				cmn = cmn->rewriteRegister(
					OFFSET_amd64_RSP,
					CrashExpressionAdd::get(
						CrashExpressionConst::get(8),
						CrashExpressionRegister::get(OFFSET_amd64_RSP)));

			assert(cmn->isStubFree());
			cmn = backtrack_crash_machine_node_for_statements(
				node->when,
				cmn,
				irsb->stmts,
				instr_end,
				true,
				oracle);
			assert(cmn->isStubFree());

			/* All done. */
			node->cmn = cmn;
			DBG_CALC_CMNS("%s -> %s\n", node->when.name(), cmn->name());
		}
	}
}

/* Build the acyclic CFG and use that to infer ``correct'' crash
   machine nodes for every instruction. */
void
CrashCFG::build(MachineState<unsigned long> *ms,
		const Oracle &oracle,
		CrashMachine *cm)
{
	build_cfg(ms, oracle, cm);
	resolve_stubs();
	break_cycles(oracle);
	calculate_cmns(ms, cm, oracle);
}

/* Construct a new CMN which is equivalent to running all of the
   stores out of base and then running sub. */
static CrashMachineNode *
mergeCmns(CrashMachineNode *base, CrashMachineNode *sub)
{
	abstractStoresT stores(base->stores);
	stores.insert(stores.end(),
		      sub->stores.begin(),
		      sub->stores.end());
	switch (sub->type) {
	case CrashMachineNode::CM_NODE_LEAF:
		return new CrashMachineNode(sub->origin_rip,
					    sub->leafCond,
					    stores);
	case CrashMachineNode::CM_NODE_STUB:
		return new CrashMachineNode(sub->origin_rip,
					    stores);
	case CrashMachineNode::CM_NODE_BRANCH:
		return new CrashMachineNode(sub->origin_rip,
					    sub->branchCond,
					    sub->trueTarget,
					    sub->falseTarget,
					    stores);
	}
	abort();
}

static CrashMachineNode *
simplify_cmn(CrashMachineNode *cmn)
{
	if (!cmn)
		return NULL;

	switch (cmn->type) {
	case CrashMachineNode::CM_NODE_STUB:
		/* These should already have been stripped out by our caller. */
		abort();
		return cmn;
	case CrashMachineNode::CM_NODE_LEAF:
		if (cmn->leafCond->isConstant()) {
			/* The stores are irrelevant in this case */
			cmn->stores.clear();
			cmn->changed();
		}
		break;

	case CrashMachineNode::CM_NODE_BRANCH:
		assert(cmn->trueTarget || cmn->falseTarget);
		cmn->sanity_check();
		cmn->falseTarget = simplify_cmn(cmn->falseTarget);
		cmn->trueTarget = simplify_cmn(cmn->trueTarget);
		assert(cmn->trueTarget || cmn->falseTarget);
		cmn->sanity_check();
		if (!cmn->falseTarget) {
			cmn = mergeCmns(cmn, cmn->trueTarget);
			break;
		}
		if (!cmn->trueTarget) {
			cmn = mergeCmns(cmn, cmn->falseTarget);
			break;
		}
		unsigned long lc;
		cmn->branchCond = cmn->branchCond->simplify(1000);
		if (cmn->branchCond->isConstant(lc)) {
			if (lc)
				cmn = mergeCmns(cmn, cmn->trueTarget);
			else
				cmn = mergeCmns(cmn, cmn->falseTarget);
		} else {
			if (cmn->falseTarget->origin_rip < cmn->trueTarget->origin_rip) {
				CrashMachineNode *t;
				cmn->branchCond = CrashExpressionNot::get(cmn->branchCond);
				t = cmn->trueTarget;
				cmn->trueTarget = cmn->falseTarget;
				cmn->falseTarget = t;
			}
			if (cmns_bisimilar(cmn->trueTarget, cmn->falseTarget))
				cmn = mergeCmns(cmn, cmn->trueTarget);
		}
		cmn->changed();
		break;
	default:
		abort();
	}
	cmn->sanity_check();
	return cmn;
}

static CrashMachineNode *
buildCrashMachineNode(MachineState<unsigned long> *ms,
		      const CrashTimestamp &when,
		      CrashMachine *cm,
		      const Oracle &oracle)
{
	if (cm->hasKey(when))
		return cm->get(when);
	CrashCFG *cfg = new CrashCFG();
	cfg->add_root(when);
	cfg->build(ms, oracle, cm);
	return cfg->get_cmn(when);
}

class MemTraceExtractor : public EventRecorder<unsigned long> {
public:
	Oracle *oracle;
	MemTraceExtractor(Oracle *o) : oracle(o) {}
	void record(Thread<unsigned long> *thr,
		    ThreadEvent<unsigned long> *evt);
	void visit(HeapVisitor &hv) {}
};

void
MemTraceExtractor::record(Thread<unsigned long> *thr,
			  ThreadEvent<unsigned long> *evt)
{
	unsigned long rsp;
	if (thr->tid != oracle->crashingTid)
		return;
	rsp = thr->regs.get_reg(REGISTER_IDX(RSP));
	if (LoadEvent<unsigned long> *le =
	    dynamic_cast<LoadEvent<unsigned long> *>(evt)) {
		/* Arbitrarily assume that stacks are never deeper
		   than 8MB.  Also assume that the red zone is only
		   128 bytes, and we never access more than 8 bytes
		   past its nominal end. */
		if (le->addr >= rsp - 136 &&
		    le->addr < rsp + (8 << 20))
			oracle->load_event(CrashTimestamp(thr), le->addr);
	} else if (StoreEvent<unsigned long> *se =
		   dynamic_cast<StoreEvent<unsigned long> *>(evt)) {
		if (se->addr >= rsp - 136 &&
		    se->addr < rsp + (8 << 20))
			oracle->store_event(CrashTimestamp(thr), se->addr);
	}
}

unsigned long
memory_lookup(std::map<unsigned long, unsigned long> *memory, unsigned long addr)
{
	return (*memory)[addr];
}

static void
findRemoteCriticalSections(CrashMachineNode *cmn,
			   const CrashTimestamp &when,
			   const Oracle &oracle,
			   MachineState<unsigned long> *ms)
{
	std::map<unsigned long, unsigned long> memory;
	CrashMachineNode *last = NULL;
	unsigned nr_good, nr_bad, nr_unknown;

	cmn = cmn->resolveLoads(memory, ms);
	cmn = simplify_cmn(cmn);
	if (cmn->willDefinitelyCrash() || cmn->willDefinitelyNotCrash())
		return;

	nr_good = 0;
	nr_bad = 0;
	nr_unknown = 0;
	for (std::vector<Oracle::address_log_entry>::const_iterator m_it =
		     oracle.address_log.begin();
	     m_it != oracle.address_log.end();
	     m_it++) {
		memory[m_it->addr] = m_it->val;
		CrashMachineNode *new_cmn =
			cmn->resolveLoads(memory, ms);
		new_cmn = simplify_cmn(new_cmn);
		if (last &&
		    (1 || !cmns_bisimilar(last, new_cmn))) {
			if (new_cmn->willDefinitelyCrash())
				nr_bad++;
			else if (new_cmn->willDefinitelyNotCrash())
				nr_good++;
			else
				nr_unknown++;
		}
		last = new_cmn;
	}
	if (nr_good != 0)
		printf("%s: %d %d %d (%s)\n",
		       when.name(),
		       nr_good,
		       nr_bad,
		       nr_unknown,
		       cmn->name());
}

class RemoveProbablyConstantReferencesMapper : public CPMapper {
public:
	const Oracle &oracle;
	MachineState<unsigned long> *ms;
	Thread<unsigned long> *thr;
	RemoveProbablyConstantReferencesMapper(
		const Oracle &_oracle,
		MachineState<unsigned long> *_ms,
		Thread<unsigned long> *_thr)
		: oracle(_oracle),
		  ms(_ms),
		  thr(_thr)
	{
	}
	CrashExpression *operator()(CrashExpression *e) {
		e = e->simplify(1000);
		CrashExpressionLoad *cel = dynamic_cast<CrashExpressionLoad *>(e);
		unsigned long addr;
		if (cel &&
		    cel->addr->isConstant(addr) &&
		    oracle.constant_addresses.count(addr) != 0) {
			return CrashExpressionConst::get(
				CrashExpressionLoad::fetch(addr, ms, thr));
		}
		return e;
	}
};

static CrashMachineNode *
removeProbablyConstantReferences(CrashMachineNode *start,
				 const Oracle &oracle,
				 MachineState<unsigned long> *ms,
				 Thread<unsigned long> *thr)
{
	if (oracle.constant_addresses.empty())
		return start;
	RemoveProbablyConstantReferencesMapper rpcrm(oracle, ms, thr);
	return start->map(rpcrm);
}

int
main(int argc, char *argv[])
{
	init_sli();

	LogReaderPtr ptr;
	VexPtr<LogReader<unsigned long> > lf(LogFile::open(argv[1], &ptr));
	VexPtr<MachineState<unsigned long> > ms(MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr, ALLOW_GC));
	//ms->findThread(ThreadId(7))->exitted = true;
	
	Oracle oracle;

	/* Figure out which thread crashed.  We usei sby replaying the
	   entire log and then looking at the very last record, but
	   hat's really stupid, because all we really need to know is
	   which thread got signalled.  Could trivially do that by
	   just looking at the last record, but I'm lazy, so hard-code
	   for now. */
	oracle.crashingTid = ThreadId(1);

#if 0
	VexPtr<Thread<unsigned long> > crashedThread;
	Interpreter<unsigned long> i(ms);
	i.replayLogfile(lf, ptr, ALLOW_GC);
	ms = i.currentState;

	crashedThread = NULL;
	for (unsigned x = 0; x < ms->threads->size(); x++) {
		if (ms->threads->index(x)->crashed) {
			if (crashedThread)
				printf("Multiple crashed threads?\n");
			crashedThread = ms->threads->index(x);
		}
	}
	if (!crashedThread) {
		printf("No crashed threads.\n");
		return 0;
	}

	oracle.crashingTid = crashedThread->tid;
#endif
	
        /* Extract a memory trace */
	{
		VexPtr<EventRecorder<unsigned long> > mte(new MemTraceExtractor(&oracle));
		Interpreter<unsigned long> i2(ms->dupeSelf());
		VexPtr<LogWriter<unsigned long> > dummy_lw(NULL);
		i2.replayLogfile(lf, ptr,
				 ALLOW_GC, NULL, dummy_lw, mte);
		ms = i2.currentState;
	}

	VexPtr<Thread<unsigned long> > crashedThread;
	crashedThread = ms->findThread(oracle.crashingTid);
	printf("Selected thread %d as crasher\n", crashedThread->tid._tid());

	if (crashedThread->currentIRSB) {
		printf("Crashed at step %d in:\n", crashedThread->currentIRSBOffset);
		ppIRSB(crashedThread->currentIRSB);
		assert(crashedThread->currentIRSBOffset != 0);
	} else if (1) {
		printf("Crashed because we jumped at a bad RIP %lx\n",
		       crashedThread->currentIRSBRip);

		/* If we don't have a current IRSB, build one based on
		 * the last thing in the ring buffer. */
		crashedThread->currentIRSB =
			ms->addressSpace->getIRSBForAddress(
				crashedThread->controlLog.rbegin()->translated_rip);
		/* We should be at the end of that... */
		assert(crashedThread->currentIRSBOffset ==
		       crashedThread->currentIRSB->stmts_used + 1);
		/* Don't double-process the last thing in the ring. */
		crashedThread->controlLog.pop_back();

		/* If this was a call, it failed. */
		if (crashedThread->currentIRSB->jumpkind == Ijk_Call)
			crashedThread->currentCallStack.pop_back();
	} else {
		printf("Crashed by syscall\n");
		crashedThread->currentIRSB =
			ms->addressSpace->getIRSBForAddress(
				crashedThread->currentIRSBRip);
	}

	/* Build the footstep log.  This has a record for every
	   instruction in the dynamic trace, which says:

	   -- What the RIP was
	   -- Whether we exited due to a branch or a fall-through (true for
	   branch, false for fall-through).

	   The log is constructed in reverse order, so the most recent
	   footsteps are at the front.

	   It mostly gets used as a control flow oracle when static
	   analysis fails.
	*/

	/* Do the current IRSB first */
	CrashTimestamp ts(crashedThread);
	for (int idx = crashedThread->currentIRSBOffset;
	     idx >= 0;
	     idx--) {
		if (idx < crashedThread->currentIRSB->stmts_used &&
		    crashedThread->currentIRSB->stmts[idx]->tag == Ist_IMark) {
			ts.rip = crashedThread->currentIRSB->stmts[idx]->Ist.IMark.addr;
			oracle.addRipTrace(ts, false);
		}
	}

	/* Now walk back over the earlier IRSBs */
	unsigned long prev_rip = crashedThread->regs.rip();
	for (ring_buffer<Thread<unsigned long>::control_log_entry, 100>::reverse_iterator it =
		     crashedThread->controlLog.rbegin();
	     it != crashedThread->controlLog.rend();
	     it++) {
	        IRSB *irsb = ms->addressSpace->getIRSBForAddress(it->translated_rip);
		bool exited_by_branch;
		int exit_idx;
		if (it->exit_idx == irsb->stmts_used + 1) {
			exited_by_branch = false;
			exit_idx = it->exit_idx - 2;
			if (irsb->jumpkind == Ijk_Ret)
				ts.callStack.push_back(prev_rip);
			else if (irsb->jumpkind == Ijk_Call)
				ts.callStack.pop_back();
		} else {
			exited_by_branch = true;
			exit_idx = it->exit_idx - 1;
		}
		for (int idx = exit_idx;
		     idx >= 0;
		     idx--) {
			if (irsb->stmts[idx]->tag == Ist_IMark) {
				ts.rip = irsb->stmts[idx]->Ist.IMark.addr;
				oracle.addRipTrace(ts, exited_by_branch);
				exited_by_branch = false;
				prev_rip = irsb->stmts[idx]->Ist.IMark.addr;
			}
		}
	}


	/* Look at the crashing statement to derive a proximal cause
	 * of the crash. */
	CrashTimestamp when(crashedThread);

	CrashMachineNode *cmn;
        int instr_start;
        if (crashedThread->currentIRSBOffset == crashedThread->currentIRSB->stmts_used + 1) {
		/* We made it to the end of the block and then crashed
		   trying to start the next one -> the next address
		   must be bad. */
		for (instr_start = crashedThread->currentIRSBOffset-2;
		     crashedThread->currentIRSB->stmts[instr_start]->tag != Ist_IMark;
		     instr_start--)
			;
		abstractStoresT stores;
		when.rip = crashedThread->currentIRSB->stmts[instr_start]->Ist.IMark.addr;
		when.changed();
		if (1) {
			cmn = new CrashMachineNode(
				when.rip,
				CrashExpressionBadAddr::get(
					CrashExpression::get(crashedThread->currentIRSB->next)),
				stores);
		} else {
			cmn = new CrashMachineNode(
				when.rip,
				CrashExpressionConst::get(1),
				stores);
		}
		crashedThread->currentIRSBOffset -= 1;
	} else {
		for (instr_start = crashedThread->currentIRSBOffset-1;
		     crashedThread->currentIRSB->stmts[instr_start]->tag != Ist_IMark;
		     instr_start--)
			;
		cmn = statementToCrashReason(
			when,
			crashedThread->currentIRSB->stmts[crashedThread->currentIRSBOffset - 1]);
	}
        cmn = backtrack_crash_machine_node_for_statements(
		when,
		cmn,
		crashedThread->currentIRSB->stmts + instr_start,
		crashedThread->currentIRSBOffset - instr_start,
		false,
		oracle);

	cmn->sanity_check();

	printf("Proximal cause is %s\n", cmn->name());

	/* Go and build the crash machine */
	VexPtr<CrashMachine> cm(new CrashMachine());

	/* Install the proximal cause, so that we have something to
	   bootstrap with. */
        cm->set(when, cmn);

	/* Returning from the function which crashed is assumed to
	   mean that the bug has been averted. */
	{
		CrashTimestamp tmpTs;
		tmpTs = when;
		while (!tmpTs.callStack.empty()) {
			tmpTs.rip = tmpTs.callStack.back();
			tmpTs.callStack.pop_back();
			cm->set(tmpTs,
				new CrashMachineNode(
					tmpTs.rip,
					CrashExpressionConst::get(0),
					abstractStoresT()));
		}
	}

	/* Incorporate stuff from the dynamic trace in reverse
	 * order. */
	for (Oracle::RipTraceIterator it = oracle.begin_rip_trace();
	     it != oracle.end_rip_trace();
	     it++) {
		if (!cm->hasKey(*it)) {
			CrashMachineNode *cmn;
			cmn = buildCrashMachineNode(ms,
						    *it,
						    cm,
						    oracle);
			cmn = simplify_cmn(cmn);
			cm->set(*it, cmn);
			printf("CMN for %s is %s\n",
			       (*it).name(), cmn->name());
		}
	}

        /* Now try to figure out what the relevant addresses are for
	   each CMN.*/
        Thread<unsigned long>::snapshot_log_entry &sle(*crashedThread->snapshotLog.begin());
        VexPtr<MachineState<unsigned long> > snapshotMs(sle.ms->dupeSelf());
	cm->calculate_relevant_addresses(snapshotMs,
					 lf,
					 sle.ptr,
					 ALLOW_GC);

	/* Build the overall interesting address list */
	oracle.interesting_addresses.clear();
	for (CrashMachine::contentT::iterator it = cm->content->begin();
	     it != cm->content->end();
	     it++) {
		printf("CMN %lx -> %s ",
		       it.key().rip,
		       it.value().first->name());
		for (std::set<unsigned long>::iterator it2 = it.value().second.begin();
		     it2 != it.value().second.end();
		     it2++) {
			oracle.interesting_addresses.insert(*it2);
			printf("%lx ", *it2);
		}
		printf("\n");
	}

#if 0 /* Unconfuse emacs */
(
#endif
	printf("Interesting addresses:\n");
	for (std::set<unsigned long>::iterator it = oracle.interesting_addresses.begin();
	     it != oracle.interesting_addresses.end();
	     it++)
		printf("%lx\n", *it);

	/* Collect the logs of those addresses */
	snapshotMs = sle.ms->dupeSelf();
	oracle.collect_interesting_access_log(
		snapshotMs,
		lf,
		sle.ptr,
		ALLOW_GC);

	printf("Critical sections:\n");
	/* Now, for each machine, walk over the relevant address logs
	 * and figure out when the CMN goes green and red. */
	for (CrashMachine::contentT::iterator cmn_it = cm->content->begin();
	     cmn_it != cm->content->end();
	     cmn_it++) {
		cmn_it.value().first = removeProbablyConstantReferences(cmn_it.value().first, oracle, ms,
									crashedThread);
		findRemoteCriticalSections(cmn_it.value().first, cmn_it.key(), oracle, ms);
		LibVEX_maybe_gc(ALLOW_GC);
	}

	dbg_break("finished");

	return 0;
}
