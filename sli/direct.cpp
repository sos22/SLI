#include <typeinfo>
#include <deque>

#include "sli.h"

#include "libvex_guest_offsets.h"

#include "guest_generic_bb_to_IR.h"
#include "guest_amd64_defs.h"

class CrashTimestamp : public Named {
protected:
	char *mkName() const { return my_asprintf("%d:%d:%d", tid._tid(),
						  decode_nr,
						  statement_nr); }					    
public:
	ThreadId tid; /* Which thread are we talking about */
	unsigned statement_nr; /* How many statements have we run in this block */
	unsigned decode_nr; /* How many blocks have we run in this thread */
	CrashTimestamp(ThreadId _tid,
		       unsigned _stmt,
		       unsigned _decode)
		: tid(_tid),
		  statement_nr(_stmt),
		  decode_nr(_decode)
	{
	}
	CrashTimestamp() {}
	CrashTimestamp reduceOneStatement() const {
		assert(statement_nr != 0);
		return CrashTimestamp(tid, statement_nr - 1, decode_nr);
	}
	CrashTimestamp reduceOneBlock(int n) const {
		assert(statement_nr == 0);
		return CrashTimestamp(tid, n, decode_nr - 1);
	}
	unsigned long hash() const {
		return tid.hash() ^ (statement_nr * 7) ^ (decode_nr * 4519);
	}
	bool operator==(const CrashTimestamp &c) const {
		return tid == c.tid && statement_nr == c.statement_nr &&
			decode_nr == c.decode_nr;
	}
	bool operator<(const CrashTimestamp &t) const {
		assert(tid == t.tid);
		if (decode_nr < t.decode_nr) {
			return true;
		} else if (decode_nr == t.decode_nr) {
			if (statement_nr < t.statement_nr)
				return true;
			else
				return false;
		} else {
			return false;
		}
	}
};

class CrashExpression;

class CPMapper {
public:
	virtual CrashExpression *operator()(CrashExpression *e) { return e; }
};

class CrashExpression : public GarbageCollected<CrashExpression>, public Named {
	mutable unsigned long hashval;
	mutable bool have_hash;

	static const int nr_intern_heads = 4095;
	static CrashExpression *intern_heads[nr_intern_heads];
	CrashExpression *next_intern;
	CrashExpression **pprev_intern;

	CrashExpression *simplified;
	unsigned simplified_hardness;
protected:
	CrashExpression() { pprev_intern = &next_intern; }
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
		unsigned long newhash = _hash();
		if (newhash == hashval)
			return;
		hashval = newhash;
		if (next_intern)
			next_intern->pprev_intern = pprev_intern;
		*pprev_intern = next_intern;
		int head = hashval % nr_intern_heads;
		next_intern = intern_heads[head];
		if (intern_heads[head])
			intern_heads[head]->pprev_intern = &next_intern;
		intern_heads[head] = this;
		pprev_intern = &intern_heads[head];
	}

	static CrashExpression *intern(CrashExpression *what) {
		CrashExpression *cursor;
		int head = what->hash() % nr_intern_heads;
		cursor = intern_heads[head];
		while (cursor) {
			if (cursor->eq(what)) {
				if (cursor->next_intern)
					cursor->next_intern->pprev_intern = cursor->pprev_intern;
				*cursor->pprev_intern = cursor->next_intern;
				what = cursor;
				break;
			}
			cursor = cursor->next_intern;
		}
		what->next_intern = intern_heads[head];
		if (intern_heads[head])
			intern_heads[head]->pprev_intern = &what->next_intern;
		intern_heads[head] = what;
		what->pprev_intern = &intern_heads[head];
		return what;
	}

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
	NAMED_CLASS
};

CrashExpression *CrashExpression::intern_heads[CrashExpression::nr_intern_heads];

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
};

class CrashExpressionLoad : public CrashExpression {
	CrashExpressionLoad(CrashTimestamp _when, CrashExpression *_addr)
		: when(_when), addr(_addr)
	{
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
	static CrashExpression *get(CrashTimestamp when,
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
};

#define mk_binop(name, hashop)						\
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
	};

#define most_binops(x)						\
	x(Add, +)						\
	x(Xor, ^)						\
	x(And, &)						\
	x(Or, |)						\
	x(Shl, <<)

#define all_binops(x)				\
	most_binops(x)				\
	x(Equal, * 46278 + 472389 *)

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
};

class CrashExpressionUnsignedLessThan : public CrashExpressionBinop {		
	CrashExpressionUnsignedLessThan(CrashExpression *l,		
				      CrashExpression *r)		
		: CrashExpressionBinop(l, r)			       
	{							
	}							
	unsigned long _hash() const {				
		return l->hash() * 4451 + r->hash() * 9227;
	}
protected:							
	const char *__mkName() const { return "UnsignedLessThan"; }			
	CrashExpression *_simplify(unsigned hardness) {
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
	bool _eq(const CrashExpression *o) const {			
		const CrashExpressionUnsignedLessThan *t =			
			dynamic_cast<const CrashExpressionUnsignedLessThan *>(o); 
		if (t)							
			return t->l->eq(l) && t->r->eq(r);		
		else							
			return false;					
	}								
public:								
	static CrashExpression *get(CrashExpression *l,			
				    CrashExpression *r) {		
		return intern(new CrashExpressionUnsignedLessThan(l, r))->simplify();	
	}								
	CrashExpression *semiDupe(CrashExpression *l, CrashExpression *r) { 
		if (l == this->l && r == this->r)			
			return this;					
		return get(l, r);					
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
CrashExpressionShl::_simplify(unsigned hardness)
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
};

#define mk_unop(name, op)						\
	class CrashExpression ## name : public CrashExpressionUnary {	\
		CrashExpression ## name (CrashExpression *_l)		\
		: CrashExpressionUnary(_l)				\
		{							\
		}							\
	protected:							\
	const char *__mkName() const { return #name ; }			\
	unsigned long _hash() const {					\
		return op l->hash();					\
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
	};

mk_unop(Neg, -)
mk_unop(Not, 0x7f8ff8ac608cb30d ^)
mk_unop(BadAddr, 76348956389 *)

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
protected:
	char *mkName() const {
		switch (type) {
		case CM_NODE_LEAF:
			return my_asprintf("%lx: leaf{%s}", rip, leafCond->name());
		case CM_NODE_STUB:
			return my_asprintf("%lx: stub", rip);
		case CM_NODE_BRANCH:
			return my_asprintf("%lx: branch{%s, %s, %s}",
					   rip,
					   branchCond->name(),
					   trueTarget ? trueTarget->name() : "(null)",
					   falseTarget ? falseTarget->name() : "(null)");
		}
		abort();
	}
public:
	CrashMachineNode(unsigned long _rip, CrashExpression *e) {
		rip = _rip;
		type = CM_NODE_LEAF;
		leafCond = e;
	}
	CrashMachineNode(unsigned long _rip) {
		rip = _rip;
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
		switch (type) {
		case CM_NODE_LEAF:
		case CM_NODE_STUB:
			return;
		case CM_NODE_BRANCH:
			assert(trueTarget || falseTarget);
			if (trueTarget)
				trueTarget->sanity_check();
			if (falseTarget)
				falseTarget->sanity_check();
			return;
		}
		abort();
	}

	struct store_record {
		CrashTimestamp when;
		CrashExpression *addr;
		CrashExpression *data;
		store_record(CrashTimestamp _when,
			     CrashExpression *_addr,
			     CrashExpression *_data)
			: when(_when), addr(_addr), data(_data)
		{
		}
	};

	unsigned long rip;
	std::deque<store_record> stores;

	enum { CM_NODE_LEAF = 52, CM_NODE_BRANCH, CM_NODE_STUB } type;

	/* Crash condition for leaf nodes */
	CrashExpression *leafCond;

	/* Internal binary branches.  branchCond might be constant, in
	   which case only one of the targets will relevant (and the
	   other might well be NULL). */
	CrashExpression *branchCond;
	CrashMachineNode *trueTarget;
	CrashMachineNode *falseTarget;
	bool capturedExecutionTookTrueBranch;

	CrashMachineNode *map(CPMapper &m)
	{
		CrashMachineNode *res;
		switch (type) {
		case CM_NODE_LEAF: {
			CrashExpression *l = leafCond->map(m);
			if (l == leafCond)
				return this;
			res = new CrashMachineNode(rip);
			res->type = CM_NODE_LEAF;
			res->leafCond = l;
			break;
		}
		case CM_NODE_BRANCH: {
			CrashExpression *c = branchCond->map(m);
			CrashMachineNode *t = trueTarget ? trueTarget->map(m) : NULL;
			CrashMachineNode *f = falseTarget ? falseTarget->map(m) : NULL;
			if (c == branchCond && t == trueTarget &&
			    f == falseTarget)
				return this;
			res = new CrashMachineNode(rip);
			res->type = CM_NODE_BRANCH;
			res->branchCond = c;
			res->trueTarget = t;
			res->falseTarget = f;
			break;
		}
		case CM_NODE_STUB:
			return this;
		}
		for (std::deque<store_record>::iterator it = stores.begin();
		     it != stores.end();
		     it++) {
			store_record n(it->when,
				       it->addr->map(m),
				       it->data->map(m));
			res->stores.push_back(n);
		}
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

	void changed() { clearName(); }
	void visit(HeapVisitor &hv) {
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
		for (std::deque<store_record>::iterator it = stores.begin();
		     it != stores.end();
		     it++) {
			hv(it->addr);
			hv(it->data);
		}
	}
	NAMED_CLASS
};

class CrashMachine : public GarbageCollected<CrashMachine>, public Named {
	typedef gc_map<unsigned long,
		       CrashMachineNode *,
		       __default_hash_function<unsigned long>,
		       __default_eq_function<unsigned long>,
		       __visit_function_heap<CrashMachineNode *> >
	nodeMapT;
	nodeMapT *nodeMap;
protected:
	virtual ~CrashMachine() {}
	char *mkName() const;
public:
	typedef nodeMapT::iterator iterator;
	CrashMachineNode *start;
	CrashTimestamp when;

	void changed() { clearName(); }
	CrashMachine(CrashTimestamp _when)
		: nodeMap(new nodeMapT()),
		  when(_when)
	{
	}
	CrashMachine()
		: nodeMap(new nodeMapT())
	{
	}

	CrashMachineNode *get(unsigned long rip) {
		if (rip == 0x7fde5be4601a)
			return get(0x7fde5be45fc8);
		if (nodeMap->hasKey(rip))
			return nodeMap->get(rip);
		else
			return NULL;
	}
	void set(CrashMachineNode *cmn) {
		if (!nodeMap->hasKey(cmn->rip)) {
			/* If we find several possible crash reasons
			   for one location, we pick the first one
			   which we find, because it tends to be the
			   easiest to analyse. */
			nodeMap->set(cmn->rip, cmn);
		}
	}

	iterator begin() { return nodeMap->begin(); }
	iterator end() { return nodeMap->end(); }

	void visit(HeapVisitor &hv) { hv(nodeMap); hv(start); }
	NAMED_CLASS
};

char *
CrashMachine::mkName() const
{
	return my_asprintf("%s start at %s",
			   when.name(),
			   start->name());
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
#define do_binop(x, _1)							\
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
		default:
			abort();
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
		case Iop_Not8:
		case Iop_Not16:
		case Iop_Not32:
		case Iop_Not64:
			return CrashExpressionBitwiseNot::get(
				CrashExpression::get(e->Iex.Unop.arg));
		default:
			abort();
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
			abort();
		}
	case Iex_Mux0X:
		return CrashExpressionMux::get(
			CrashExpression::get(e->Iex.Mux0X.cond),
			CrashExpression::get(e->Iex.Mux0X.expr0),
			CrashExpression::get(e->Iex.Mux0X.exprX));
	default:
		abort();
	}
}

static CrashMachineNode *
exprToCrashReason(CrashTimestamp when, IRExpr *expr)
{
	return NULL;
}

static CrashMachineNode *
statementToCrashReason(CrashTimestamp when, IRStmt *irs, unsigned long rip)
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
		if (!r)
			r = new CrashMachineNode(
				rip,
				CrashExpressionBadAddr::get(
					CrashExpression::get(irs->Ist.Store.addr)));
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
			return new CrashMachineNode(
				rip,
				CrashExpressionBadAddr::get(
					CrashExpression::get(irs->Ist.Dirty.details->args[0])));
		}
		return NULL;
	}
}

static CrashMachineNode *
backtrack_crash_machine_node_for_statements(
	CrashTimestamp *when,
	CrashMachineNode *node,
	IRStmt **statements,
	int nr_statements,
	bool ignore_branches)
{
	int i;

	if (node->falseTarget) {
		assert(node->falseTarget->rip != node->rip);
	}

	for (i = nr_statements - 1; i >= 0; i--)  {
		IRStmt *stmt = statements[i];

		*when = when->reduceOneStatement();

		switch (stmt->tag) {
		case Ist_NoOp:
		case Ist_AbiHint:
		case Ist_MBE:
		case Ist_IMark:
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
					*when,
					CrashExpression::get(
						stmt->Ist.Dirty.details->args[0])));
			break;

		case Ist_Store:
			node->stores.push_front(
				CrashMachineNode::store_record(
					*when,
					CrashExpression::get(
						stmt->Ist.Store.addr),
					CrashExpression::get(
						stmt->Ist.Store.data)));
			break;

		case Ist_Exit:
			if (!ignore_branches) {
				/* Only handle two-way branches */
				assert(!node->trueTarget);
				node->trueTarget = new CrashMachineNode(stmt->Ist.Exit.dst->Ico.U64);
				node->trueTarget->type = CrashMachineNode::CM_NODE_STUB;
				node->branchCond = CrashExpression::get(stmt->Ist.Exit.guard);
				assert(node->trueTarget->rip != node->falseTarget->rip);
			}
			break;

		case Ist_CAS:
			node = node->rewriteTemporary(
				stmt->Ist.CAS.details->oldLo,
				CrashExpressionLoad::get(
					*when,
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


/* We know that after some instruction the crash machine will be
   @successor. What's the crash machine before the instruction?  The
   instruction is represented as a list of VEX statements. */
/* This is only correct for internal nodes (i.e. not leaves) where we
   don't take any branches in the instruction.  There can be branches
   in the instruction, we just can't take them. */
static CrashMachineNode *
crashMachineNodeForInstruction(CrashTimestamp *when,
			       CrashMachineNode *successor,
			       IRStmt **statements,
			       int nr_statements)
{
	if (successor) {
		assert(successor->rip != statements[0]->Ist.IMark.addr);
	}

	CrashMachineNode *res = new CrashMachineNode(statements[0]->Ist.IMark.addr);

	res->type = CrashMachineNode::CM_NODE_BRANCH;
	res->branchCond = CrashExpressionConst::get(0);
	res->falseTarget = successor;

	res = backtrack_crash_machine_node_for_statements(when, res, statements, nr_statements, false);

	return res;
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
	assert(cmn1->type != CrashMachineNode::CM_NODE_STUB);
	if (cmn1->type == CrashMachineNode::CM_NODE_LEAF) {
		return cmn1->leafCond->eq(cmn2->leafCond);
	} else {
		assert(cmn1->type == CrashMachineNode::CM_NODE_BRANCH);
		return cmn1->branchCond->eq(cmn2->branchCond) &&
			cmns_bisimilar(cmn1->trueTarget,
				       cmn2->trueTarget) &&
			cmns_bisimilar(cmn1->falseTarget,
				       cmn2->falseTarget);
	}
}

static CrashMachineNode *
easy_simplify_cmn(CrashMachineNode *cmn)
{
	/* Do a very basic kind of CMN simplification */
	bool progress = true;
	while (progress) {
		progress = false;
		while (cmn->type == CrashMachineNode::CM_NODE_BRANCH &&
		       !cmn->trueTarget) {
			cmn = cmn->falseTarget;
			progress = true;
		}
		while (cmn->type == CrashMachineNode::CM_NODE_BRANCH &&
		       !cmn->falseTarget) {
			cmn = cmn->trueTarget;
			progress = true;
		}
		while (cmn->type == CrashMachineNode::CM_NODE_BRANCH &&
		       cmns_bisimilar(cmn->trueTarget, cmn->falseTarget)) {
			cmn = cmn->trueTarget;
			progress = true;
		}
	}
	return cmn;
}

static void
updateCrashMachineForBlock(CrashMachine *cm,
			   unsigned long start,
			   int exit_idx,
			   MachineState<unsigned long> *ms,
			   bool leaf)
{
	IRSB *irsb = ms->addressSpace->getIRSBForAddress(start);
	int stmt_start, stmt_end;
	CrashMachineNode *node;
	unsigned long rip;

	assert(exit_idx <= irsb->stmts_used + 1);

	if (!leaf && exit_idx != irsb->stmts_used + 1) {
		/* Special case when we have a taken branch */
		int x;
		assert(irsb->stmts[exit_idx - 1]->tag == Ist_Exit);
		for (x = exit_idx - 1; irsb->stmts[x]->tag != Ist_IMark; x--)
			;
		node = new CrashMachineNode(irsb->stmts[x]->Ist.IMark.addr);
		node->type = CrashMachineNode::CM_NODE_BRANCH;
		node->branchCond = CrashExpression::get(irsb->stmts[exit_idx-1]->Ist.Exit.guard);

		/* Hackety hackety hack: assume that conditional
		   branches are always the last statement in the
		   block. */
		if (exit_idx == irsb->stmts_used) {
			if (irsb->next->tag == Iex_Const)
				rip = irsb->next->Iex.Const.con->Ico.U64;
			else
				rip = 0;
		} else {
			assert(irsb->stmts[exit_idx]->tag == Ist_IMark);
			rip = irsb->stmts[exit_idx]->Ist.IMark.addr;
		}

		node->falseTarget = new CrashMachineNode(rip);
		node->falseTarget->type = CrashMachineNode::CM_NODE_STUB;
		node->trueTarget = cm->start;
		node->capturedExecutionTookTrueBranch = true;
		stmt_end = exit_idx - 2;

		cm->when = cm->when.reduceOneBlock(stmt_end);
		node = backtrack_crash_machine_node_for_statements(
			&cm->when,
			node,
			irsb->stmts + x,
			stmt_end - x,
			false);
		if (x == 0) {
			cm->start = node;
			cm->changed();
			return;
		}
		stmt_end = x - 1;
	} else if (leaf) {
		node = cm->start;
		if (node->falseTarget) {
			assert(node->falseTarget->rip != node->rip);
		}
		stmt_end = exit_idx;
		cm->when = cm->when.reduceOneBlock(stmt_end+1);
	} else {
		node = cm->start;
		stmt_end = exit_idx - 2;
		cm->when = cm->when.reduceOneBlock(stmt_end+1);
	}

	if (node->falseTarget) {
		assert(node->falseTarget->rip != node->rip);
	}

	while (stmt_end > 0) {
		for (stmt_start = stmt_end;
		     irsb->stmts[stmt_start]->tag != Ist_IMark;
		     stmt_start--)
			;
		rip = irsb->stmts[stmt_start]->Ist.IMark.addr;
		if (node->falseTarget) {
			assert(node->falseTarget->rip != node->rip);
		}
		assert(node->rip != rip);
		node = crashMachineNodeForInstruction(
			&cm->when, node, irsb->stmts + stmt_start, stmt_end - stmt_start + 1);
		if (node->falseTarget) {
			assert(node->falseTarget->rip != node->rip);
		}

		assert(rip == node->rip);
		cm->set(node);
		stmt_end = stmt_start - 1;
	}

	cm->start = node;
	cm->changed();
}

class SimplifyHardMapper : public CPMapper {
public:
	CrashExpression *operator()(CrashExpression *ce) {
		if (CrashExpressionStackPtr *p =
		    dynamic_cast<CrashExpressionStackPtr *>(ce))
			return p->l;
		else
			return ce->simplify(1000);
	}
};

static CrashMachineNode *
backtrack_crash_machine_node_for_instruction(
	MachineState<unsigned long> *ms,
	CrashMachineNode *node)
{
	IRSB *irsb = ms->addressSpace->getIRSBForAddress(node->rip);
	int instr_end;
	for (instr_end = 1;
	     instr_end < irsb->stmts_used &&
		     irsb->stmts[instr_end]->tag != Ist_IMark &&
		     irsb->stmts[instr_end]->tag != Ist_Exit;
	     instr_end++)
		;
	CrashTimestamp when(ThreadId(),
			    instr_end,
			    99);
	return backtrack_crash_machine_node_for_statements(
		&when, node, irsb->stmts, instr_end, false);
}

static unsigned long
extract_call_follower(IRSB *irsb)
{
	/* We expect a call to look like this:

	   0:   ------ IMark(0x7fde5bdd85a7, 5) ------
	   1:   t0 = Sub64(GET:I64(32),0x8:I64)
	   2:   PUT(32) = t0
	   3:   STle(t0) = 0x7fde5bdd85ac:I64
	   4:   t1 = 0x7fde5be62750:I64
	   5:   ====== AbiHint(Sub64(t0,0x80:I64), 128, t1) ======
	   goto {Call} 0x7fde5be62750:I64
   
	   Or so.  The WrTmp at statement 4 is optional, but the rest
	   has to be there.  We process statements in reverse order
	   from the end, checking that things match as we go. */
	int idx = irsb->stmts_used - 1;

	if (idx < 0 ||
	    irsb->stmts[idx]->tag != Ist_AbiHint)
		abort();
	idx--;
	if (idx < 0)
		abort();
	if (irsb->stmts[idx]->tag == Ist_WrTmp)
		idx--;
	if (idx < 0)
		abort();
	if (irsb->stmts[idx]->tag != Ist_Store)
		abort();
	if (irsb->stmts[idx]->Ist.Store.data->tag != Iex_Const)
		abort();
	return irsb->stmts[idx]->Ist.Store.data->Iex.Const.con->Ico.U64;
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
public:
	CrashCFGNode(unsigned long r, unsigned long t, unsigned long f)
		: rip(r), trueTargetRip(t), falseTargetRip(f)
	{}
	unsigned long rip;
	unsigned long trueTargetRip;
	bool brokeCycleTrueTarget;
	CrashCFGNode *trueTarget;

	unsigned long falseTargetRip;
	bool brokeCycleFalseTarget;
	CrashCFGNode *falseTarget;

	bool visitedByCycleBreaker;
	bool onCycleBreakerPath;

	CrashMachineNode *cmn;

	void visit(HeapVisitor &hv) { hv(trueTarget); hv(falseTarget); hv(cmn); }
	NAMED_CLASS
};

class CrashCFG : public GarbageCollected<CrashCFG> {
	typedef gc_map<unsigned long, CrashCFGNode *,
		       __default_hash_function<unsigned long>,
		       __default_eq_function<unsigned long>,
		       __visit_function_heap<CrashCFGNode *> > nodeMapT;
	nodeMapT *nodeMap;

	/* Things which we need to visit, but haven't reached yet. */
	std::vector<unsigned long> grey;

	std::vector<unsigned long> roots;

	void build_cfg(MachineState<unsigned long> *ms,
		       CrashMachine *partial_cm);
	void resolve_stubs();
	void break_cycles(CrashMachine *partial_cm);
	void break_cycles_visit_branch(CrashCFGNode *n,
				       CrashCFGNode *&branch,
				       bool &branchGuard,
				       CrashMachine *partial_cm);
	void break_cycles_from(CrashCFGNode *n,
			       CrashMachine *partial_cm);
	void calculate_cmns(CrashMachine *partial_cm,
			    MachineState<unsigned long> *ms);
public:
	CrashCFG()
		: nodeMap(new nodeMapT())
	{
	}

	void add_root(unsigned long x) { roots.push_back(x); grey.push_back(x); }
	void build(MachineState<unsigned long> *ms,
		   CrashMachine *partial_cm);
	CrashMachineNode *get_cmn(unsigned long rip) {
		return nodeMap->get(rip)->cmn;
	}

	void visit(HeapVisitor &hv) { hv(nodeMap); }
	NAMED_CLASS
};


static bool
get_fallthrough_rip(IRSB *irsb, int instr_end, unsigned long *out, bool *do_pop)
{
	if (instr_end == irsb->stmts_used) {
		if (irsb->jumpkind == Ijk_Call) {
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

void
CrashCFG::build_cfg(MachineState<unsigned long> *ms,
		    CrashMachine *partial_cm)
{
	static unsigned nr_nodes = 0;
	while (!grey.empty()) {
		unsigned long rip = grey.back();
		grey.pop_back();
		if (nodeMap->hasKey(rip))
			continue;
		IRSB *irsb = ms->addressSpace->getIRSBForAddress(rip);
		int instr_end;
		unsigned long nonFallThroughTarget = 0;
		for (instr_end = 1;
		     instr_end < irsb->stmts_used &&
			     irsb->stmts[instr_end]->tag != Ist_IMark;
		     instr_end++) {
			if (irsb->stmts[instr_end]->tag == Ist_Exit) {
				assert(nonFallThroughTarget == 0);
				nonFallThroughTarget =
					irsb->stmts[instr_end]->Ist.Exit.dst->Ico.U64;
			}
		}
		unsigned long fallThroughTarget = 0;
		get_fallthrough_rip(irsb, instr_end, &fallThroughTarget, NULL);
		if (nonFallThroughTarget)
			grey.push_back(nonFallThroughTarget);
		if (!fallThroughTarget &&
		    instr_end == irsb->stmts_used &&
		    irsb->jumpkind == Ijk_Ret) {
			/* Cheat and grab the return address out of
			   the dynamic trace, if it's available. */
			CrashMachineNode *dynamic =
				partial_cm->get(rip);
			if (dynamic && dynamic->falseTarget)
				fallThroughTarget = dynamic->falseTarget->rip;
		}

		if (fallThroughTarget)
			grey.push_back(fallThroughTarget);
		CrashCFGNode *newNode =
			new CrashCFGNode(rip, nonFallThroughTarget, fallThroughTarget);
		nodeMap->set(rip, newNode);
		nr_nodes++;
	}
	printf("CFG has %d nodes.\n", nr_nodes);
}

void
CrashCFG::resolve_stubs()
{
	for (nodeMapT::iterator it = nodeMap->begin();
	     it != nodeMap->end();
	     it++) {
		CrashCFGNode *n = it.value();
		if (n->trueTargetRip)
			n->trueTarget = nodeMap->get(n->trueTargetRip);
		if (n->falseTargetRip)
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
void
CrashCFG::break_cycles_visit_branch(CrashCFGNode *n,
				    CrashCFGNode *&branch,
				    bool &branchGuard,
				    CrashMachine *partial_cm)
{
	if (branch) {
		if (branch->onCycleBreakerPath) {
			/* We have a cycle.  Break it. */
			branchGuard = true;
			branch = NULL;
		} else {
			break_cycles_from(branch, partial_cm);
		}
	}
}
void
CrashCFG::break_cycles_from(CrashCFGNode *n,
			    CrashMachine *partial_cm)
{
	if (n->visitedByCycleBreaker)
		return;
	assert(!n->onCycleBreakerPath);
	n->onCycleBreakerPath = true;

	bool visitTrueTargetFirst = false;

	/* If the partial CM has a node for this RIP, we prefer to
	 * visit the branch which it exitted on first.  This helps
	 * keep the approximation as accurate as possible on the path
	 * which the program actually executed.  Otherwise, we visit
	 * the false path first, as that corresponds to the
	 * fall-through execution, and that tends to encourage the
	 * visiter to keep the simplest possible execution and avoids
	 * unnecessary partitioning. */
	CrashMachineNode *partial = partial_cm->get(n->rip);
	if (partial)
		visitTrueTargetFirst = partial->capturedExecutionTookTrueBranch;

	if (visitTrueTargetFirst) {
		break_cycles_visit_branch(n, n->trueTarget, n->brokeCycleTrueTarget, partial_cm);
		break_cycles_visit_branch(n, n->falseTarget, n->brokeCycleFalseTarget, partial_cm);
	} else {
		break_cycles_visit_branch(n, n->falseTarget, n->brokeCycleFalseTarget, partial_cm);
		break_cycles_visit_branch(n, n->trueTarget, n->brokeCycleTrueTarget, partial_cm);
	}
	n->onCycleBreakerPath = false;
	n->visitedByCycleBreaker = true;
}
void
CrashCFG::break_cycles(CrashMachine *partial_cm)
{
	/* We start enumeration from the roots, because that helps to
	   keep the important bits of the graph structure intact. */
	for (std::vector<unsigned long>::iterator it = roots.begin();
	     it != roots.end();
	     it++)
		break_cycles_from(nodeMap->get(*it), partial_cm);
}

void
CrashCFG::calculate_cmns(CrashMachine *partial_cm,
			 MachineState<unsigned long> *ms)
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
			CrashMachineNode *cmn;

			/* If the partial CM has a stub-free CMN for
			   this RIP, just use that. */
			cmn = partial_cm->get(node->rip);
			if (cmn && cmn->isStubFree()) {
				node->cmn = cmn;
				progress = true;
				continue;
			}
			if (node->trueTarget && !node->trueTarget->cmn)
				continue;
			if (node->falseTarget && !node->falseTarget->cmn)
				continue;
			/* Okay, both exits either have a CMN or don't
			 * exist.  That means we should be able to
			 * derive a CMN for this node. */
			progress = true;
			if (!node->trueTarget && !node->falseTarget) {
				/* Don't know where we go after this
				   node, and it wasn't executed in the
				   dynamic execution -> assume it's
				   sufficiently different from the
				   captured one that we avoid the
				   crash. */
				node->cmn = new CrashMachineNode(
					node->rip,
					CrashExpressionConst::get(0));
				continue;
			}

			IRSB *irsb = ms->addressSpace->getIRSBForAddress(node->rip);
			int instr_end;
			for (instr_end = 1;
			     instr_end < irsb->stmts_used && irsb->stmts[instr_end]->tag != Ist_IMark;
			     instr_end++)
				;
			cmn = new CrashMachineNode(node->rip);
			cmn->type = CrashMachineNode::CM_NODE_BRANCH;
			if (node->falseTarget && node->trueTarget) {
				/* We have both fall-through and
				   non-fall-through exits. */
				assert(irsb->stmts[instr_end-1]->tag == Ist_Exit);
				cmn->branchCond = CrashExpression::get(irsb->stmts[instr_end-1]->Ist.Exit.guard);
				cmn->trueTarget = node->trueTarget->cmn;
				cmn->falseTarget = node->falseTarget->cmn;

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
				cmn->branchCond = CrashExpressionConst::get(0);
				cmn->falseTarget = node->falseTarget->cmn;

				if (instr_end == irsb->stmts_used &&
				    irsb->jumpkind == Ijk_Call) {
					/* We pretty much ignore
					   calls, but we do have to do
					   enough fixup to pop the
					   return address. */
					cmn = cmn->rewriteRegister(
						OFFSET_amd64_RSP,
						CrashExpressionAdd::get(
							CrashExpressionConst::get(8),
							CrashExpressionRegister::get(OFFSET_amd64_RSP)));
				}

			} else {
				/* We have a true target but not a
				   false one.  The fall-through branch
				   must have been culled. */
				assert(node->trueTarget);
				assert(irsb->stmts[instr_end-1]->tag == Ist_Exit);
				instr_end--; /* Ignore final branch in IRSB */
				cmn->branchCond = CrashExpressionConst::get(1);
				cmn->trueTarget = node->trueTarget->cmn;
			}

			/* cmn is now valid at the exit of this
			   instruction.  Backtrack it to get the CMN
			   for the start of the instruction. */
			CrashTimestamp when(ThreadId(),
					    12345678,
					    instr_end);
			assert(cmn->isStubFree());
			cmn = backtrack_crash_machine_node_for_statements(
				&when,
				cmn,
				irsb->stmts,
				instr_end,
				true);
			assert(cmn->isStubFree());

			/* All done. */
			node->cmn = cmn;
		}
	}
}

/* Build the acyclic CFG and use that to infer ``correct'' crash
   machine nodes for every instruction. */
void
CrashCFG::build(MachineState<unsigned long> *ms,
		CrashMachine *partial_cm)
{
	build_cfg(ms, partial_cm);
	resolve_stubs();
	break_cycles(partial_cm);
	calculate_cmns(partial_cm, ms);
}

static CrashMachineNode *
getStaticMachine(CrashMachine *dynamic_cm,
		 CrashMachine *static_cm,
		 CrashMachineNode *dynamic_cmn,
		 MachineState<unsigned long> *ms)
{
	CrashMachineNode *static_cmn;

	if (!dynamic_cmn)
		return NULL;

	static_cmn = static_cm->get(dynamic_cmn->rip);
	if (static_cmn) {
		printf("memocache hit: %s -> %s\n", dynamic_cmn->name(),
		       static_cmn->name());
		return static_cmn;
	}

	if (dynamic_cmn->type == CrashMachineNode::CM_NODE_LEAF) {
		static_cmn = dynamic_cmn;
	} else if (dynamic_cmn->type == CrashMachineNode::CM_NODE_BRANCH) {
		static_cmn = new CrashMachineNode(dynamic_cmn->rip);
		static_cmn->type = CrashMachineNode::CM_NODE_BRANCH;
		static_cmn->branchCond = dynamic_cmn->branchCond;
		assert(dynamic_cmn->trueTarget || dynamic_cmn->falseTarget);
		static_cmn->trueTarget =
			getStaticMachine(dynamic_cm,
					 static_cm,
					 dynamic_cmn->trueTarget,
					 ms);
		static_cmn->falseTarget =
			getStaticMachine(dynamic_cm,
					 static_cm,
					 dynamic_cmn->falseTarget,
					 ms);
		assert(static_cmn->trueTarget || static_cmn->falseTarget);
		assert(static_cmn->isStubFree());
		static_cmn = backtrack_crash_machine_node_for_instruction(
			ms, static_cmn);
		assert(static_cmn->isStubFree());
	} else {
		assert(dynamic_cmn->type == CrashMachineNode::CM_NODE_STUB);

		CrashCFG *cfg = new CrashCFG();
		cfg->add_root(dynamic_cmn->rip);
		cfg->build(ms, dynamic_cm);
		static_cmn = cfg->get_cmn(dynamic_cmn->rip);
		assert(static_cmn->isStubFree());
	}

	assert(static_cmn->isStubFree());
	assert(static_cmn->rip == dynamic_cmn->rip);
	static_cm->set(static_cmn);

	return easy_simplify_cmn(static_cmn);
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
		return cmn;
	case CrashMachineNode::CM_NODE_BRANCH:
		assert(cmn->trueTarget || cmn->falseTarget);
		cmn->sanity_check();
		cmn->falseTarget = simplify_cmn(cmn->falseTarget);
		cmn->trueTarget = simplify_cmn(cmn->trueTarget);
		assert(cmn->trueTarget || cmn->falseTarget);
		cmn->sanity_check();
		if (!cmn->falseTarget) {
			cmn = cmn->trueTarget;
			break;
		}
		if (!cmn->trueTarget) {
			cmn = cmn->falseTarget;
			break;
		}
		unsigned long lc;
		cmn->branchCond = cmn->branchCond->simplify(1000);
		if (cmn->branchCond->isConstant(lc)) {
			if (lc)
				cmn = cmn->trueTarget;
			else
				cmn = cmn->falseTarget;
		} else {
			if (cmn->falseTarget->rip < cmn->trueTarget->rip) {
				CrashMachineNode *t;
				cmn->branchCond = CrashExpressionNot::get(cmn->branchCond);
				t = cmn->trueTarget;
				cmn->trueTarget = cmn->falseTarget;
				cmn->falseTarget = t;
			}
			if (cmns_bisimilar(cmn->trueTarget, cmn->falseTarget))
				cmn = cmn->trueTarget;
		}
		cmn->changed();
		break;
	default:
		abort();
	}
	cmn->sanity_check();
	return cmn;
}
/* Attempt to convert the crash machine which we derived dynamically
   into a shiny new static one. */
static CrashMachine *
staticise(CrashMachine *cm, MachineState<unsigned long> *ms)
{
	CrashMachine *res = new CrashMachine();

	res->start = getStaticMachine(cm, res, cm->start, ms);
	assert(res->start->isStubFree());
	res->start->sanity_check();
	res->start = simplify_cmn(res->start);
	for (CrashMachine::iterator it = res->begin();
	     it != res->end();
	     it++) {
		it.value() = simplify_cmn(it.value());
	}
	return res;
}

int
main(int argc, char *argv[])
{
	init_sli();

	LogReaderPtr ptr;
	VexPtr<LogReader<unsigned long> > lf(LogFile::open(argv[1], &ptr));
	VexPtr<MachineState<unsigned long> > ms(MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr, ALLOW_GC));

	Interpreter<unsigned long> i(ms);
	i.replayLogfile(lf, ptr, ALLOW_GC);

	Thread<unsigned long> *crashedThread;
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

	printf("Selected thread %d as crasher\n", crashedThread->tid._tid());

	printf("Crashed at step %d in:\n", crashedThread->currentIRSBOffset);
	ppIRSB(crashedThread->currentIRSB);

	assert(crashedThread->currentIRSBOffset != 0);

	/* Step one: examine the current statement to figure out the
	   proximal cause of the crash. */
	CrashTimestamp when(crashedThread->tid,
			    crashedThread->currentIRSBOffset - 1,
			    crashedThread->decode_counter);
	CrashMachineNode *cmn;
	{
		int idx;
		for (idx = crashedThread->currentIRSBOffset;
		     crashedThread->currentIRSB->stmts[idx]->tag != Ist_IMark;
		     idx--)
			;
		cmn = statementToCrashReason(
			when,
			crashedThread->currentIRSB->stmts[crashedThread->currentIRSBOffset - 1],
			crashedThread->currentIRSB->stmts[idx]->Ist.IMark.addr + 1);
	}

	printf("Proximal cause is %s\n", cmn->name());

	VexPtr<CrashMachine> cm(new CrashMachine(when));
	cm->start = cmn;
	cmn->sanity_check();

	/* Step two: work our way backwards, expanding the crash reason as we go. */
	cm->when.statement_nr = 0;
	cm->when.decode_nr = crashedThread->decode_counter;
	updateCrashMachineForBlock(cm,
				   crashedThread->currentIRSBRip,
				   crashedThread->currentIRSBOffset - 2,
				   ms,
				   true);

	printf("Cause after backtracking current IRSB is %s\n", cm->name());

	/* And now do the same for the logged IRSBs */
	{
		unsigned cntr = 0;
		for (ring_buffer<std::pair<unsigned long, int>, 100>::reverse_iterator it = crashedThread->irsbExits.rbegin();
		     it != crashedThread->irsbExits.rend() && cntr < 20;
		     it++, cntr++) {
			updateCrashMachineForBlock(cm,
						   it->first,
						   it->second,
						   ms,
						   false);
			printf("Cause after backtracking IRSB %lx:%d is %s\n",
			       it->first,
			       it->second,
			       cm->name());
		}
	}

	printf("Reason before stub resolution %s\n",
	       cm->name());

	cm->start->sanity_check();

	cm = staticise(cm, ms);

	printf("Reason after stub resolution %s\n",
	       cm->name());

	printf("Other machine nodes:\n");
	for (CrashMachine::iterator it = cm->begin();
	     it != cm->end();
	     it++)
		printf("%lx: %s\n", it.key(), it.value()->name());

#if 0
	/* Step 3: Go through the expression and try to resolve
	 * stack-local references. */
	ResolveStackMapper rsm;

	do {
		rsm.progress = false;
		rsm.cr = cr;
		cr = cr->map(rsm);
	} while (rsm.progress);

	printf("After stack resolution, reason %s\n",
	       cr->name());

	/* Step 5: run a final simplification pass */
	SimplifyHardMapper shm;
	CrashReason *cr2 = cr->map(shm);

	printf("Final cause %s\n", cr2->name());

#endif

	dbg_break("finished");

	return 0;
}
