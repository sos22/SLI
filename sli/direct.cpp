#include <typeinfo>

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

class CrashPredicate;
class CrashExpression;

class CPMapper {
public:
	virtual CrashPredicate *operator()(CrashPredicate *p) { return p; }
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

#define mk_binop(name, hashop, commutes, associates, zero_ident)	\
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
	x(Add, +, true, true, true)				\
	x(Xor, ^, true, true, true)				\
	x(And, &, true, true, false)				\
	x(Or, |, true, true, false)				\
	x(Shl, <<, false, false, false)

#define all_binops(x)				\
	most_binops(x)				\
	x(Equal, * 46278 + 472389 * , true, false, false)

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

class CrashPredicate : public GarbageCollected<CrashPredicate>, public Named {
protected:
	virtual void _visit(HeapVisitor &hv) = 0;
	virtual const char *_mkName() const = 0;
	char *mkName() const {
		return my_asprintf("%s", _mkName());
	}
public:
	virtual ~CrashPredicate() {}
	void visit(HeapVisitor &hv) { _visit(hv); }
	void destruct() { this->~CrashPredicate(); }
	virtual CrashPredicate *map(CPMapper &m) = 0;
	virtual unsigned complexity() const = 0;
	virtual bool isConstant(bool &l) const = 0;
	bool isConstant() const { bool ign; return isConstant(ign); }
	NAMED_CLASS
};

class CrashPredicateConstant : public CrashPredicate {
	CrashPredicateConstant(bool _v) : v(_v) {}
protected:
	void _visit(HeapVisitor &hv) {}
	const char *_mkName() const { return v ? "true" : "false"; }
public:
	bool v;
	CrashPredicate *map(CPMapper &m) { return m(this); }
	unsigned complexity() const { return 0; }
	bool isConstant(bool &l) const { l = v; return true; }
	static CrashPredicate *get(bool val) {
		return new CrashPredicateConstant(val);
	}
};

class CrashPredicateBadAddr : public CrashPredicate {
	CrashPredicateBadAddr(CrashExpression *_addr)
		: addr(_addr)
	{
	}
protected:
	void _visit(HeapVisitor &hv) { hv(addr); }
	const char *_mkName() const { return my_asprintf("bad address %s", addr->name()); }
public:
	CrashExpression *addr;
	static CrashPredicate *get(CrashExpression *addr) {
		return new CrashPredicateBadAddr(addr);
	}
	static CrashPredicate *get(IRExpr *addr) {
		return get(CrashExpression::get(addr));
	}
	CrashPredicate *map(CPMapper &m) {
		return m(get(addr->map(m)));
	}
	unsigned complexity() const { return addr->complexity() + 1; }
	bool isConstant(bool &l) const { return false; }
};

class CrashReason : public GarbageCollected<CrashReason>, public Named {
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
	CrashReason(const CrashReason &x);
protected:
	char *mkName() const {
		char *b = my_asprintf("%s: %s", when.name(), data_reason->name());
		for (std::vector<CrashPredicate *>::const_iterator it = control_reasons.begin();
		     it != control_reasons.end();
		     it++) {
			char *b2;
			b2 = my_asprintf("%s;\n%s", b, (*it)->name());
			free(b);
			b = b2;
		}
		return b;
	}
public:
	struct store_record : public Named {
	protected:
		char *mkName() const { return my_asprintf("%s: %s -> %s",
							  when.name(),
							  value->name(),
							  addr->name()); }
	public:
		CrashTimestamp when;
		CrashExpression *addr;
		CrashExpression *value;
	};
	CrashTimestamp when;
	CrashPredicate *data_reason;
	std::vector<CrashPredicate *> control_reasons;
	std::vector<store_record> storesIssued;

	void addControlReason(CrashPredicate *cp)
	{
		bool c;
		if (cp->isConstant(c)) {
			assert(c);
			return;
		}
		control_reasons.push_back(cp);
		clearName();
	}

	CrashReason(CrashTimestamp _when, CrashPredicate *r, const std::vector<store_record> &si,
		    const std::vector<CrashPredicate *> &cr)
		: when(_when), data_reason(r), control_reasons(cr), storesIssued(si)
	{
	}
	CrashReason *map(CPMapper &cm) {
		std::vector<store_record> newSi;
		for (std::vector<store_record>::iterator it = storesIssued.begin();
		     it != storesIssued.end();
		     it++) {
			store_record sr;
			sr.when = it->when;
			sr.addr = it->addr->map(cm);
			sr.value = it->value->map(cm);
			newSi.push_back(sr);
		}
		std::vector<CrashPredicate *> newCr;
		for (std::vector<CrashPredicate *>::iterator it = control_reasons.begin();
		     it != control_reasons.end();
		     it++) {
			CrashPredicate *newCp = (*it)->map(cm);
			bool b;
			if (newCp->isConstant(b)) {
				if (!b) {
					/* This can happen, if we get
					   the aliasing pattern wrong.
					   Oh well. */
					printf("Whoops: %s -> %s\n",
					       (*it)->name(),
					       newCp->name());
				}
			} else {
				newCr.push_back(newCp);
			}
		}
		return new CrashReason(when, data_reason->map(cm), newSi, newCr);
	}
	CrashReason *reduceTimestampOneStatement() const {
		return new CrashReason(when.reduceOneStatement(),
				       data_reason,
				       storesIssued,
				       control_reasons);
	}
	CrashReason *reduceTimestampOneBlock(int n) const {
		return new CrashReason(when.reduceOneBlock(n),
				       data_reason,
				       storesIssued,
				       control_reasons);
	}
	CrashReason *issueStore(CrashExpression *addr, CrashExpression *data) const {
		printf("Issue store %s to %s at %s\n", data->name(), addr->name(), when.name());
		CrashReason *cr = new CrashReason(when,
						  data_reason,
						  storesIssued,
						  control_reasons);
		store_record sr;
		sr.when = when;
		sr.addr = addr;
		sr.value = data;
		cr->storesIssued.push_back(sr);
		return cr;
	}
	CrashReason *rewriteTemporary(IRTemp what, CrashExpression *to) {
		RewriteTmpMapper t(what, to);
		return map(t);
	}
	CrashReason *rewriteRegister(Int offset, CrashExpression *to) {
		RewriteRegisterMapper t(offset, to);
		return map(t);
	}
	void visit(HeapVisitor &hv) {
		hv(data_reason);
		for (std::vector<store_record>::iterator it = storesIssued.begin();
		     it != storesIssued.end();
		     it++) {
			hv(it->addr);
			hv(it->value);
		}
		for (std::vector<CrashPredicate *>::iterator it = control_reasons.begin();
		     it != control_reasons.end();
		     it++)
			hv(*it);
	}
	void destruct() { this->~CrashReason(); }

	NAMED_CLASS
};

class CrashPredicateNot : public CrashPredicate {
	CrashPredicateNot(CrashPredicate *_l)
		: l(_l)
	{
	}
	CrashPredicate *l;
protected:
	void _visit(HeapVisitor &hv) { hv(l); }
	const char *_mkName() const { return vex_asprintf("¬(%s)",
							  l->name()); }
public:
	static CrashPredicate *get(CrashPredicate *l)
	{
		bool c;
		if (l->isConstant(c))
			return CrashPredicateConstant::get(!c);
		return new CrashPredicateNot(l);
	}

	CrashPredicate *map(CPMapper &m) {
		return m(get(l->map(m)));
	}
	unsigned complexity() const { return l->complexity() + 1; }
	bool isConstant(bool &out) const { return l->isConstant(out); }
};

class CrashPredicateLift : public CrashPredicate {
	CrashPredicateLift(CrashExpression *_l)
		: l(_l)
	{
	}
protected:
	void _visit(HeapVisitor &hv) { hv(l); }
	const char *_mkName() const { return l->name(); }
public:
	CrashExpression *l;

	static CrashPredicate *get(CrashExpression *l)
	{
		unsigned long v;
		if (l->isConstant(v))
			return CrashPredicateConstant::get(!!v);
		return new CrashPredicateLift(l);
	}

	CrashPredicate *map(CPMapper &m) {
		return m(get(l->map(m)));
	}

	unsigned complexity() const { return l->complexity() + 1; }

	bool isConstant(bool &out) const {
		unsigned long v;
		if (l->isConstant(v)) {
			out = !!v;
			return true;
		} else {
			return false;
		}
	}
};

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
#define do_binop(x, _1, _2, _3, _4)					\
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

static CrashReason *
exprToCrashReason(CrashTimestamp when, IRExpr *expr)
{
	return NULL;
}

static CrashReason *
statementToCrashReason(CrashTimestamp when, IRStmt *irs)
{
	CrashReason *r;

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
			std::vector<CrashReason::store_record> i;
			std::vector<CrashPredicate *> i2;
			r = new CrashReason(when, CrashPredicateBadAddr::get(irs->Ist.Store.addr), i, i2);
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
			std::vector<CrashReason::store_record> i;
			std::vector<CrashPredicate *> i2;
			return new CrashReason(when, CrashPredicateBadAddr::get(irs->Ist.Dirty.details->args[0]), i, i2);
		}
		return NULL;
	}
}

static CrashReason *
updateCrashReasonForStatement(CrashReason *cr,
			      IRStmt *stmt)
{
	CrashReason *n = cr->reduceTimestampOneStatement();
	switch (stmt->tag) {
	case Ist_NoOp:
	case Ist_AbiHint:
	case Ist_MBE:
	case Ist_IMark:
		return n;
	case Ist_Put: {
		CrashExpression *d = CrashExpression::get(stmt->Ist.Put.data);
		if (stmt->Ist.Put.offset == OFFSET_amd64_RSP ||
		    stmt->Ist.Put.offset == OFFSET_amd64_RBP)
			d = CrashExpressionStackPtr::get(d);
		return n->rewriteRegister(stmt->Ist.Put.offset,
					  d);
	}
	case Ist_WrTmp:
		return n->rewriteTemporary(stmt->Ist.WrTmp.tmp,
					   CrashExpression::get(stmt->Ist.WrTmp.data));
	case Ist_Dirty:
		if (strncmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_",
			    12))
			abort(); /* don't know how to deal with these */
		return n->rewriteTemporary(
			stmt->Ist.Dirty.details->tmp,
			CrashExpressionLoad::get(
				n->when,
				CrashExpression::get(
					stmt->Ist.Dirty.details->args[0])));
	case Ist_Store:
		return n->issueStore(
		       CrashExpression::get(
			       stmt->Ist.Store.addr),
		       CrashExpression::get(
			       stmt->Ist.Store.data));
	case Ist_Exit: {
		CrashReason *cr2 = new CrashReason(
			cr->when.reduceOneStatement(),
			cr->data_reason,
			cr->storesIssued,
			cr->control_reasons);
		cr2->addControlReason(
			CrashPredicateNot::get(
				CrashPredicateLift::get(
					CrashExpression::get(stmt->Ist.Exit.guard))));
		return cr2;
	}

	case Ist_CAS:
		return n->rewriteTemporary(
			stmt->Ist.CAS.details->oldLo,
			CrashExpressionLoad::get(
				n->when,
				CrashExpression::get(
					stmt->Ist.CAS.details->addr)));
	default:
		/* Dunno what to do here. */
		abort();
	}
}

static CrashReason *
updateCrashReasonForTakenBranch(CrashReason *cr,
				IRStmt *stmt)
{
	assert(stmt->tag == Ist_Exit);
	cr->addControlReason(CrashPredicateLift::get(
				     CrashExpression::get(stmt->Ist.Exit.guard)));
	return cr->reduceTimestampOneStatement();
}

class ResolveStackMapper : public CPMapper {
public:
	CrashReason *cr;
	bool progress;

	CrashExpression *operator()(CrashExpression *ce) {
		CrashExpressionLoad *cel =
			dynamic_cast<CrashExpressionLoad *>(ce);
		if (!cel || !cel->addr->pointsAtStack())
			return ce;
		for (std::vector<CrashReason::store_record>::iterator it = cr->storesIssued.begin();
		     it != cr->storesIssued.end();
		     it++) {
			/* We assume that stack references are simple
			   enough that the simplifier can always tell
			   whether two expressions are equal.
			   Otherwise, we'll miss some assignments,
			   which would be bad. */
			if (it->when < cel->when &&
			    ce->complexity() > it->value->complexity()) {
				CrashExpression *c =
					CrashExpressionEqual::get(
						cel->addr,
						it->addr)->simplify(100);
				if (c->isTrue()) {
					progress = true;
					return it->value;
				}
			}
		}
		return ce;
	}
	CrashPredicate *operator()(CrashPredicate *cp) {
		CrashPredicateLift *cpl =
			dynamic_cast<CrashPredicateLift *>(cp);
		if (!cpl)
			return cp;
		return CrashPredicateLift::get(cpl->l->simplify(10000));
	}
};

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
	VexPtr<CrashReason> cr(
		statementToCrashReason(CrashTimestamp(crashedThread->tid,
						      crashedThread->currentIRSBOffset - 1,
						      crashedThread->decode_counter),
				       crashedThread->currentIRSB->stmts[crashedThread->currentIRSBOffset - 1]));

	printf("Proximal cause is %s\n", cr->name());

	/* Step two: work our way backwards, expanding the crash reason as we go. */
	for (int i = crashedThread->currentIRSBOffset - 2;
	     i >= 0;
	     i--) {
		cr = updateCrashReasonForStatement(cr,
						   crashedThread->currentIRSB->stmts[i]);
	}

	printf("Cause after backtracking current IRSB is %s\n", cr->name());

	unsigned long prev_rip = crashedThread->currentIRSBRip;

	/* And now do the same for the logged IRSBs */
	{
		unsigned cntr = 0;
		for (ring_buffer<std::pair<unsigned long, int>, 100>::reverse_iterator it = crashedThread->irsbExits.rbegin();
		     it != crashedThread->irsbExits.rend();
		     it++, cntr++) {
			if (cntr == 43)
				dbg_break("Here we are.\n");
			IRSB *irsb = ms->addressSpace->getIRSBForAddress(it->first);
			assert(irsb->stmts_used >= it->second);
			int i = it->second - 1;
			cr = cr->reduceTimestampOneBlock(it->second);
			if (irsb->stmts[i]->tag == Ist_Exit &&
			    irsb->stmts[i]->Ist.Exit.dst->Ico.U64 == prev_rip) {
				cr = updateCrashReasonForTakenBranch(cr, irsb->stmts[i]);
				i--;
			}
			for (; i >= 0; i--)
				cr = updateCrashReasonForStatement(cr, irsb->stmts[i]);
			printf("Cause after backtracking IRSB at %lx:%d %s\n",
			       it->first, it->second, cr->name());
			prev_rip = it->first;
		}
	}

	printf("Reason before stack resolution %s\n",
	       cr->name());

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

	dbg_break("finished");

	return 0;
}
