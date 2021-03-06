#ifndef BDD_HPP__
#define BDD_HPP__

#include <libvex_ir.h>
#include <libvex_alloc.h>
#include <libvex_parse.h>

#include "smr.hpp"
#include "hash_table.hpp"

extern bool bdd_use_dereferences;

class bbdd;
template <typename _leafT, typename _subtreeT> class _bdd;

/* Should only ever be created by bdd_orderings, but it needs to be
   stashed in a union in _bdd, so it can't have any constructors, so
   we can't enforce it with the type system.  Just have to be
   careful. */
/* Note that enforce_crash.cpp::setVariable() depends on the details
   of the BDD ordering for correctness! */
/* So does expressionevalmapt.cpp::setEntryPoint(). */
class bdd_rank {
	friend class bdd_ordering;
	long val;
	struct clsT {
		enum { cls_entry, cls_hb, cls_norm } tag;
		int hb1, hb2;
		bool operator<(const clsT &o) const {
			if (tag < o.tag)
				return true;
			else if (tag > o.tag || tag != cls_hb)
				return false;
			else if (hb1 < o.hb1)
				return true;
			else if (hb1 > o.hb1)
				return false;
			else
				return hb2 < o.hb2;
		}
		bool operator>(const clsT &o) const {
			if (tag > o.tag)
				return true;
			else if (tag < o.tag || tag != cls_hb)
				return false;
			else if (hb1 > o.hb1)
				return true;
			else if (hb1 < o.hb1)
				return false;
			else
				return hb2 > o.hb2;
		}
		bool operator==(const clsT &o) const {
			return tag == o.tag &&
				(tag != cls_hb ||
				 (hb1 == o.hb1 && hb2 == o.hb2));
		}
	} cls;
public:
	enum ordering { lt, gt, eq };
	ordering compare(const bdd_rank &o) const
	{
		if (cls < o.cls)
			return lt;
		if (cls > o.cls)
			return gt;
		if (val < o.val)
			return lt;
		if (val > o.val)
			return gt;
		return eq;
	}
	bool operator <(const bdd_rank &o) const
	{
		return compare(o) == lt;
	}
	bool operator <=(const bdd_rank &o) const
	{
		auto c = compare(o);
		return c == lt || c == eq;
	}
	bool operator==(const bdd_rank &o) const
	{
		return compare(o) == eq;
	}
	bool operator!=(const bdd_rank &o) const
	{
		return compare(o) != eq;
	}
	bool parse(const char *, const char **);

	/* You might think that this should be a Named class, rather
	 * than having a prettyPrint method, and you'd be almost
	 * right, except that making it Named means introducing a
	 * vtable pointer and the name pointer itself, so making the
	 * structure 16 bytes bigger.  We have a *lot* of these, and
	 * we also need to copy them around a *lot*, and without Named
	 * they're only 8 bytes, so that's actually worth worrying
	 * about. */
	void prettyPrint(FILE *f) const;
};

/* Thing for specifying variable ordering. */
class bdd_ordering : public GcCallback<&ir_heap> {
	void runGc(HeapVisitor &hv);
	sane_map<const IRExpr *, bdd_rank> variableRankings;

	sane_map<bdd_rank::clsT, std::set<long> > alreadyUsed;
public:
	class rank_hint {
		rank_hint() {};
	public:
		enum { start, near, end, never } flavour;
		bdd_rank _near;
		static rank_hint Start() {
			rank_hint h;
			h.flavour = start;
			return h;
		}
		static rank_hint End() {
			rank_hint h;
			h.flavour = end;
			return h;
		}
		static rank_hint Never() {
			rank_hint h;
			h.flavour = never;
			return h;
		}
		static rank_hint Near(const bdd_rank &__near) {
			rank_hint h;
			h.flavour = near;
			h._near = __near;
			return h;
		}
		template <typename t> static rank_hint Near(t *what) {
			if (what->isLeaf()) {
				return Start();
			} else {
				return Near(what->internal().rank);
			}
		}
	};
	template <typename leafT, typename subtreeT> bdd_rank rankVariable(const _bdd<leafT, subtreeT> *a) {
		assert(!a->isLeaf());
		return a->internal().rank;
	}
	bdd_rank rankVariable(const IRExpr *e, const rank_hint &hint);
	typedef enum { lt, eq, gt} ordT;
	template <typename aT, typename bT>
	ordT operator()(const aT *a, const bT *b) {
		bdd_rank ra = rankVariable(a);
		bdd_rank rb = rankVariable(b);
		if (ra < rb)
			return lt;
		else if (ra == rb)
			return eq;
		else
			return gt;
	}
	void enumVariables(std::vector<IRExpr *> &out) {
		out.reserve(out.size() + variableRankings.size());
		for (auto it = variableRankings.begin(); it != variableRankings.end(); it++)
			out.push_back(const_cast<IRExpr *>(it->first));
	}
	bdd_ordering()
		: GcCallback<&ir_heap>(true)
	{
	}
	void prettyPrint(FILE *, const std::set<bdd_rank> *needed) const;
	bool parse(const char *buf, const char **end);
};

template <typename _leafT, typename _subtreeT>
class _bdd : public GarbageCollected<_bdd<_leafT, _subtreeT>, &ir_heap> {
public:
	typedef _leafT leafT;
	typedef HashedMapSmall<HashedPtr<bbdd>, _subtreeT *> enablingTableT;
	struct internalT {
		bdd_rank rank;
		/* Must be Ity_I1 */
		IRExpr *condition;
		_subtreeT *trueBranch;
		_subtreeT *falseBranch;
	};
private:
	const bool _isLeaf;
	union _contentT {
		unsigned char _leaf[sizeof(leafT)];
		unsigned char _internal[sizeof(internalT)];
	} content;

	template <typename scopeT,
		  _subtreeT *parseLeaf(scopeT *, const char *, const char **)>
	static _subtreeT *_parse(scopeT *scope,
				 const char *,
				 const char **,
				 std::map<int, _subtreeT *> &labels);
	template <typename scopeT> static const typename std::map<leafT, bbdd *> &to_selectors(scopeT *, _subtreeT *, std::map<_subtreeT *, std::map<leafT, bbdd *> > &);
	/* This should only be used by ::zip(); everything else
	 * produces ready-reduced BDDs. */
	template <typename scopeT, typename zipInternalT> static _subtreeT *reduceBdd(scopeT *scope, std::map<_subtreeT *, _subtreeT *> &reduced, _subtreeT *start);

	leafT &unsafe_leaf() {
		assert(isLeaf());
		return *(leafT *)content._leaf;
	}

	template <typename scopeT, typename bscopeT, typename zipT> static _subtreeT *restructure_zip(
		scopeT *scp,
		bscopeT *bscope,
		const zipT &root,
		std::map<zipT, _subtreeT *> &memo);
	void dotPrintNodes(FILE *f, std::set<const _bdd *> &) const;
	void dotPrintEdges(FILE *f, std::set<const _bdd *> &) const;
public:
	internalT &unsafe_internal() {
		assert(!isLeaf());
		return *(internalT *)content._internal;
	}

	virtual void _prettyPrint(FILE *f, leafT what) const = 0;
protected:
	virtual void _visit(HeapVisitor &hv, leafT &leaf) const = 0;
	virtual void _sanity_check(leafT leaf) const = 0;

	explicit _bdd(leafT leaf)
		: _isLeaf(true), content()
	{
		new (&unsafe_leaf()) leafT(leaf);
	}
	_bdd(const bdd_rank &rank, IRExpr *cond, _subtreeT *trueB, _subtreeT *falseB)
		: _isLeaf(false), content()
	{
		unsafe_internal().rank = rank;
		unsafe_internal().condition = cond;
		unsafe_internal().trueBranch = trueB;
		unsafe_internal().falseBranch = falseB;
	}
	template <typename scopeT,
		  _subtreeT *(*parseLeaf)(scopeT *, const char *, const char **)>
	static bool _parse(scopeT *, _subtreeT **, const char *, const char **);

	template <typename scopeT, typename zipInternalT> static _subtreeT *zip(
		scopeT *scp,
		zipInternalT &where);

	~_bdd()
	{
		if (isLeaf())
			unsafe_leaf().~leafT();
		else
			unsafe_internal().rank.~bdd_rank();
	}
public:
	bool isLeaf() const {
		return _isLeaf;
	}
	const leafT &leaf() const {
		assert(isLeaf());
		return *(const leafT *)content._leaf;
	}
	const internalT &internal() const {
		assert(!isLeaf());
		return *(const internalT *)content._internal;
	}
	void sanity_check(bdd_ordering *ordering = NULL) const {
		if (isLeaf()) {
			_sanity_check(leaf());
		} else {
			internal().condition->sanity_check();
			assert(internal().condition->type() == Ity_I1);
			assert(internal().condition->tag != Iex_Mux0X);
			internal().trueBranch->sanity_check(ordering);
			internal().falseBranch->sanity_check(ordering);
			if (!internal().trueBranch->isLeaf()) {
				assert(internal().rank < internal().trueBranch->internal().rank);
			}
			if (!internal().falseBranch->isLeaf()) {
				assert(internal().rank < internal().falseBranch->internal().rank);
			}
			if (ordering) {
				assert(internal().rank == ordering->rankVariable(internal().condition, bdd_ordering::rank_hint::Never()));
			}
		}
	}

	void inputExpressions(std::vector<IRExpr *> &out);
	void prettyPrint(FILE *f);
	void labelledPrint(FILE *f, std::map<_subtreeT *, int> &labels);

	/* Simplify @thing under the assumption that @assumption is
	 * true. */
	template <typename scopeT> static _subtreeT *assume(scopeT *,
							    _subtreeT *thing,
							    bbdd *assumption);

	/* An enabling table is a map from BBDDs to int BDDs.  The
	   idea is that the caller arranges that at most one of the
	   BBDDs is true (i.e. enabled) for any context and we then
	   select the matching intbdd.  @from_enabling flattens an
	   enabling table into a single int BDD */
	template <typename scopeT> static _subtreeT *from_enabling(
		scopeT *scp,
		const enablingTableT &inp,
		_subtreeT *defaultValue);

	/* Kind of the inverse of from_enabling: convert an MTBDD into
	   a set of BBDDs, one for each possible terminal, such that
	   there's always precisely one BBDD which evaluates to true,
	   and the associated terminal is the result of the original
	   MTBDD. */
	/* Note that scopeT is always bbdd::scope, but it's a pain to
	   do that without a circular dependency between _bdd and
	   bbdd.  The template lets us break that dependency. */
	template <typename scopeT> static typename std::map<leafT, bbdd *> to_selectors(scopeT *, _subtreeT *);

	/* Special case of an enabling table.  ifelse(a, b, c)
	   evaluates to the same thing as b if a is true and to the
	   same thing as c otherwise. */
	template <typename scopeT> static _subtreeT *ifelse(
		scopeT *scp,
		bbdd *cond,
		_subtreeT *ifTrue,
		_subtreeT *ifFalse);

	/* Like a zip, but allows the BDD to be ``restructured'' as we
	   walk our way down the tree. */
	template <typename scopeT, typename bscopeT, typename zipT> static _subtreeT *restructure_zip(
		scopeT *scp,
		bscopeT *bscope,
		const zipT &root);

	_subtreeT *trueBranch(const bdd_rank &cond) {
		if (!isLeaf() && cond == internal().rank)
			return internal().trueBranch;
		else
			return (_subtreeT *)this;
	}
	_subtreeT *falseBranch(const bdd_rank &cond) {
		if (!isLeaf() && cond == internal().rank)
			return internal().falseBranch;
		else
			return (_subtreeT *)this;
	}

	unsigned long hash() const {
		if (isLeaf())
			return (unsigned long)leaf() * 57348958027;
		return (unsigned long)internal().condition * 57349651 +
			(unsigned long)internal().trueBranch * 57352199 +
			(unsigned long)internal().falseBranch * 57356099;
	}

	void dotPrint(FILE *f) const;

	void visit(HeapVisitor &hv) {
		/* Bit of a hack: content is const except for things
		   possibly being moved around by the GC. */
		if (isLeaf()) {
			_visit(hv, unsafe_leaf());
		} else {
			hv(unsafe_internal().condition);
			hv(unsafe_internal().trueBranch);
			hv(unsafe_internal().falseBranch);
		}
	}
	NAMED_CLASS
};

template <typename t>
class bdd_scope {
	struct entry {
		bdd_rank rank;
		t *trueB;
		t *falseB;
		entry(const bdd_rank &_rank, t *_trueB, t *_falseB)
			: rank(_rank), trueB(_trueB), falseB(_falseB)
		{}
		bool operator<(const entry &o) const {
			switch (rank.compare(o.rank)) {
			case bdd_rank::lt:
				return true;
			case bdd_rank::gt:
				return false;
			case bdd_rank::eq:
				break;
			}
			if (trueB < o.trueB)
				return true;
			if (trueB > o.trueB)
				return false;
			return falseB < o.falseB;
		}
	};
	std::map<entry, t *> intern;
	void normalise(IRExpr *cond, t *&, t *&);
	t *mkInternal(IRExpr *a, const bdd_rank &r, t *, t *);

	void checkInternSize() const;

protected:
	void runGc(HeapVisitor &hv);
public:
	long nr_ever;

	t *internBdd(t *);
	t *node(IRExpr *, const bdd_rank &, t *, t *);
	bdd_ordering *ordering;

	bdd_scope(bdd_ordering *_ordering)
		: nr_ever(0), ordering(_ordering)
	{}
};


template <typename t> class const_bdd_scope
	: public bdd_scope<t>,
	  private GcCallback<&ir_heap> {
	std::map<typename t::leafT, t *> lookup;
	void runGc(HeapVisitor &hv) {
		for (auto it = lookup.begin();
		     it != lookup.end();
			) {
			it->second = hv.visited(it->second);
			if (it->second == NULL)
				lookup.erase(it++);
			else
				it++;
		}
		bdd_scope<t>::runGc(hv);
	}
public:
	t *cnst(const typename t::leafT &i) {
		auto it_did_insert = lookup.insert(std::pair<typename t::leafT, t *>(i, (t *)NULL));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert)
			it->second = new t(i);
		return it->second;
	}
	const_bdd_scope(bdd_ordering *_ordering)
		: bdd_scope<t>(_ordering),
		  GcCallback<&ir_heap>(true)
	{}
};

class bbdd;

template <typename constT, typename subtreeT> class const_bdd
	: public _bdd<constT, subtreeT> {
public:
	typedef constT leafT;
	typedef const_bdd_scope<subtreeT> scope;
private:
	void _visit(HeapVisitor &, constT &) const {
	}
	template <IRExpr *mkConst(constT)> static IRExpr *to_irexpr(subtreeT *, std::map<subtreeT *, IRExpr *> &memo);
protected:
	template <IRExpr *mkConst(constT)> static IRExpr *to_irexpr(subtreeT *);

	const_bdd(bdd_rank rank, IRExpr *cond, subtreeT *trueB, subtreeT *falseB)
		: _bdd<constT, subtreeT>(rank, cond, trueB, falseB)
	{}
	const_bdd(constT b)
		: _bdd<constT, subtreeT>(b)
	{}
	static subtreeT *replaceTerminal(
		scope *scp,
		constT from,
		constT to,
		subtreeT *in,
		std::map<subtreeT *, subtreeT *> &);
public:
	static subtreeT *replaceTerminal(
		scope *scp,
		constT from,
		constT to,
		subtreeT *in);
};

class bbdd : public const_bdd<bool, bbdd> {
	friend class const_bdd_scope<bbdd>;
	friend class bdd_scope<bbdd>;
	friend class _bdd<bool, bbdd>;

#ifdef NDEBUG
	void _sanity_check(bool) const {}
#else
	void _sanity_check(bool b) const {
		assert(b == true || b == false);
	}
#endif
public:
	void _prettyPrint(FILE *f, bool b) const {
		fprintf(f, "%s", b ? "<true>" : "<false>");
	}
private:
	static bbdd *parseBool(bbdd::scope *scope, const char *str, const char **suffix) {
		if (parseThisString("<true>", str, suffix)) {
			return scope->cnst(true);
		} else if (parseThisString("<false>", str, suffix)) {
			return scope->cnst(false);
		} else {
			return NULL;
		}
	}
	bbdd(bdd_rank rank, IRExpr *cond, bbdd *trueB, bbdd *falseB)
		: const_bdd<bool, bbdd>(rank, cond, trueB, falseB)
	{}
	bbdd(bool b)
		: const_bdd<bool, bbdd>(b)
	{}
	static IRExpr *mkConst(bool b) {
		return IRExpr_Const_U1(b);
	}
	static bbdd *_var(scope *, IRExpr *a, std::map<IRExpr *, bbdd *> &memo, const bdd_ordering::rank_hint &hint);
	static bbdd *invert(scope *, bbdd *a, std::map<bbdd *, bbdd *> &memo);
public:
	static bbdd *Or(scope *, bbdd *a, bbdd *b);
	static bbdd *And(scope *, bbdd *a, bbdd *b);
	static bbdd *var(scope *, IRExpr *a, const bdd_ordering::rank_hint &hint);
	static bbdd *invert(scope *scp, bbdd *a) {
		std::map<bbdd *, bbdd *> memo;
		return invert(scp, a, memo);
	}
	static bbdd *assume(scope *scp,
			    bbdd *thing,
			    bbdd *assumption) {
		return const_bdd<bool, bbdd>::assume(scp, thing, assumption);
	}
	static IRExpr *to_irexpr(bbdd *b) {
		return const_bdd<bool, bbdd>::to_irexpr<mkConst>(b);
	}
	static bool parse(bbdd::scope *scope, bbdd **out, const char *str, const char **suffix) {
		return _bdd<bool, bbdd>::_parse<bbdd::scope, parseBool>(scope, out, str, suffix);
	}
};

class intbdd : public const_bdd<int, intbdd> {
	friend class const_bdd_scope<intbdd>;
	friend class bdd_scope<intbdd>;
	friend class _bdd<int, intbdd>;
	void _sanity_check(int) const {
	}
	void _prettyPrint(FILE *f, int k) const {
		fprintf(f, "<%d>", k);
	}
	static bool parseInt(int *out, const char *str, const char **suffix) {
		int r;
		if (parseThisChar('<', str, &str) &&
		    parseDecimalInt(&r, str, &str) &&
		    parseThisChar('>', str, suffix)) {
			*out = r;
			return true;
		}
		return false;
	}
	intbdd(bdd_rank rank, IRExpr *cond, intbdd *trueB, intbdd *falseB)
		: const_bdd<int, intbdd>(rank, cond, trueB, falseB)
	{}
	intbdd(int b)
		: const_bdd<int, intbdd>(b)
	{}
public:
	/* Simplify @thing under the assumption that @assumption is
	 * true. */
	static intbdd *assume(scope *scp,
			      intbdd *thing,
			      bbdd *assumption) {
		return const_bdd<int, intbdd>::assume(scp, thing, assumption);
	}
};

class smrbdd : public const_bdd<StateMachineRes, smrbdd> {
	friend class const_bdd_scope<smrbdd>;
	friend class bdd_scope<smrbdd>;
	friend class _bdd<StateMachineRes, smrbdd>;
#ifdef NDEBUG
	void _sanity_check(StateMachineRes) const {}
#else
	void _sanity_check(StateMachineRes r) const {
		assert(r == smr_crash || r == smr_survive || r == smr_unreached);
	}
#endif
	void _prettyPrint(FILE *f, StateMachineRes r) const {
		fprintf(f, "<%s>", nameSmr(r));
	}
	static smrbdd *parseLeaf(scope *scp, const char *str, const char **suffix)
	{
		StateMachineRes r;
		if (!parseThisChar('<', str, &str) ||
		    !parseSmr(&r, str, &str) ||
		    !parseThisChar('>', str, suffix))
			return NULL;
		return scp->cnst(r);
	}

	smrbdd(bdd_rank rank, IRExpr *cond, smrbdd *trueB, smrbdd *falseB)
		: const_bdd<StateMachineRes, smrbdd>(rank, cond, trueB, falseB)
	{}
	smrbdd(StateMachineRes b)
		: const_bdd<StateMachineRes, smrbdd>(b)
	{}
public:
	static bool parse(scope *scp, smrbdd **out, const char *str, const char **suffix) {
		return _bdd<StateMachineRes, smrbdd>::_parse<scope, parseLeaf>(scp, out, str, suffix);
	}
	static smrbdd *ignore_unreached(scope *scp, smrbdd *what);
};

class exprbdd;

class exprbdd_scope : public bdd_scope<exprbdd>, private GcCallback<&ir_heap> {
	friend class exprbdd;

	std::map<IRExpr *, exprbdd *> leaves;

	void runGc(HeapVisitor &hv);
	exprbdd *cnst(IRExpr *what);

public:
	exprbdd_scope(bdd_ordering *_ordering)
		: bdd_scope<exprbdd>(_ordering),
		  GcCallback<&ir_heap>(true)
	{}
};

class exprbdd : public _bdd<IRExpr *, exprbdd> {
public:
	typedef IRExpr *leafT;
	typedef exprbdd_scope scope;
private:
	friend class bdd_scope<exprbdd>;
	friend class exprbdd_scope;
	friend class _bdd<IRExpr *, exprbdd>;

	typedef _bdd<IRExpr *, exprbdd> parentT;

	static exprbdd *parseLeaf(scope *, const char *, const char **);
	void _visit(HeapVisitor &hv, IRExpr *&leaf) const {
		hv(leaf);
	}
	void _sanity_check(IRExpr *leaf) const {
		leaf->sanity_check();
	}
	void _prettyPrint(FILE *f, leafT what) const {
		fprintf(f, "<");
		ppIRExpr(what, f);
		fprintf(f, ">");
	}
	exprbdd(bdd_rank _rank, IRExpr *cond, exprbdd *trueB, exprbdd *falseB)
		: parentT(_rank, cond, trueB, falseB)
	{}
	exprbdd(leafT b)
		: parentT(b)
	{}
	static exprbdd *_var(scope *scope, bbdd::scope *, IRExpr *, std::map<IRExpr *, exprbdd *> &memo,
			     const bdd_ordering::rank_hint &hint);
	static IRExpr *to_irexpr(exprbdd *what, std::map<exprbdd *, IRExpr *> &memo);
	static bbdd *to_bbdd(bbdd::scope *scope, exprbdd *, std::map<exprbdd *, bbdd *> &);

	static exprbdd *load(scope *, bbdd::scope *, IRType, exprbdd *, std::map<exprbdd *, exprbdd *> &);

public:
	static bool parse(scope *scp, exprbdd **out, const char *str, const char **suffix) {
		return parentT::_parse<scope, parseLeaf>(scp, out, str, suffix);
	}
	static IRExpr *to_irexpr(exprbdd *);
	static exprbdd *var(scope *scope, bbdd::scope *, IRExpr *, const bdd_ordering::rank_hint &hint);
	IRType type() const {
		if (isLeaf())
			return leaf()->type();
		else
			return internal().trueBranch->type();
	}
	void sanity_check(bdd_ordering *ordering = NULL) const;

	static exprbdd *load(scope *scope, bbdd::scope *, IRType, exprbdd *);
	static exprbdd *unop(scope *scope, bbdd::scope *, IROp, exprbdd *);
	static exprbdd *binop(scope *scope, bbdd::scope *, IROp, exprbdd *, exprbdd *);
	static exprbdd *triop(scope *scope, bbdd::scope *, IROp, exprbdd *, exprbdd *, exprbdd *);
	static exprbdd *qop(scope *scope, bbdd::scope *, IROp, exprbdd *, exprbdd *, exprbdd *, exprbdd *);
	static exprbdd *associative(scope *scope, bbdd::scope *, IROp, exprbdd **, int);
	static exprbdd *ccall(scope *scope, bbdd::scope *, IRCallee *, IRType, exprbdd **, int);
	static exprbdd *coerceTypes(scope *, bbdd::scope *, IRType ty, exprbdd *);

	static bbdd *to_bbdd(bbdd::scope *scope, exprbdd *);
};

struct qs_args {
	/* The expression to simplify */
	IRExpr *what;
	/* Mask of bits which might conceivably be interesting. */
	unsigned long mask;
	qs_args(IRExpr *_what, unsigned long _mask)
		: what(_what), mask(_mask)
	{}
	explicit qs_args(IRExpr *);
	bool operator<(const qs_args &o) const {
		if (mask < o.mask) {
			return true;
		} else if (o.mask < mask) {
			return false;
		} else {
			return what < o.what;
		}
	}
};
IRExpr *quickSimplify(const qs_args &, std::map<qs_args, IRExpr *> &memo);

#endif /* !BDD_HPP__ */
