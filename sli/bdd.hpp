#ifndef BDD_HPP__
#define BDD_HPP__

#include <libvex_ir.h>
#include <libvex_alloc.h>
#include <libvex_parse.h>

#include "smr.hpp"

class bbdd;

/* Thing for specifying variable ordering. */
class bdd_ordering : public GcCallback<&ir_heap> {
	void runGc(HeapVisitor &hv);
	std::map<const IRExpr *, long> variableRankings;
	long nextRanking;
	long rankVariable(const IRExpr *e);
public:
	typedef enum { lt, eq, gt} ordT;
	ordT operator()(const IRExpr *a, const IRExpr *b) {
		if (a == b)
			return eq;
		long ra = rankVariable(a);
		long rb = rankVariable(b);
		if (ra < rb)
			return lt;
		else if (ra == rb)
			return eq;
		else
			return gt;
	}
	bool before(const IRExpr *a, const IRExpr *b) {
		return (*this)(a, b) == lt;
	}
	bool equal(const IRExpr *a, const IRExpr *b) {
		return (*this)(a, b) == eq;
	}
	void enumVariables(std::vector<IRExpr *> &out) {
		out.reserve(out.size() + variableRankings.size());
		for (auto it = variableRankings.begin(); it != variableRankings.end(); it++)
			out.push_back(const_cast<IRExpr *>(it->first));
	}
	bdd_ordering() : GcCallback<&ir_heap>(true), nextRanking(0) {}
	template <typename subtreeT> subtreeT *trueBranch(subtreeT *bdd, IRExpr *cond) {
		if (!bdd->isLeaf && equal(cond, bdd->content.condition))
			return bdd->content.trueBranch;
		else
			return bdd;
	}
	template <typename subtreeT> subtreeT *falseBranch(subtreeT *bdd, IRExpr *cond) {
		if (!bdd->isLeaf && equal(cond, bdd->content.condition))
			return bdd->content.falseBranch;
		else
			return bdd;
	}
	void prettyPrint(FILE *) const;
	bool parse(const char *buf, const char **end);
};

template <typename _leafT, typename _subtreeT>
class _bdd : public GarbageCollected<_bdd<_leafT, _subtreeT>, &ir_heap> {
public:
	typedef _leafT leafT;
	typedef std::map<bbdd *, _subtreeT *> enablingTableT;
private:
	template <typename scopeT,
		  _subtreeT *parseLeaf(scopeT *, const char *, const char **)>
	static _subtreeT *_parse(scopeT *scope,
				 const char *,
				 const char **,
				 std::map<int, _subtreeT *> &labels);
	template <typename scopeT, typename zipInternalT> static _subtreeT *zip(
		scopeT *,
		zipInternalT,
		std::map<zipInternalT, _subtreeT *> &memo);
	template <typename scopeT> static const typename std::map<leafT, bbdd *> &to_selectors(scopeT *, _subtreeT *, std::map<_subtreeT *, std::map<leafT, bbdd *> > &);
protected:
	virtual void _visit(HeapVisitor &hv, leafT &leaf) const = 0;
	virtual void _sanity_check(leafT leaf) const = 0;
	virtual void _prettyPrint(FILE *f, leafT what) const = 0;

	_bdd(leafT leaf)
		: isLeaf(true), content()
	{
		contentT *_content = const_cast<contentT *>(&content);
		_content->leaf = leaf;
	}
	_bdd(IRExpr *cond, _subtreeT *trueB, _subtreeT *falseB)
		: isLeaf(false), content()
	{
		contentT *_content = const_cast<contentT *>(&content);
		_content->condition = cond;
		_content->trueBranch = trueB;
		_content->falseBranch = falseB;
	}
	template <typename scopeT,
		  _subtreeT *(*parseLeaf)(scopeT *, const char *, const char **)>
	static bool _parse(scopeT *, _subtreeT **, const char *, const char **);

	template <typename scopeT, typename zipInternalT> static _subtreeT *zip(
		scopeT *scp,
		zipInternalT where) {
		std::map<zipInternalT, _subtreeT *> memo;
		return zip(scp, where, memo);
	}
public:
	const bool isLeaf;
	union contentT {
		leafT leaf;
		struct {
			/* Must be Ity_I1 */
			IRExpr *condition;
			_subtreeT *trueBranch;
			_subtreeT *falseBranch;
		};
	};
	const contentT content;
	void sanity_check(bdd_ordering *ordering = NULL) const {
		assert(isLeaf == true || isLeaf == false);
		if (isLeaf) {
			_sanity_check(content.leaf);
		} else {
			content.condition->sanity_check();
			assert(content.condition->type() == Ity_I1);
			assert(content.condition->tag != Iex_Mux0X);
			content.trueBranch->sanity_check(ordering);
			content.falseBranch->sanity_check(ordering);
			if (ordering) {
				if (!content.trueBranch->isLeaf)
					assert(ordering->before(content.condition, content.trueBranch->content.condition));
				if (!content.falseBranch->isLeaf)
					assert(ordering->before(content.condition, content.falseBranch->content.condition));
			}
		}
	}

	void inputExpressions(std::vector<IRExpr *> &out);
	void prettyPrint(FILE *f);

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

	void visit(HeapVisitor &hv) {
		/* Bit of a hack: content is const except for things
		   possibly being moved around by the GC. */
		contentT *_content = const_cast<contentT *>(&content);
		if (isLeaf) {
			_visit(hv, _content->leaf);
		} else {
			hv(_content->condition);
			hv(_content->trueBranch);
			hv(_content->falseBranch);
		}
	}
	NAMED_CLASS
};

template <typename t>
class bdd_scope {
	struct entry {
		IRExpr *cond;
		t *trueB;
		t *falseB;
		entry(IRExpr *_cond, t *_trueB, t *_falseB)
			: cond(_cond), trueB(_trueB), falseB(_falseB)
		{}
		bool operator<(const entry &o) const {
			if (cond < o.cond)
				return true;
			if (cond > o.cond)
				return false;
			if (trueB < o.trueB)
				return true;
			if (trueB > o.trueB)
				return false;
			return falseB < o.falseB;
		}
	};
	std::map<entry, t *> intern;
public:
	t *makeInternal(IRExpr *a, t *, t *);
	bdd_ordering *ordering;

	bdd_scope(bdd_ordering *_ordering)
		: ordering(_ordering)
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

template <typename constT, typename subtreeT> class const_bdd : public _bdd<constT, subtreeT> {
public:
	typedef constT leafT;
	typedef const_bdd_scope<subtreeT> scope;
private:
	void _visit(HeapVisitor &, constT &) const {
	}
	template <IRExpr *mkConst(constT)> static IRExpr *to_irexpr(subtreeT *, std::map<subtreeT *, IRExpr *> &memo);
protected:
	template <IRExpr *mkConst(constT)> static IRExpr *to_irexpr(subtreeT *);

	const_bdd(IRExpr *cond, subtreeT *trueB, subtreeT *falseB)
		: _bdd<constT, subtreeT>(cond, trueB, falseB)
	{}
	const_bdd(constT b)
		: _bdd<constT, subtreeT>(b)
	{}
public:
};

class bbdd : public const_bdd<bool, bbdd> {
	friend class const_bdd_scope<bbdd>;
	friend class bdd_scope<bbdd>;

	void _sanity_check(bool b) const {
		assert(b == true || b == false);
	}
	void _prettyPrint(FILE *f, bool b) const {
		fprintf(f, "%s", b ? "<true>" : "<false>");
	}
	static bbdd *parseBool(bbdd::scope *scope, const char *str, const char **suffix) {
		if (parseThisString("<true>", str, suffix)) {
			return scope->cnst(true);
		} else if (parseThisString("<false>", str, suffix)) {
			return scope->cnst(false);
		} else {
			return NULL;
		}
	}
	bbdd(IRExpr *cond, bbdd *trueB, bbdd *falseB)
		: const_bdd<bool, bbdd>(cond, trueB, falseB)
	{}
	bbdd(bool b)
		: const_bdd<bool, bbdd>(b)
	{}
	static IRExpr *mkConst(bool b) {
		return IRExpr_Const_U1(b);
	}
	static bbdd *_var(scope *, IRExpr *a);
public:
	static bbdd *Or(scope *, bbdd *a, bbdd *b);
	static bbdd *And(scope *, bbdd *a, bbdd *b);
	static bbdd *var(scope *, IRExpr *a);
	static bbdd *invert(scope *, bbdd *a);
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
	intbdd(IRExpr *cond, intbdd *trueB, intbdd *falseB)
		: const_bdd<int, intbdd>(cond, trueB, falseB)
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
	void _sanity_check(StateMachineRes r) const {
		assert(r == smr_crash || r == smr_survive || r == smr_unreached);
	}
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

	smrbdd(IRExpr *cond, smrbdd *trueB, smrbdd *falseB)
		: const_bdd<StateMachineRes, smrbdd>(cond, trueB, falseB)
	{}
	smrbdd(StateMachineRes b)
		: const_bdd<StateMachineRes, smrbdd>(b)
	{}
public:
	static bool parse(scope *scp, smrbdd **out, const char *str, const char **suffix) {
		return _bdd<StateMachineRes, smrbdd>::_parse<scope, parseLeaf>(scp, out, str, suffix);
	}
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
	exprbdd(IRExpr *cond, exprbdd *trueB, exprbdd *falseB)
		: parentT(cond, trueB, falseB)
	{}
	exprbdd(leafT b)
		: parentT(b)
	{}
	static exprbdd *_var(scope *scope, bbdd::scope *, IRExpr *);
	static IRExpr *to_irexpr(exprbdd *what, std::map<exprbdd *, IRExpr *> &memo);
public:
	static bool parse(scope *scp, exprbdd **out, const char *str, const char **suffix) {
		return parentT::_parse<scope, parseLeaf>(scp, out, str, suffix);
	}
	static IRExpr *to_irexpr(exprbdd *);
	static exprbdd *var(scope *scope, bbdd::scope *, IRExpr *);
	IRType type() const {
		if (isLeaf)
			return content.leaf->type();
		else
			return content.trueBranch->type();
	}
	void sanity_check(bdd_ordering *ordering = NULL) const;
};

#endif /* !BDD_HPP__ */
