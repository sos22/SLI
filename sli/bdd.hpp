#ifndef BDD_HPP__
#define BDD_HPP__

#include <libvex_ir.h>
#include <libvex_alloc.h>
#include <libvex_parse.h>

/* Thing for specifying variable ordering. */
class bdd_ordering {
public:
	typedef enum { lt, eq, gt} ordT;
	ordT operator()(const IRExpr *a, const IRExpr *b) ;
	bool before(const IRExpr *a, const IRExpr *b) {
		return (*this)(a, b) == lt;
	}
};

template <typename _leafT, typename _subtreeT>
class _bdd : public GarbageCollected<_bdd<_leafT, _subtreeT>, &ir_heap> {
public:
	typedef _bdd<_leafT, _subtreeT> thisT;
	typedef _leafT leafT;
protected:
	virtual void _visit(HeapVisitor &hv, leafT &leaf) const = 0;
	virtual void _sanity_check(leafT leaf) const = 0;
	virtual void _prettyPrint(FILE *f, leafT what) const = 0;

	_bdd(leafT leaf)
		: isLeaf(true)
	{
		content.leaf = leaf;
	}
	_bdd(IRExpr *cond, _subtreeT *trueB, _subtreeT *falseB)
		: isLeaf(false)
	{
		content.condition = cond;
		content.trueBranch = trueB;
		content.falseBranch = falseB;
	}
public:
	bool isLeaf;
	union {
		leafT leaf;
		struct {
			/* Must be Ity_I1 */
			IRExpr *condition;
			_subtreeT *trueBranch;
			_subtreeT *falseBranch;
		};
	} content;
	void sanity_check(bdd_ordering *ordering = NULL) const {
		assert(isLeaf == true || isLeaf == false);
		if (isLeaf) {
			_sanity_check(content.leaf);
		} else {
			content.condition->sanity_check();
			assert(content.condition->type() == Ity_I1);
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

	void visit(HeapVisitor &hv) {
		if (isLeaf) {
			_visit(hv, content.leaf);
		} else {
			hv(content.condition);
			hv(content.trueBranch);
			hv(content.falseBranch);
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


class bbdd;

typedef bdd_scope<bbdd> bbdd_scope;

class bbdd : public _bdd<bool, bbdd> {
	friend class bdd_scope<bbdd>;

	static VexPtr<bbdd, &ir_heap> trueLeaf;
	static VexPtr<bbdd, &ir_heap> falseLeaf;

	void _sanity_check(bool b) const {
		assert(b == true || b == false);
	}
	void _visit(HeapVisitor &, bool &) const {
	}
	void _prettyPrint(FILE *f, bool b) const {
		if (b)
			fprintf(f, "true");
		else
			fprintf(f, "false");
	}

	bbdd(IRExpr *cond, bbdd *trueB, bbdd *falseB)
		: _bdd<bool, bbdd>(cond, trueB, falseB)
	{}
	bbdd(bool b)
		: _bdd<bool, bbdd>(b)
	{}

	static bbdd *zip(bbdd_scope *scope,
			 bbdd *a,
			 bbdd *b,
			 bbdd *(*)(bool, bool),
			 std::map<std::pair<bbdd *, bbdd *>, bbdd *> &memo);
	static bbdd *zip(bbdd_scope *scope,
			 bbdd *a,
			 bbdd *b,
			 bbdd *(*f)(bool, bool)) {
		std::map<std::pair<bbdd *, bbdd *>, bbdd *> memo;
		return zip(scope, a, b, f, memo);
	}
public:
	static bbdd *cnst(bool b) {
		if (b)
			return trueLeaf;
		else
			return falseLeaf;
	}
	static bbdd *Or(bbdd_scope *scope, bbdd *a, bbdd *b);
	static bbdd *And(bbdd_scope *scope, bbdd *a, bbdd *b);
	static bbdd *var(bbdd_scope *scope, IRExpr *a);
	static bbdd *invert(bbdd_scope *scope, bbdd *a);
	static bbdd *assume(bbdd_scope *scope,
			    bbdd *thing,
			    bbdd *assumption);
};

class intbdd;
class intbdd_scope : public bdd_scope<intbdd> {
	std::map<int, intbdd *> content;
public:
	intbdd *cnst(int k);
	intbdd_scope(bdd_ordering *_ordering)
		: bdd_scope<intbdd>(_ordering)
	{}
};

class intbdd : public _bdd<int, intbdd> {
public:
	typedef std::map<bbdd *, intbdd *> enablingTableT;
private:
	friend class bdd_scope<intbdd>;
	friend class intbdd_scope;

	void _visit(HeapVisitor &, int &) const {}
	void _sanity_check(int) const {}
	void _prettyPrint(FILE *f, int k) const {
		fprintf(f, "<%d>", k);
	}

	intbdd(int _k)
		: _bdd<int, intbdd>(_k)
	{}
	intbdd(IRExpr *cond, intbdd *a, intbdd *b)
		: _bdd<int, intbdd>(cond, a, b)
	{}
	static intbdd *from_enabling(intbdd_scope *scope,
				     const enablingTableT &inp,
				     std::map<enablingTableT, intbdd *> &memo);
	static intbdd *assume(intbdd_scope *scope,
			      intbdd *thing,
			      bbdd *assumption,
			      std::map<std::pair<intbdd *, bbdd *>, intbdd *> &memo);
public:
	static intbdd *cnst(intbdd_scope *scope, int k) { return scope->cnst(k); }
	/* An enabling table is a map from BBDDs to int BDDs.  The
	   idea is that the caller arranges that at most one of the
	   BBDDs is true (i.e. enabled) for any context and we then
	   select the matching intbdd.  @from_enabling flattens an
	   enabling table into a single int BDD */
	static intbdd *from_enabling(intbdd_scope *scope,
				     const enablingTableT &inp);

	/* Simplify @thing under the assumption that @assumption is
	 * true. */
	static intbdd *assume(intbdd_scope *scope,
			      intbdd *thing,
			      bbdd *assumption);
};

#endif /* !BDD_HPP__ */
