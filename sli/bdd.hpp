#ifndef BDD_HPP__
#define BDD_HPP__

#include <libvex_ir.h>
#include <libvex_alloc.h>
#include <libvex_parse.h>

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
	bdd_ordering() : GcCallback<&ir_heap>(true), nextRanking(0) {}
};

template <typename _leafT, typename _subtreeT>
class _bdd : public GarbageCollected<_bdd<_leafT, _subtreeT>, &ir_heap> {
public:
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

template <typename constT, typename subtreeT> class const_bdd : public _bdd<constT, subtreeT> {
public:
	typedef constT leafT;
	typedef const_bdd_scope<subtreeT> scope;
private:
	void _visit(HeapVisitor &, constT &) const {
	}

protected:
	class binary_zip_internal {
	public:
		subtreeT *first;
		subtreeT *second;
		IRExpr *bestCond(bdd_ordering *ordering) const;
		binary_zip_internal trueSucc(bdd_ordering *, IRExpr *cond) const;
		binary_zip_internal falseSucc(bdd_ordering *, IRExpr *cond) const;
		binary_zip_internal(subtreeT *_first, subtreeT *_second)
			: first(_first), second(_second)
		{}
		bool isLeaf() const;
		subtreeT *leafzip(subtreeT *(*f)(leafT, leafT)) const {
			assert(isLeaf());
			return f(first->content.leaf, second->content.leaf);
		}
		bool operator<(const binary_zip_internal &o) const {
			if (first < o.first)
				return true;
			if (first > o.first)
				return false;
			return second < o.second;
		}
	};
	template <typename scopeT, typename zipInternalT, typename zipLeafT> static subtreeT *zip(
		scopeT *,
		zipInternalT,
		zipLeafT,
		std::map<zipInternalT, subtreeT *> &memo);
	template <typename scopeT, typename zipInternalT, typename zipLeafT> static subtreeT *zip(
		scopeT *scp,
		zipInternalT where,
		zipLeafT leaf) {
		std::map<zipInternalT, subtreeT *> memo;
		return zip(scp, where, leaf, memo);
	}

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

	bbdd(IRExpr *cond, bbdd *trueB, bbdd *falseB)
		: const_bdd<bool, bbdd>(cond, trueB, falseB)
	{}
	bbdd(bool b)
		: const_bdd<bool, bbdd>(b)
	{}
public:
	static bbdd *Or(scope *, bbdd *a, bbdd *b);
	static bbdd *And(scope *, bbdd *a, bbdd *b);
	static bbdd *var(scope *, IRExpr *a);
	static bbdd *invert(scope *, bbdd *a);
	static bbdd *assume(scope *,
			    bbdd *thing,
			    bbdd *assumption);
};

class intbdd : public const_bdd<int, intbdd> {
	friend class const_bdd_scope<intbdd>;
	friend class bdd_scope<intbdd>;
public:
	typedef std::map<bbdd *, intbdd *> enablingTableT;
private:
	void _sanity_check(int) const {
	}
	void _prettyPrint(FILE *f, int k) const {
		fprintf(f, "<%d>", k);
	}

	static intbdd *from_enabling(scope *,
				     const enablingTableT &inp,
				     std::map<enablingTableT, intbdd *> &memo);
	static intbdd *assume(scope *,
			      intbdd *thing,
			      bbdd *assumption,
			      std::map<std::pair<intbdd *, bbdd *>, intbdd *> &memo);
	intbdd(IRExpr *cond, intbdd *trueB, intbdd *falseB)
		: const_bdd<int, intbdd>(cond, trueB, falseB)
	{}
	intbdd(int b)
		: const_bdd<int, intbdd>(b)
	{}
public:
	/* An enabling table is a map from BBDDs to int BDDs.  The
	   idea is that the caller arranges that at most one of the
	   BBDDs is true (i.e. enabled) for any context and we then
	   select the matching intbdd.  @from_enabling flattens an
	   enabling table into a single int BDD */
	static intbdd *from_enabling(scope *,
				     const enablingTableT &inp);

	/* Simplify @thing under the assumption that @assumption is
	 * true. */
	static intbdd *assume(scope *,
			      intbdd *thing,
			      bbdd *assumption);
};

#endif /* !BDD_HPP__ */
