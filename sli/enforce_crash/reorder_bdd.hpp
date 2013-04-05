#ifndef REORDER_BDD_HPP__
#define REORDER_BDD_HPP__

#include "bdd.hpp"
#include "weak_map.hpp"

class input_expression;

template <typename resT, typename argT> class oneArgClosurePure {
public:
	virtual resT operator()(const argT &arg) const = 0;
};

/* These represent variables in the new BDD ordering. */
class reorder_bbdd_cond : public Named {
	reorder_bbdd_cond()
		: rank(),
		  cond((IRExpr *)0xf001b),
		  evaluatable((bool)97)
	{}
	char *mkName() const {
		return my_asprintf("expr = %s, %sevaluatable",
				   nameIRExpr(cond),
				   evaluatable ? "" : "not ");
	}
public:
	const bdd_rank rank;
	IRExpr *const cond;
	const bool evaluatable;

	static reorder_bbdd_cond leaf() {
		return reorder_bbdd_cond();
	}
	reorder_bbdd_cond(const bdd_rank &_rank,
			  IRExpr *_cond,
			  bool _evaluatable)
		: rank(_rank), cond(_cond), evaluatable(_evaluatable)
	{
	}

	bool operator ==(const reorder_bbdd_cond &o) const {
		if (cond != o.cond || evaluatable != o.evaluatable) {
			return false;
		}
		assert(rank == o.rank);
		return true;
	}
	bool operator <(const reorder_bbdd_cond &o) const {
		if (evaluatable < o.evaluatable) {
			return false;
		} else if (evaluatable > o.evaluatable) {
			return true;
		} else {
			return rank < o.rank;
		}
	}
	bool visit(HeapVisitor &hv) const {
		IRExpr *nCond = hv.visited(cond);
		if (!nCond) {
			return false;
		}
		*const_cast<IRExpr **>(&cond) = nCond;
		return true;
	}
	void reallyVisit(HeapVisitor &hv) {
		hv(cond);
	}
};

	       
/* Like BBDD, but order according to reorder_bbdd_cond rather than the
   simple bdd_rank. */
class reorder_bbdd : public GarbageCollected<reorder_bbdd, &ir_heap> {
	struct memo_key {
		reorder_bbdd_cond cond;
		const reorder_bbdd *trueBranch;
		const reorder_bbdd *falseBranch;
		memo_key(const reorder_bbdd_cond &_cond,
			 const reorder_bbdd *_trueBranch,
			 const reorder_bbdd *_falseBranch)
			: cond(_cond),
			  trueBranch(_trueBranch),
			  falseBranch(_falseBranch)
		{}
		bool operator <(const memo_key &o) const {
			if (trueBranch < o.trueBranch) {
				return true;
			} else if (o.trueBranch < trueBranch) {
				return false;
			} else if (falseBranch < o.falseBranch) {
				return true;
			} else if (o.falseBranch < falseBranch) {
				return false;
			} else {
				return cond < o.cond;
			}
		}
	};
	class construction_memo : public weak_map<memo_key, const reorder_bbdd *,
						  construction_memo, &ir_heap> {
	public:
		bool visitKey(HeapVisitor &hv, memo_key &what) {
			if (!what.cond.visit(hv)) {
				return false;
			}
			what.trueBranch = hv.visited(what.trueBranch);
			what.falseBranch = hv.visited(what.falseBranch);
			return what.trueBranch && what.falseBranch;
		}
	};
	class bbdd_to_reorder_memo : public weak_map<bbdd *, const reorder_bbdd *,
						     bbdd_to_reorder_memo, &ir_heap> {
	};
	static construction_memo cons_memo;
	static bbdd_to_reorder_memo conv_memo;
	static VexPtr<const reorder_bbdd, &ir_heap> trueCnst;
	static VexPtr<const reorder_bbdd, &ir_heap> falseCnst;

	explicit reorder_bbdd(bool v)
		: isLeaf(true),
		  leaf(v),
		  cond(reorder_bbdd_cond::leaf()),
		  trueBranch((const reorder_bbdd *)0xfead),
		  falseBranch((const reorder_bbdd *)0xb00f),
		  equiv_bbdd(NULL)
	{}
	reorder_bbdd(const reorder_bbdd_cond &_cond,
		     const reorder_bbdd *_trueBranch,
		     const reorder_bbdd *_falseBranch,
		     bbdd *_equivBbdd)
		: isLeaf(false), leaf(bool(96)), cond(_cond),
		  trueBranch(_trueBranch), falseBranch(_falseBranch),
		  equiv_bbdd(_equivBbdd)
	{}

	const reorder_bbdd *fixupEvalable(const oneArgClosurePure<bool, IRExpr *> &evalable,
					  sane_map<const reorder_bbdd *, const reorder_bbdd *> &) const;

public:
	bool isLeaf;
	bool leaf;
	reorder_bbdd_cond cond;
	const reorder_bbdd *trueBranch;
	const reorder_bbdd *falseBranch;
	mutable bbdd *equiv_bbdd;

	static const reorder_bbdd *from_bbdd(bbdd *, const oneArgClosurePure<bool, IRExpr *> &evalable,
					     sane_map<const reorder_bbdd *, const reorder_bbdd *> &);
	bbdd *to_bbdd(bbdd::scope *) const;

	static const reorder_bbdd *ifelse(const reorder_bbdd_cond &cond,
					  const reorder_bbdd *trueBranch,
					  const reorder_bbdd *falseBranch,
					  bbdd *equiv_bbdd);

	static const reorder_bbdd *Leaf(bool b) {
		if (b) {
			if (!trueCnst) {
				trueCnst = new reorder_bbdd(true);
			}
			return trueCnst;
		} else {
			if (!falseCnst) {
				falseCnst = new reorder_bbdd(false);
			}
			return falseCnst;
		}
	}
	void visit(HeapVisitor &hv) {
		if (!isLeaf) {
			cond.reallyVisit(hv);
			hv(trueBranch);
			hv(falseBranch);
			hv(equiv_bbdd);
		}
	}
	NAMED_CLASS
};

void pp_reorder(const reorder_bbdd *bbdd);

#ifdef NDEBUG
static inline void sanity_check_reorder(const reorder_bbdd *) {}
#else
void sanity_check_reorder(const reorder_bbdd *);
#endif

#endif /* !REORDER_BDD_HPP__ */
