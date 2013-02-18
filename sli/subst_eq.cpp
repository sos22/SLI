/* Bits for simplifying a BDD to take advantage of known-true
   equalities at interesting points in the graph. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "simplify_irexpr.hpp"
#include "bdd.hpp"
#include "allowable_optimisations.hpp"

namespace substeq {

class eq_set {
	std::set<IRExpr *> trueExprs;
	std::set<IRExpr *> falseExprs;
	std::map<IRExpr *, IRExpr *> rewrites;
	enum rewrite_order {
		rewrite_l2r, rewrite_eq, rewrite_r2l
	};
	static rewrite_order rewriteOrder(IRExpr *a, IRExpr *b);
public:
	void setTrue(IRExpr *);
	void setFalse(IRExpr *expr) {
		falseExprs.insert(expr);
	}
	void clear() {
		trueExprs.clear();
		falseExprs.clear();
		rewrites.clear();
	}
	void intersectPlusTrue(const eq_set &o, IRExpr *cond) {
		for (auto it = trueExprs.begin(); it != trueExprs.end(); ) {
			if (cond == *it || o.trueExprs.count(*it)) {
				it++;
			} else {
				trueExprs.erase(it++);
			}
		}
		for (auto it = falseExprs.begin(); it != falseExprs.end(); ) {
			if (o.falseExprs.count(*it)) {
				it++;
			} else {
				falseExprs.erase(it++);
			}
		}		
	}
	void intersectPlusFalse(const eq_set &o, IRExpr *cond) {
		for (auto it = trueExprs.begin(); it != trueExprs.end(); ) {
			if (o.trueExprs.count(*it)) {
				it++;
			} else {
				trueExprs.erase(it++);
			}
		}
		for (auto it = falseExprs.begin(); it != falseExprs.end(); ) {
			if (cond == *it || o.falseExprs.count(*it)) {
				it++;
			} else {
				falseExprs.erase(it++);
			}
		}		
	}
	IRExpr *rewrite(IRExpr *) const;
};

/* Estimate of the amount of bytecode we need to emit to validate
   @what, or nothing if the expression can't be bytecode evaled. */
static Maybe<int>
complexity(IRExpr *what, sane_map<IRExpr *, Maybe<int> > &memo)
{
	/* A couple of easy cases without looking in the hash
	   table. */
	if (what->tag == Iex_EntryPoint) {
		/* EntryPoints can usually be done at compile time
		   without any bytecode at all. */
		return 0;
	}
	if (what->tag == Iex_Get || what->tag == Iex_Const ||
	    what->tag == Iex_HappensBefore || what->tag == Iex_ControlFlow) {
		return 1;
	}
	if (what->tag == Iex_CCall || what->tag == Iex_FreeVariable ||
	    what->tag == Iex_GetI) {
		return Maybe<int>::nothing();
	}
	auto it_did_insert = memo.insert(what, -99999);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	switch (what->tag) {
	case Iex_Get:
	case Iex_GetI:
		abort();
	case Iex_Qop: {
		IRExprQop *q = (IRExprQop *)what;
		it->second = complexity(q->arg1, memo) +
			complexity(q->arg2, memo) +
			complexity(q->arg3, memo) +
			complexity(q->arg4, memo) +
			1;
		break;
	}
	case Iex_Triop: {
		IRExprTriop *q = (IRExprTriop *)what;
		it->second = complexity(q->arg1, memo) +
			complexity(q->arg2, memo) +
			complexity(q->arg3, memo) +
			1;
		break;
	}
	case Iex_Binop: {
		IRExprBinop *q = (IRExprBinop *)what;
		it->second = complexity(q->arg1, memo) +
			complexity(q->arg2, memo) +
			1;
		break;
	}
	case Iex_Unop: {
		IRExprUnop *q = (IRExprUnop *)what;
		it->second = complexity(q->arg, memo) +
			1;
		break;
	}
	case Iex_Const:
		abort();
	case Iex_Mux0X:
		/* Shouldn't be any, because this is pulled out of a BDD */
		abort();
	case Iex_CCall:
		abort();
	case Iex_Associative: {
		IRExprAssociative *q = (IRExprAssociative *)what;
		Maybe<int> acc(0);
		if ((q->op >= Iop_And8 && q->op <= Iop_And64) ||
		    (q->op >= Iop_Or8 && q->op <= Iop_Or64) ||
		    q->op == Iop_Or1 || q->op == Iop_And1) {
			for (int i = 0; i < q->nr_arguments; i++) {
				auto j(complexity(q->contents[i], memo));
				if (j.valid) {
					acc = acc + j;
				}
			}
		} else {
			for (int i = 0; i < q->nr_arguments; i++) {
				acc = acc + complexity(q->contents[i], memo);
			}
		}
		it->second = acc;
		break;
	}
	case Iex_Load:
		it->second = complexity(((IRExprLoad *)what)->addr, memo) + 1;
		break;
	case Iex_HappensBefore:
	case Iex_FreeVariable:
	case Iex_EntryPoint:
	case Iex_ControlFlow:
		abort();
	}
	return it->second;
}

/* Decide whether we want to rewrite from l to r or from r to l.  The
   aim here is to reduce the amount of bytecode we need to emit in
   order to validate them.  */
eq_set::rewrite_order
eq_set::rewriteOrder(IRExpr *l, IRExpr *r)
{
	if (l == r) {
		return rewrite_eq;
	}
	sane_map<IRExpr *, Maybe<int> > complex_memo;
	auto l_complex = complexity(l, complex_memo);
	auto r_complex = complexity(r, complex_memo);
	if (l_complex.valid && r_complex.valid) {
		if (l_complex.content < r_complex.content) {
			return rewrite_r2l;
		} else if (r_complex.content < l_complex.content) {
			return rewrite_l2r;
		}
		/* Note fall-through */
	} else if (l_complex.valid && !r_complex.valid) {
		return rewrite_r2l;
	} else if (!l_complex.valid && r_complex.valid) {
		return rewrite_l2r;
	} else {
		assert(!l_complex.valid && !r_complex.valid);
	}

	if (l < r) {
		return rewrite_r2l;
	} else {
		return rewrite_l2r;
	}
}

void
eq_set::setTrue(IRExpr *what)
{
	trueExprs.insert(what);
	if (what->tag != Iex_Binop) {
		return;
	}
	IRExprBinop *eq = (IRExprBinop *)what;
	if (eq->op < Iop_CmpEQ8 || eq->op > Iop_CmpEQ64) {
		return;
	}
	assert(eq->arg1 != eq->arg2);
	switch (rewriteOrder(eq->arg1, eq->arg2)) {
	case rewrite_l2r:
		if (!rewrites.count(eq->arg1)) {
			rewrites[eq->arg1] = eq->arg2;
		}
		return;
	case rewrite_r2l:
		if (rewrites.count(eq->arg2)) {
			rewrites[eq->arg2] = eq->arg1;
		}
		return;
	case rewrite_eq:
		abort();
	}
	abort();
}

IRExpr *
eq_set::rewrite(IRExpr *what) const
{
	if (trueExprs.count(what)) {
		return IRExpr_Const_U1(true);
	}
	if (falseExprs.count(what)) {
		return IRExpr_Const_U1(false);
	}
	struct : public IRExprTransformer {
		const std::map<IRExpr *, IRExpr *> *rewrites;
		IRExpr *transformIRExpr(IRExpr *e) {
			auto it = rewrites->find(e);
			if (it != rewrites->end()) {
				return it->second;
			}
			return IRExprTransformer::transformIRExpr(e);
		}
	} doit;
	doit.rewrites = &rewrites;
	return simplifyIRExpr(doit.doit(what), AllowableOptimisations::defaultOptimisations);
}

static bbdd *
do_eq_rewrites(bbdd::scope *scope, bbdd *what, const std::map<bbdd *, eq_set> &constraints,
	       sane_map<bbdd *, bbdd *> &memo)
{
	if (what->isLeaf()) {
		return what;
	}
	auto it_did_insert = memo.insert(what, (bbdd *)0xf001);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	auto it2 = constraints.find(what);

	IRExpr *newCond;
	if (it2 == constraints.end()) {
		newCond = what->internal().condition;
	} else {
		newCond = it2->second.rewrite(what->internal().condition);
	}
	if (newCond->tag == Iex_Const) {
		IRExprConst *iec = (IRExprConst *)newCond;
		if (iec->Ico.content.U1) {
			it->second = do_eq_rewrites(scope, what->internal().trueBranch, constraints, memo);
		} else {
			it->second = do_eq_rewrites(scope, what->internal().falseBranch, constraints, memo);
		}
	} else {
		auto t = do_eq_rewrites(scope, what->internal().trueBranch, constraints, memo);
		auto f = do_eq_rewrites(scope, what->internal().falseBranch, constraints, memo);

		if (newCond == what->internal().condition &&
		    t == what->internal().trueBranch &&
		    f == what->internal().falseBranch) {
			it->second = what;
		} else {
			it->second = bbdd::ifelse(
				scope,
				bbdd::var(scope, newCond),
				t,
				f);
		}
	}
	return it->second;
}

/* Build a mapping from bbdd nodes to expressions which are definitely
   true in that node and those which are definitely false, then try to
   use that mapping to simplify the bbdd a little bit. */
/* Note that this isn't context sensitive, to avoid horrible
 * exponential blow-ups. */
static bbdd *
subst_eq(bbdd::scope *scope, bbdd *what)
{
	std::map<bbdd *, int> neededPredecessors;

	/* Figure out what order we're going to visit nodes in */
	std::vector<bbdd *> q;
	std::set<bbdd *> visited;
	neededPredecessors[what] = 0;
	q.push_back(what);
	while (!q.empty()) {
		bbdd *n = q.back();
		q.pop_back();
		if (n->isLeaf() ||
		    !visited.insert(n).second) {
			continue;
		}
		neededPredecessors[n->internal().trueBranch]++;
		neededPredecessors[n->internal().falseBranch]++;
		q.push_back(n->internal().trueBranch);
		q.push_back(n->internal().falseBranch);
	}

	/* Map from nodes to expressions which are known to be true or
	   false when we reach that node. */
	sane_map<bbdd *, eq_set> constrainedContext;

	bool do_rewrite = false;

	/* Build the constainedContext map. */
	constrainedContext[what].clear();
	q.push_back(what);
	while (!q.empty()) {
		bbdd *n = q.back();
		q.pop_back();
		if (n->isLeaf()) {
			continue;
		}
		assert(neededPredecessors.count(n));
		assert(neededPredecessors[n] == 0);
		if (!constrainedContext.count(n)) {
			/* We've managed to eliminate all paths to
			   this node.  Go us. */
			continue;
		}
		const eq_set &ctxt(constrainedContext[n]);
		IRExpr *newCond = ctxt.rewrite(n->internal().condition);

		assert(n->internal().condition->tag != Iex_Const);

		do_rewrite |= (newCond != n->internal().condition);

		bool condIsTrue;
		bool condIsFalse;
		if (newCond->tag == Iex_Const) {
			IRExprConst *iec = (IRExprConst *)newCond;
			if (iec->Ico.content.U1) {
				condIsTrue = true;
				condIsFalse = false;
			} else {
				condIsTrue = false;
				condIsFalse = true;
			}
		} else {
			condIsTrue = false;
			condIsFalse = false;
		}

		if (!condIsFalse) {
			auto t_it_did_insert = constrainedContext.insert(n->internal().trueBranch, ctxt);
			if (t_it_did_insert.second) {
				t_it_did_insert.first->second.setTrue(newCond);
			} else {
				eq_set &trueCtxt(t_it_did_insert.first->second);
				trueCtxt.intersectPlusTrue(ctxt, newCond);
			}
		}

		if (!condIsTrue) {
			auto f_it_did_insert = constrainedContext.insert(n->internal().falseBranch, ctxt);
			if (f_it_did_insert.second) {
				f_it_did_insert.first->second.setFalse(newCond);
			} else {
				eq_set &falseCtxt(f_it_did_insert.first->second);
				falseCtxt.intersectPlusFalse(ctxt, newCond);
			}
		}

		assert(neededPredecessors.count(n->internal().trueBranch));
		assert(neededPredecessors[n->internal().trueBranch] > 0);
		if (--neededPredecessors[n->internal().trueBranch] == 0) {
			q.push_back(n->internal().trueBranch);
		}
		assert(neededPredecessors.count(n->internal().falseBranch));
		assert(neededPredecessors[n->internal().falseBranch] > 0);
		if (--neededPredecessors[n->internal().falseBranch] == 0) {
			q.push_back(n->internal().falseBranch);
		}
	}

	if (!do_rewrite) {
		/* No point in trying this */
		return what;
	}

	sane_map<bbdd *, bbdd *> memo;
	return do_eq_rewrites(scope, what, constrainedContext, memo);
}


/* End of namespace */
}

bbdd *
subst_eq(bbdd::scope *scope, bbdd *what)
{
	return substeq::subst_eq(scope, what);
}
