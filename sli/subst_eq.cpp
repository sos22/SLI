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

/* Decide whether we want to rewrite from l to r or from r to l.  The
   rules are:

   -- If they're both Gets, we rewrite to reduce the register number,
   -- If one's a Get and the other isn't, we rewrite the non-Get to
      turn it into a Get.
   -- If one's an arithmetic op (associative, binop, unop, etc) and
      other's a load, we rewrite the arithmetic op into the load.
*/
eq_set::rewrite_order
eq_set::rewriteOrder(IRExpr *l, IRExpr *r)
{
	if (l == r) {
		return rewrite_eq;
	}
	if (l->tag == Iex_Const) {
		if (r->tag == Iex_Const) {
			/* Rewriting a const into a const is an
			   interesting idea.  Don't do it. */
			return rewrite_eq;
		} else {
			return rewrite_r2l;
		}
	}
	if (r->tag == Iex_Const) {
		return rewrite_l2r;
	}
	if (l->tag == Iex_Get) {
		IRExprGet *lg = (IRExprGet *)l;
		if (r->tag == Iex_Get) {
			IRExprGet *rg = (IRExprGet *)r;
			if (lg->tag < rg->tag) {
				return rewrite_r2l;
			} else {
				return rewrite_l2r;
			}
		} else {
			return rewrite_r2l;
		}
	}
	if (r->tag == Iex_Get) {
		return rewrite_l2r;
	}

	if (l->tag == Iex_Load) {
		if (r->tag == Iex_Load) {
			return rewriteOrder( ((IRExprLoad *)l)->addr,
					     ((IRExprLoad *)r)->addr );
		} else {
			return rewrite_r2l;
		}
	} else if (r->tag == Iex_Load) {
		return rewrite_r2l;
	}

	switch (l->tag) {
	case Iex_Qop: {
		auto *lq = (IRExprQop *)l;
		switch (r->tag) {
		case Iex_Qop:{
			auto *rq = (IRExprQop *)r;
			if (rq->op < lq->op) {
				return rewrite_l2r;
			} else if (rq->op > lq->op) {
				return rewrite_r2l;
			}
			auto a = rewriteOrder(lq->arg1, rq->arg1);
			if (a != rewrite_eq) {
				return a;
			}
			a = rewriteOrder(lq->arg2, rq->arg2);
			if (a != rewrite_eq) {
				return a;
			}
			a = rewriteOrder(lq->arg3, rq->arg3);
			if (a != rewrite_eq) {
				return a;
			}
			return rewriteOrder(lq->arg4, rq->arg4);
		}
		default:
			return rewrite_l2r;
		}
	}
	case Iex_Triop: {
		auto *lq = (IRExprTriop *)l;
		switch (r->tag) {
		case Iex_Qop:
			return rewrite_r2l;
		case Iex_Triop: {
			auto *rq = (IRExprTriop *)r;
			if (rq->op < lq->op) {
				return rewrite_l2r;
			} else if (rq->op > lq->op) {
				return rewrite_r2l;
			}
			auto a = rewriteOrder(lq->arg1, rq->arg1);
			if (a != rewrite_eq) {
				return a;
			}
			a = rewriteOrder(lq->arg2, rq->arg2);
			if (a != rewrite_eq) {
				return a;
			}
			return rewriteOrder(lq->arg3, rq->arg3);
		}
		default:
			return rewrite_l2r;
		}
	}
	case Iex_CCall: {
		auto *lq = (IRExprCCall *)l;
		int l_nr_args;
		for (l_nr_args = 0; lq->args[l_nr_args]; l_nr_args++) {
		}
		switch (r->tag) {
		case Iex_Qop:
		case Iex_Triop:
			return rewrite_r2l;
		case Iex_CCall: {
			auto *rq = (IRExprCCall *)r;
			int r_nr_args;
			for (r_nr_args = 0; rq->args[r_nr_args]; r_nr_args++) {
			}
			if (r_nr_args < l_nr_args) {
				return rewrite_l2r;
			} else if (r_nr_args > l_nr_args) {
				return rewrite_r2l;
			}
			for (int i = 0; i < l_nr_args; i++) {
				auto a = rewriteOrder(lq->args[i], rq->args[i]);
				if (a != rewrite_eq) {
					return a;
				}
			}
			if (rq->cee->addr < lq->cee->addr) {
				return rewrite_l2r;
			} else if (rq->cee->addr > lq->cee->addr) {
				return rewrite_r2l;
			} else {
				return rewrite_eq;
			}
		}
		default:
			return rewrite_l2r;
		}
	}
	case Iex_Binop: {
		auto *lq = (IRExprBinop *)l;
		switch (r->tag) {
		case Iex_Qop:
		case Iex_Triop:
		case Iex_CCall:
			return rewrite_r2l;
		case Iex_Binop: {
			auto *rq = (IRExprBinop *)r;
			if (rq->op < lq->op) {
				return rewrite_l2r;
			} else if (rq->op > lq->op) {
				return rewrite_r2l;
			}
			auto a = rewriteOrder(lq->arg1, rq->arg1);
			if (a != rewrite_eq) {
				return a;
			}
			return rewriteOrder(lq->arg2, rq->arg2);
		}
		default:
			return rewrite_l2r;
		}
	}
	case Iex_Associative: {
		auto *lq = (IRExprAssociative *)l;
		switch (r->tag) {
		case Iex_Qop:
		case Iex_Triop:
		case Iex_CCall:
		case Iex_Binop:
			return rewrite_r2l;
		case Iex_Associative: {
			auto *rq = (IRExprAssociative *)r;
			if (rq->nr_arguments < lq->nr_arguments) {
				return rewrite_l2r;
			} else if (rq->nr_arguments > lq->nr_arguments) {
				return rewrite_r2l;
			}
			for (int i = 0; i < lq->nr_arguments; i++) {
				auto a = rewriteOrder(lq->contents[i],
						      rq->contents[i]);
				if (a != rewrite_eq) {
					return a;
				}
			}
			if (lq->op < rq->op) {
				return rewrite_l2r;
			} else if (lq->op > rq->op) {
				return rewrite_r2l;
			} else {
				return rewrite_eq;
			}
		}
		default:
			return rewrite_r2l;
		}
	}
	case Iex_Unop: {
		auto *lq = (IRExprUnop *)l;
		switch (r->tag) {
		case Iex_Qop:
		case Iex_Triop:
		case Iex_CCall:
		case Iex_Binop:
		case Iex_Associative:
			return rewrite_r2l;
		case Iex_Unop: {
			auto *rq = (IRExprUnop *)r;
			if (rq->op < lq->op) {
				return rewrite_l2r;
			} else if (rq->op > lq->op) {
				return rewrite_r2l;
			}
			return rewriteOrder(lq->arg, rq->arg);
		}
		default:
			abort();
		}
	}
	default:
		abort();
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
