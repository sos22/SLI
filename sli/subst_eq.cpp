/* Bits for simplifying a BDD to take advantage of known-true
   equalities at interesting points in the graph. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "simplify_irexpr.hpp"
#include "bdd.hpp"
#include "allowable_optimisations.hpp"

namespace substeq {

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

enum rewrite_order {
	rewrite_l2r, rewrite_eq, rewrite_r2l
};

/* Decide whether we want to rewrite from l to r or from r to l.  The
   aim here is to reduce the amount of bytecode we need to emit in
   order to validate them.  */
static rewrite_order
rewriteOrder(IRExpr *l, IRExpr *r)
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

/* Set @out to @out & (in1 + in2) */
template<typename t> static void
intersectPlus(std::set<t> &out, const std::set<t> &in1, t in2)
{
	for (auto it = out.begin(); it != out.end(); ) {
		if (*it == in2 || in1.count(*it)) {
			it++;
		} else {
			out.erase(it++);
		}
	}
}

static bool
isEqConstraint(IRExpr *what)
{
	if (what->tag != Iex_Binop) {
		return false;
	}
	IROp op = ((IRExprBinop *)what)->op;
	return op >= Iop_CmpEQ8 && op <= Iop_CmpEQ64;
}

static IRExpr *
do_rewrite(IRExpr *what, const std::map<IRExpr *, IRExpr *> &rewrites)
{
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
eq_rewrites(bbdd::scope *scope, bbdd *what, const std::map<bbdd *, std::map<IRExpr *, IRExpr *> > &rewrites,
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
	auto r_it = rewrites.find(what);
	assert(r_it != rewrites.end());
	auto newCond = do_rewrite(what->internal().condition, r_it->second);
	auto t = eq_rewrites(scope, what->internal().trueBranch, rewrites, memo);
	auto f = eq_rewrites(scope, what->internal().falseBranch, rewrites, memo);
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
	return it->second;
}

static void
addRewritesFor(std::map<IRExpr *, IRExpr *> &rules, IRExpr *expr)
{
	assert(isEqConstraint(expr));
	IRExpr *arg1 = ((IRExprBinop *)expr)->arg1;
	IRExpr *arg2 = ((IRExprBinop *)expr)->arg2;
	assert(arg1 != arg2);
	switch (rewriteOrder(arg1, arg2)) {
	case rewrite_l2r:
		rules[arg1] = arg2;
		return;
	case rewrite_r2l:
		rules[arg2] = arg1;
		return;
	case rewrite_eq:
		abort();
	}
	abort();
}

/* Build a mapping from bbdd nodes to expressions which are definitely
   true in that node, then try to use that mapping to simplify the
   bbdd a little bit. */
/* Note that this isn't context sensitive, to avoid horrible
 * exponential blow-ups. */
static bbdd *
subst_eq(bbdd::scope *scope, bbdd *what)
{
	std::map<bbdd *, std::set<bbdd *> > predecessors;

	/* Build a map from nodes to the set of nodes which
	   immediately preceed them on paths from the root. */
	std::vector<bbdd *> q;
	std::set<bbdd *> visited;
	predecessors[what].clear();
	q.push_back(what);
	while (!q.empty()) {
		bbdd *n = q.back();
		q.pop_back();
		if (n->isLeaf() ||
		    !visited.insert(n).second) {
			continue;
		}
		predecessors[n->internal().trueBranch].insert(n);
		predecessors[n->internal().falseBranch].insert(n);
		q.push_back(n->internal().trueBranch);
		q.push_back(n->internal().falseBranch);
	}

	/* Map from nodes to expressions which are known to be true
	 * when we reach that node, starting from the root. */
	sane_map<bbdd *, std::set<IRExpr *> > forwardConstraint;

	/* Build forwardConstraint using a consistent advance. */
	forwardConstraint[what].clear();
	std::map<bbdd *, int> neededPredecessors;
	for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
		neededPredecessors[it->first] = it->second.size();
	}
	neededPredecessors[what] = 0;
	q.push_back(what);
	while (!q.empty()) {
		bbdd *n = q.back();
		q.pop_back();
		if (n->isLeaf()) {
			continue;
		}
		assert(n->internal().condition->tag != Iex_Const);
		assert(neededPredecessors.count(n));
		assert(neededPredecessors[n] == 0);
		assert(forwardConstraint.count(n));

		const std::set<IRExpr *> &ctxt(forwardConstraint[n]);
		assert(!ctxt.count(n->internal().condition));
		auto t_it_did_insert = forwardConstraint.insert(n->internal().trueBranch, ctxt);
		if (t_it_did_insert.second) {
			if (isEqConstraint(n->internal().condition)) {
				t_it_did_insert.first->second.insert(n->internal().condition);
			}
		} else {
			std::set<IRExpr *> &trueCtxt(t_it_did_insert.first->second);
			intersectPlus(trueCtxt, ctxt, n->internal().condition);
		}
		auto f_it_did_insert = forwardConstraint.insert(n->internal().falseBranch, ctxt);
		if (!t_it_did_insert.second) {
			std::set<IRExpr *> &falseCtxt(f_it_did_insert.first->second);
			falseCtxt &= ctxt;
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

	/* Converse of forwardConstraint: all of the conditions which
	   are definitely true on any path from a node to the true
	   leaf. */
	std::map<bbdd *, std::set<IRExpr *> > backwardConstraint;
	std::map<bbdd *, int> neededSuccessors;
	for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
		if ( it->first->isLeaf()) {
			q.push_back(it->first);
			backwardConstraint[it->first].clear();
			neededSuccessors[it->first] = 0;
		} else {
			neededSuccessors[it->first] = 2;
		}
	}
	while (!q.empty()) {
		bbdd *n = q.back();
		q.pop_back();

		assert(neededSuccessors.count(n));
		assert(neededSuccessors[n] == 0);

		if (!n->isLeaf()) {
			assert(backwardConstraint.count(n->internal().trueBranch));
			assert(backwardConstraint.count(n->internal().falseBranch));
			assert(!backwardConstraint.count(n));
			const std::set<IRExpr *> &trueB(backwardConstraint[n->internal().trueBranch]);
			const std::set<IRExpr *> &falseB(backwardConstraint[n->internal().falseBranch]);
			std::set<IRExpr *> &res(backwardConstraint[n]);
			if (n->internal().falseBranch->isLeaf() &&
			    !n->internal().falseBranch->leaf()) {
				res = trueB;
				if (isEqConstraint(n->internal().condition)) {
					res.insert(n->internal().condition);
				}
			} else {
				res = trueB & falseB;
			}
		}

		assert(predecessors.count(n));
		const std::set<bbdd *> &pred(predecessors[n]);
		for (auto it = pred.begin(); it != pred.end(); it++) {
			bbdd *b = *it;
			assert(neededSuccessors.count(b));
			assert(neededSuccessors[b] > 0);
			assert(neededSuccessors[b] <= 2);
			if (--neededSuccessors[b] == 0) {
				q.push_back(b);
			}
		}
	}

	std::map<bbdd *, std::map<IRExpr *, IRExpr *> > rewriteRules;
	for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
		bbdd *n = it->first;
		assert(forwardConstraint.count(n));
		assert(backwardConstraint.count(n));
		assert(!rewriteRules.count(n));
		std::map<IRExpr *, IRExpr *> &rules(rewriteRules[n]);
		const std::set<IRExpr *> ctxt1(forwardConstraint[n]);
		const std::set<IRExpr *> ctxt2(backwardConstraint[n]);
		for (auto it2 = ctxt1.begin(); it2 != ctxt1.end(); it2++) {
			addRewritesFor(rules, *it2);
		}
		for (auto it2 = ctxt2.begin(); it2 != ctxt2.end(); it2++) {
			addRewritesFor(rules, *it2);
		}
	}
	sane_map<bbdd *, bbdd *> memo;
	return eq_rewrites(scope, what, rewriteRules, memo);
}


/* End of namespace */
}

bbdd *
subst_eq(bbdd::scope *scope, bbdd *what)
{
	return substeq::subst_eq(scope, what);
}
