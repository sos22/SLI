/* Bits for simplifying a BDD to take advantage of known-true
   equalities at interesting points in the graph. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "simplify_irexpr.hpp"
#include "bdd.hpp"
#include "allowable_optimisations.hpp"

#ifndef NDEBUG
static bool debug_subst_eq = false;
#else
#define debug_subst_eq false
#endif

namespace substeq {

static void
print_bbdd_labels(bbdd *what, std::map<bbdd *, int> &labels)
{
	/* Figure out how much space to reserve for the label
	   column. */
	int label_width;
	{
		std::vector<bbdd *> pending;
		std::set<bbdd *> visited;
		pending.push_back(what);
		while (!pending.empty()) {
			bbdd *n = pending.back();
			pending.pop_back();
			if (!visited.insert(n).second ||
			    n->isLeaf()) {
				continue;
			}
			pending.push_back(n->internal().trueBranch);
			pending.push_back(n->internal().falseBranch);
		}
		size_t acc = 10;
		label_width = 1;
		while (acc < visited.size()) {
			label_width++;
			acc *= 10;
		}
	}

	std::vector<std::pair<bbdd *, int> > pending;
	pending.push_back(std::pair<bbdd *, int>(what, 0));
	int next_label = 0;
	while (!pending.empty()) {
		bbdd *n = pending.back().first;
		int depth = pending.back().second;
		pending.pop_back();
		auto it_did_insert = labels.insert(std::pair<bbdd *, int>(n, next_label));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert) {
			printf("%*d", label_width, next_label);
			next_label++;
		} else {
			printf("%*s", label_width, "");
		}
		printf(" ");
		for (int i = 0; i < depth; i++) {
			printf("%c", '0' + (i % 10));
		}
		printf(" ");
		if (did_insert) {
			if (n->isLeaf()) {
				if (n->leaf()) {
					printf("true");
				} else {
					printf("false");
				}
			} else {
				ppIRExpr(n->internal().condition, stdout);
				pending.push_back(std::pair<bbdd *, int>(n->internal().falseBranch, depth + 1));
				pending.push_back(std::pair<bbdd *, int>(n->internal().trueBranch, depth + 1));
			}
		} else {
			printf("-> %d", it->second);
		}
		printf("\n");
	}
}

static void
printExprSet(const std::set<IRExpr *> &a, FILE *f)
{
	fprintf(f, "{");
	for (auto it = a.begin(); it != a.end(); it++) {
		if (it != a.begin()) {
			fprintf(f, ", ");
		}
		ppIRExpr(*it, f);
	}
	fprintf(f, "}");
}

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
	return doit.doit(what);
}

static bbdd *
eq_rewrites(bbdd::scope *scope,
	    bbdd *what,
	    const std::map<bbdd *, std::map<IRExpr *, IRExpr *> > &rewrites,
	    std::map<IRExpr *, IRExpr *> &simplMemo,
	    sane_map<bbdd *, bbdd *> &memo,
	    std::map<bbdd *, int> &labels)
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
	newCond = quickSimplify(newCond, simplMemo);
	if (newCond->tag == Iex_Const) {
		if ( ((IRExprConst *)newCond)->Ico.content.U1 ) {
			if (debug_subst_eq) {
				printf("l%d: condition is true\n",
				       labels[what]);
			}
			it->second = eq_rewrites(scope, what->internal().trueBranch, rewrites, simplMemo, memo, labels);
		} else {
			if (debug_subst_eq) {
				printf("l%d: condition is false\n",
				       labels[what]);
			}
			it->second = eq_rewrites(scope, what->internal().falseBranch, rewrites, simplMemo, memo, labels);
		}
	} else {
		auto t = eq_rewrites(scope, what->internal().trueBranch, rewrites, simplMemo, memo, labels);
		auto f = eq_rewrites(scope, what->internal().falseBranch, rewrites, simplMemo, memo, labels);
		if (debug_subst_eq && newCond != what->internal().condition) {
			printf("l%d: %s -> %s\n", labels[what],
			       nameIRExpr(what->internal().condition),
			       nameIRExpr(newCond));
		}
		if (t == what->internal().trueBranch &&
		    f == what->internal().falseBranch) {
			it->second = what;
		} else {
			/* Note that we only make use of the
			   substitution if it can reduce the condition
			   all the way to a constant.  If it just
			   simplifies it a little, but not all the
			   way, we throw it away.  That's because
			   applying the simplification here tends to
			   screw up the variable ordering, which makes
			   the BDD exponentially bigger, which more
			   than outweighs the benefits of slightly
			   simpler conditions. */
			it->second = scope->node(
				what->internal().condition,
				what->internal().rank,
				t,
				f);
		}
	}
	return it->second;
}

static void
addRewritesFor(std::map<IRExpr *, IRExpr *> &rules,
	       std::map<IRExpr *, IRExpr *> &simplMemo,
	       IRExpr *expr)
{
	assert(isEqConstraint(expr));
	IRExpr *arg1 = ((IRExprBinop *)expr)->arg1;
	IRExpr *arg2 = ((IRExprBinop *)expr)->arg2;

	if (arg1 == arg2) {
		/* Special case, to avoid a potential infinite loop. */
		rules[expr] = IRExpr_Const_U1(1);
		return;
	}

	if (arg1->tag == Iex_Const &&
	    arg2->tag == Iex_Associative &&
	    ((IRExprAssociative *)arg2)->op >= Iop_Add8 &&
	    ((IRExprAssociative *)arg2)->op <= Iop_Add64) {
		/* Bit of a special case: if we have k == x + y,
		   consider using the rule x == y - k instead,
		   because that sometimes helps a bit. */
		IRExprAssociative *arg2a = (IRExprAssociative *)arg2;
		Maybe<int> complexities[arg2a->nr_arguments];
		sane_map<IRExpr *, Maybe<int> > memo;
		int nr_uneval = 0;
		for (int i = 0; nr_uneval < 2 && i < arg2a->nr_arguments; i++) {
			complexities[i] = complexity(arg2a->contents[i], memo);
			nr_uneval += complexities[i].valid == false;
		}
		/* If we have multiple unevaluatable sub-expressions
		   then we just give up and rewrite the whole RHS to
		   the LHS. */
		if (nr_uneval > 1) {
			rules[arg2] = arg1;
			return;
		}
		IRExpr *args[arg2a->nr_arguments];
		IRExpr *lhs = NULL;
		int j = 0;
		if (nr_uneval == 1) {
			/* If we have precisely one unevalable then
			   that goes on the left and everything else
			   goes on the right. */
			for (int i = 0; i < arg2a->nr_arguments; i++) {
				if (complexities[i].valid) {
					args[j++] = arg2a->contents[i];
				} else {
					assert(!lhs);
					lhs = arg2a->contents[i];
				}
			}
		} else {
			/* Okay, all expressions evaluatable.  Rewrite
			   to remove the most complicated one. */
			int bestIdx = 0;
			assert(complexities[0].valid);
			for (int i = 1; i < arg2a->nr_arguments; i++) {
				assert(complexities[i].valid);
				if (complexities[i].content > complexities[bestIdx].content) {
					bestIdx = i;
				}
			}
			lhs = arg2a->contents[bestIdx];
			for (int i = 0; i < arg2a->nr_arguments; i++) {
				if (i != bestIdx) {
					args[j++] = arg2a->contents[i];
				}
			}
		}
		assert(lhs);
		switch (arg2a->op) {
		case Iop_Add8:
			lhs = IRExpr_Unop(Iop_Neg8, lhs);
			break;
		case Iop_Add16:
			lhs = IRExpr_Unop(Iop_Neg16, lhs);
			break;
		case Iop_Add32:
			lhs = IRExpr_Unop(Iop_Neg32, lhs);
			break;
		case Iop_Add64:
			lhs = IRExpr_Unop(Iop_Neg64, lhs);
			break;
		default:
			abort();
		}
		lhs = quickSimplify(lhs, simplMemo);
		assert(j == arg2a->nr_arguments - 1);
		IRExprConst *arg1c = (IRExprConst *)arg1;
		IRExprConst *transConst = NULL;
		switch (arg1c->Ico.ty) {
		case Ity_I1:
			abort();
		case Ity_I8:
			if (arg1c->Ico.content.U8 != 0) {
				transConst = IRExpr_Const_U8(
					-arg1c->Ico.content.U8);
			}
			break;
		case Ity_I16:
			if (arg1c->Ico.content.U16 != 0) {
				transConst = IRExpr_Const_U16(
					-arg1c->Ico.content.U16);
			}
			break;
		case Ity_I32:
			if (arg1c->Ico.content.U32 != 0) {
				transConst = IRExpr_Const_U32(
					-arg1c->Ico.content.U32);
			}
			break;
		case Ity_I64:
			if (arg1c->Ico.content.U64 != 0) {
				transConst = IRExpr_Const_U64(
					-arg1c->Ico.content.U64);
			}
			break;
		case Ity_I128:
		case Ity_INVALID:
			abort();
		}
		if (transConst) {
			args[j++] = transConst;
		}
		IRExpr *rhs = quickSimplify(
			IRExpr_Associative_Copy(
				arg2a->op,
				j,
				args),
			simplMemo);
		rules[lhs] = rhs;
		return;
	}

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
_subst_eq(bbdd::scope *scope, bbdd *what)
{
	std::map<bbdd *, int> labels;
	if (debug_subst_eq) {
		printf("subst_eq:\n");
		print_bbdd_labels(what, labels);
	}

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

		if (debug_subst_eq) {
			printf("Forwards: n%d -> ", labels[n]);
			printExprSet(ctxt, stdout);
			printf("\n");
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
			if (debug_subst_eq) {
				printf("Backwards: n%d -> ", labels[n]);
				printExprSet(res, stdout);
				printf("\n");
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

	std::map<IRExpr *, IRExpr *> simplMemo;

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
			addRewritesFor(rules, simplMemo, *it2);
		}
		for (auto it2 = ctxt2.begin(); it2 != ctxt2.end(); it2++) {
			addRewritesFor(rules, simplMemo, *it2);
		}
	}
	sane_map<bbdd *, bbdd *> memo;
	return eq_rewrites(scope, what, rewriteRules, simplMemo, memo, labels);
}

static bbdd *
subst_eq(bbdd::scope *scope, bbdd *what)
{
	while (1) {
		bbdd *n = _subst_eq(scope, what);
		if (n == what) {
			return n;
		}
		what = n;
	}
}

/* End of namespace */
}

bbdd *
subst_eq(bbdd::scope *scope, bbdd *what)
{
	return substeq::subst_eq(scope, what);
}
