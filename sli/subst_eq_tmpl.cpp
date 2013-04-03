namespace substeq {

#ifndef NDEBUG
extern bool debug_subst_eq;
#elif !defined(debug_subst_eq)
#define debug_subst_eq false
#endif

void printExprSet(const std::set<IRExpr *> &a, FILE *f);
bool isEqConstraint(IRExpr *what);
void addRewritesFor(std::map<IRExpr *, IRExpr *> &rules,
		    std::map<IRExpr *, IRExpr *> &simplMemo,
		    IRExpr *expr);
IRExpr *do_rewrite(IRExpr *what, const std::map<IRExpr *, IRExpr *> &rewrites);

template <typename bddT> static void
print_bddT_labels(bddT *what, std::map<bddT *, int> &labels)
{
	/* Figure out how much space to reserve for the label
	   column. */
	int label_width;
	{
		std::vector<bddT *> pending;
		std::set<bddT *> visited;
		pending.push_back(what);
		while (!pending.empty()) {
			bddT *n = pending.back();
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

	std::vector<std::pair<bddT *, int> > pending;
	pending.push_back(std::pair<bddT *, int>(what, 0));
	int next_label = 0;
	while (!pending.empty()) {
		bddT *n = pending.back().first;
		int depth = pending.back().second;
		pending.pop_back();
		auto it_did_insert = labels.insert(std::pair<bddT *, int>(n, next_label));
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
				n->_prettyPrint(stdout, n->leaf());
			} else {
				ppIRExpr(n->internal().condition, stdout);
				pending.push_back(std::pair<bddT *, int>(n->internal().falseBranch, depth + 1));
				pending.push_back(std::pair<bddT *, int>(n->internal().trueBranch, depth + 1));
			}
		} else {
			printf("-> %d", it->second);
		}
		printf("\n");
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

template <typename scopeT, typename bddT> static bddT *
eq_rewrites(scopeT *scope,
	    bddT *what,
	    const std::map<bddT *, std::map<IRExpr *, IRExpr *> > &rewrites,
	    std::map<qs_args, IRExpr *> &simplMemo,
	    sane_map<bddT *, bddT *> &memo,
	    std::map<bddT *, int> &labels)
{
	if (what->isLeaf()) {
		return what;
	}
	auto it_did_insert = memo.insert(what, (bddT *)0xf001);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	auto r_it = rewrites.find(what);
	assert(r_it != rewrites.end());
	auto newCond = do_rewrite(what->internal().condition, r_it->second);
	newCond = quickSimplify(qs_args(newCond), simplMemo);
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

/* Build a mapping from bbdd nodes to expressions which are definitely
   true in that node, then try to use that mapping to simplify the
   bbdd a little bit. */
/* Note that this isn't context sensitive, to avoid horrible
 * exponential blow-ups. */
template <typename scopeT, typename bddT, bool falseBranchesFalse(bddT *)> static bddT *
_subst_eq(scopeT *scope, bddT *what)
{
	std::map<bddT *, int> labels;
	if (debug_subst_eq) {
		printf("subst_eq:\n");
		print_bddT_labels(what, labels);
	}

	std::map<bddT *, std::set<bddT *> > predecessors;

	/* Build a map from nodes to the set of nodes which
	   immediately preceed them on paths from the root. */
	std::vector<bddT *> q;
	std::set<bddT *> visited;
	predecessors[what].clear();
	q.push_back(what);
	while (!q.empty()) {
		bddT *n = q.back();
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
	sane_map<bddT *, std::set<IRExpr *> > forwardConstraint;

	/* Build forwardConstraint using a consistent advance. */
	forwardConstraint[what].clear();
	std::map<bddT *, int> neededPredecessors;
	for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
		neededPredecessors[it->first] = it->second.size();
	}
	neededPredecessors[what] = 0;
	q.push_back(what);
	while (!q.empty()) {
		bddT *n = q.back();
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
	std::map<bddT *, std::set<IRExpr *> > backwardConstraint;
	std::map<bddT *, int> neededSuccessors;
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
		bddT *n = q.back();
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
			if (falseBranchesFalse(n)) {
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
		const std::set<bddT *> &pred(predecessors[n]);
		for (auto it = pred.begin(); it != pred.end(); it++) {
			bddT *b = *it;
			assert(neededSuccessors.count(b));
			assert(neededSuccessors[b] > 0);
			assert(neededSuccessors[b] <= 2);
			if (--neededSuccessors[b] == 0) {
				q.push_back(b);
			}
		}
	}

	std::map<qs_args, IRExpr *> simplMemo;

	std::map<bddT *, std::map<IRExpr *, IRExpr *> > rewriteRules;
	for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
		bddT *n = it->first;
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
			if (*it2 != n->internal().condition) {
				addRewritesFor(rules, simplMemo, *it2);
			}
		}
	}
	sane_map<bddT *, bddT *> memo;
	return eq_rewrites(scope, what, rewriteRules, simplMemo, memo, labels);
}

template <typename s, typename t, bool fbf(t *)> static t *
subst_eq(s *scope, t *what)
{
	while (1) {
		t *n = _subst_eq<s, t, fbf>(scope, what);
		if (n == what) {
			return n;
		}
		what = n;
	}
}

};

template <typename scopeT, typename subtreeT, bool falseBranchFalse(subtreeT *)> subtreeT *
tmpl_subst_eq(scopeT *scope, subtreeT *what)
{
	return substeq::subst_eq<scopeT, subtreeT, falseBranchFalse>(scope, what);
}
