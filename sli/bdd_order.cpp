#include "sli.h"
#include "bdd.hpp"

namespace bdd_order {
#if 0
}
#endif

template <typename t> static void
count_nodes(t *n, std::set<t *> &memo)
{
	if (memo.insert(n).second && !n->isLeaf()) {
		count_nodes(n->internal().trueBranch, memo);
		count_nodes(n->internal().falseBranch, memo);
	}
}

template <typename t> static void
enumVars(t *n, std::set<t *> &memo, std::set<IRExpr *> &vars)
{
	if (!n->isLeaf() && memo.insert(n).second) {
		vars.insert(n->internal().condition);
		enumVars(n->internal().trueBranch, memo, vars);
		enumVars(n->internal().falseBranch, memo, vars);
	}
}
template <typename t> static void
enumVars(t *n, std::set<IRExpr *> &vars)
{
	std::set<t *> memo;
	enumVars(n, memo, vars);
}

Heap reordering_heap;

typedef std::vector<IRExpr *> orderingT;

struct reordered : public GarbageCollected<reordered, &reordering_heap> {
	struct contentT {
		bool isLeaf;
		union {
			struct {
				IRExpr *key;
				reordered *trueB;
				reordered *falseB;
			} internal;
			void *leaf;
		};
		bool operator<(const contentT &o) const {
			if (isLeaf < o.isLeaf) {
				return true;
			} else if (isLeaf > o.isLeaf) {
				return false;
			}
			if (isLeaf) {
				return leaf < o.leaf;
			}
			if (internal.key < o.internal.key) {
				return true;
			} else if (internal.key > o.internal.key) {
				return false;
			} else if (internal.trueB < o.internal.trueB) {
				return true;
			} else if (internal.trueB > o.internal.trueB) {
				return false;
			} else {
				return internal.falseB < o.internal.falseB;
			}
		}
	};
	contentT content;
	reordered(const contentT &from)
		: content(from)
	{
	}
	void pp(FILE *f, int depth) const;
	void visit(HeapVisitor &) { abort(); }
	NAMED_CLASS
};

void
reordered::pp(FILE *f, int depth) const
{
	if (content.isLeaf) {
		fprintf(f, "%*sLeaf %p\n", depth * 3, "", content.leaf);
	} else {
		fprintf(f, "%*sInternal %p\n", depth * 3, "", content.internal.key);
		content.internal.trueB->pp(f, depth + 1);
		content.internal.falseB->pp(f, depth + 1);
	}
}

template <typename t, typename scp> static t *
setVariable(scp *scope, t *what, IRExpr *var, bool setTo, sane_map<t *, t *> &memo)
{
	if (what->isLeaf()) {
		return what;
	}
	auto it_did_insert = memo.insert(what, (t *)0xcafe);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (what->internal().condition == var) {
			if (setTo) {
				it->second = what->internal().trueBranch;
			} else {
				it->second = what->internal().falseBranch;
			}
		} else {
			auto tb = setVariable(scope, what->internal().trueBranch, var, setTo, memo);
			auto fb = setVariable(scope, what->internal().falseBranch, var, setTo, memo);
			if (tb == what->internal().trueBranch &&
			    fb == what->internal().falseBranch) {
				it->second = what;
			} else {
				it->second = scope->node(what->internal().condition, what->internal().rank, tb, fb);
			}
		}
	}
	return it->second;
}

template <typename t, typename scp> static t *
setVariable(scp *scope, t *what, IRExpr *var, bool setTo)
{
	sane_map<t *, t *> memo;
	return setVariable(scope, what, var, setTo, memo);
}

static void
reorder_size(reordered *a, std::set<reordered *> &memo)
{
	if (!memo.insert(a).second || a->content.isLeaf) {
		return;
	}
	reorder_size(a->content.internal.trueB, memo);
	reorder_size(a->content.internal.falseB, memo);
}

static unsigned long
reorder_size(reordered *a, reordered *b)
{
	std::set<reordered *> memo;
	reorder_size(a, memo);
	reorder_size(b, memo);
	return memo.size();
}

static unsigned long
reorder_size(reordered *a)
{
	std::set<reordered *> memo;
	reorder_size(a, memo);
	return memo.size();
}

template <typename t, typename scp> static reordered *
optimal_reordering(scp *scope,
		   t *what,
		   sane_map<t *, reordered *> &memo,
		   sane_map<reordered::contentT, reordered *> &intern)
{
	auto it_did_insert = memo.insert(what, (reordered *)0xf001b);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;

	if (!did_insert) {
		return it->second;
	}
	reordered::contentT result;
	if (what->isLeaf()) {
		result.isLeaf = true;
		result.leaf = what;
	} else {
		std::set<IRExpr *> remainingVars;
		enumVars(what, remainingVars);
		assert(!remainingVars.empty());

		result.isLeaf = false;
		result.internal.key = (IRExpr *)0xd00d;

		/* splits[x].first = what you get if you set x to true.
		   splits[x].second = what you get if you set x to false. */
		std::map<IRExpr *, std::pair<t *, t *> > splits;
		for (auto it = remainingVars.begin(); it != remainingVars.end(); it++) {
			auto trueB = setVariable(scope, what, *it, true);
			auto falseB = setVariable(scope, what, *it, false);
			assert(trueB != what);
			assert(falseB != what);
			if (trueB->isLeaf() || falseB->isLeaf()) {
				/* If we have the option of making the
				   BDD linear then that's always a
				   good idea. */
				result.internal.key = *it;
				result.internal.trueB = optimal_reordering(scope, trueB, memo, intern);
				result.internal.falseB = optimal_reordering(scope, falseB, memo, intern);
				goto found_it;
			}
			splits[*it] = std::pair<t *, t *>(trueB, falseB);
		}

		/* Didn't manage to find an easy case -> do it exhaustively. */
		unsigned long bestCost = ~0ul;
		for (auto it = remainingVars.begin(); it != remainingVars.end(); it++) {
			assert(splits.count(*it));
			std::pair<t *, t *> &split(splits[*it]);
			auto trueB = split.first;
			auto falseB = split.second;
			auto trueR = optimal_reordering(scope, trueB, memo, intern);
			reordered *falseR;
			if (trueB == falseB) {
				falseR = trueR;
			} else {
				falseR = optimal_reordering(scope, falseB, memo, intern);
			}
			if (trueR == falseR) {
				unsigned long thisOneCost = reorder_size(trueR);
				if (thisOneCost + 1 < bestCost) {
					bestCost = thisOneCost + 1;
					result = trueR->content;
				}
			} else {
				unsigned long thisOneCost = reorder_size(trueR, falseR);
				if (thisOneCost + 1 < bestCost) {
					bestCost = thisOneCost + 1;
					result.internal.key = *it;
					result.internal.trueB = trueR;
					result.internal.falseB = falseR;
				}
			}
		}
	}
found_it:
	auto it2_di2 = intern.insert(result, (reordered *)0xbabe);
	if (it2_di2.second) {
		it2_di2.first->second = new reordered(result);
	}
	it->second = it2_di2.first->second;
	return it2_di2.first->second;
}

static void
printReordered(reordered *what, int field_width, std::set<reordered *> &visited,
	       const sane_map<reordered *, int> &labels, int depth)
{
	if (field_width != 0) {
		auto it = labels.find(what);
		if (it != labels.end() && !visited.count(what) && !what->content.isLeaf) {
			printf("[%*d]", field_width - 2, it->second);
		} else {
			printf("%*s", field_width, "");
		}
	}
	for (int i = 0; i < depth; i++) {
		if (i % 5 == 0) {
			printf("%d", (i/5)%10);
		} else {
			printf(" ");
		}
	}
	if (what->content.isLeaf) {
		printf("Leaf: %p\n", what->content.leaf);
	} else if (!visited.insert(what).second) {
		assert(field_width != 0);
		auto it = labels.find(what);
		assert(it != labels.end());
		printf("[->%*d]\n", field_width - 2, it->second);
	} else {
		printf("Internal: ");
		ppIRExpr(what->content.internal.key, stdout);
		printf("\n");
		printReordered(what->content.internal.trueB, field_width,
			       visited, labels, depth + 1);
		printReordered(what->content.internal.falseB, field_width,
			       visited, labels, depth + 1);
	}
}

static void
printReordered(reordered *what)
{
	sane_map<reordered *, int> labels;
	std::set<reordered *> visited;
	std::vector<reordered *> q;
	int next_label = 1;

	q.push_back(what);
	while (!q.empty()) {
		reordered *w = q.back();
		q.pop_back();
		if (!visited.insert(w).second || w->content.isLeaf) {
			continue;
		}
		if (visited.count(w->content.internal.trueB)) {
			if (!labels.count(w->content.internal.trueB)) {
				labels[w->content.internal.trueB] = next_label;
				next_label++;
			}
		} else {
			q.push_back(w->content.internal.trueB);
		}
		if (visited.count(w->content.internal.falseB)) {
			if (!labels.count(w->content.internal.falseB)) {
				labels[w->content.internal.falseB] = next_label;
				next_label++;
			}
		} else {
			q.push_back(w->content.internal.falseB);
		}
	}

	int field_width;
	if (next_label == 1) {
		field_width = 0;
	} else {
		field_width = 2;
		int max_field = 1;
		while (max_field < next_label) {
			max_field *= 10;
			field_width++;
		}
	}

	visited.clear();
	printReordered(what, field_width, visited, labels, 0);
}

template <typename t, typename scope> static double
badness(scope *scp, t *bdd)
{
	std::set<t *> memo1;
	count_nodes(bdd, memo1);

	sane_map<t *, reordered *> memo;
	sane_map<reordered::contentT, reordered *> intern;
	reordered *rr = optimal_reordering(scp, bdd, memo, intern);
	unsigned long bestSize = reorder_size(rr);
	printf("Best semi-order has %ld nodes, ours had %ld\n", bestSize, memo1.size());
	printf("Best semi-ordering:\n");

	printReordered(rr);

	LibVEX_gc(reordering_heap);

	return double(memo1.size()) / bestSize - 1;
}

};

double
bdd_ordering_badness(bbdd::scope *scope, bbdd *what)
{
	return bdd_order::badness(scope, what);
}
double
bdd_ordering_badness(smrbdd::scope *scope, smrbdd *what)
{
	return bdd_order::badness(scope, what);
}
double
bdd_ordering_badness(exprbdd::scope *scope, exprbdd *what)
{
	return bdd_order::badness(scope, what);
}
