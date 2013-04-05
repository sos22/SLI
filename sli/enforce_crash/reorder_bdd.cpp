#include "sli.h"
#include "reorder_bdd.hpp"
#include "input_expression.hpp"

reorder_bbdd::construction_memo reorder_bbdd::cons_memo;
reorder_bbdd::bbdd_to_reorder_memo reorder_bbdd::conv_memo;
VexPtr<const reorder_bbdd, &ir_heap> reorder_bbdd::trueCnst;
VexPtr<const reorder_bbdd, &ir_heap> reorder_bbdd::falseCnst;

/* Print a reorder_bbdd to stdout, for debugging. */
void
pp_reorder(const reorder_bbdd *bbdd)
{
	sane_map<const reorder_bbdd *, int> labels;
	int next_label = 1;
	std::vector<const reorder_bbdd *> pending;
	pending.push_back(bbdd);
	while (!pending.empty()) {
		const reorder_bbdd *q = pending.back();
		pending.pop_back();
		if (!q) {
			continue;
		}
		auto it_did_insert = labels.insert(q, 0);
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (!did_insert) {
			if (it->second == 0) {
				it->second = next_label;
				next_label++;
			}
		} else if (!q->isLeaf) {
			pending.push_back(q->trueBranch);
			pending.push_back(q->falseBranch);
		}
	}
	int label_width;
	if (next_label == 1) {
		label_width = 0;
	} else {
		int pow10 = 10;
		label_width = 1;
		while (pow10 < next_label) {
			label_width++;
			pow10 *= 10;
		}
	}

	std::set<const reorder_bbdd *> printed;
	std::vector<std::pair<const reorder_bbdd *, int> > pqueue;
	pqueue.push_back(std::pair<const reorder_bbdd *, int>(bbdd, 0));
	while (!pqueue.empty()) {
		auto q = pqueue.back();
		pqueue.pop_back();

		if (label_width != 0) {
			int l;
			if (!labels.count(q.first) || printed.count(q.first)) {
				l = 0;
			} else {
				l = labels[q.first];
			}
			if (l) {
				printf("[%*d]", label_width, l);
			} else {
				printf("%*s", label_width + 2, "");
			}
		}
		for (int i = 0; i < q.second; i++) {
			printf("%d", i % 10);
		}
		printf(" ");
		if (!q.first) {
			printf("!!!NULL!!!");
		} else if (!printed.insert(q.first).second) {
			assert(labels.count(q.first));
			printf("[->%d]", labels[q.first]);
		} else if (q.first->isLeaf) {
			if (q.first->leaf) {
				printf("true");
			} else {
				printf("false");
			}
		} else {
			printf("ife %s", q.first->cond.name());
			pqueue.push_back(std::pair<const reorder_bbdd *, int>(q.first->falseBranch, q.second + 1));
			pqueue.push_back(std::pair<const reorder_bbdd *, int>(q.first->trueBranch, q.second + 1));
		}
		printf("\n");
	}
}

#ifndef NDEBUG
void
sanity_check_reorder(const reorder_bbdd *what)
{
	std::set<const reorder_bbdd *> visited;
	std::vector<const reorder_bbdd *> q;

	q.push_back(what);
	while (!q.empty()) {
		auto i = q.back();
		q.pop_back();
		if (i->isLeaf) {
			continue;
		}
		if (!visited.insert(i).second) {
			continue;
		}
		assert(i->trueBranch != what);
		assert(i->falseBranch != what);
		assert(i->trueBranch != i->falseBranch);
		assert(i->trueBranch->isLeaf || i->cond < i->trueBranch->cond);
		assert(i->falseBranch->isLeaf || i->cond < i->falseBranch->cond);
		q.push_back(i->trueBranch);
		q.push_back(i->falseBranch);
	}
}
#endif

/* reorder_bbdd ifelse operator.  Constructs a new reorder_bbdd
   representing ifelse(cond, t, f), reordering cond through t and f if
   necessary.  @equiv_bbdd is either NULL or a BBDD which is
   semantically equivalent to ifelse(cond, t, f); it will be cached in
   the reorder_bbdd structure and used later if we need to convert
   this node back to BBDD form. */
const reorder_bbdd *
reorder_bbdd::ifelse(const reorder_bbdd_cond &cond,
		     const reorder_bbdd *t,
		     const reorder_bbdd *f,
		     bbdd *equiv_bbdd)
{
	/* Avoid angering the OOM killer unnecessarily. */
	if (cons_memo.size() > 10000000) {
		if (!_timed_out) {
			fprintf(stderr, "whoops, too many reorder_bbdds.  Forcing a timeout\n");
		}
		_timed_out = true;
		return t;
	}

	if (!t->isLeaf && cond == t->cond) {
		t = t->trueBranch;
	}
	if (!f->isLeaf && cond == f->cond) {
		f = f->falseBranch;
	}
	if (t == f) {
		if (!t->equiv_bbdd) {
			t->equiv_bbdd = equiv_bbdd;
		}
		return t;
	}
	assert(t->isLeaf || !(cond == t->cond));
	assert(f->isLeaf || !(cond == f->cond));
	auto it_did_insert = cons_memo.insert(memo_key(cond, t, f), (const reorder_bbdd *)0xfee1);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	if ( t->isLeaf && f->isLeaf) {
		it->second = new reorder_bbdd(cond, t, f, equiv_bbdd);
		return it->second;
	}

	bool reorder_true = !t->isLeaf && t->cond < cond;
	bool reorder_false = !f->isLeaf && f->cond < cond;
	if (reorder_true && reorder_false) {
		/* Ordering violation on both branches. */
		if (t->cond < f->cond) {
			it->second = ifelse(
				t->cond,
				ifelse(
					f->cond,
					ifelse(
						cond,
						t->trueBranch,
						f->trueBranch,
						NULL),
					ifelse(
						cond,
						t->trueBranch,
						f->falseBranch,
						NULL),
					NULL),
				ifelse(
					f->cond,
					ifelse(
						cond,
						t->falseBranch,
						f->trueBranch,
						NULL),
					ifelse(
						cond,
						t->falseBranch,
						f->falseBranch,
						NULL),
					NULL),
				equiv_bbdd);
		} else if (t->cond == f->cond) {
			it->second = ifelse(
				t->cond,
				ifelse(
					cond,
					t->trueBranch,
					f->trueBranch,
					NULL),
				ifelse(
					cond,
					t->falseBranch,
					f->trueBranch,
					NULL),
				equiv_bbdd);
		} else {
			assert(f->cond < t->cond);
			it->second = ifelse(
				f->cond,
				ifelse(
					t->cond,
					ifelse(
						cond,
						t->trueBranch,
						f->trueBranch,
						NULL),
					ifelse(
						cond,
						t->falseBranch,
						f->trueBranch,
						NULL),
					NULL),
				ifelse(
					t->cond,
					ifelse(
						cond,
						t->trueBranch,
						f->falseBranch,
						NULL),
					ifelse(
						cond,
						t->falseBranch,
						f->falseBranch,
						NULL),
					NULL),
				equiv_bbdd);
		}
	} else if (reorder_true && !reorder_false) {
		/* Ordering violation only on the true branch. */
		auto t2 = ifelse(
			cond,
			t->trueBranch,
			f,
			NULL);
		auto f2 = ifelse(
			cond,
			t->falseBranch,
			f,
			NULL);
		it->second = ifelse(
			t->cond,
			t2,
			f2,
			equiv_bbdd);
	} else if (!reorder_true && reorder_false) {
		/* Ordering violation on the false branch only */
		it->second = ifelse(
			f->cond,
			ifelse(
				cond,
				t,
				f->trueBranch,
				NULL),
			ifelse(
				cond,
				t,
				f->falseBranch,
				NULL),
			equiv_bbdd);
	} else {
		/* No ordering violations */
		it->second = new reorder_bbdd(cond,
					      t,
					      f,
					      equiv_bbdd);
	}

	return it->second;
}

/* @this was constructed with one set of avail expressions, and the
   set has now changed.  Convert everything over to the new set.  This
   will re-use the old structure whenever possible. */
const reorder_bbdd *
reorder_bbdd::fixupEvalable(reorder_evaluatable &evaluatable) const
{
	if (isLeaf) {
		return this;
	}
	auto it_did_insert = evaluatable.memo.insert(this, (reorder_bbdd *)0xbabe);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	auto t = trueBranch->fixupEvalable(evaluatable);
	auto f = falseBranch->fixupEvalable(evaluatable);
	bool shouldBeEval = evaluatable(cond.cond);
	if (shouldBeEval == cond.evaluatable &&
	    t == trueBranch &&
	    f == falseBranch) {
		it->second = this;
	} else {
		it->second =
			ifelse(
				reorder_bbdd_cond(cond.rank,
						  cond.cond,
						  shouldBeEval),
				t,
				f,
				equiv_bbdd);
	}
	return it->second;
}

/* Convert @what to an unordered BBDD */
const reorder_bbdd *
reorder_bbdd::from_bbdd(bbdd *what, reorder_evaluatable &evalable)
{
	if (what->isLeaf()) {
		return reorder_bbdd::Leaf(what->leaf());
	}
	auto it_did_insert = conv_memo.insert(what, (reorder_bbdd *)0xf001a);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second->fixupEvalable(evalable);
	}
	it->second =
		ifelse(reorder_bbdd_cond(what->internal().rank,
					 what->internal().condition,
					 evalable(what->internal().condition)),
		       from_bbdd(what->internal().trueBranch, evalable),
		       from_bbdd(what->internal().falseBranch, evalable),
		       what);
	return it->second;
}

/* Convert an unordered BBDD back into an ordinary BBDD */
bbdd *
reorder_bbdd::to_bbdd(bbdd::scope *scope) const
{
	if (isLeaf) {
		return scope->cnst(leaf);
	}
	if (!equiv_bbdd) {
		equiv_bbdd = bbdd::ifelse(
			scope,
			bbdd::var(scope, cond.cond, bdd_ordering::rank_hint::Near(cond.rank)),
			trueBranch->to_bbdd(scope),
			falseBranch->to_bbdd(scope));
	}
	return equiv_bbdd;
}

/* Given that @what is reordered to have the monotonicity property,
   find the strongest condition A which only tests expressions
   evaluatable using inputs @avail such that @what implies A */
static const reorder_bbdd *
availCondition(const reorder_bbdd *what,
	       sane_map<const reorder_bbdd *, const reorder_bbdd *> &memo)
{
       if (what->isLeaf) {
               return what;
       }
       if (!what->cond.evaluatable) {
               return reorder_bbdd::Leaf(true);
       }
       auto it_did_insert = memo.insert(what, (const reorder_bbdd *)0xf001c);
       auto it = it_did_insert.first;
       auto did_insert = it_did_insert.second;
       if (!did_insert) {
               return it->second;
       }
       auto t = availCondition(what->trueBranch, memo);
       auto f = availCondition(what->falseBranch, memo);
       if (t == f) {
               it->second = t;
       } else if (t == what->trueBranch && f == what->falseBranch) {
               it->second = what;
       } else {
               it->second = reorder_bbdd::ifelse(
                       what->cond,
                       t,
                       f,
                       NULL);
       }
       return it->second;
}

/* Given that @what is reordered to have the monotonicity property,
   find a condition B such that
   @what = B && availCondition(what, avail) */
static const reorder_bbdd *
unavailCondition(const reorder_bbdd *what,
                sane_map<const reorder_bbdd *, const reorder_bbdd *> &memo)
{
       if (what->isLeaf) {
               return what;
       }
       if (!what->cond.evaluatable) {
               return what;
       }
       auto it_did_insert = memo.insert(what, (const reorder_bbdd *)0xf001d);
       auto it = it_did_insert.first;
       auto did_insert = it_did_insert.second;
       if (!did_insert) {
               return it->second;
       }
       auto t = unavailCondition(what->trueBranch, memo);
       auto f = unavailCondition(what->falseBranch, memo);
       if (t == f || (t->isLeaf && !t->leaf)) {
               it->second = f;
       } else if (f->isLeaf && !f->leaf) {
               it->second = t;
       } else if (t == what->trueBranch && f == what->falseBranch) {
               it->second = what;
       } else {
               it->second = reorder_bbdd::ifelse(
                       what->cond,
                       t,
                       f,
                       NULL);
       }
       return it->second;
}

/* Split a BDD X into components A and B such that X == A.B and A only
   relies on expressions in @avail.  The intent is that A should be as
   strong (i.e. unlikely to be true) as possible, but that's not
   really formalised. */
/* The trick here is to reorder @what so that all of the expressions
   which can be evaluated using @avail are checked before all of the
   expressions which can't be.  We can then build A by taking that
   expression and replacing all branches from an evaluatable
   expression to an unevaluatable one with branches to 1.  We build B
   by taking the reordered expression and completely removing any
   branches from an evaluatable node to the constant false leaf. */
std::pair<const reorder_bbdd *, const reorder_bbdd *>
splitExpressionOnAvailability(const reorder_bbdd *what)
{
	const reorder_bbdd *avail;
	{
		sane_map<const reorder_bbdd *, const reorder_bbdd *> memo;
		avail = availCondition(what, memo);
	}
	sanity_check_reorder(avail);

	const reorder_bbdd *unavail;
	{
		sane_map<const reorder_bbdd *, const reorder_bbdd *> memo;
		unavail = unavailCondition(what, memo);
	}
	sanity_check_reorder(unavail);

	return std::pair<const reorder_bbdd *, const reorder_bbdd *>(unavail, avail);
}
