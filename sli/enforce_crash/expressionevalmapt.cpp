/* Gubbins for figuring out where to evaluate the various fragments of
   side-condition.  The bulk of this is a scheme for reordering the
   variables in a BDD (so that evaluatable bits are near the root) and
   something to use that to factor the BDDs into evaluatable and
   unevaluatable components. */
#include "sli.h"
#include "enforce_crash.hpp"

#ifndef NDEBUG
static bool debug_eem = false;
static bool debug_ubbdd = false;
#else
#define debug_eem false
#define debug_ubbdd false
#endif

/* First, a couple of random bits which don't really belong here but
   which don't really belong anywhere else either. */
happensAfterMapT::happensAfterMapT(const SummaryId &summary,
				   const std::set<const IRExprHappensBefore *> &trueHb,
				   const std::set<const IRExprHappensBefore *> &falseHb,
				   ThreadAbstracter &abs,
				   CrashCfg &cfg,
				   const MaiMap &mai)
{
	for (auto it = trueHb.begin(); it != trueHb.end(); it++) {
		const IRExprHappensBefore *e = *it;
		for (auto before_it = abs.begin(summary, mai, e->before, cfg); !before_it.finished(); before_it.advance()) {
			Instruction<ThreadCfgLabel> *const before = before_it.get();
			if (!before)
				continue;
			for (auto after_it = abs.begin(summary, mai, e->after, cfg); !after_it.finished(); after_it.advance()) {
				auto after = after_it.get();
				if (!after)
					continue;
				happensAfter[before].insert(after);
				happensBefore[after].insert(before);
			}
		}
	}
	for (auto it = falseHb.begin(); it != falseHb.end(); it++) {
		const IRExprHappensBefore *e = *it;
		for (auto before_it = abs.begin(summary, mai, e->before, cfg); !before_it.finished(); before_it.advance()) {
			Instruction<ThreadCfgLabel> *const before = before_it.get();
			if (!before)
				continue;
			for (auto after_it = abs.begin(summary, mai, e->after, cfg); !after_it.finished(); after_it.advance()) {
				auto after = after_it.get();
				if (!after)
					continue;
				happensAfter[after].insert(before);
				happensBefore[before].insert(after);
			}
		}
	}
}

happensBeforeMapT::happensBeforeMapT(const SummaryId &summary,
				     const MaiMap &mai,
				     const std::set<const IRExprHappensBefore *> &trueHb,
				     const std::set<const IRExprHappensBefore *> &falseHb,
				     instructionDominatorMapT &idom,
				     CrashCfg &cfg,
				     expressionStashMapT &exprStashPoints,
				     ThreadAbstracter &abs,
				     int &next_hb_id)
{
	for (auto it = trueHb.begin(); it != trueHb.end(); it++) {
		auto hb = *it;
		const MemoryAccessIdentifier &beforeMai(hb->before);
		const MemoryAccessIdentifier &afterMai(hb->after);
		for (auto before_it = abs.begin(summary, mai, beforeMai, cfg); !before_it.finished(); before_it.advance()) {
			Instruction<ThreadCfgLabel> *beforeInstr = before_it.get();
			if (!beforeInstr)
				continue;
			for (auto after_it = abs.begin(summary, mai, afterMai, cfg); !after_it.finished(); after_it.advance()) {
				Instruction<ThreadCfgLabel> *afterInstr = after_it.get();
				if (!afterInstr)
					continue;
				happensBeforeEdge *hbe =
					new happensBeforeEdge(
						beforeInstr,
						afterInstr,
						idom,
						exprStashPoints,
						next_hb_id++);
				(*this)[hbe->before->rip].insert(hbe);
				(*this)[hbe->after->rip].insert(hbe);
			}
		}
	}
	for (auto it = falseHb.begin(); it != falseHb.end(); it++) {
		auto hb = *it;
		const MemoryAccessIdentifier &beforeMai(hb->after);
		const MemoryAccessIdentifier &afterMai(hb->before);
		for (auto before_it = abs.begin(summary, mai, beforeMai, cfg); !before_it.finished(); before_it.advance()) {
			Instruction<ThreadCfgLabel> *beforeInstr = before_it.get();
			if (!beforeInstr)
				continue;
			for (auto after_it = abs.begin(summary, mai, afterMai, cfg); !after_it.finished(); after_it.advance()) {
				Instruction<ThreadCfgLabel> *afterInstr = after_it.get();
				if (!afterInstr)
					continue;
				happensBeforeEdge *hbe =
					new happensBeforeEdge(
						beforeInstr,
						afterInstr,
						idom,
						exprStashPoints,
						next_hb_id++);
				(*this)[hbe->before->rip].insert(hbe);
				(*this)[hbe->after->rip].insert(hbe);
			}
		}
	}
}

typedef Instruction<ThreadCfgLabel> *instr_t;

static void
print_expr_set(const std::set<input_expression> &s, FILE *f)
{
	fprintf(f, "{");
	for (auto it = s.begin(); it != s.end(); it++) {
		fprintf(f, "%s%s",
			it == s.begin() ? "" : ", ",
			it->name());
	}
	fprintf(f, "}");
}

/* Simplify a BBDD given that we know precisely where we're going to
   enter it.  We rely on the fact that any entry point expressions
   will always be at the root of the BDD. */
/* (Update comment to bdd.hpp::bdd_rank if that changes) */
static bbdd *
setEntryPoint(bbdd::scope *scope,
	      bbdd *in,
	      unsigned thread,
	      const CfgLabel &label)
{
	if (in->isLeaf() ||
	    in->internal().condition->tag != Iex_EntryPoint) {
		return in;
	}
	IRExprEntryPoint *c = (IRExprEntryPoint *)in->internal().condition;
	if (c->thread != thread) {
		/* We can use makeInternal rather than ifelse because
		   we never change the order of expressions at all. */
		return scope->makeInternal(
			c,
			in->internal().rank,
			setEntryPoint(scope, in->internal().trueBranch, thread, label),
			setEntryPoint(scope, in->internal().falseBranch, thread, label));
	} else if (c->label == label) {
		return setEntryPoint(scope,
				     in->internal().trueBranch,
				     thread,
				     label);
	} else {
		return setEntryPoint(scope,
				     in->internal().falseBranch,
				     thread,
				     label);
	}
}

/* Figure out the side-condition which needs to be checked at the
   start of an instruction, given the side conditions at all of its
   predecessors (or the entry side condition, if this is a root). */
static bbdd *
calcEntryNeeded(bbdd::scope *scope,
		instr_t instr,
		const ThreadAbstracter &abs,
		const std::map<instr_t, std::set<instr_t> > &predecessors,
		const std::set<instr_t> &roots,
		bbdd *entryNeeded,
		const std::map<instr_t, bbdd *> &leftoverCondition)
{
	bbdd *res;
	auto it = predecessors.find(instr);
	assert(it != predecessors.end());
	const std::set<instr_t> &pred(it->second);
	if (pred.empty()) {
		/* Special handling for root instructions.
		   Whereas most instructions take their
		   initial condition from the union of their
		   predecessors's left over conditions, roots
		   take their initial conditions from this
		   map. */
		assert(roots.count(instr));
		res = setEntryPoint(
			scope,
			entryNeeded,
			abs.lookup(instr->rip.thread).raw_id(),
			instr->rip.label);
	} else {
		res = scope->cnst(true);
		assert(!roots.count(instr));
		for (auto it = pred.begin(); it != pred.end(); it++) {
			/* Should this be And or Or?  If we
			   use And then we're guaranteed to
			   test every condition which needs to
			   be tested, but we might sometimes
			   double-test some of them.  If we
			   use Or then we'd never double-test
			   but might sometimes skip some
			   conditions.  Double-testing is
			   safer than skipping, so use And. */
			auto it2 = leftoverCondition.find(*it);
			assert(it2 != leftoverCondition.end());
			assert(it2->second);
			res = bbdd::And(scope, res, it2->second);
		}
	}
	return res;
}

/* Can this expression be evaluated if we only have access to the
   input expressions in @avail? */
static bool
evaluatable(IRExpr *what, const std::set<input_expression> &avail)
{
	struct v {
		static visit_result Get(const std::set<input_expression> *state,
					const IRExprGet *i) {
			if (!state->count(input_expression::registr(i))) {
				return visit_abort;
			} else {
				return visit_continue;
			}
		}
		static visit_result ControlFlow(const std::set<input_expression> *state,
						const IRExprControlFlow *i) {
			if (!state->count(input_expression::control_flow(i))) {
				return visit_abort;
			} else {
				return visit_continue;
			}
		}
		static visit_result EntryPoint(const std::set<input_expression> *state,
					       const IRExprEntryPoint *i) {
			if (!state->count(input_expression::entry_point(i))) {
				return visit_abort;
			} else {
				return visit_continue;
			}
		}
	};
	static irexpr_visitor<const std::set<input_expression> > visitor;
	visitor.Get = v::Get;
	visitor.ControlFlow = v::ControlFlow;
	visitor.EntryPoint = v::EntryPoint;
	return visit_irexpr(&avail, &visitor, what) == visit_continue;
}

/* Like a BBDD, but doesn't immediately fail if you violate the
 * ordering constraints. */
/* Maintaining ordering is still useful from a performance point of
   view, especially if you're later going to convert it back to a
   BBDD */
class unordered_bbdd : public GarbageCollected<unordered_bbdd, &ir_heap> {
	struct memo_key {
		IRExpr *cond;
		const unordered_bbdd *trueBranch;
		const unordered_bbdd *falseBranch;
		memo_key(IRExpr *_cond,
			 const unordered_bbdd *_trueBranch,
			 const unordered_bbdd *_falseBranch)
			: cond(_cond),
			  trueBranch(_trueBranch),
			  falseBranch(_falseBranch)
		{}
		bool operator <(const memo_key &o) const {
			if (cond < o.cond) {
				return true;
			} else if (cond > o.cond) {
				return false;
			} else if (trueBranch < o.trueBranch) {
				return true;
			} else if (trueBranch > o.trueBranch) {
				return false;
			} else {
				return falseBranch < o.falseBranch;
			}
		}
	};
	static sane_map<memo_key, unordered_bbdd *> memo;
	static const unordered_bbdd *trueConst;
	static const unordered_bbdd *falseConst;

	explicit unordered_bbdd(bool v)
		: in_table(false),
		  isLeaf(true),
		  leaf(v),
		  condition((IRExpr *)0xf001),
		  trueBranch((unordered_bbdd *)0xdead),
		  falseBranch((unordered_bbdd *)0xbeef)
	{}

	unordered_bbdd *_intern()
	{
		if (isLeaf || in_table) {
			return this;
		}
		trueBranch = const_cast<unordered_bbdd *>(trueBranch)->_intern();
		falseBranch = const_cast<unordered_bbdd *>(falseBranch)->_intern();
		auto it_did_insert = memo.insert(memo_key(condition, trueBranch, falseBranch), this);
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert) {
			in_table = true;
		}
		return it->second;
	}

	bool in_table;
public:
	bool isLeaf;
	bool leaf;
	IRExpr *condition;
	bdd_rank rank;
	const unordered_bbdd *trueBranch;
	const unordered_bbdd *falseBranch;

	unordered_bbdd()
		: in_table(false)
	{}

	static const unordered_bbdd *Leaf(bool l) {
		if (l) {
			return trueConst;
		} else {
			return falseConst;
		}
	}
	static const unordered_bbdd *Node(IRExpr *condition,
					  const bdd_rank &rank,
					  const unordered_bbdd *t,
					  const unordered_bbdd *f)
	{
		auto it_did_insert =
			memo.insert(memo_key(condition, t, f), (unordered_bbdd *)0xcafe);
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (!did_insert) {
			return it->second;
		}
		unordered_bbdd *res = new unordered_bbdd();
		res->in_table = true;
		res->isLeaf = false;
		res->leaf = (bool)99;
		res->condition = condition;
		res->rank = rank;
		res->trueBranch = t;
		res->falseBranch = f;
		it->second = res;
		return res;
	}
	const unordered_bbdd *intern()
	{
		return _intern();
	}
	static void reset() {
		memo.clear();
		trueConst = new unordered_bbdd(true);
		falseConst = new unordered_bbdd(false);
	}
	void visit(HeapVisitor &) {
		/* These should never be live at GC time. */
		abort();
	}
	NAMED_CLASS
};
sane_map<unordered_bbdd::memo_key, unordered_bbdd *> unordered_bbdd::memo;
const unordered_bbdd *unordered_bbdd::trueConst;
const unordered_bbdd *unordered_bbdd::falseConst;

/* Print an unordered_bbdd to stdout, for debugging. */
#ifndef NDEBUG
static void
pp_unordered(const unordered_bbdd *bbdd)
{
	sane_map<const unordered_bbdd *, int> labels;
	int next_label = 1;
	std::vector<const unordered_bbdd *> pending;
	pending.push_back(bbdd);
	while (!pending.empty()) {
		const unordered_bbdd *q = pending.back();
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

	std::set<const unordered_bbdd *> printed;
	std::vector<std::pair<const unordered_bbdd *, int> > pqueue;
	pqueue.push_back(std::pair<const unordered_bbdd *, int>(bbdd, 0));
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
			printf("ife %s", nameIRExpr(q.first->condition));
			pqueue.push_back(std::pair<const unordered_bbdd *, int>(q.first->falseBranch, q.second + 1));
			pqueue.push_back(std::pair<const unordered_bbdd *, int>(q.first->trueBranch, q.second + 1));
		}
		printf("\n");
	}
}
#else
static void
pp_unordered(const unordered_bbdd *)
{
}
#endif

/* Convert @what to an unordered BBDD */
static const unordered_bbdd *
bbdd_to_unordered(bbdd *what)
{
	std::map<bbdd *, unordered_bbdd *> memo;
	std::vector<std::pair<const unordered_bbdd **, bbdd *> > relocs;
	unordered_bbdd *newRoot;

	/* Shut compiler up */
	newRoot = (unordered_bbdd *)0xf001;

	relocs.push_back(std::pair<const unordered_bbdd **, bbdd *>(
				 const_cast<const unordered_bbdd **>(&newRoot),
				 what));
	while (!relocs.empty()) {
		auto a = relocs.back();
		relocs.pop_back();
		auto it_did_insert = memo.insert(std::pair<bbdd *, unordered_bbdd *>(a.second, (unordered_bbdd *)0xdead));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert) {
			unordered_bbdd *res;
			if (a.second->isLeaf()) {
				res = (unordered_bbdd *)unordered_bbdd::Leaf(a.second->leaf());
			} else {
				res = new unordered_bbdd();
				res->isLeaf = false;
				res->leaf = (bool)98;
				res->condition = a.second->internal().condition;
				res->rank = a.second->internal().rank;
				res->trueBranch = (unordered_bbdd *)0xf001;
				res->falseBranch = (unordered_bbdd *)0xbabe;
				relocs.push_back(
					std::pair<const unordered_bbdd **, bbdd *>
					(&res->trueBranch,
					 a.second->internal().trueBranch));
				relocs.push_back(
					std::pair<const unordered_bbdd **, bbdd *>
					(&res->falseBranch,
					 a.second->internal().falseBranch));
			}
			it->second = res;
		}
		*a.first = it->second;
	}
	return newRoot->intern();
}

/* Restructre @expr so that any expressions which can be evaluated
   using only @avail will be evaluated before any which cannot be so
   evaluated. */
static const unordered_bbdd *
reorder_for_avail(const unordered_bbdd *expr,
		  const std::set<input_expression> &avail,
		  sane_map<const unordered_bbdd *, const unordered_bbdd *> &memo)
{
	if (expr->isLeaf ||
	    (expr->trueBranch->isLeaf && expr->falseBranch->isLeaf)) {
		return expr;
	}
	auto it_did_insert = memo.insert(expr, (const unordered_bbdd *)0xfee1);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}

	/* Convert child trees first */
	auto t = reorder_for_avail(expr->trueBranch, avail, memo);
	auto f = reorder_for_avail(expr->falseBranch, avail, memo);
	if (t == f) {
		it->second = t;
		return t;
	}

	/* ife(a, b, c) -> construct a node taking the condition from
	   a.  The true and false branches are b and c */
	struct {
		const unordered_bbdd *operator()(
			const unordered_bbdd *key_from,
			const unordered_bbdd *t,
			const unordered_bbdd *f) {
			if (t == f) {
				return t;
			} else {
				return unordered_bbdd::Node(
					key_from->condition,
					key_from->rank,
					t,
					f);
			}
		}
	} ife;

	/* recur(a, b, c) -> like ife(a, b, c), except that we
	   recursively reorder in the result.  i.e. this is valid if
	   the a->b or a->c edges might include a monotonicity
	   violation, whereas ife isn't. */
	struct {
		const std::set<input_expression> *avail;
		sane_map<const unordered_bbdd *, const unordered_bbdd *> *memo;
		const unordered_bbdd *operator()(
			const unordered_bbdd *key_from,
			const unordered_bbdd *t,
			const unordered_bbdd *f)
		{
			if (t == f) {
				return t;
			} else {
				return reorder_for_avail(
					unordered_bbdd::Node(
						key_from->condition,
						key_from->rank,
						t,
						f),
					*avail,
					*memo);
			}
		}
	} recur;
	recur.avail = &avail;
	recur.memo = &memo;

	/* So now we know that the children are monotone, so that if
	   any nodes test something in @avail then the root of the
	   child must test something in @avail.  Therefore, the only
	   way that this node or any of its children could violate the
	   monotone property is if we do not test an available
	   expression but one of our children does.  Check for that
	   case and fix it up if necessary. */
	if (evaluatable(expr->condition, avail)) {
		/* We test an avail expression, so cannot violate
		 * monotonicity. */
		if (t == expr->trueBranch && f == expr->falseBranch) {
			it->second = expr;
		} else {
			it->second = unordered_bbdd::Node(
				expr->condition,
				expr->rank,
				t,
				f);
		}
	} else if (!t->isLeaf && evaluatable(t->condition, avail)) {
		/* Uh oh.  We violate the property on the true branch */
		if (!f->isLeaf && evaluatable(f->condition, avail)) {
			/* Violate on both branches.  Tricky. */
			/* If the ordering is current <our_cond> <true_cond> <false_cond>
			   then we want to go to <true_cond> <false_cond> <our_cond>
			   i.e. swap with true branch first and then false branch.
			   If it's <our_cond> <false_cond> <true_cond>
			   then we want to go to <false_cond> <true_cond> <our_cond>
			   i.e. swap with false branch first. */
			auto tt = t->trueBranch;
			auto tf = t->falseBranch;
			auto ft = f->trueBranch;
			auto ff = f->falseBranch;
			auto a = expr;
			auto b = t;
			auto c = f;
			assert(tt != tf);
			assert(ft != ff);
			if (t->rank < f->rank) {
				it->second =
					ife(b,
					    ife(c,
						recur(a,
						      tt,
						      ft),
						recur(a,
						      tt,
						      ff)),
					    ife(c,
						recur(a,
						      tf,
						      ft),
						recur(a,
						      tf,
						      ff)));
			} else if (t->rank == f->rank) {
				it->second =
					ife(b,
					    recur(a, tt, ft),
					    recur(a, tf, ff));
			} else {
				it->second =
					ife(c,
					    ife(b,
						recur(a,
						      tt,
						      ft),
						recur(a,
						      tf,
						      ft)),
					    ife(b,
						recur(a,
						      tt,
						      ff),
						recur(a,
						      tf,
						      ff)));
			}
		} else {
			/* Only a violation on the true branch.  We
			   have ife(a, ife(b, X, Y), Z) and
			   we need to turn it into
			   ife(b, ife(a, X, Y), ife(a, Y, Z)) */
			auto a = expr;
			auto b = expr->trueBranch;
			auto X = b->trueBranch;
			auto Y = b->falseBranch;
			auto Z = a->falseBranch;
			it->second =
				ife(b,
				    recur(a, X, Z),
				    recur(a, Y, Z));
		}
	} else if (!f->isLeaf && evaluatable(f->condition, avail)) {
		/* Violation on the false branch.  Turn
		   ife(a, X, ife(b, Y, Z)) into
		   ife(b, ife(a, X, Y), ife(a, X, Z))
		*/
		auto a = expr;
		auto b = expr->falseBranch;
		auto X = a->trueBranch;
		auto Y = b->trueBranch;
		auto Z = b->falseBranch;
		it->second =
			ife(b,
			    recur(a, X, Y),
			    recur(a, X, Z));
	} else {
		/* Neither branch violates the ordering constraint.
		   Phew. */
		if (t == expr->trueBranch && f == expr->falseBranch) {
			it->second = expr;
		} else {
			it->second = unordered_bbdd::Node(
				expr->condition,
				expr->rank,
				t,
				f);
		}
	}

	return it->second;
}

/* Given that @what is reordered to have the monotonicity property,
   find the strongest condition A which only tests expressions
   evaluatable using inputs @avail such that @what implies A */
static const unordered_bbdd *
availCondition(const unordered_bbdd *what,
	       const std::set<input_expression> &avail,
	       sane_map<const unordered_bbdd *, const unordered_bbdd *> &memo)
{
	if (what->isLeaf) {
		return what;
	}
	if (!evaluatable(what->condition, avail)) {
		return unordered_bbdd::Leaf(true);
	}
	auto it_did_insert = memo.insert(what, (const unordered_bbdd *)0xf001);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	auto t = availCondition(what->trueBranch, avail, memo);
	auto f = availCondition(what->falseBranch, avail, memo);
	if (t == f) {
		it->second = t;
	} else if (t == what->trueBranch && f == what->falseBranch) {
		it->second = what;
	} else {
		it->second = unordered_bbdd::Node(
			what->condition,
			what->rank,
			t,
			f);
	}
	return it->second;
}

/* Given that @what is reordered to have the monotonicity property,
   find a condition B such that
   @what = B && availCondition(what, avail) */
static const unordered_bbdd *
unavailCondition(const unordered_bbdd *what,
		 const std::set<input_expression> &avail,
		 sane_map<const unordered_bbdd *, const unordered_bbdd *> &memo)
{
	if (what->isLeaf) {
		return what;
	}
	if (!evaluatable(what->condition, avail)) {
		return what;
	}
	auto it_did_insert = memo.insert(what, (const unordered_bbdd *)0xf001);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	auto t = unavailCondition(what->trueBranch, avail, memo);
	auto f = unavailCondition(what->falseBranch, avail, memo);
	if (t == f || (t->isLeaf && !t->leaf)) {
		it->second = f;
	} else if (f->isLeaf && !f->leaf) {
		it->second = t;
	} else if (t == what->trueBranch && f == what->falseBranch) {
		it->second = what;
	} else {
		it->second = unordered_bbdd::Node(
			what->condition,
			what->rank,
			t,
			f);
	}
	return it->second;
}

/* Convert an unordered BBDD back into an ordinary BBDD */
static bbdd *
unordered_to_bbdd(bbdd::scope *scope, const unordered_bbdd *src,
		  sane_map<const unordered_bbdd *, bbdd *> &memo)
{
	auto it_did_insert = memo.insert(src, (bbdd *)0xdead);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (src->isLeaf) {
			it->second = scope->cnst(src->leaf);
		} else {
			it->second = bbdd::ifelse(
				scope,
				bbdd::var(scope, src->condition),
				unordered_to_bbdd(scope, src->trueBranch, memo),
				unordered_to_bbdd(scope, src->falseBranch, memo));
		}
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
static std::pair<bbdd *, bbdd *>
splitExpressionOnAvailability(bbdd::scope *scope,
			      bbdd *what,
			      const std::set<input_expression> &avail)
{
	unordered_bbdd::reset();
	if (debug_ubbdd) {
		printf("Split expression, avail ");
		print_expr_set(avail, stdout);
		printf("\n");
		what->prettyPrint(stdout);
	}

	const unordered_bbdd *u_what = bbdd_to_unordered(what);
	if (debug_ubbdd) {
		printf("Converted to UBBDD:\n");
		pp_unordered(u_what);
	}

	{
		sane_map<const unordered_bbdd *, const unordered_bbdd *> memo;
		u_what = reorder_for_avail(u_what, avail, memo);
		if (debug_ubbdd) {
			printf("Reordered:\n");
			pp_unordered(u_what);
		}
	}
	const unordered_bbdd *u_avail;
	{
		sane_map<const unordered_bbdd *, const unordered_bbdd *> memo;
		u_avail = availCondition(u_what, avail, memo);
		if (debug_ubbdd) {
			printf("Available fragment:\n");
			pp_unordered(u_avail);
		}
	}
	const unordered_bbdd *u_unavail;
	{
		sane_map<const unordered_bbdd *, const unordered_bbdd *> memo;
		u_unavail = unavailCondition(u_what, avail, memo);
		if (debug_ubbdd) {
			printf("Unavailable fragment:\n");
			pp_unordered(u_unavail);
		}
	}
	bbdd *b_avail;
	bbdd *unavail;
	{
		sane_map<const unordered_bbdd *, bbdd *> memo;
		b_avail = unordered_to_bbdd(scope, u_avail, memo);
		unavail = unordered_to_bbdd(scope, u_unavail, memo);
		if (debug_ubbdd) {
			printf("Convert back to BBDD; avail =\n");
			b_avail->prettyPrint(stdout);
			printf("Unavail =\n");
			unavail->prettyPrint(stdout);
		}
	}
	return std::pair<bbdd *, bbdd *>(unavail, b_avail);
}

static std::set<input_expression>
availOnEntryAndLocalStash(instr_t i,
			  const std::map<instr_t, std::set<instr_t> > &predecessors,
			  const std::map<instr_t, std::set<input_expression> > &availabilityMap,
			  const expressionStashMapT &stashMap)
{
	std::set<input_expression> res;
	auto pred_it = predecessors.find(i);
	assert(pred_it != predecessors.end());
	const std::set<instr_t> &pred(pred_it->second);
	for (auto it = pred.begin(); it != pred.end(); it++) {
		auto avail_it = availabilityMap.find(*it);
		assert(avail_it != availabilityMap.end());
		if (it == pred.begin()) {
			res = avail_it->second;
		} else {
			res &= avail_it->second;
		}
	}
	auto stash_it = stashMap.find(i->rip);
	if (stash_it != stashMap.end()) {
		const std::set<input_expression> &stashedHere(stash_it->second);
		for (auto it = stashedHere.begin(); it != stashedHere.end(); it++) {
			if (it->tag == input_expression::inp_register ||
			    it->tag == input_expression::inp_entry_point) {
				res.insert(*it);
			}
		}
	}
	return res;
}

/* Constructor for the eval map.  Figure out precisely where we're
   going to eval the side condition (which may involve splitting it up
   into several places to do incremental eval). */
/* Note that this is responsible for setting
   happensBeforeEdge::sideCondition, in addition to constructing
   itself. */
expressionEvalMapT::expressionEvalMapT(bbdd::scope *scope,
				       CrashCfg &cfg,
				       crashEnforcementRoots &roots,
				       expressionStashMapT &stashMap,
				       happensBeforeMapT &hbMap,
				       ThreadAbstracter &abs,
				       bbdd *sideCondition)
{
	if (debug_eem) {
		printf("expressionEvalMapT()\n");
		cfg.prettyPrint(stdout);
		roots.prettyPrint(stdout);
		stashMap.prettyPrint(stdout);
		hbMap.prettyPrint(stdout);
		printf("Side condition:\n");
		sideCondition->prettyPrint(stdout);
	}

	/* Count the predecessors for each instruction, so that we
	 * know when it's safe to process it. */
	std::map<instr_t, unsigned> pendingPredecessors;
	std::map<instr_t, std::set<instr_t> > predecessors;
	std::vector<instr_t> pendingInstrs;
	std::set<instr_t> seen;
	std::set<instr_t> rootInstrs;
	for (auto it = roots.begin(); !it.finished(); it.advance()) {
		auto i = cfg.findInstr(it.threadCfgLabel());
		assert(i);
		pendingInstrs.push_back(i);
		pendingPredecessors[i] = 0;
		predecessors[i].clear();
		rootInstrs.insert(i);
	}
	while (!pendingInstrs.empty()) {
		auto i = pendingInstrs.back();
		pendingInstrs.pop_back();
		if (!seen.insert(i).second) {
			continue;
		}
		for (auto it = i->successors.begin(); it != i->successors.end(); it++) {
			if (it->instr) {
				assert(!rootInstrs.count(it->instr));
				pendingPredecessors[it->instr]++;
				predecessors[it->instr].insert(i);
				pendingInstrs.push_back(it->instr);
			}
		}
	}

	/* Now figure out what inputs are available where. */
	std::map<instr_t, std::set<input_expression> > availabilityMap;
	for (auto it = rootInstrs.begin(); it != rootInstrs.end(); it++) {
		pendingInstrs.push_back(*it);
	}
	/* First pass just finds things which are available in the
	 * local thread. */
	while (!pendingInstrs.empty()) {
		auto i = pendingInstrs.back();
		pendingInstrs.pop_back();
		assert(pendingPredecessors.count(i));
		assert(pendingPredecessors[i] == 0);

		assert(!availabilityMap.count(i));
		std::set<input_expression> &avail(availabilityMap[i]);
		assert(avail.empty());

		/* Entry availability is intersection of all of the
		   predecessor exit availabilities. */
		const std::set<instr_t> &pred(predecessors[i]);
		for (auto it = pred.begin(); it != pred.end(); it++) {
			assert(availabilityMap.count(*it));
			if (it == pred.begin()) {
				avail = availabilityMap[*it];
			} else {
				avail &= availabilityMap[*it];
			}
		}

		/* Now use that to calculate exit availability. */
		auto stashit = stashMap.find(i->rip);
		if (stashit != stashMap.end()) {
			avail |= stashit->second;
		}

		availabilityMap[i] = avail;

		for (auto it = i->successors.begin(); it != i->successors.end(); it++) {
			if (it->instr && --pendingPredecessors[it->instr] == 0) {
				pendingInstrs.push_back(it->instr);
			}
		}
	}

	if (debug_eem) {
		printf("Thread-local availability map:\n");
		for (auto it = availabilityMap.begin();
		     it != availabilityMap.end();
		     it++) {
			printf("\t%s -> ", it->first->rip.name());
			print_expr_set(it->second, stdout);
			printf("\n");
		}
	}

	/* Now do the cross-thread stuff, using an iteration to fixed
	 * point. */
	for (auto it = hbMap.begin(); it != hbMap.end(); it++) {
		const std::set<happensBeforeEdge *> &edges(it->second);
		for (auto it2 = edges.begin(); it2 != edges.end(); it2++) {
			auto edge = *it2;
			assert(availabilityMap.count(edge->before));
			assert(availabilityMap.count(edge->after));
			std::set<input_expression> &availBefore(availabilityMap[edge->before]);
			std::set<input_expression> &availAfter(availabilityMap[edge->after]);
			std::set<input_expression> combined =
				availBefore | availAfter;
			if (availBefore |= combined) {
				pendingInstrs.push_back(edge->before);
			}
			if (availAfter |= combined) {
				pendingInstrs.push_back(edge->after);
			}
		}
	}
	while (!pendingInstrs.empty()) {
		auto i = pendingInstrs.back();
		pendingInstrs.pop_back();
		assert(availabilityMap.count(i));
		const std::set<input_expression> &avail(availabilityMap[i]);
		for (auto it = i->successors.begin(); it != i->successors.end(); it++) {
			if (it->instr) {
				if (availabilityMap[it->instr] |= avail) {
					pendingInstrs.push_back(it->instr);
				}
			}
		}
	}

	if (debug_eem) {
		printf("Cross-thread availability map:\n");
		for (auto it = availabilityMap.begin();
		     it != availabilityMap.end();
		     it++) {
			printf("\t%s -> ", it->first->rip.name());
			print_expr_set(it->second, stdout);
			printf("\n");
		}
	}

	/* Now figure out what side condition we want to check at
	   every instruction.  For each node, we take the condition at
	   the start of the node and split it into a component which
	   can be evaluated at that instruction (this->evalAt) and a
	   component which has to be deferred
	   (@leftoverCondition).  */
	std::map<instr_t, bbdd *> leftoverCondition;

	for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
		pendingPredecessors[it->first] = it->second.size();
	}
	std::set<happensBeforeEdge *> allEdges;
	for (auto it = hbMap.begin(); it != hbMap.end(); it++) {
		allEdges |= it->second;
	}
	if (debug_eem) {
		printf("Local predecessor count map:\n");
		for (auto it = pendingPredecessors.begin();
		     it != pendingPredecessors.end();
		     it++) {
			printf("\t%s -> %d\n",
			       it->first->rip.name(),
			       it->second);
		}
	}
	for (auto it = allEdges.begin(); it != allEdges.end(); it++) {
		auto hb = *it;
		assert(pendingPredecessors.count(hb->before));
		assert(pendingPredecessors.count(hb->after));
		pendingPredecessors[hb->after]++;
	}
	for (auto it = allEdges.begin(); it != allEdges.end(); it++) {
		auto hb = *it;
		pendingPredecessors[hb->before] +=
			predecessors[hb->after].size();
	}
	if (debug_eem) {
		printf("Predecessor count map:\n");
		for (auto it = pendingPredecessors.begin();
		     it != pendingPredecessors.end();
		     it++) {
			printf("\t%s -> %d\n",
			       it->first->rip.name(),
			       it->second);
		}
	}

	for (auto it = pendingPredecessors.begin(); it != pendingPredecessors.end(); it++) {
		if (it->second == 0) {
			pendingInstrs.push_back(it->first);
		}
	}

	while (!pendingInstrs.empty()) {
		auto i = pendingInstrs.back();
		pendingInstrs.pop_back();
		assert(pendingPredecessors.count(i));
		assert(pendingPredecessors[i] == 0);

		if (debug_eem) {
			printf("Consider %s\n", i->rip.name());
		}

		/* At the start of the instruction, we have to check
		   everything which hasn't been checked by one of our
		   predecessors. */
		bbdd *entryNeeded;
		entryNeeded = calcEntryNeeded(scope, i, abs, predecessors,
					      rootInstrs, sideCondition,
					      leftoverCondition);
		if (hbMap.count(i->rip)) {
			if (debug_eem) {
				printf("Entry needed without HBs:\n");
				entryNeeded->prettyPrint(stdout);
			}
			const std::set<happensBeforeEdge *> &hbEdges(hbMap[i->rip]);
			for (auto it = hbEdges.begin();
			     it != hbEdges.end();
			     it++) {
				auto hb = *it;
				/* If something is tested by the other
				   end of a control flow edge then we
				   don't need to test it at this
				   end. */
				entryNeeded = bbdd::Or(
					scope,
					entryNeeded,
					calcEntryNeeded(
						scope,
						hb->before == i ?
							hb->after :
							hb->before,
						abs,
						predecessors,
						rootInstrs,
						sideCondition,
						leftoverCondition));
				if (debug_eem) {
					printf("With HB edge %p:\n", hb);
					entryNeeded->prettyPrint(stdout);
				}
			}
		} else if (debug_eem) {
			printf("Non-HB entry needed:\n");
			entryNeeded->prettyPrint(stdout);
		}

		/* The expression needs to be split into four phases:

		   -- Things which can be evaled once we've done
		      register stashes.
		   -- Things which can be evaled once we've done
		      RX.
		   -- Things which can be evaled once we've done
		      control flow
		   -- Things which have to be deferred.
		*/
		bbdd *leftover;
		leftover = entryNeeded;

		/* What's available at the start of the
		 * instruction? */
		std::set<input_expression> availExprs(
			availOnEntryAndLocalStash(i, predecessors,
						  availabilityMap,
						  stashMap));
		if (debug_eem) {
			printf("Avail with local stashes only: ");
			print_expr_set(availExprs, stdout);
			printf("\n");
		}

		/* What can we evaluate with that? */
		auto split1 = splitExpressionOnAvailability(
			scope,
			leftover,
			availExprs);
		if (debug_eem) {
			printf("Left over after register and entry point:\n");
			split1.first->prettyPrint(stdout);
			printf("Eval here after register and entry point:\n");
			split1.second->prettyPrint(stdout);
		}
		leftover = split1.first;
		if (!split1.second->isLeaf()) {
			evalAt[i->rip].after_regs = split1.second;
		}

		/* What about once we've done the RX operations? */
		/* Figure out what's available.  The message includes
		   everything which was available at the start of the
		   sending state, plus register and entry point
		   stashes in that state. */
		if (hbMap.count(i->rip)) {
			const std::set<happensBeforeEdge *> &hbEdges(hbMap[i->rip]);

			/* Process incoming messages first. */
			bool haveIncomingEdge = false;
			std::set<input_expression> rxed_expressions;
			bbdd *rx_checked = scope->cnst(false);
			for (auto it = hbEdges.begin();
			     it != hbEdges.end();
			     it++) {
				auto hb = *it;
				if (hb->after != i) {
					continue;
				}
				if (debug_eem) {
					printf("RX edge:\n");
					hb->prettyPrint(stdout);
				}
				if (haveIncomingEdge) {
					rxed_expressions &= availOnEntryAndLocalStash(
						hb->before,
						predecessors,
						availabilityMap,
						stashMap);
				} else {
					haveIncomingEdge = true;
					rxed_expressions = availOnEntryAndLocalStash(
						hb->before,
						predecessors,
						availabilityMap,
						stashMap);
				}
				if (hb->sideCondition) {
					rx_checked = bbdd::Or(
						scope,
						rx_checked,
						hb->sideCondition);
				} else {
					rx_checked = scope->cnst(true);
				}
			}

			if (haveIncomingEdge) {
				availExprs |= rxed_expressions;
				leftover = bbdd::assume(
					scope,
					leftover,
					rx_checked);

				if (debug_eem) {
					printf("Avail with RX effects: ");
					print_expr_set(availExprs, stdout);
					printf("\nrx_checked:\n");
					rx_checked->prettyPrint(stdout);
					printf("leftover:\n");
					leftover->prettyPrint(stdout);
				}
			}


			/* Now process message transmits */
			std::set<input_expression> acquired_by_tx;
			bool have_tx_edge = false;
			bbdd *tx_leftover = NULL;

			for (auto it = hbEdges.begin(); it != hbEdges.end(); it++) {
				auto hb = *it;
				if (hb->before != i) {
					continue;
				}

				if (debug_eem) {
					printf("Consider TX edge:\n");
					hb->prettyPrint(stdout);
				}
				assert(!hb->sideCondition);

				std::set<input_expression> availOnOtherSide(
					availOnEntryAndLocalStash(
						hb->after,
						predecessors,
						availabilityMap,
						stashMap));
				if (have_tx_edge) {
					acquired_by_tx &= availOnOtherSide;
				} else {
					acquired_by_tx = availOnOtherSide;
					have_tx_edge = true;
				}

				std::set<input_expression> availForThisMessage(availExprs);
				availForThisMessage |= availOnOtherSide;

				/* What can we evaluate on this edge? */
				auto split = splitExpressionOnAvailability(
					scope,
					leftover,
					availForThisMessage);
				if (debug_eem) {
					printf("Eval here after TX:\n");
					split.second->prettyPrint(stdout);
				}
				if (!split.second->isLeaf()) {
					hb->sideCondition = split.second;
				}
				if (tx_leftover) {
					tx_leftover = bbdd::Or(
						scope,
						tx_leftover,
						split.first);
				} else {
					tx_leftover = split.first;
				}

				/* That might unblock our successor. */
				assert(pendingPredecessors[hb->after] > 0);
				if (--pendingPredecessors[hb->after] == 0) {
					pendingInstrs.push_back(hb->after);
				}
			}

			if (have_tx_edge) {
				assert(tx_leftover);
				availExprs |= acquired_by_tx;
				leftover = tx_leftover;
				if (debug_eem) {
					printf("Avail with TX effects: ");
					print_expr_set(availExprs, stdout);
					printf("\ntx_leftover:\n");
					tx_leftover->prettyPrint(stdout);
				}
			}
		}

		/* Finally, look at control-flow related stashes */
		availExprs = availabilityMap[i];
		if (debug_eem) {
			printf("Final avail: ");
			print_expr_set(availExprs, stdout);
			printf("\n");
		}
		auto split3 = splitExpressionOnAvailability(
			scope,
			leftover,
			availExprs);
		if (debug_eem) {
			printf("Left over after control flow:\n");
			split3.first->prettyPrint(stdout);
			printf("Eval here after control flow:\n");
			split3.second->prettyPrint(stdout);
		}
		leftover = split3.first;
		if (!split3.second->isLeaf()) {
			evalAt[i->rip].after_control_flow = split3.second;
		}

		/* Anything left after that is really leftover. */
		leftoverCondition[i] = leftover;

		for (auto it = i->successors.begin(); it != i->successors.end(); it++) {
			if (it->instr) {
				assert(pendingPredecessors[it->instr] > 0);
				if (--pendingPredecessors[it->instr] == 0) {
					pendingInstrs.push_back(it->instr);
				}
				if (hbMap.count(it->instr->rip)) {
					const std::set<happensBeforeEdge *> &hbEdges(hbMap[it->instr->rip]);
					for (auto it2 = hbEdges.begin();
					     it2 != hbEdges.end();
					     it2++) {
						auto hb = *it2;
						if (hb->after == it->instr) {
							assert(pendingPredecessors[hb->before] > 0);
							if (--pendingPredecessors[hb->before] == 0) {
								pendingInstrs.push_back(hb->before);
							}
						}
					}
				}
			}
		}
	}

}

bbdd *
expressionEvalMapT::after_regs(const ThreadCfgLabel &label) const
{
	auto it = evalAt.find(label);
	if (it == evalAt.end()) {
		return NULL;
	} else {
		return it->second.after_regs;
	}
}
bbdd *
expressionEvalMapT::after_control_flow(const ThreadCfgLabel &label) const
{
	auto it = evalAt.find(label);
	if (it == evalAt.end()) {
		return NULL;
	} else {
		return it->second.after_control_flow;
	}
}

/* True if we need to eval anything at @label. */
bool
expressionEvalMapT::count(const ThreadCfgLabel &label) const
{
	return evalAt.count(label) != 0;
}

void
expressionEvalMapT::runGc(HeapVisitor &hv)
{
	for (auto it = evalAt.begin(); it != evalAt.end(); it++) {
		hv(it->second.after_regs);
		hv(it->second.after_control_flow);
	}
}

/* Combine two disjoint eval maps */
void
expressionEvalMapT::operator |=(const expressionEvalMapT &o)
{
	for (auto it = o.evalAt.begin(); it != o.evalAt.end(); it++) {
		auto it2_did_insert = evalAt.insert(it->first, it->second);
		auto it2 = it2_did_insert.first;
		auto did_insert = it2_did_insert.second;
		if (!did_insert) {
			/* This is safe because every slice is
			   supposed to use a different abstract thread
			   ID */
			abort();
		}
	}
}

void
expressionEvalMapT::prettyPrint(FILE *f) const
{
	fprintf(f, "\texpressionEvalMap:\n");
	for (auto it = evalAt.begin(); it != evalAt.end(); it++) {
		fprintf(f, "\t\t%s ->\n", it->first.name());
		if (it->second.after_regs) {
			fprintf(f, "\t\t\tafter_regs =\n");
			it->second.after_regs->prettyPrint(f);
		}
		if (it->second.after_control_flow) {
			fprintf(f, "\t\t\tafter_control_flow =\n");
			it->second.after_control_flow->prettyPrint(f);
		}
	}
}

bool
expressionEvalMapT::parse(bbdd::scope *scope, const char *str, const char **suffix)
{
	if (!parseThisString("expressionEvalMap:\n", str, &str)) {
		return false;
	}
	while (1) {
		ThreadCfgLabel l;
		if (!l.parse(str, &str) ||
		    !parseThisString(" ->\n", str, &str)) {
			break;
		}
		bbdd *after_regs = NULL;
		bbdd *after_cf = NULL;
		if (parseThisString("after_regs =\n", str, &str)) {
			if (!bbdd::parse(scope, &after_regs, str, &str)) {
				return false;
			}
		}
		if (parseThisString("after_control_flow =\n", str, &str)) {
			if (!bbdd::parse(scope, &after_cf, str, &str)) {
				return false;
			}
		}
		assert(!evalAt.count(l));
		evalAt[l].after_regs = after_regs;
		evalAt[l].after_control_flow = after_cf;
	}
	*suffix = str;
	return true;
}

expressionEvalMapT::expressionEvalMapT()
{
}
