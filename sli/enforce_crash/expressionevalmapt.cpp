/* Gubbins for figuring out where to evaluate the various fragments of
   side-condition.  The bulk of this is a scheme for reordering the
   variables in a BDD (so that evaluatable bits are near the root) and
   something to use that to factor the BDDs into evaluatable and
   unevaluatable components. */
#include "sli.h"
#include "enforce_crash.hpp"

#ifndef NDEBUG
static bool debug_eem = false;
static bool debug_eem_dead = false;
static bool debug_eem_schedule = false;
static bool debug_ubbdd = false;
#else
#define debug_eem false
#define debug_eem_dead false
#define debug_eem_schedule false
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
	    (in->internal().condition->tag != Iex_EntryPoint &&
	     in->internal().condition->tag != Iex_ControlFlow)) {
		return in;
	}
	/* We can use makeInternal rather than ifelse because we never
	   change the order of expressions at all. */
	if (in->internal().condition->tag == Iex_ControlFlow) {
		return scope->makeInternal(
			in->internal().condition,
			in->internal().rank,
			setEntryPoint(scope, in->internal().trueBranch, thread, label),
			setEntryPoint(scope, in->internal().falseBranch, thread, label));
	} else {
		IRExprEntryPoint *c = (IRExprEntryPoint *)in->internal().condition;
		if (c->thread != thread) {
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
	if (roots.count(instr)) {
		/* Special handling for root instructions.
		   Whereas most instructions take their
		   initial condition from the union of their
		   predecessors's left over conditions, roots
		   take their initial conditions from this
		   map. */
		res = setEntryPoint(
			scope,
			entryNeeded,
			abs.lookup(instr->rip.thread).raw_id(),
			instr->rip.label);
	} else {
		res = scope->cnst(true);
	}
	for (auto it = pred.begin(); it != pred.end(); it++) {
		/* Should this be And or Or?  If we use And then we're
		   guaranteed to test every condition which needs to
		   be tested, but we might sometimes double-test some
		   of them.  If we use Or then we'd never double-test
		   but might sometimes skip some conditions.
		   Double-testing is safer than skipping, so use
		   And. */
		auto it2 = leftoverCondition.find(*it);
		assert(it2 != leftoverCondition.end());
		assert(it2->second);
		res = bbdd::And(scope, res, it2->second);
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

/* These represent variables in the new BDD ordering. */
class reorder_bbdd_cond : public Named {
	reorder_bbdd_cond()
		: rank(),
		  cond((IRExpr *)0xf001),
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

template <typename key, typename value, typename extension, Heap *heap> class weak_map
	: public sane_map<key, value>, GcCallback<heap> {
	void runGc(HeapVisitor &hv) {
		sane_map<key, value> n;
		extension *ths = static_cast<extension *>(this);
		for (auto it = this->begin(); it != this->end(); it++) {
			key k(it->first);
			value v(it->second);
			if (ths->visitKey(hv, k) &&
			    ths->visitValue(hv, v)) {
				n.insert(k, v);
			}
		}
		this->clear();
		for (auto it = n.begin(); it != n.end(); it++) {
			this->insert(it->first, it->second);
		}
	}
public:
	weak_map()
		: GcCallback<heap>(true)
	{}

	/* These should be overridden in derived classes */
	bool visitKey(HeapVisitor &hv, key &what) {
		what = hv.visited(what);
		return what != NULL;
	}
	bool visitValue(HeapVisitor &hv, value &what) {
		what = hv.visited(what);
		return what != NULL;
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

	const reorder_bbdd *fixupEvalable(const std::set<input_expression> &avail,
					  sane_map<const reorder_bbdd *, const reorder_bbdd *> &) const;

public:
	bool isLeaf;
	bool leaf;
	reorder_bbdd_cond cond;
	const reorder_bbdd *trueBranch;
	const reorder_bbdd *falseBranch;
	mutable bbdd *equiv_bbdd;

	static const reorder_bbdd *from_bbdd(bbdd *, const std::set<input_expression> &avail,
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
		cond.reallyVisit(hv);
		hv(trueBranch);
		hv(falseBranch);
		hv(equiv_bbdd);
	}
	NAMED_CLASS
};
reorder_bbdd::construction_memo reorder_bbdd::cons_memo;
reorder_bbdd::bbdd_to_reorder_memo reorder_bbdd::conv_memo;
VexPtr<const reorder_bbdd, &ir_heap> reorder_bbdd::trueCnst;
VexPtr<const reorder_bbdd, &ir_heap> reorder_bbdd::falseCnst;

/* Print a reorder_bbdd to stdout, for debugging. */
#ifndef NDEBUG
static void
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
static void
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
#else
static void
pp_reorder(const reorder_bbdd *)
{
}
static void
sanity_check_reorder(const reorder_bbdd *)
{
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
reorder_bbdd::fixupEvalable(const std::set<input_expression> &avail,
			    sane_map<const reorder_bbdd *, const reorder_bbdd *> &memo) const
{
	if (isLeaf) {
		return this;
	}
	auto it_did_insert = memo.insert(this, (reorder_bbdd *)0xbabe);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	auto t = trueBranch->fixupEvalable(avail, memo);
	auto f = falseBranch->fixupEvalable(avail, memo);
	bool shouldBeEval = evaluatable(cond.cond, avail);
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
reorder_bbdd::from_bbdd(bbdd *what,
			const std::set<input_expression> &avail,
			sane_map<const reorder_bbdd *, const reorder_bbdd *> &availMemo)
{
	if (what->isLeaf()) {
		return reorder_bbdd::Leaf(what->leaf());
	}
	auto it_did_insert = conv_memo.insert(what, (reorder_bbdd *)0xf001);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second->fixupEvalable(avail, availMemo);
	}
	it->second =
		ifelse(reorder_bbdd_cond(what->internal().rank,
					 what->internal().condition,
					 evaluatable(what->internal().condition, avail)),
		       from_bbdd(what->internal().trueBranch, avail, availMemo),
		       from_bbdd(what->internal().falseBranch, avail, availMemo),
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
			bbdd::var(scope, cond.cond),
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
	       const std::set<input_expression> &avail,
	       sane_map<const reorder_bbdd *, const reorder_bbdd *> &memo)
{
	if (what->isLeaf) {
		return what;
	}
	if (!what->cond.evaluatable) {
		return reorder_bbdd::Leaf(true);
	}
	auto it_did_insert = memo.insert(what, (const reorder_bbdd *)0xf001);
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
		 const std::set<input_expression> &avail,
		 sane_map<const reorder_bbdd *, const reorder_bbdd *> &memo)
{
	if (what->isLeaf) {
		return what;
	}
	if (!what->cond.evaluatable) {
		return what;
	}
	auto it_did_insert = memo.insert(what, (const reorder_bbdd *)0xf001);
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
static std::pair<bbdd *, bbdd *>
splitExpressionOnAvailability(bbdd::scope *scope,
			      bbdd *what,
			      const std::set<input_expression> &avail)
{
	if (debug_ubbdd) {
		printf("Split expression, avail ");
		print_expr_set(avail, stdout);
		printf("\n");
		what->prettyPrint(stdout);
	}

	sane_map<const reorder_bbdd *, const reorder_bbdd *> availMemo;
	const reorder_bbdd *u_what = reorder_bbdd::from_bbdd(what, avail, availMemo);
	if (debug_ubbdd) {
		printf("Converted to UBBDD:\n");
		pp_reorder(u_what);
	}
	sanity_check_reorder(u_what);

	const reorder_bbdd *u_avail;
	{
		sane_map<const reorder_bbdd *, const reorder_bbdd *> memo;
		u_avail = availCondition(u_what, avail, memo);
		if (debug_ubbdd) {
			printf("Available fragment:\n");
			pp_reorder(u_avail);
		}
	}
	sanity_check_reorder(u_avail);

	const reorder_bbdd *u_unavail;
	{
		sane_map<const reorder_bbdd *, const reorder_bbdd *> memo;
		u_unavail = unavailCondition(u_what, avail, memo);
		if (debug_ubbdd) {
			printf("Unavailable fragment:\n");
			pp_reorder(u_unavail);
		}
	}
	sanity_check_reorder(u_unavail);

	bbdd *b_avail;
	bbdd *unavail;
	b_avail = u_avail->to_bbdd(scope);
	unavail = u_unavail->to_bbdd(scope);
	if (debug_ubbdd) {
		printf("Convert back to BBDD; avail =\n");
		b_avail->prettyPrint(stdout);
		printf("Unavail =\n");
		unavail->prettyPrint(stdout);
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

	if (debug_eem_schedule && !debug_eem) {
		printf("expressionEvalMapT:\n");
		cfg.prettyPrint(stdout);
		roots.prettyPrint(stdout);
		hbMap.prettyPrint(stdout);
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
				pendingPredecessors[it->instr]++;
				predecessors[it->instr].insert(i);
				pendingInstrs.push_back(it->instr);
			}
		}
	}

	/* Now figure out what inputs are available where. */
	std::map<instr_t, std::set<input_expression> > availabilityMap;
	for (auto it = pendingPredecessors.begin(); it != pendingPredecessors.end(); it++) {
		if (it->second == 0) {
			pendingInstrs.push_back(it->first);
		}
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
	if (debug_eem || debug_eem_schedule) {
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
	if (debug_eem || debug_eem_schedule) {
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

	std::set<instr_t> deadStates;
	while (!pendingInstrs.empty()) {
		auto i = pendingInstrs.back();
		pendingInstrs.pop_back();
		assert(pendingPredecessors.count(i));
		assert(pendingPredecessors[i] == 0);

		if (debug_eem || debug_eem_schedule) {
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
			auto simpl = subst_eq(scope, split1.second);
			if (simpl->isLeaf()) {
				if (simpl->leaf() == false) {
					if (debug_eem_dead) {
						printf("Side condition for %s is unsatisfiable!\n",
						       i->rip.name());
					}
					deadStates.insert(i);
					continue;
				}
			} else {
				evalAt[i->rip].after_regs = simpl;
			}
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

				if (!leftover) {
					/* There's no way for the RX
					   condition to be satisfied.
					   That means this state can
					   never be reached.  Arrange
					   for it to be killed off
					   later. */
					deadStates.insert(i);
					if (debug_eem_dead) {
						printf("rx_checked is unsatisfiable, killing %s!\n",
						       i->rip.name());
					}
					continue;
				}

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
					hb->sideCondition = subst_eq(scope, split.second);
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
				if (debug_eem_schedule) {
					printf("Unblock %s via HB edge (%d left)\n",
					       hb->after->rip.name(),
					       pendingPredecessors[hb->after]);
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
			auto simpl = subst_eq(scope, split3.second);
			if (!simpl->isLeaf()) {
				evalAt[i->rip].after_control_flow = simpl;
			} else if (simpl->leaf() == false) {
				deadStates.insert(i);
			}
		}

		/* Anything left after that is really leftover. */
		leftoverCondition[i] = leftover;

		for (auto it = i->successors.begin(); it != i->successors.end(); it++) {
			if (it->instr) {
				assert(pendingPredecessors[it->instr] > 0);
				if (--pendingPredecessors[it->instr] == 0) {
					pendingInstrs.push_back(it->instr);
				}
				if (debug_eem_schedule) {
					printf("Unblock direct successor %s (%d left)\n",
					       it->instr->rip.name(),
					       pendingPredecessors[it->instr]);
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
							if (debug_eem_schedule) {
								printf("Unblock %s via hb edge (%d left)\n",
								       hb->before->rip.name(),
								       pendingPredecessors[hb->before]);
								hb->prettyPrint(stdout);
							}
						}
					}
				}
			}
		}
	}

	if (deadStates.empty()) {
		for (auto it = pendingPredecessors.begin(); it != pendingPredecessors.end(); it++) {
			assert(it->second == 0);
		}
	}

	/* Now deal with the dead states.  These are states which we
	   can definitely never reach due to the side conditions being
	   provably false, so go and kill them all off. */
	while (1) {
		std::set<instr_t> newDead;
		newDead.clear();
		/* Remove control-flow dead states */
		for (auto it = deadStates.begin(); it != deadStates.end(); it++) {
			instr_t dead = *it;
			if (debug_eem_dead) {
				printf("Trying to remove dead instruction %s...\n", dead->rip.name());
			}
			const std::set<instr_t> &pred(predecessors[dead]);
			for (auto it2 = pred.begin(); it2 != pred.end(); it2++) {
				instr_t pred = *it2;
				bool found = false;
				/* Remove all edges to dead successors */
				for (auto it3 = pred->successors.begin();
				     it3 != pred->successors.end();
					) {
					if (it3->instr == dead) {
						if (debug_eem_dead) {
							printf("Kill %s->%s edge\n",
							       pred->rip.name(),
							       dead->rip.name());
						}
						it3 = pred->successors.erase(it3);
						found = true;
					} else {
						it3++;
					}
				}
				/* If that killed off all the
				   successors of this state then this
				   state also becomes dead. */
				if (found && pred->successors.empty()) {
					if (debug_eem_dead) {
						printf("Killed off all successors of %s.\n", pred->rip.name());
					}
					newDead.insert(pred);
				}
			}

			/* Remove hb-dead states.  If the source or
			   destination of an edge are dead then the other end
			   is dead as well. */
			const std::set<happensBeforeEdge *> &hbs(hbMap[dead->rip]);
			for (auto it2 = hbs.begin(); it2 != hbs.end(); it2++) {
				auto hb = *it2;
				if (debug_eem_dead) {
					printf("Kill hb edge:\n");
					hb->prettyPrint(stdout);
				}
				if (hb->before == dead) {
					/* This dead instruction is
					   sending a message.  The
					   receive must receive some
					   message, so if we're the
					   only sender then the
					   receiver is dead as
					   well. */
					std::set<happensBeforeEdge *> &other(hbMap[hb->after->rip]);
					other.erase(hb);
					bool keep = false;
					for (auto it = other.begin(); !keep && it != other.end(); it++) {
						if ( (*it)->after == hb->after ) {
							keep = true;
						}
					}
					if (!keep) {
						if (debug_eem_dead) {
							printf("HB kills %s\n", hb->after->rip.name());
						}
						newDead.insert(hb->after);
					}
				} else {
					/* Conversely: dead is
					   receiving a message, so see
					   if the transmitted is also
					   dead. */
					std::set<happensBeforeEdge *> &other(hbMap[hb->before->rip]);
					other.erase(hb);
					bool keep = false;
					for (auto it = other.begin(); !keep && it != other.end(); it++) {
						if ( (*it)->before == hb->before ) {
							keep = true;
						}
					}
					if (!keep) {
						if (debug_eem_dead) {
							printf("HB kills %s\n", hb->before->rip.name());
						}
						newDead.insert(hb->before);
					}
				}
			}

			/* This thing is dead, so needs to be culled
			 * from the HB map. */
			hbMap.erase(dead->rip);
		}
		if (deadStates == newDead) {
			break;
		}
		deadStates = newDead;
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
