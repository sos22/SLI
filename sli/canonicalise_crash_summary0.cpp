#include "sli.h"
#include "offline_analysis.hpp"
#include "inferred_information.hpp"
#include "dummy_oracle.hpp"
#include "allowable_optimisations.hpp"
#include "state_machine.hpp"
#include "sat_checker.hpp"
#include "visitor.hpp"

#include "cfgnode_tmpl.cpp"

#ifndef NDEBUG
static bool debug_root_reduce = false;
#else
#define debug_root_reduce false
#endif

template <typename t>
class _saneIterator {
	t cursor;
	t end;
public:
	typedef typename t::value_type value_type;
	_saneIterator(const t &begin, const t &_end)
		: cursor(begin), end(_end)
	{}
	bool finished() const {
		return cursor == end;
	}
	void operator++(int) {
		cursor++;
	}
	typename t::value_type &operator *() {
		return *cursor;
	}
};
template <typename t> _saneIterator<t>
saneIterator(const t &begin, const t &end)
{
	return _saneIterator<t>(begin, end);
}
template <typename k, typename v> _saneIterator<typename std::map<k, v>::iterator>
saneIterator(std::map<k, v> &m)
{
	return saneIterator(m.begin(), m.end());
}
template <typename k> _saneIterator<typename std::vector<k>::iterator>
saneIterator(std::vector<k> &m)
{
	return saneIterator(m.begin(), m.end());
}

template <typename underlying_it1, typename underlying_it2>
class concatIterator {
	enum { ph_1, ph_2, ph_finished } phase;
	underlying_it1 cursor1;
	underlying_it2 cursor2;
public:
	concatIterator(const underlying_it1 &_begin1,
		       const underlying_it2 &_begin2)
		: phase(ph_1),
		  cursor1(_begin1),
		  cursor2(_begin2)
	{
		if (cursor1.finished()) {
			phase = ph_2;
			if (cursor2.finished())
				phase = ph_finished;
		}
	}
	bool finished() const {
		return phase == ph_finished;
	}
	void operator++(int) {
		switch (phase) {
		case ph_1:
			cursor1++;
			if (cursor1.finished()) {
				phase = ph_2;
				if (cursor2.finished())
					phase = ph_finished;
			}
			break;
		case ph_2:
			cursor2++;
			if (cursor2.finished())
				phase = ph_finished;
			break;
		case ph_finished:
			abort();
		}
	}
	const typename underlying_it1::value_type &operator*() {
		switch (phase) {
		case ph_1:
			return *cursor1;
		case ph_2:
			return *cursor2;
		case ph_finished:
			abort();
		}
		abort();
	}
	const typename underlying_it1::value_type *operator->() {
		switch (phase) {
		case ph_1:
			return &*cursor1;
		case ph_2:
			return &*cursor2;
		case ph_finished:
			abort();
		}
		abort();
	}
};
template <typename a, typename b> concatIterator<a, b>
concatIterators(const a &a1, const b &b1)
{
	return concatIterator<a, b>(a1, b1);
}

template <typename t>
class ptrIterator {
	int nr_ptrs;
	int cursor;
	t **content;
public:
	ptrIterator(t *a, ...)
		: cursor(0), content(NULL)
	{
		if (a == NULL) {
			nr_ptrs = 0;
			return;
		}
		nr_ptrs = 1;
		va_list args;
		va_start(args, a);
		while (1) {
			t *b = va_arg(args, t *);
			if (!b)
				break;
			nr_ptrs++;
		}
		va_end(args);

		content = (t **)malloc(sizeof(t *) * nr_ptrs);
		content[0] = a;
		va_start(args, a);
		int i = 1;
		while (1) {
			t *b = va_arg(args, t*);
			if (!b)
				break;
			content[i] = b;
			i++;
		}
		assert(i == nr_ptrs);
	}
	~ptrIterator()
	{
		free(content);
	}
	ptrIterator(const ptrIterator &other)
		: nr_ptrs(other.nr_ptrs),
		  cursor(other.cursor)
	{
		content = (t **)malloc(sizeof(t *) * nr_ptrs);
		memcpy(content, other.content, sizeof(t *) * nr_ptrs);
	}
	void operator=(const ptrIterator &other)
	{
		nr_ptrs = other.nr_ptrs;
		cursor = other.cursor;
		if (content)
			free(content);
		content = (t **)malloc(sizeof(t *) * nr_ptrs);
		memcpy(content, other.content, sizeof(t *) * nr_ptrs);
	}
	bool finished() const {
		return cursor == nr_ptrs;
	}
	void operator++(int) {
		assert(!finished());
		cursor++;
	}
	t *&operator *() {
		return content[cursor];
	}
};

template <typename t>
struct intersectSets {
	const std::set<t> &a;
	const std::set<t> &b;
	intersectSets(const std::set<t> &_a, const std::set<t> &_b)
		: a(_a), b(_b)
	{}
	struct iterator {
		typename std::set<t>::const_iterator a_iterator;
		typename std::set<t>::const_iterator a_iterator_end;
		typename std::set<t>::const_iterator b_iterator;
		typename std::set<t>::const_iterator b_iterator_end;
		iterator(const typename std::set<t>::const_iterator &_a_iterator,
			 const typename std::set<t>::const_iterator &_a_iterator_end,
			 const typename std::set<t>::const_iterator &_b_iterator,
			 const typename std::set<t>::const_iterator &_b_iterator_end)
			: a_iterator(_a_iterator),
			  a_iterator_end(_a_iterator_end),
			  b_iterator(_b_iterator),
			  b_iterator_end(_b_iterator_end)
		{
			advance();
		}
		bool finished() const {
			return a_iterator == a_iterator_end || b_iterator == b_iterator_end;
		}
		const t &operator *() {
			assert(*a_iterator == *b_iterator);
			return *a_iterator;
		}
		void operator++(int) {
			assert(!finished());
			a_iterator++;
			b_iterator++;
			advance();
		}
		void advance(void) {
			while (!finished()) {
				if (*a_iterator < *b_iterator)
					a_iterator++;
				else if (*b_iterator < *a_iterator)
					b_iterator++;
				else
					break;
			}
		}
	};
	iterator begin() const {
		return iterator(a.begin(), a.end(),
				b.begin(), b.end());
	}
};
template <typename t> intersectSets<t>
operator &(const std::set<t> &_a, const std::set<t> &_b)
{
	return intersectSets<t>(_a, _b);
}

template <typename t, typename s> void
operator |=(std::set<t> &dest, const s &other)
{
	for (auto it = other.begin();
	     !it.finished();
	     it++)
		dest.insert(*it);
}

static CrashSummary *
rewriteEntryPointExpressions(CrashSummary *cs, const std::map<std::pair<unsigned, CfgLabel>, std::pair<unsigned, CfgLabel> > &rules)
{
	struct : public StateMachineTransformer {
		const std::map<std::pair<unsigned, CfgLabel>, std::pair<unsigned, CfgLabel> > *rules;
		IRExpr *transformIex(IRExprEntryPoint *iep) {
			std::pair<unsigned, CfgLabel> key(iep->thread, iep->label);
			auto it = rules->find(key);
			if (it != rules->end())
				return IRExprEntryPoint::mk(it->second.first, it->second.second);
			return iep;
		}
		bool rewriteNewStates() const { return false; }
	} doit;
	doit.rules = &rules;
	return transformCrashSummary(cs, doit);
}

static void
findMinimalRoots(StateMachine *sm,
		 const std::set<const CFGNode *> &needed,
		 std::map<std::pair<unsigned, CfgLabel>, std::pair<unsigned, CfgLabel> > &rootRewrites)
{
	for (auto it = sm->cfg_roots.begin(); it != sm->cfg_roots.end(); it++) {
		CFGNode *n = const_cast<CFGNode *>(it->first.node);
		while (!needed.count(n)) {
			int nr_successors = 0;
			for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++) {
				if (it2->instr)
					nr_successors++;
			}
			if (nr_successors != 1)
				break;
			for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++) {
				if (it2->instr) {
					n = it2->instr;
					break;
				}
			}
		}
		if (debug_root_reduce) {
			printf("Root rewrite: %d:%s -> %d:%s\n",
			       it->first.thread, it->first.node->label.name(),
			       it->first.thread, n->label.name());
		}
		rootRewrites.insert(
			std::pair<std::pair<unsigned, CfgLabel>,
			          std::pair<unsigned, CfgLabel> >(
					  std::pair<unsigned, CfgLabel>(it->first.thread, it->first.node->label),
					  std::pair<unsigned, CfgLabel>(it->first.thread, n->label)));
		it->first.node = n;
	}
}

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

static CrashSummary *
optimise_crash_summary(VexPtr<CrashSummary, &ir_heap> cs,
		       const VexPtr<OracleInterface> &oracle,
		       GarbageCollectionToken token)
{
	VexPtr<MaiMap, &ir_heap> mai(cs->mai);
	cs->loadMachine = optimiseStateMachine(
		cs->scopes,
		mai,
		cs->loadMachine,
		AllowableOptimisations::defaultOptimisations.
			enableassumePrivateStack().
			enableignoreSideEffects().
			enablenoLocalSurvival(),
		oracle,
		true,
		token);
	cs->storeMachine = optimiseStateMachine(
		cs->scopes,
		mai,
		cs->storeMachine,
		AllowableOptimisations::defaultOptimisations.
			enableassumePrivateStack().
			enableassumeNoInterferingStores(),
		oracle,
		true,
		token);
	cs->crashCondition = bbdd::assume(&cs->scopes->bools,
					  cs->crashCondition,
					  cs->inferredAssumption);
	cs->crashCondition = subst_eq(&cs->scopes->bools,
				      cs->crashCondition);
	cs->inferredAssumption = subst_eq(&cs->scopes->bools,
					  cs->inferredAssumption);
	cs->mai = mai;

	/* The only reason we maintain the CFG is so that we can
	   resolve references into it from the machines and
	   verification condition.  There's not much point in hanging
	   on to nodes which are no longer referenced from anywhere.
	   The definition of ``referenced'' is slightly subtle:

	   -- Obviously, and explicit references from memory accesses
              count.
	   -- Registers implicitly reference all of the roots of the
              CFG.
	   -- Any node on a path between two nodes which are referenced
	      in one of the first two senses is also considered to
	      be referenced.
	*/
	std::set<const CFGNode *> needed;

	HashedSet<HashedPtr<CFGNode> > allNodes;
	for (auto it = concatIterators(saneIterator(cs->loadMachine->cfg_roots),
				       saneIterator(cs->storeMachine->cfg_roots));
	     !it.finished();
	     it++) {
		enumerateCFG(const_cast<CFGNode *>(it->first.node), allNodes);
	}

	/* Find references of the first sense */
	{
		std::set<MemoryAccessIdentifier> mais;
		cs->loadMachine->root->enumerateMentionedMemoryAccesses(mais);
		cs->storeMachine->root->enumerateMentionedMemoryAccesses(mais);
		for (auto it = mais.begin(); it != mais.end(); it++) {
			for (auto it2 = cs->mai->begin(*it); !it2.finished(); it2.advance()) {
				if (debug_root_reduce) {
					printf("Root %s is needed because of %s\n",
					       it2.node()->label.name(),
					       it->name());
				}
				needed.insert(it2.node());
			}
		}
	}

	/* Find references of the second sense */
	{
		struct {
			static visit_result Get(void *, const IRExprGet *ieg) {
				if (ieg->reg.isReg())
					return visit_abort;
				else
					return visit_continue;
			}
		} foo;
		static bdd_visitor<void> visitor;
		visitor.irexpr.Get = foo.Get;
		if (visit_crash_summary((void *)NULL, &visitor, cs) == visit_abort) {
			for (auto it = concatIterators(saneIterator(cs->loadMachine->cfg_roots),
						       saneIterator(cs->storeMachine->cfg_roots));
			     !it.finished();
			     it++) {
				if (debug_root_reduce) {
					printf("%s is needed because of register reference\n",
					       it->first.node->label.name());
				}
				needed.insert(it->first.node);
			}
		}
	}

	/* Find references in the third sense.  This is a three step
	   process:

	   1) find nodes which can reach a directly referenced node.
	   2) find nodes which are reachable from a directly referenced node.
	   3) Intersect those sets.
	*/
	{
		/* Find nodes which can reach a referenced node. */
		std::set<const CFGNode *> reachesReferencedNode(needed);
		bool progress = true;
		while (progress) {
			progress = false;
			for (auto it = allNodes.begin(); !it.finished(); it.advance()) {
				const CFGNode *n = *it;
				if (reachesReferencedNode.count(n))
					continue;
				for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++) {
					if (it2->instr && reachesReferencedNode.count(it2->instr)) {
						reachesReferencedNode.insert(n);
						progress = true;
						break;
					}
				}
			}
		}
		/* And find nodes which are reachable from a referenced
		 * node. */
		std::set<const CFGNode *> reachableFromReferencedNode;
		std::queue<const CFGNode *> pending;
		for (auto it = needed.begin(); it != needed.end(); it++)
			pending.push(*it);
		while (!pending.empty()) {
			const CFGNode *n = pending.front();
			pending.pop();
			if (!reachableFromReferencedNode.insert(n).second)
				continue;
			for (auto it = n->successors.begin(); it != n->successors.end(); it++)
				if (it->instr)
					pending.push(it->instr);
		}

		/* We need anything in the intersection of those two
		 * sets. */
		needed |= reachableFromReferencedNode & reachesReferencedNode;
	}


	/* Now trim the CFG down a bit.  First step: any transition
	 * from a needed node to a not-needed one can be killed. */
	for (auto it = allNodes.begin(); !it.finished(); it.advance()) {
		CFGNode *n = *it;
		if (!needed.count(n))
			continue;
		for (auto it2 = n->successors.begin(); it2 != n->successors.end(); it2++) {
			if (it2->instr && !needed.count(it2->instr))
				it2->instr = NULL;
		}
	}

	/* Now try to rationalise the roots a little bit.  Ideally,
	   we'd like to trim the roots back a bit so as to remove
	   anything which isn't necessary.  Complication is that the
	   roots of the new graph have to correspond with the roots of
	   the old one, in a way which isn't entirely well defined.
	   Be conservative for now: if a root isn't needed and it has
	   a single successor, replace it with that successor. */
	std::map<std::pair<unsigned, CfgLabel>, std::pair<unsigned, CfgLabel> > rootRewrites;
	findMinimalRoots(cs->loadMachine, needed, rootRewrites);
	findMinimalRoots(cs->storeMachine, needed, rootRewrites);

	cs = rewriteEntryPointExpressions(cs, rootRewrites);

	/* Remove any roots which can't reach needed instructions. */
	for (auto it = cs->loadMachine->cfg_roots.begin();
	     it != cs->loadMachine->cfg_roots.end();
		) {
		bool reachesNeededInstr = false;
		std::queue<const CFGNode *> pending;
		std::set<const CFGNode *> visited;
		pending.push(it->first.node);
		while (!reachesNeededInstr && !pending.empty()) {
			const CFGNode *n = pending.front();
			pending.pop();
			if (!visited.insert(n).second)
				continue;
			if (needed.count(n))
				reachesNeededInstr = true;
			for (auto it = n->successors.begin(); it != n->successors.end(); it++)
				if (it->instr)
					pending.push(it->instr);
		}
		if (reachesNeededInstr)
			it++;
		else
			it = cs->loadMachine->cfg_roots.erase(it);
	}
	for (auto it = cs->storeMachine->cfg_roots.begin();
	     it != cs->storeMachine->cfg_roots.end();
		) {
		bool reachesNeededInstr = false;
		std::queue<const CFGNode *> pending;
		std::set<const CFGNode *> visited;
		pending.push(it->first.node);
		while (!reachesNeededInstr && !pending.empty()) {
			const CFGNode *n = pending.front();
			pending.pop();
			if (!visited.insert(n).second)
				continue;
			if (needed.count(n))
				reachesNeededInstr = true;
			for (auto it = n->successors.begin(); it != n->successors.end(); it++)
				if (it->instr)
					pending.push(it->instr);
		}
		if (reachesNeededInstr)
			it++;
		else
			cs->storeMachine->cfg_roots.erase(it++);
	}

	rootRewrites.clear();

	/* Try a bit harder to rationalise the roots.  This version
	 * only works for single-rooted CFGs.  The idea is to replace
	 * the root with the least dominator of all of the needed
	 * instructions. */
	for (auto it0 = ptrIterator<StateMachine>(cs->loadMachine, cs->storeMachine, NULL);
	     !it0.finished();
	     it0++) {
		StateMachine *s = *it0;
		if (s->cfg_roots.size() != 1)
			continue;

		/* We want to find a dominator of all of the needed
		   instructions i.e. some instruction I such that
		   every path from the root to a needed instruction
		   passes through I.  We want to find the least such
		   dominator in the sense that if some other
		   instruction I' is also a dominator then every path
		   from I' to a needed instruction must pass through
		   I. */
		unsigned thread = s->cfg_roots.begin()->first.thread;
		CFGNode *root = const_cast<CFGNode *>(s->cfg_roots.begin()->first.node);
		HashedSet<HashedPtr<CFGNode> > nodes;
		enumerateCFG(root, nodes);
		std::set<CFGNode *> nodesSet;
		for (auto it = nodes.begin(); !it.finished(); it.advance())
			nodesSet.insert(it->get());

		/* First, calculate the dominators map for all
		 * instructions. */
		std::map<CFGNode *, std::set<CFGNode *> > dominators;
		for (auto it = nodes.begin(); !it.finished(); it.advance())
			if (*it == root)
				dominators[*it].insert(*it);
			else
				dominators[*it] = nodesSet;
		std::queue<CFGNode *> pending;
		for (auto it = nodes.begin(); !it.finished(); it.advance())
			pending.push(*it);
		while (!pending.empty()) {
			CFGNode *p = pending.front();
			pending.pop();
			const std::set<CFGNode *> &thisNode(dominators[p]);
			for (auto it = p->successors.begin(); it != p->successors.end(); it++) {
				if (it->instr) {
					std::set<CFGNode *> &otherNode(dominators[it->instr]);
					bool done_something = false;
					for (auto it2 = otherNode.begin();
					     it2 != otherNode.end();
						) {
						if (*it2 != it->instr && !thisNode.count(*it2)) {
							otherNode.erase(it2++);
							done_something = true;
						} else {
							it2++;
						}
					}
					if (done_something)
						pending.push(it->instr);
				}
			}
		}

		/* Initial candidates: everything which dominators
		 * every needed instruction. */
		auto it = needed.begin();
		while (it != needed.end() && !nodes.contains(const_cast<CFGNode *>(*it)))
			it++;
		if (it == needed.end()) {
			/* Weird... the whole cfg is redundant.  Kill
			 * it. */
			s->cfg_roots.clear();
			continue;
		}
		std::set<CFGNode *> candidates(dominators[const_cast<CFGNode *>(*it)]);
		it++;
		for (; it != needed.end(); it++) {
			if (!nodes.contains(const_cast<CFGNode *>(*it)))
				continue;
			std::set<CFGNode *> &dom(dominators[const_cast<CFGNode *>(*it)]);
			for (auto it2 = candidates.begin(); it2 != candidates.end(); ) 
				if (dom.count(*it2))
					it2++;
				else
					candidates.erase(it2++);
		}

		if (candidates.empty())
			continue;

		/* The final result is a candidate which is not
		   dominated by anything else in the candidate set. */
		CFGNode *result;
		auto it2 = candidates.begin();
		result = *it2;
		it2++;
		for ( ; it2 != candidates.end(); it2++) {
			if (dominators[*it2].count(result))
				result = *it2;
		}
		rootRewrites.insert(
			std::pair<std::pair<unsigned, CfgLabel>,
			          std::pair<unsigned, CfgLabel> >(
					  std::pair<unsigned, CfgLabel>(thread, root->label),
					  std::pair<unsigned, CfgLabel>(thread, result->label)));
		std::map<StateMachine::entry_point, StateMachine::entry_point_ctxt> newRoots;
		s->cfg_roots.begin()->first.node = result;
	}

	cs = rewriteEntryPointExpressions(cs, rootRewrites);

	/* Now walk the MAI map and remove anything which has become
	 * redundant. */
	HashedSet<HashedPtr<CFGNode> > remainingNodes;
	for (auto it = concatIterators(saneIterator(cs->loadMachine->cfg_roots),
				       saneIterator(cs->storeMachine->cfg_roots));
	     !it.finished();
	     it++) {
		enumerateCFG(const_cast<CFGNode *>(it->first.node), remainingNodes);
	}
	for (auto it = mai->begin(); !it.finished(); ) {
		for (auto it2 = it.begin(); !it2.finished(); ) {
			if (remainingNodes.contains(const_cast<CFGNode *>(it2.node())))
				it2.advance();
			else
				it2.erase();
		}
		if (it.empty())
			it.erase();
		else
			it.advance();
	}
	return cs;
}

int
main(int argc, char *argv[])
{
	if (argc != 3)
		errx(1, "need two arguments: input and output summaries");

	init_sli();

	CrashSummary *summary;
	char *first_line;

	SMScopes scopes;
	summary = readBugReport(&scopes, argv[1], &first_line);

	summary = optimise_crash_summary(summary, new DummyOracle(summary), ALLOW_GC);

	FILE *f = fopen(argv[2], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);

	return 0;
}
