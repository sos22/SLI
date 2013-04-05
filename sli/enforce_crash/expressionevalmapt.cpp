/* Gubbins for figuring out where to evaluate the various fragments of
   side-condition.  The bulk of this is a scheme for reordering the
   variables in a BDD (so that evaluatable bits are near the root) and
   something to use that to factor the BDDs into evaluatable and
   unevaluatable components. */
#include "sli.h"
#include "enforce_crash.hpp"
#include "timers.hpp"
#include "reorder_bdd.hpp"

extern FILE *bubble_plot_log;

#ifndef NDEBUG
static bool debug_eem = false;
static bool debug_eem_predecessors = false;
static bool debug_eem_availability = false;
static bool debug_eem_dead = false;
static bool debug_eem_schedule = false;
static bool debug_ubbdd = false;
#else
#define debug_eem false
#define debug_eem_predecessors false
#define debug_eem_availability false
#define debug_eem_dead false
#define debug_eem_schedule false
#define debug_ubbdd false
#endif

/* First, a couple of random bits which don't really belong here but
   which don't really belong anywhere else either. */
happensBeforeMapT::happensBeforeMapT(const SummaryId &summary,
				     const MaiMap &mai,
				     const std::set<const IRExprHappensBefore *> &trueHb,
				     const std::set<const IRExprHappensBefore *> &falseHb,
				     CrashCfg &cfg,
				     ThreadAbstracter &abs,
				     int &next_hb_id)
{
	fprintf(bubble_plot_log, "%f: start happensBeforeMapT() constructor\n", now());
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
						next_hb_id++);
				(*this)[hbe->before->rip].insert(hbe);
				(*this)[hbe->after->rip].insert(hbe);
			}
		}
	}
	fprintf(bubble_plot_log, "%f: stop happensBeforeMapT() constructor\n", now());
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
		return scope->node(
			in->internal().condition,
			in->internal().rank,
			setEntryPoint(scope, in->internal().trueBranch, thread, label),
			setEntryPoint(scope, in->internal().falseBranch, thread, label));
	} else {
		IRExprEntryPoint *c = (IRExprEntryPoint *)in->internal().condition;
		if (c->thread != thread) {
			return scope->node(
				in->internal().condition,
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
class evaluatable : public reorder_evaluatable {
	const std::set<input_expression> &avail;
public:
	evaluatable(const std::set<input_expression> &_avail)
		: avail(_avail)
	{}
	void prettyPrint(FILE *f) const {
		fprintf(f, "avail: ");
		print_expr_set(avail, f);
	}
	bool operator()(IRExpr *const &arg) const;
};
bool
evaluatable::operator()(IRExpr *const &what) const
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

static std::pair<bbdd *, bbdd *>
splitExpressionOnAvailability(bbdd::scope *scope, bbdd *what, const std::set<input_expression> &avail)
{
	if (debug_ubbdd) {
		printf("Split expression, avail ");
		print_expr_set(avail, stdout);
		printf("\n");
		what->prettyPrint(stdout);
	}

	evaluatable evalable(avail);
	const reorder_bbdd *u_what = reorder_bbdd::from_bbdd(what, evalable);
	if (debug_ubbdd) {
		printf("Converted to UBBDD:\n");
		pp_reorder(u_what);
	}
	sanity_check_reorder(u_what);
	auto pair = splitExpressionOnAvailability(u_what);
	auto u_unavail = pair.first;
	auto u_avail = pair.second;

	auto b_avail = u_avail->to_bbdd(scope);
	auto unavail = u_unavail->to_bbdd(scope);
	if (debug_ubbdd) {
		printf("Convert back to BBDD; avail =\n");
		b_avail->prettyPrint(stdout);
		printf("Unavail =\n");
		unavail->prettyPrint(stdout);
	}
	return std::pair<bbdd *, bbdd *>(unavail, b_avail);
}

static void
buildPredecessorMap(const CrashCfg &cfg,
		    const crashEnforcementRoots &roots,
		    std::map<instr_t, std::set<instr_t> > &predecessors,
		    std::set<instr_t> &rootInstrs)
{
	assert(predecessors.empty());
	assert(rootInstrs.empty());

	std::vector<instr_t> pendingInstrs;
	for (auto it = roots.begin(); !it.finished(); it.advance()) {
		auto i = cfg.findInstr(it.threadCfgLabel());
		assert(i);
		pendingInstrs.push_back(i);
		rootInstrs.insert(i);
		predecessors[i].clear();
	}
	std::set<instr_t> seen;
	while (!pendingInstrs.empty()) {
		auto i = pendingInstrs.back();
		pendingInstrs.pop_back();
		if (!seen.insert(i).second) {
			continue;
		}
		for (auto it = i->successors.begin(); it != i->successors.end(); it++) {
			if (it->instr) {
				predecessors[it->instr].insert(i);
				pendingInstrs.push_back(it->instr);
			}
		}
	}

	if (debug_eem_predecessors) {
		printf("Predecessor map:\n");
		for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
			printf("\t%s -> [", it->first->rip.name());
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				if (it2 != it->second.begin()) {
					printf(", ");
				}
				printf("%s", (*it2)->rip.name());
			}
			printf("]\n");
		}
	}
}

static void
buildInputAvailabilityMap(std::map<instr_t, std::set<instr_t> > &predecessors,
			  expressionStashMapT &stashMap,
			  happensBeforeMapT &hbMap,
			  std::map<instr_t, std::set<input_expression> > &availabilityMap)
{
	/* First pass just finds things which are available in the
	 * local thread. */
	std::map<instr_t, unsigned> nrPendingPredecessors;
	std::vector<instr_t> pendingInstrs;
	for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
		nrPendingPredecessors[it->first] = it->second.size();
		if (it->second.size() == 0) {
			pendingInstrs.push_back(it->first);
		}
	}
	while (!pendingInstrs.empty()) {
		auto i = pendingInstrs.back();
		pendingInstrs.pop_back();
		assert(nrPendingPredecessors.count(i));
		assert(nrPendingPredecessors[i] == 0);
#ifndef NDEBUG
		nrPendingPredecessors.erase(i);
#endif
		assert(!availabilityMap.count(i));
		std::set<input_expression> &avail(availabilityMap[i]);
		assert(avail.empty());

		if (debug_eem_availability) {
			printf("Calc availability at %s\n", i->rip.name());
		}
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

		if (debug_eem_availability) {
			printf("\tLocal entry avail: ");
			print_expr_set(avail, stdout);
			printf("\n");
		}

		/* Now use that to calculate exit availability. */
		auto stashit = stashMap.find(i->rip);
		if (stashit != stashMap.end()) {
			avail |= stashit->second;
		}

		if (debug_eem_availability) {
			printf("\tLocal exit avail: ");
			print_expr_set(avail, stdout);
			printf("\n");
		}

		availabilityMap[i] = avail;

		for (auto it = i->successors.begin(); it != i->successors.end(); it++) {
			if (it->instr) {
				assert(nrPendingPredecessors.count(it->instr));
				assert(nrPendingPredecessors[it->instr] > 0);
				if (--nrPendingPredecessors[it->instr] == 0) {
					pendingInstrs.push_back(it->instr);
				}
			}
		}
	}
	assert(nrPendingPredecessors.empty());

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
}

class node_schedule {
	std::map<instr_t, unsigned> pendingPredecessors;
	std::vector<instr_t> pendingInstrs;
public:
	void build(const std::map<instr_t, std::set<instr_t> > &predecessors,
		   const std::set<happensBeforeEdge *> &allEdges);
	void unblock(instr_t what);
	bool finished() const;
	instr_t next();
	void finishEdgeBefore(happensBeforeEdge *e);
	void finishEdgeAfter(happensBeforeEdge *e);
	void finishControlPredecessor(Instruction<ThreadCfgLabel>::successor_t&);
	void check_cycles() const;
};

void
node_schedule::build(const std::map<instr_t, std::set<instr_t> > &predecessors,
		     const std::set<happensBeforeEdge *> &allEdges)
{
	for (auto it = predecessors.begin(); it != predecessors.end(); it++) {
		pendingPredecessors[it->first] = it->second.size();
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
		auto it2 = predecessors.find(hb->after);
		assert(it2 != predecessors.end());
		pendingPredecessors[hb->before] += it2->second.size();
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
}

bool
node_schedule::finished() const
{
	return pendingInstrs.empty();
}

instr_t
node_schedule::next()
{
	instr_t res;
	res = pendingInstrs.back();
	assert(pendingPredecessors.count(res));
	assert(pendingPredecessors[res] == 0);
	pendingInstrs.pop_back();
	pendingPredecessors.erase(res);

	if (debug_eem || debug_eem_schedule) {
		printf("Consider %s\n", res->rip.name());
	}

	return res;
}

void
node_schedule::unblock(instr_t ins)
{
	assert(pendingPredecessors.count(ins));
	assert(pendingPredecessors[ins] > 0);
	if (--pendingPredecessors[ins] == 0) {
		pendingInstrs.push_back(ins);
	}
}

void
node_schedule::finishEdgeBefore(happensBeforeEdge *hb)
{
	unblock(hb->after);
	if (debug_eem_schedule) {
		printf("Unblock %s via HB edge (%d left)\n",
		       hb->after->rip.name(),
		       pendingPredecessors[hb->after]);
	}
}

void
node_schedule::finishEdgeAfter(happensBeforeEdge *hb)
{
	unblock(hb->before);
	if (debug_eem_schedule) {
		printf("Unblock %s via HB edge (%d left) (after)\n",
		       hb->before->rip.name(),
		       pendingPredecessors[hb->before]);
		hb->prettyPrint(stdout);
	}
}

void
node_schedule::finishControlPredecessor(Instruction<ThreadCfgLabel>::successor_t &i)
{
	unblock(i.instr);
	if (debug_eem_schedule) {
		printf("Unblock direct successor %s (%d left)\n",
		       i.instr->rip.name(),
		       pendingPredecessors[i.instr]);
	}
}

void
node_schedule::check_cycles() const
{
	bool failed = false;
	for (auto it = pendingPredecessors.begin(); it != pendingPredecessors.end(); it++) {
		assert(it->second != 0);
		printf("Failed; %s is still live (%d)\n",
		       it->first->rip.name(), it->second);
		failed = true;
	}
	if (failed) {
		fprintf(stderr, "WARNING: HB graph becomes cyclic when messages are synchronous!\n");
	}
}

/* Figure out what bits of the condition we can evaluate at the start
 * of the instruction. */
struct instrEntryPhaseRes {
	bool dead;
	bbdd *remainder;
	bbdd *evalHere;
	bbdd *newAssumption;
};
static instrEntryPhaseRes
instrEntryPhase(bbdd::scope *scope,
		bbdd *const entryCondition,
		bbdd *const entryAssumption,
		const std::set<input_expression> &availExprs)
{
	auto split1 = splitExpressionOnAvailability(
		scope,
		entryCondition,
		availExprs);
	if (debug_eem) {
		printf("Left over after register and entry point:\n");
		split1.first->prettyPrint(stdout);
		printf("Eval here after register and entry point:\n");
		split1.second->prettyPrint(stdout);
	}
	instrEntryPhaseRes res;
	res.newAssumption = entryAssumption;
	if (split1.second->isLeaf()) {
		if (split1.second->leaf() == false) {
			res.dead = true;
		} else {
			res.dead = false;
			res.remainder = entryCondition;
			res.evalHere = split1.second;
		}
		return res;
	}

	auto simpl = bbdd::assume(scope, split1.second, entryAssumption);
	if (!simpl) {
		instrEntryPhaseRes res;
		res.dead = true;
		return res;
	}

	simpl = subst_eq(scope, simpl);
	if (simpl != split1.second && debug_eem) {
		printf("Resimplify:\n");
		simpl->prettyPrint(stdout);
	}
	if (simpl->isLeaf()) {
		if (simpl->leaf() == false) {
			res.dead = true;
			return res;
		}
	} else {
		res.newAssumption = bbdd::And(scope, entryAssumption, simpl);
		res.remainder = split1.first;
	}
	res.evalHere = simpl;
	res.dead = false;
	return res;
}

/* Update our state to reflect having received messages. */
struct instrRxPhaseRes {
	std::set<input_expression> rxed_expressions;
	bbdd *checkedHere;
};
static instrRxPhaseRes
instrRxPhase(bbdd::scope *scope,
	     instr_t i,
	     const std::set<happensBeforeEdge *> &hbEdges,
	     const std::map<instr_t, std::set<instr_t> > &predecessors,
	     const std::map<instr_t, std::set<input_expression> > &availabilityMap,
	     const expressionStashMapT &stashMap,
	     const std::set<input_expression> &availExprs)
{
	/* What about once we've done the RX operations? */
	/* Figure out what's available.  The message includes
	   everything which was available at the start of the
	   sending state, plus register and entry point
	   stashes in that state. */

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
		hb->content |= availExprs;
		if (hb->sideCondition) {
			rx_checked = bbdd::Or(
				scope,
				rx_checked,
				hb->sideCondition);
		} else {
			rx_checked = scope->cnst(true);
		}
	}
	
	instrRxPhaseRes res;
	if (haveIncomingEdge) {
		res.rxed_expressions = rxed_expressions;
		res.checkedHere = rx_checked;
	} else {
		res.checkedHere = NULL;
	}
	return res;
}

static void
instrTxPhase(bbdd::scope *scope,
	     instr_t i,
	     const std::set<happensBeforeEdge *> &hbEdges,
	     const std::map<instr_t, std::set<instr_t> > &predecessors,
	     const std::map<instr_t, std::set<input_expression> > &availabilityMap,
	     const expressionStashMapT &stashMap,
	     bbdd *const entryNeeded,
	     bbdd *const entryAssumption,
	     bbdd *&exitNeeded,
	     std::set<input_expression> &availExprs,
	     node_schedule &schedule,
	     sane_map<instr_t, bbdd *> &alreadyEvaled)
{
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

		hb->content |= availExprs;

		std::set<input_expression> availForThisMessage(availExprs);
		availForThisMessage |= availOnOtherSide;

		/* What can we evaluate on this edge? */
		auto split = splitExpressionOnAvailability(
			scope,
			entryNeeded,
			availForThisMessage);
		if (debug_eem) {
			printf("Eval here after TX:\n");
			split.second->prettyPrint(stdout);
		}
		if (!split.second->isLeaf()) {
			hb->sideCondition = subst_eq(scope, split.second);
			if (debug_eem && hb->sideCondition != split.second) {
				printf("subst_eq reduces edge condition to:\n");
				hb->sideCondition->prettyPrint(stdout);
			}
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
		schedule.finishEdgeBefore(hb);
		{
			auto it2_did_insert = alreadyEvaled.insert(hb->after, entryAssumption);
			auto it2 = it2_did_insert.first;
			auto did_insert = it2_did_insert.second;
			if (!did_insert) {
				it2->second = bbdd::And(scope, it2->second, entryAssumption);
			}
		}
	}

	if (have_tx_edge) {
		assert(tx_leftover);
		availExprs |= acquired_by_tx;
		exitNeeded = tx_leftover;
		if (debug_eem) {
			printf("Avail with TX effects: ");
			print_expr_set(availExprs, stdout);
			printf("\ntx_leftover:\n");
			exitNeeded->prettyPrint(stdout);
		}
	}
}

/* What can we do once we know what our successor instruction is? */
static std::pair<bbdd *, bbdd *>
instrCfPhase(bbdd::scope *scope,
	     instr_t i,
	     const std::map<instr_t, std::set<input_expression> > &availabilityMap,
	     bbdd *entryNeeded,
	     bbdd *currentAssumption)
{
	auto it = availabilityMap.find(i);
	assert(it != availabilityMap.end());
	const std::set<input_expression> &availExprs(it->second);
	if (debug_eem) {
		printf("Final avail: ");
		print_expr_set(availExprs, stdout);
		printf("\n");
	}
	auto split3 = splitExpressionOnAvailability(
		scope,
		entryNeeded,
		availExprs);
	if (debug_eem) {
		printf("Left over after control flow:\n");
		split3.first->prettyPrint(stdout);
		printf("Eval here after control flow:\n");
		split3.second->prettyPrint(stdout);
	}
	std::pair<bbdd *, bbdd *> res;
	res.first = split3.first;
	res.second = split3.second;
	if (!split3.second->isLeaf()) {
		res.second = bbdd::assume(scope, split3.second, currentAssumption);
		if (res.second) {
			res.second = subst_eq(scope, res.second);
			if (res.second != split3.second && debug_eem) {
				printf("Simplifies to:\n");
				res.second->prettyPrint(stdout);
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

	bbdd *assumption = scope->cnst(true);

	if (debug_eem_schedule && !debug_eem) {
		printf("expressionEvalMapT:\n");
		cfg.prettyPrint(stdout);
		roots.prettyPrint(stdout);
		hbMap.prettyPrint(stdout);
	}

	std::map<instr_t, std::set<instr_t> > predecessors;
	std::set<instr_t> rootInstrs;
	std::map<instr_t, std::set<input_expression> > availabilityMap;

	fprintf(bubble_plot_log, "%f: start determine input availability\n", now());
	buildPredecessorMap(cfg, roots, predecessors, rootInstrs);
	buildInputAvailabilityMap(predecessors, stashMap, hbMap, availabilityMap);
	fprintf(bubble_plot_log, "%f: stop determine input availability\n", now());


	std::set<happensBeforeEdge *> allEdges;
	for (auto it = hbMap.begin(); it != hbMap.end(); it++) {
		allEdges |= it->second;
	}

	/* Now figure out what side condition we want to check at
	   every instruction.  For each node, we take the condition at
	   the start of the node and split it into a component which
	   can be evaluated at that instruction (this->evalAt) and a
	   component which has to be deferred
	   (@leftoverCondition).  */
	std::map<instr_t, bbdd *> leftoverCondition;
	/* And the condition which we've already evaluated */
	sane_map<instr_t, bbdd *> alreadyEvaled;

	node_schedule schedule;
	schedule.build(predecessors, allEdges);

	/* Assumption at the roots comes from the crash summary */
	for (auto it = roots.begin(); !it.finished(); it.advance()) {
		alreadyEvaled[cfg.findInstr(it.threadCfgLabel())] = assumption;
	}

	TimeoutTimer tmr;
	tmr.timeoutAfterSeconds(60);

	fprintf(bubble_plot_log, "%f: start place side conditions\n", now());
	std::set<instr_t> deadStates;
	while (!TIMEOUT && !schedule.finished()) {
		auto i = schedule.next();

		/* At the start of the instruction, we have to check
		   everything which hasn't been checked by one of our
		   predecessors. */
		bbdd *entryNeeded;
		entryNeeded = calcEntryNeeded(scope, i, abs, predecessors,
					      rootInstrs, sideCondition,
					      leftoverCondition);
		bbdd *entryAssumption = alreadyEvaled[i];
		assert(i);
		{
			bbdd *entryNeeded2 = bbdd::assume(scope, entryNeeded, entryAssumption);
			if (!entryNeeded2) {
				deadStates.insert(i);
				if (debug_eem_dead) {
					printf("entryNeeded is unsatisfiable, killing %s!\n",
					       i->rip.name());
				}
				continue;
			}
			if (debug_eem && entryNeeded != entryNeeded2) {
				printf("Entry assumption:\n");
				entryAssumption->prettyPrint(stdout);
				printf("reduces needed from:\n");
				entryNeeded->prettyPrint(stdout);
				printf("to:\n");
				entryNeeded2->prettyPrint(stdout);
			}
			entryNeeded = entryNeeded2;
		}

		bbdd *currentAssumption = entryAssumption;

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

		/* Figure out what we can do as soon as we start the
		 * instruction */
		auto entryPhase = instrEntryPhase(scope, leftover, currentAssumption, availExprs);
		if (entryPhase.dead) {
			deadStates.insert(i);
			if (debug_eem_dead) {
				printf("Register and entry point condition is unsatisfiable, killing %s!\n",
				       i->rip.name());
			}
			continue;
		}
		leftover = entryPhase.remainder;
		evalAt[i->rip].after_regs = entryPhase.evalHere;
		currentAssumption = entryPhase.newAssumption;

		{
			auto hb_it = hbMap.find(i->rip);
			if (hb_it != hbMap.end()) {
				/* Figure out what we can do once
				 * we've received incoming messages */
				auto rxPhase = instrRxPhase(
					scope,
					i,
					hb_it->second,
					predecessors,
					availabilityMap,
					stashMap,
					availExprs);
				availExprs |= rxPhase.rxed_expressions;
				if (rxPhase.checkedHere) {
					currentAssumption = bbdd::And(
						scope,
						currentAssumption,
						rxPhase.checkedHere);
					leftover = bbdd::assume(
						scope,
						leftover,
						rxPhase.checkedHere);
					if (!leftover) {
						deadStates.insert(i);
						if (debug_eem_dead) {
							printf("RX condition is unsatisfiable, killing %s!\n",
							       i->rip.name());
						}
						continue;
					}
					if (debug_eem) {
						printf("Avail with RX effects: ");
						print_expr_set(availExprs, stdout);
						printf("\nrx_checked:\n");
						rxPhase.checkedHere->prettyPrint(stdout);
						printf("leftover:\n");
						leftover->prettyPrint(stdout);
					}
				}

				/* Figure out what we can do once
				 * we've transmitted outgoing
				 * messages. */
				instrTxPhase(
					scope,
					i,
					hb_it->second,
					predecessors,
					availabilityMap,
					stashMap,
					leftover,
					currentAssumption,
					leftover,
					availExprs,
					schedule,
					alreadyEvaled);
			}
		}

		/* Figure out what we can do once we've figure out
		 * where we're going next. */
		std::pair<bbdd *, bbdd *>instrCf = instrCfPhase(
			scope,
			i,
			availabilityMap,
			leftover,
			currentAssumption);
		if (!instrCf.second || (instrCf.second->isLeaf() && !instrCf.second->leaf())) {
			if (debug_eem_dead) {
				printf("post-control-flow condition is unsatisfiable, killing %s\n",
				       i->rip.name());
			}
			deadStates.insert(i);
			continue;
		}
		if (!instrCf.second->isLeaf()) {
			evalAt[i->rip].after_control_flow = instrCf.second;
			currentAssumption = bbdd::And(scope,
						      currentAssumption,
						      instrCf.second);
		}
		leftoverCondition[i] = instrCf.first;

		for (auto it = i->successors.begin(); it != i->successors.end(); it++) {
			if (it->instr) {
				{
					auto it2_did_insert = alreadyEvaled.insert(it->instr, currentAssumption);
					auto it2 = it2_did_insert.first;
					auto did_insert = it2_did_insert.second;
					if (!did_insert) {
						it2->second = bbdd::Or(scope, it2->second, currentAssumption);
					}
				}
				schedule.finishControlPredecessor(*it);
				if (hbMap.count(it->instr->rip)) {
					const std::set<happensBeforeEdge *> &hbEdges(hbMap[it->instr->rip]);
					for (auto it2 = hbEdges.begin();
					     it2 != hbEdges.end();
					     it2++) {
						auto hb = *it2;
						if (hb->after == it->instr) {
							schedule.finishEdgeAfter(hb);
						}
					}
				}
			}
		}
	}
	tmr.cancel();
	fprintf(bubble_plot_log, "%f: stop place side conditions\n", now());

	if (TIMEOUT) {
		fprintf(bubble_plot_log, "%f: failed place side conditions\n", now());
		return;
	}

	if (deadStates.empty()) {
		schedule.check_cycles();
	}

	fprintf(bubble_plot_log, "%f: start simplify plan\n", now());		
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

			/* Kill it from the roots list, as well. */
			roots.erase(dead->rip);
		}
		if (deadStates == newDead) {
			break;
		}
		deadStates = newDead;
	}
	fprintf(bubble_plot_log, "%f: stop simplify plan\n", now());		
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
