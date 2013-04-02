#include <sys/fcntl.h>
#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "offline_analysis.hpp"
#include "intern.hpp"
#include "genfix.hpp"
#include "dnf.hpp"
#include "simplify_ordering.hpp"
#include "enforce_crash.hpp"
#include "allowable_optimisations.hpp"
#include "alloc_mai.hpp"
#include "sat_checker.hpp"
#include "visitor.hpp"
#include "timers.hpp"

extern FILE *bubble_plot_log;

#ifndef NDEBUG
static bool debug_declobber_instructions = false;
static bool debug_expr_slice = false;
#else
#define debug_declobber_instructions false
#define debug_expr_slice false
#endif

unsigned long
__trivial_hash_function(const VexRip &vr)
{
	return vr.hash();
}

void
instrToInstrSetMap::print(FILE *f) const
{
	for (auto it = begin(); it != end(); it++) {
		fprintf(f, "%s -> {", it->first->label.name());
		for (auto it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			fprintf(f, "%s", (*it2)->label.name());
		}
		fprintf(f, "}\n");
	}
}

#ifndef NDEBUG
/* There should be no HB edges in our side condition.  These utility
   functions are useful for checking that. */
static void
assertHbEdgeFree(IRExpr *what)
{
	struct v {
		static visit_result Hb(void *, const IRExprHappensBefore *) {
			return visit_abort;
		}
	};
	static irexpr_visitor<void> visitor;
	visitor.HappensBefore = v::Hb;
	assert(visit_irexpr((void *)NULL, &visitor, what) != visit_abort);
}
static void
assertHbEdgeFree(bbdd *what, std::set<bbdd *> &memo)
{
	if (what->isLeaf()) {
		return;
	}
	if (!memo.insert(what).second) {
		return;
	}
	assertHbEdgeFree(what->internal().condition);
	assertHbEdgeFree(what->internal().trueBranch, memo);
	assertHbEdgeFree(what->internal().falseBranch, memo);
}
static void
assertHbEdgeFree(bbdd *what)
{
	std::set<bbdd *> memo;
	assertHbEdgeFree(what, memo);
}
#else
static void
assertHbEdgeFree(bbdd *)
{
}
#endif

static bool
exprUsesInput(const bbdd *haystack, const input_expression &needle)
{
	if (!haystack) {
		return false;
	}
	struct v {
		static visit_result Iex(const input_expression *needle,
					const IRExpr *iex) {
			if (needle->matches(iex)) {
				return visit_abort;
			} else {
				return visit_continue;
                        }
                }
	};
	static struct bdd_visitor<const input_expression> visitor;
	visitor.irexpr.Iex = v::Iex;
	return visit_const_bdd(&needle, &visitor, haystack);
}

static bool
instrUsesExpr(Instruction<ThreadCfgLabel> *instr, const input_expression &expr, crashEnforcementData &ced)
{
	{
		auto it = ced.happensBeforePoints.find(instr->rip);
		if (it != ced.happensBeforePoints.end()) {
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				happensBeforeEdge *hbe = *it2;
				if (hbe->before->rip == instr->rip) {
					for (auto it3 = hbe->content.begin();
					     !it3.finished();
					     it3.advance()) {
						if (it3.get() == expr) {
							return true;
						}
					}
					if (exprUsesInput(hbe->sideCondition, expr)) {
						return true;
					}
				}
			}
		}
	}

	if (exprUsesInput(ced.expressionEvalPoints.after_regs(instr->rip), expr) ||
	    exprUsesInput(ced.expressionEvalPoints.after_control_flow(instr->rip), expr)) {
		return true;
	}
	return false;
}

static void
optimiseHBContent(crashEnforcementData &ced)
{
	std::set<happensBeforeEdge *> hbEdges;
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
	     it++)
		hbEdges.insert(it->second.begin(), it->second.end());
	bool progress = true;
	while (progress) {
		progress = false;
		for (auto it = hbEdges.begin(); it != hbEdges.end(); it++) {
			happensBeforeEdge *hbe = *it;
			for (auto it = hbe->content.begin(); !it.finished(); ) {
				bool must_keep = false;
				std::queue<Instruction<ThreadCfgLabel> *> pending;
				if (hbe->sideCondition &&
				    exprUsesInput(hbe->sideCondition, it.get())) {
					must_keep = true;
				}
				pending.push(hbe->after);
				while (!must_keep && !pending.empty()) {
					Instruction<ThreadCfgLabel> *l = pending.front();
					pending.pop();
					if (instrUsesExpr(l, it.get(), ced)) {
						must_keep = true;
					}
					for (unsigned y = 0; y < l->successors.size(); y++)
						pending.push(l->successors[y].instr);
				}
				if (must_keep) {
					it.advance();
				} else {
					it.erase();
					progress = true;
				}
			}
		}
	}
}

struct expr_slice {
	std::set<const IRExprHappensBefore *> trueSlice;
	std::set<const IRExprHappensBefore *> falseSlice;
	mutable bbdd *leftOver;
	bool operator <(const expr_slice &o) const {
		if (trueSlice < o.trueSlice)
			return true;
		if (trueSlice > o.trueSlice)
			return false;
		return falseSlice < o.falseSlice;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "\t{");
		bool comma = false;
		for (auto it = trueSlice.begin();
		     it != trueSlice.end();
		     it++) {
			if (comma)
				fprintf(f, ", ");
			comma = true;
			ppIRExpr(*it, f);
		}
		for (auto it = falseSlice.begin();
		     it != falseSlice.end();
		     it++) {
			if (comma)
				fprintf(f, ", ");
			comma = true;
			fprintf(f, "¬");
			ppIRExpr(*it, f);
		}
		fprintf(f, "} -> ");
		leftOver->prettyPrint(f);
		fprintf(f, "\n");		
	}
	bool simplifyAndCheckForContradiction();
};

bool
expr_slice::simplifyAndCheckForContradiction()
{
	if (debug_expr_slice) {
		printf("%s\n", __func__);
		prettyPrint(stdout);
	}
	if (leftOver->isLeaf() && !leftOver->leaf()) {
		if (debug_expr_slice) {
			printf("Leftover is a contradiction\n");
			return true;
		}
	}
	sane_map<MemoryAccessIdentifier, std::set<MemoryAccessIdentifier> > happensAfter;
	for (auto it = trueSlice.begin(); it != trueSlice.end(); it++) {
		auto hb = *it;
		happensAfter[hb->before].insert(hb->after);
	}
	for (auto it = falseSlice.begin(); it != falseSlice.end(); it++) {
		auto hb = *it;
		happensAfter[hb->after].insert(hb->before);
	}
	/* Add in the implicit control-flow edges */
	std::map<int, std::set<int> > mais;
	for (auto it = happensAfter.begin(); it != happensAfter.end(); it++) {
		const MemoryAccessIdentifier &before(it->first);
		mais[before.tid].insert(before.id);
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			const MemoryAccessIdentifier &after(*it2);
			mais[after.tid].insert(after.id);
		}
	}
	if (debug_expr_slice) {
		printf("MAI map:\n");
		for (auto it = mais.begin(); it != mais.end(); it++) {
			printf("\t%d -> {", it->first);
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				if (it2 != it->second.begin()) {
					printf(", ");
				}
				printf("%d", *it2);
			}
			printf("}\n");
		}
	}
	if (!mais.empty()) {
		for (auto it = mais.begin(); it != mais.end(); it++) {
			int tid = it->first;
			const std::set<int> &ids(it->second);
			if (ids.empty()) {
				continue;
			}
			auto it2 = ids.begin();
			auto it3 = it2;
			it3++;
			while (it3 != ids.end()) {
				MemoryAccessIdentifier before(*it2, tid);
				MemoryAccessIdentifier after(*it3, tid);
				if (debug_expr_slice) {
					printf("Add control-flow edge %s -> %s\n",
					       before.name(), after.name());
				}
				happensAfter[before].insert(after);
				it3++;
				it2++;
			}
		}
	}

	if (debug_expr_slice) {
		printf("Edges:\n");
		for (auto it = happensAfter.begin(); it != happensAfter.end(); it++) {
			printf("\t%s -> {", it->first.name());
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				if (it2 != it->second.begin()) {
					printf(", ");
				}
				printf("%s", it2->name());
			}
			printf("}\n");
		}
	}

	/* Topo sort to check for cycles. */
	sane_map<MemoryAccessIdentifier, int> nrPredecessors;
	std::set<MemoryAccessIdentifier> unsorted;
	for (auto it = happensAfter.begin(); it != happensAfter.end(); it++) {
		const MemoryAccessIdentifier &before(it->first);
		nrPredecessors[before] = 0;
		mais[before.tid].insert(before.id);
		unsorted.insert(before);
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			const MemoryAccessIdentifier &after(*it2);
			nrPredecessors[after] = 0;
			unsorted.insert(after);
		}
	}
	for (auto it = happensAfter.begin(); it != happensAfter.end(); it++) {
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			nrPredecessors[*it2]++;
		}
	}
	if (debug_expr_slice) {
		printf("Toposort predecessor count:\n");
		for (auto it = nrPredecessors.begin(); it != nrPredecessors.end(); it++) {
			printf("\t%s -> %d\n", it->first.name(), it->second);
		}
	}

	std::vector<MemoryAccessIdentifier> q;
	for (auto it = nrPredecessors.begin(); it != nrPredecessors.end(); it++) {
		if (it->second == 0) {
			q.push_back(it->first);
		}
	}
	while (!q.empty()) {
		const MemoryAccessIdentifier mai(q.back());
		q.pop_back();
		if (debug_expr_slice) {
			printf("Toposort reaches %s\n", mai.name());
		}
		assert(nrPredecessors.count(mai));
		assert(nrPredecessors[mai] == 0);
		assert(unsorted.count(mai));
		unsorted.erase(mai);
		const std::set<MemoryAccessIdentifier> &after(happensAfter[mai]);
		for (auto it = after.begin(); it != after.end(); it++) {
			assert(nrPredecessors.count(*it));
			assert(nrPredecessors[*it] > 0);
			if (--nrPredecessors[*it] == 0) {
				q.push_back(*it);
			}
		}
	}
	if (!unsorted.empty()) {
		/* Can't complete toposort -> HB graph has a cycle */
		if (debug_expr_slice) {
			printf("Toposort failed\n");
		}
		return true;
	}

	/* The graph is acyclic, so it is in principle possible to
	   enforce it.  Now do a transitive reduction to remove
	   redundant edges.  This is a bit of a hack: just consider
	   every edge in turn and check whether it's transitively
	   redundant, and then remove it if it is.*/
	for (auto it = happensAfter.begin(); it != happensAfter.end(); it++) {
		const MemoryAccessIdentifier &before(it->first);
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			const MemoryAccessIdentifier &after(*it2);
			if (before.tid == after.tid) {
				/* Intra-thread edges are never redundant. */
				continue;
			}
			if (debug_expr_slice) {
				printf("Check %s->%s for transitive redundancy\n",
				       before.name(), after.name());
			}
			std::set<MemoryAccessIdentifier> reachableFromBefore;
			bool redundant = false;
			q.clear();
			q.push_back(before);
			reachableFromBefore.insert(before);
			while (!redundant && !q.empty()) {
				MemoryAccessIdentifier edgeStart(q.back());
				q.pop_back();
				if (debug_expr_slice) {
					printf("\tExpand from %s\n", edgeStart.name());
				}
				assert(reachableFromBefore.count(edgeStart));
				const std::set<MemoryAccessIdentifier> &edgeEnds(happensAfter[edgeStart]);
				for (auto it3 = edgeEnds.begin(); it3 != edgeEnds.end(); it3++) {
					const MemoryAccessIdentifier &edgeEnd(*it3);
					if (edgeStart == before && edgeEnd == after) {
						/* We don't want to
						   include the edge
						   which we're testing
						   for redundancy in
						   the reachability
						   test. */
						continue;
					}
					if (debug_expr_slice) {
						printf("\tConsider %s->%s\n",
						       edgeStart.name(), edgeEnd.name());
					}
					if (edgeEnd == after) {
						/* Any other edge to
						   @after makes the
						   before->after edge
						   redundant. */
						redundant = true;
						break;
					}
					if (reachableFromBefore.insert(edgeEnd).second) {
						/* edgeEnd is new, so
						   have to explore
						   from here as
						   well. */
						if (debug_expr_slice) {
							printf("\tDiscover %s\n",
							       edgeEnd.name());
						}
						q.push_back(edgeEnd);
					}
				}
			}

			if (redundant) {
				/* Yep, this is a redundant edge. */
				if (debug_expr_slice) {
					printf("Edge is redundant!\n");
				}
				for (auto it = trueSlice.begin();
				     it != trueSlice.end();
					) {
					auto hb = *it;
					if (hb->before == before &&
					    hb->after == after) {
						trueSlice.erase(it++);
					} else {
						it++;
					}
				}
				for (auto it = falseSlice.begin();
				     it != falseSlice.end();
					) {
					auto hb = *it;
					if (hb->after == before &&
					    hb->before == after) {
						falseSlice.erase(it++);
					} else {
						it++;
					}
				}
			}
		}
	}

	if (debug_expr_slice) {
		printf("%s finished\n", __func__);
		prettyPrint(stdout);
	}
	return false;
}

static bool
buildCED(const SummaryId &summaryId,
	 const expr_slice &c,
	 std::map<ConcreteThread, std::set<std::pair<CfgLabel, long> > > &rootsCfg,
	 CrashSummary *summary,
	 crashEnforcementData *out,
	 ThreadAbstracter &abs,
	 int &next_hb_id,
	 AddressSpace *as)
{
	/* Figure out what we actually need to keep track of */
	std::set<input_expression> neededExpressions;
	enumerateNeededExpressions(c.leftOver, neededExpressions);

	*out = crashEnforcementData(&summary->scopes->bools,
				    summaryId,
				    *summary->mai,
				    neededExpressions,
				    abs,
				    rootsCfg,
				    c.trueSlice,
				    c.falseSlice,
				    c.leftOver,
				    next_hb_id,
				    summary,
				    as);
	optimiseHBContent(*out);
	return true;
}

/* Check whether the ordering in @slice is consistent with a total
   ordering over threads.  Those don't actually enforce any
   concurrency, so aren't very interesting. */
static bool
consistentOrdering(const expr_slice &slice)
{
	int thread_a;
	int thread_b;
	bool found_a_thread = false;

	/* Shut compiler up */
	thread_a = -98;
	thread_b = -99;

	for (auto it = slice.trueSlice.begin(); it != slice.trueSlice.end(); it++) {
		if ((*it)->tag == Iex_HappensBefore) {
			IRExprHappensBefore *e = (IRExprHappensBefore *)*it;
			if (!found_a_thread) {
				thread_a = e->before.tid;
				thread_b = e->after.tid;
				found_a_thread = true;
			} else {
				if (thread_a != e->before.tid ||
				    thread_b != e->after.tid)
					return false;
			}
		}
	}
	for (auto it = slice.falseSlice.begin(); it != slice.falseSlice.end(); it++) {
		if ((*it)->tag == Iex_HappensBefore) {
			IRExprHappensBefore *e = (IRExprHappensBefore *)*it;
			if (!found_a_thread) {
				thread_a = e->after.tid;
				thread_b = e->before.tid;
				found_a_thread = true;
			} else {
				if (thread_a != e->after.tid ||
				    thread_b != e->before.tid)
					return false;
			}
		}
	}
	return true;
}

/* Munge a side condition to make it easier to evaluate.  This is
   allowed to slightly change the value of the condition if that makes
   the eval much easier, but shouldn't push things too far. */
/* Generally, taking a true expression and making it false is more
   dangerous than taking a false expression and making it true */
static bbdd *
heuristicSimplify(bbdd::scope *scope, bbdd *e, std::map<bbdd *, bbdd *> &memo)
{
	if (e->isLeaf()) {
		return e;
	}
	auto it_did_insert = memo.insert(std::pair<bbdd *, bbdd *>(e, (bbdd *)0xf001));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		/* it->second is already correct */
	} else {
		auto t = heuristicSimplify(scope, e->internal().trueBranch, memo);
		auto f = heuristicSimplify(scope, e->internal().falseBranch, memo);

		IRExpr *cond = e->internal().condition;
		if (cond->tag == Iex_Binop &&
		    ((IRExprBinop *)cond)->op == Iop_CmpEQ64) {
			IRExprBinop *ieb;

			ieb = (IRExprBinop *)cond;

		retry:
			/* First rule: 0 == a - b -> a == b */
			if (ieb->arg1->tag == Iex_Const &&
			    ((IRExprConst *)ieb->arg1)->Ico.content.U64 == 0 &&
			    ieb->arg2->tag == Iex_Associative &&
			    ((IRExprAssociative *)ieb->arg2)->op == Iop_Add64 &&
			    ((IRExprAssociative *)ieb->arg2)->nr_arguments == 2 &&
			    ((IRExprAssociative *)ieb->arg2)->contents[1]->tag == Iex_Unop &&
			    ((IRExprUnop *)((IRExprAssociative *)ieb->arg2)->contents[1])->op == Iop_Neg64) {
				ieb = IRExprBinop::mk(ieb->op,
						      ((IRExprAssociative *)ieb->arg2)->contents[0],
						      ((IRExprUnop *)((IRExprAssociative *)ieb->arg2)->contents[1])->arg);
			}

			/* Second rule: f(a) == f(b) -> a == b, if f
			   is sufficiently injective. */
			if (ieb->arg1->tag == ieb->arg2->tag) {
				switch (ieb->arg1->tag) {
				case Iex_Binop: {
					IRExprBinop *l = (IRExprBinop *)ieb->arg1;
					IRExprBinop *r = (IRExprBinop *)ieb->arg2;
					if (l->op != r->op)
						break;
					switch (l->op) {
					case Iop_Shl64: /* x << k is treated as
							 * injective if k is a small
							 * constant, because most of
							 * the time you don't get
							 * overflow. */
						if (r->arg2->tag == Iex_Const &&
						    l->arg2->tag == Iex_Const &&
						    ((IRExprConst *)r->arg2)->Ico.content.U8 ==
						    ((IRExprConst *)l->arg2)->Ico.content.U8 &&
						    ((IRExprConst *)l->arg2)->Ico.content.U8 < 8) {
							ieb = IRExprBinop::mk(ieb->op,
									    l->arg1,
									    r->arg1);
							goto retry;
						}
						break;
					default:
						break;
					}
					break;
				}
				case Iex_Unop: {
					IRExprUnop *l = (IRExprUnop *)ieb->arg1;
					IRExprUnop *r = (IRExprUnop *)ieb->arg2;
					if (l->op != r->op)
						break;
					switch (l->op) {
					case Iop_32Sto64:
						/* This one actually is injective */
						ieb = IRExprBinop::mk(ieb->op, l->arg, r->arg);
						goto retry;
					default:
						break;
					}
					break;
				}
				default:
					break;
				}
			}
			cond = ieb;
		}

		if (cond == e->internal().condition &&
		    t == e->internal().trueBranch &&
		    f == e->internal().falseBranch) {
			it->second = e;
		} else {
			it->second =
				bbdd::ifelse(
					scope,
					bbdd::var(scope, cond),
					t,
					f);
		}
	}
	return it->second;
}


/* We can't get at the values of free variables from the run-time
   enforcer, so we might as well remove them now.  Also remove a
   couple of other un-checkable expressions, like floating point
   operations. */
/* If we have to introduce an error, we always prefer to return 1 when
   we should return 0 (rather than returning 0 when we should return
   1) */
static bool
irexprUsesFreeVariable(const IRExpr *expr)
{
	struct foo {
		static visit_result FreeVariable(void *, const IRExprFreeVariable *) {
			return visit_abort;
		}
		static visit_result Binop(void *, const IRExprBinop *ieb) {
			if (ieb->op == Iop_CmpF32 || ieb->op == Iop_CmpF64 ||
			    ieb->op == Iop_64HLtoV128 || ieb->op == Iop_64HLto128) {
				return visit_abort;
			} else {
				return visit_continue;
			}
		}
		static visit_result Unop(void *, const IRExprUnop *i) {
			if (i->op == Iop_V128to64 || i->op == Iop_ReinterpI32asF32) {
				return visit_abort;
			} else {
				return visit_continue;
			}
		}
		static visit_result Get(void *, const IRExprGet *i) {
			/* The enforcer machinery only tracks the
			   normal registers, plus FS_ZERO. */
			assert(i->reg.isReg());
			if (i->reg.asReg() > OFFSET_amd64_R15 &&
			    i->reg.asReg() != offsetof(VexGuestAMD64State, guest_FS_ZERO)) {
				return visit_abort;
			} else {
				return visit_continue;
			}
		}
	};
	static irexpr_visitor<void> visitor;
	visitor.FreeVariable = foo::FreeVariable;
	visitor.Binop = foo::Binop;
	visitor.Unop = foo::Unop;
	visitor.Get = foo::Get;
	return visit_irexpr((void *)NULL, &visitor, expr) == visit_abort;
}
static bbdd *
removeFreeVariables(bbdd::scope *scope, bbdd *what, std::map<bbdd *, bbdd *> &memo)
{
	if (what->isLeaf()) {
		return what;
	}
	auto it_did_insert = memo.insert(std::pair<bbdd *, bbdd *>(what, (bbdd *)0xf001));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		/* it->second is already correct */
	} else if (what->isLeaf()) {
		it->second = what;
	} else {
		auto t = removeFreeVariables(scope, what->internal().trueBranch, memo);
		auto f = removeFreeVariables(scope, what->internal().falseBranch, memo);
		if (t == f) {
			it->second = t;
		} else if (irexprUsesFreeVariable(what->internal().condition)) {
			/* We can't tell whether we want to go down
			   the t branch or the f one.  We're allowed
			   to make positive approximations
			   (i.e. return 1 when we should return 0) so
			   just use t || f. */
			it->second = bbdd::Or(
				scope,
				t,
				f);
		} else if (t == what->internal().trueBranch &&
			   f == what->internal().falseBranch) {
			it->second = what;
		} else {
			it->second = scope->node(
				what->internal().condition,
				what->internal().rank,
				t,
				f);
		}
	}
	return it->second;
}

class sliced_expr : public std::set<expr_slice> {
public:
	sliced_expr operator |(const sliced_expr &a) const
	{
		sliced_expr res(*this);
		res.insert(a.begin(), a.end());
		return res;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "Sliced expr:\n");
		for (auto it = begin(); it != end(); it++)
			it->prettyPrint(f);
	}
	sliced_expr setTrue(const IRExprHappensBefore *e) const
	{
		sliced_expr res;
		for (auto it = begin();
		     it != end();
		     it++) {
			expr_slice a(*it);
			a.trueSlice.insert(e);
			if (!a.simplifyAndCheckForContradiction()) {
				res.insert(a);
			}
		}
		return res;
	}
	sliced_expr setFalse(const IRExprHappensBefore *e) const
	{
		sliced_expr res;
		for (auto it = begin();
		     it != end();
		     it++) {
			expr_slice a(*it);
			a.falseSlice.insert(e);
			if (!a.simplifyAndCheckForContradiction()) {
				res.insert(a);
			}
		}
		return res;
	}
};

static bbdd *
setVariable(bbdd::scope *scope, bbdd *what, const IRExpr *expr,
	    bool val, std::map<bbdd *, bbdd *> &memo)
{
	assert(expr->tag == Iex_HappensBefore);
	if (what->isLeaf()) {
		return what;
	}
	/* This is safe because of the BDD ordering. */
	if (what->internal().condition->tag != Iex_EntryPoint &&
	    what->internal().condition->tag != Iex_ControlFlow &&
	    what->internal().condition->tag != Iex_HappensBefore) {
		return what;
	}
	auto it_did_insert = memo.insert(std::pair<bbdd *, bbdd *>(what, (bbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		/* it->second already correct */
	} else {
		auto t = setVariable(scope, what->internal().trueBranch, expr, val, memo);
		auto f = setVariable(scope, what->internal().falseBranch, expr, val, memo);
		if (what->internal().condition == expr) {
			if (val) {
				it->second = t;
			} else {
				it->second = f;
			}
		} else if (t == f) {
			it->second = t;
		} else if (t == what->internal().trueBranch &&
			   f == what->internal().falseBranch) {
			it->second = what;
		} else {
			it->second = scope->node(
				what->internal().condition,
				what->internal().rank,
				t,
				f);
		}
	}
	return it->second;
}

static sliced_expr
slice_by_exprs(bbdd::scope *scope, bbdd *expr, const std::set<const IRExprHappensBefore *> &sliceby)
{
	if (sliceby.empty() || expr->isLeaf()) {
		expr_slice theSlice;
		theSlice.leftOver = expr;
		sliced_expr s;
		s.insert(theSlice);
		return s;
	}
	if (TIMEOUT) {
		return sliced_expr();
	}
	const IRExprHappensBefore *e = *sliceby.begin();
	std::set<const IRExprHappensBefore *> others(sliceby);
	others.erase(e);
	std::map<bbdd *, bbdd *> memo1;
	sliced_expr trueSlice(
		slice_by_exprs(scope, setVariable(scope, expr, e, true, memo1), others));
	std::map<bbdd *, bbdd *> memo2;
	sliced_expr falseSlice(
		slice_by_exprs(scope, setVariable(scope, expr, e, false, memo2), others));
	return trueSlice.setTrue(e) | falseSlice.setFalse(e);
}

static sliced_expr
slice_by_hb(bbdd::scope *scope, bbdd *expr)
{
	struct foo {
		static visit_result HappensBefore(std::set<const IRExprHappensBefore *> *state,
						  const IRExprHappensBefore *expr) {
			state->insert(expr);
			return visit_continue;
		}
	};
	static struct bdd_visitor<std::set<const IRExprHappensBefore *> > visitor;
	visitor.irexpr.HappensBefore = foo::HappensBefore;
	std::set<const IRExprHappensBefore *> hbEdges;
	visit_const_bdd(&hbEdges, &visitor, const_cast<const bbdd *>(expr));
	return slice_by_exprs(scope, expr, hbEdges);
}

crashEnforcementData
enforceCrashForMachine(const SummaryId &summaryId,
		       VexPtr<CrashSummary, &ir_heap> summary,
		       VexPtr<Oracle> &oracle,
		       ThreadAbstracter &abs,
		       int &next_hb_id)
{
	summary = internCrashSummary(summary);
	if (TIMEOUT) {
		fprintf(_logfile, "Timeout while interning summary\n");
		exit(1);
	}

	VexPtr<OracleInterface> oracleI(oracle);

	bbdd *requirement = bbdd::assume(
		&summary->scopes->bools,
		summary->crashCondition,
		summary->inferredAssumption);
	if (!requirement) {
		errx(1, "timeout");
	}

	{
		std::map<bbdd *, bbdd *> memo;
		requirement = removeFreeVariables(&summary->scopes->bools, requirement, memo);
	}
	fprintf(_logfile, "After free variable removal:\n");
	requirement->prettyPrint(_logfile);
	fprintf(_logfile, "\n");
	if (TIMEOUT) {
		fprintf(_logfile, "Killed by a timeout during simplification\n");
		exit(1);
	}

	fprintf(bubble_plot_log, "%f: start slice by hb\n", now());
	sliced_expr sliced_by_hb;
	{
		TimeoutTimer tmr;
		tmr.timeoutAfterSeconds(60);
		sliced_by_hb = slice_by_hb(&summary->scopes->bools, requirement);
		tmr.cancel();
	}
	fprintf(bubble_plot_log, "%f: stop slice by hb\n", now());

	if (TIMEOUT) {
		fprintf(bubble_plot_log, "%f: failed slice by hb\n", now());
		return crashEnforcementData();
	}

	printf("Sliced requirement:\n");
	sliced_by_hb.prettyPrint(stdout);

	fprintf(bubble_plot_log, "%f: start heuristic simplify\n", now());
	{
		std::map<bbdd *, bbdd *> memo;
		for (auto it = sliced_by_hb.begin();
		     it != sliced_by_hb.end();
			) {
			assertHbEdgeFree(it->leftOver);
			it->leftOver = heuristicSimplify(&summary->scopes->bools, it->leftOver, memo);
			if ( (!it->leftOver->isLeaf() || it->leftOver->leaf()) &&
			     !consistentOrdering(*it) ) {
				it++;
			} else {
				sliced_by_hb.erase(it++);
			}
		}
	}
	fprintf(bubble_plot_log, "%f: stop heuristic simplify\n", now());

	printf("After simplifying down:\n");
	sliced_by_hb.prettyPrint(stdout);

	std::map<ConcreteThread, std::set<std::pair<CfgLabel, long> > > rootsCfg;
	for (auto it = summary->loadMachine->cfg_roots.begin();
	     it != summary->loadMachine->cfg_roots.end();
	     it++) {
		rootsCfg[ConcreteThread(summaryId, it->first.thread)].insert(std::pair<CfgLabel, long>(it->first.node->label, it->second.rsp_delta));
	}
	for (auto it = summary->storeMachine->cfg_roots.begin();
	     it != summary->storeMachine->cfg_roots.end();
	     it++) {
		rootsCfg[ConcreteThread(summaryId, it->first.thread)].insert(std::pair<CfgLabel, long>(it->first.node->label, it->second.rsp_delta));
	}

	crashEnforcementData accumulator;
	for (auto it = sliced_by_hb.begin(); it != sliced_by_hb.end(); it++) {
		crashEnforcementData tmp;
		if (buildCED(summaryId, *it, rootsCfg, summary, &tmp, abs, next_hb_id, oracle->ms->addressSpace)) {
			printf("Intermediate CED:\n");
			tmp.prettyPrint(summary->scopes, stdout, true);
			accumulator |= tmp;
		}
	}
	return accumulator;
}

/* Try to delay stashing registers until we actually need to do so.
   We start off trying to stash them at the roots of the CFG and we
   can delay if:

   -- The node doesn't modify the register
   -- We don't try to eval anything at the node.
   -- The node isn't the before end of a happens-before edge
*/
void
optimiseStashPoints(crashEnforcementData &ced, Oracle *oracle)
{
	expressionStashMapT newMap;
	for (auto it = ced.exprStashPoints.begin();
	     it != ced.exprStashPoints.end();
		) {
		const ThreadCfgLabel &label(it->first);
		typedef std::pair<Instruction<ThreadCfgLabel> *, input_expression> entryT;
		std::set<entryT> frozenStashPoints;
		std::set<entryT> unfrozenStashPoints;

		{
			Instruction<ThreadCfgLabel> *n = ced.crashCfg.findInstr(label);
			const std::set<input_expression> &exprsToStash(it->second);
			if (!n) {
				/* This stash point cannot be reached
				 * by any root -> kill it off. */
				ced.exprStashPoints.erase(it++);
				continue;
			}
			for (auto it = exprsToStash.begin(); it != exprsToStash.end(); it++)
				unfrozenStashPoints.insert(entryT(n, *it));
		}
		while (!unfrozenStashPoints.empty()) {
			auto it = unfrozenStashPoints.begin();
			Instruction<ThreadCfgLabel> *node = it->first;
			input_expression expr(it->second);
			unfrozenStashPoints.erase(it);

			if (expr.tag == input_expression::inp_entry_point ||
			    expr.tag == input_expression::inp_control_flow) {
				/* Can never advance stash of
				 * entry point expressions. */
				frozenStashPoints.insert(entryT(node, expr));
				continue;
			}
			assert(expr.tag == input_expression::inp_register);
			const ThreadCfgLabel &label(node->rip);

			/* Can't be an eval point */
			if (ced.expressionEvalPoints.count(label)) {
				frozenStashPoints.insert(entryT(node, expr));
				continue;
			}

			/* Can't be a happens-before before point */
			{
				auto it2 = ced.happensBeforePoints.find(label);
				if (it2 != ced.happensBeforePoints.end()) {
					bool b = false;
					for (auto it3 = it2->second.begin();
					     !b && it3 != it2->second.end();
					     it3++)
						if ((*it3)->before->rip == label)
							b = true;
					if (b) {
						frozenStashPoints.insert(entryT(node, expr));
						continue;
					}
				}
			}


			/* Can't stash a register which this
			 * instruction might modify */
			const AbstractThread &absThread(node->rip.thread);
			ConcreteThread concThread(ced.roots.lookupAbsThread(absThread));
			ConcreteCfgLabel concCfgLabel(concThread.summary(), node->rip.label);
			const VexRip &vr(ced.crashCfg.labelToRip(concCfgLabel));
			IRSB *irsb = oracle->ms->addressSpace->getIRSBForAddress(ThreadRip(Oracle::STATIC_THREAD, vr), true);
			bool modifies = false;
			for (int x = 0; !modifies && x < irsb->stmts_used && irsb->stmts[x]->tag != Ist_IMark; x++) {
				if (irsb->stmts[x]->tag == Ist_Put &&
				    ((IRStmtPut *)irsb->stmts[x])->target.tid() == expr.thread &&
				    ((IRStmtPut *)irsb->stmts[x])->target.isReg() &&
				    ((IRStmtPut *)irsb->stmts[x])->target.asReg() == (int)expr.vex_offset) {
					modifies = true;
				}
			}
			if (modifies) {
				frozenStashPoints.insert(entryT(node, expr));
				continue;
			}

			/* Advance this stash point */
			for (auto it2 = node->successors.begin(); it2 != node->successors.end(); it2++)
				unfrozenStashPoints.insert(entryT(it2->instr, expr));
		}

		for (auto it2 = frozenStashPoints.begin(); it2 != frozenStashPoints.end(); it2++) {
			auto node = it2->first;
			auto expr = it2->second;
			ThreadCfgLabel label(it->first.thread, node->label);
			newMap[label].insert(expr);
		}

		it++;
	}

	ced.exprStashPoints = newMap;
}

/* We sometimes find that the CFG has a prefix which is completely
   irrelevant.  Try to remove it. */
void
optimiseCfg(crashEnforcementData &ced)
{
	struct {
		crashEnforcementData *ced;
		bool operator()(const ThreadCfgLabel &label) {
			return ced->exprStashPoints.count(label) != 0 ||
				ced->happensBeforePoints.count(label) != 0 ||
				ced->expressionEvalPoints.count(label) != 0;
		}
	} hasSideEffect = {&ced};
	crashEnforcementRoots newRoots;
	for (auto it = ced.roots.begin(); !it.finished(); it.advance()) {
		const AbstractThread thread(it.threadCfgLabel().thread);
		auto root = ced.crashCfg.findInstr(it.threadCfgLabel());
		while (1) {
			/* We can advance a root if it has a single
			   successor, and it has no stash points, and
			   it has no HB points, and it has no eval
			   points, and it isn't an exit point. */
			if (root->successors.size() != 1)
                               break;
			ThreadCfgLabel l(thread, root->label);
			if (hasSideEffect(l))
				break;
			root = root->successors[0].instr;
		}

		/* If all of the paths forwards from root N issue
		   their first side-effect at node N' then N can be
		   replaced by N'. */
		bool haveFirstSideEffect = false;
		bool failed = false;
		ThreadCfgLabel firstSideEffect;
		std::set<const Instruction<ThreadCfgLabel> *> visited;
		std::queue<const Instruction<ThreadCfgLabel> *> pending;
		pending.push(root);
		while (!failed && !pending.empty()) {
			auto n = pending.front();
			pending.pop();
			ThreadCfgLabel l(thread, n->label);

			if (hasSideEffect(l)) {
				if (haveFirstSideEffect) {
					if (firstSideEffect != l)
						failed = true;
				} else {
					firstSideEffect = l;
					haveFirstSideEffect = true;
				}
			} else {
				for (auto it = n->successors.begin();
				     it != n->successors.end();
				     it++)
					pending.push(it->instr);
			}
		}
		if (haveFirstSideEffect) {
			if (failed)
				newRoots.insert(it.concrete_tid(), it.rspDelta(), it.threadCfgLabel());
			else
				newRoots.insert(it.concrete_tid(), it.rspDelta(), firstSideEffect);
		}
	}
	ced.roots = newRoots;

	/* Anything which isn't reachable from a root can be removed
	 * from the CFG. */
	std::set<Instruction<ThreadCfgLabel> *> retain;
	std::queue<Instruction<ThreadCfgLabel> *> pending;
	for (auto it = ced.roots.begin(); !it.finished(); it.advance()) {
		pending.push(ced.crashCfg.findInstr(it.threadCfgLabel()));
	}
	while (!pending.empty()) {
		auto n = pending.front();
		pending.pop();
		if (!retain.insert(n).second)
			continue;
		for (auto it = n->successors.begin(); it != n->successors.end(); it++)
			pending.push(it->instr);
	}
	ced.crashCfg.removeAllBut(retain);
}

/* This function is responsible for setting up the patch point list
   and the force interpret list.  The preceding phases of the analysis
   have given us a set of instructions I and we must arrange that
   we're in the interpreter whenever the program executes an
   instruction from I.  The challenge is that the only way of gaining
   control is through a jump instruction, which is five bytes, and
   some of the instructions in I might themselves be smaller than five
   bytes, and so directly patching one of them might clobber something
   important.  That is itself fine *provided* that the program is
   definitely in the interpreter when it executes the instruction
   which you clobbered, which might then require us to add new entry
   points.

   Define some notation first:

   -- MustInterpret(X) means that we must be in the interpreter when we
   run instruction X.
   -- DoesInterpret(X) means that the patched program definitely will
   be in the interpreter when in runs X.
   -- Clobber(X, Y) means that trying to patch X into an entry point
   will clobber Y.
   -- Patch(X) means that we're going to replace X with an entry point.
   -- Cont(X) means that if the interpreter hits X it should continue
   interpreting.
   -- Predecessor(X, Y) is true precisely when there's some control-flow
   edge from Y to X i.e. when Y is a predecessor of X.
   -- External(X) is true if there might be some control-flow edge which
   we don't know about which ends at X.

   We control Patch and Cont; everything else is set for us in advance
   by the oracle and the CED.

   Assumptions:

   Patch(X) => DoesInterpret(X)
   !External(X) && Cont(X) && forall Y.(Predecessor(X, Y) => DoesInterpret(Y)) => DoesInterpret(X)

   In the final configuration, we need:

   Patch(X) => Cont(X)
   MustInterpret(X) => DoesInterpret(X)
   Patch(X) && Clobber(X, Y) => DoesInterpret(Y)
   Patch(X) && Clobber(X, Y) => !External(Y)

   For performance reasons, we'd also like to minimise the size of the
   Cont set.

   We treat this as an exhaustive search problem, using two possible
   maneuvers:

   -- Create a new patch point at X.  That's only valid if doing so
      wouldn't clobber an external function.  Doing this then moves
      you to a new state in which MustInterpret() contains all of the
      instructions which are clobbered by X.
   -- Use a continue point instead: set Cont(X) and then set
      MustInterpret for all of X's predecessors.
*/

struct patchStrategy {
	std::set<unsigned long> MustInterpret;
	std::set<unsigned long> Patch;
	std::set<unsigned long> Cont;
	unsigned size() const {
		return MustInterpret.size() + Cont.size();
	}
	class priorityOrder {
	public:
		bool operator ()(const patchStrategy &a, const patchStrategy &b) const {
			if (a.size() > b.size())
				return true;
			if (a.size() < b.size())
				return false;
			return a < b;
		}
	};
	bool operator<(const patchStrategy &o) const {
		if (MustInterpret < o.MustInterpret)
			return true;
		if (MustInterpret > o.MustInterpret)
			return false;
		if (Patch < o.Patch)
			return true;
		if (Patch > o.Patch)
			return false;
		return Cont < o.Cont;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "MI: {");
		for (auto it = MustInterpret.begin(); it != MustInterpret.end(); it++) {
			if (it != MustInterpret.begin())
				fprintf(f, ",");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "}; P {");
		for (auto it = Patch.begin(); it != Patch.end(); it++) {
			if (it != Patch.begin())
				fprintf(f, ",");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "}; C {");
		for (auto it = Cont.begin(); it != Cont.end(); it++) {
			if (it != Cont.begin())
				fprintf(f, ",");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "}\n");
	}
};

typedef std::priority_queue<patchStrategy, std::vector<patchStrategy>, patchStrategy::priorityOrder> patchQueueT;

static bool
patchSearch(Oracle *oracle,
	    const patchStrategy &input,
	    patchQueueT &thingsToTry)
{
	if (input.MustInterpret.empty())
		return true;

	if (debug_declobber_instructions)
		input.prettyPrint(stdout);
	unsigned long needed = *input.MustInterpret.begin();

	if (debug_declobber_instructions)
		printf("\tLook at %lx\n", needed);
	patchStrategy c(input);
	/* @needed is definitely going to be interpreted after
	 * this. */
	c.Cont.insert(needed);
	c.MustInterpret.erase(needed);

	/* Decide which maneuver to use here.  We need to either patch
	   @needed itself or bring all of its predecessors into the
	   patch. */

	/* Figure out which instructions might get clobbered by the
	 * patch */
	std::set<unsigned long> clobbered_by_patch;
	unsigned offset = 0;
	offset += getInstructionSize(oracle->ms->addressSpace, StaticRip(needed));
	while (offset < 5) {
		clobbered_by_patch.insert(needed + offset);
		offset += getInstructionSize(oracle->ms->addressSpace, StaticRip(needed + offset));
	}

	/* Can't use patch if that would clobber an external. */
	bool can_use_patch = true;
	for (auto it = clobbered_by_patch.begin(); can_use_patch && it != clobbered_by_patch.end(); it++) {
		if (oracle->isFunctionHead(StaticRip(*it)))
			can_use_patch = false;
	}
	/* Can't use patch if that would clobber/be clobbered by an
	   existing patch point. */
	for (auto it = input.Patch.begin(); can_use_patch && it != input.Patch.end(); it++) {
		if (needed > *it - 5 && needed < *it + 5)
			can_use_patch = false;
	}

	if (can_use_patch) {
		/* Try using a patch. */
		patchStrategy patched(c);
		patched.Patch.insert(needed);
		for (auto it = clobbered_by_patch.begin();
		     it != clobbered_by_patch.end();
		     it++) {
			std::set<unsigned long> predecessors;
			oracle->findPredecessors(*it, predecessors);
			for (unsigned long y = needed; y < *it; y++)
				predecessors.erase(y);
			patched.Cont.insert(*it);
			patched.MustInterpret.erase(*it);
			patched.MustInterpret.insert(predecessors.begin(), predecessors.end());
		}
		thingsToTry.push(patched);
		if (debug_declobber_instructions) {
			printf("Patch to: ");
			patched.prettyPrint(stdout);
		}
	}

	/* Try expanding to predecessors. */
	std::set<unsigned long> predecessors;
	oracle->findPredecessors(needed, predecessors);
	c.MustInterpret.insert(predecessors.begin(), predecessors.end());
	thingsToTry.push(c);
	if (debug_declobber_instructions) {
		printf("Unpatched: ");
		c.prettyPrint(stdout);
	}
	return false;
}

void
buildPatchStrategy(crashEnforcementData &ced, Oracle *oracle)
{
	patchStrategy currentPs;

	for (auto it = ced.roots.begin(); !it.finished(); it.advance()) {
		Instruction<ThreadCfgLabel> *instr = ced.crashCfg.findInstr(it.threadCfgLabel());
		assert(instr);
		const AbstractThread &absThread(instr->rip.thread);
		ConcreteThread concThread(ced.roots.lookupAbsThread(absThread));
		ConcreteCfgLabel concCfgLabel(concThread.summary(), instr->rip.label);
		const VexRip &vr(ced.crashCfg.labelToRip(concCfgLabel));

		unsigned long r = vr.unwrap_vexrip();
		if (debug_declobber_instructions)
			printf("%lx is a root\n", r);
		if (currentPs.Cont.count(r)) {
			if (debug_declobber_instructions) {
				printf("... but it's already been handled elsewhere\n");
			}
			continue;
		}
		currentPs.MustInterpret.insert(r);
		std::set<patchStrategy> visited;
		patchQueueT pses;
		pses.push(currentPs);
		while (true) {
			if (TIMEOUT) {
				return;
			}
			if (pses.empty()) {
				errx(1, "cannot build patch strategy");
			}
			patchStrategy next(pses.top());
			pses.pop();
			if (!visited.insert(next).second)
				continue;
			if (patchSearch(oracle, next, pses)) {
				/* We have a solution for this entry
				 * point.  Update currentPs and move
				 * on. */
				currentPs = next;
				break;
			}
		}
	}

	ced.patchPoints = currentPs.Patch;
	ced.interpretInstrs = currentPs.Cont;

	/* Minor optimisation: anything within five bytes of a patch
	   point is implicitly cont, so remove them. */
	for (auto it = ced.patchPoints.begin(); it != ced.patchPoints.end(); it++)
		for (unsigned x = 0; x < 5; x++)
			ced.interpretInstrs.erase(*it + x);
}

void
optimiseHBEdges(crashEnforcementData &ced)
{
	/* If an instruction receives a message from thread X then it
	   then binds to thread X and from that point on can only ever
	   send or receive with X.  That allows us to eliminate some
	   message operations. */
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
	     it++) {
		std::set<AbstractThread> mightReceiveFrom;
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			const happensBeforeEdge *hbe = *it2;
			if (hbe->after->rip == it->first)
				mightReceiveFrom.insert(hbe->before->rip.thread);
		}
		if (mightReceiveFrom.empty())
			continue;
		/* Now we know that we've definitely received from one
		   of the threads in @mightReceiveFrom, so we can only
		   send to them.  Kill off any other edges. */
		for (auto it2 = it->second.begin(); it2 != it->second.end(); ) {
			const happensBeforeEdge *hbe = *it2;
			if (hbe->before->rip == it->first &&
			    !mightReceiveFrom.count(hbe->after->rip.thread))
				it->second.erase(it2++);
			else
				it2++;
		}
	}

	/* And now get rid of any messages which are sent but never
	   received or received but never sent. */
	std::set<unsigned> sent;
	std::set<unsigned> received;
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
	     it++) {
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			if ((*it2)->before->rip == it->first)
				sent.insert( (*it2)->msg_id);
			else
				received.insert( (*it2)->msg_id);
		}
	}
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
		) {
		for (auto it2 = it->second.begin(); it2 != it->second.end(); ) {
			unsigned id = (*it2)->msg_id;
			if (!sent.count(id) || !received.count(id))
				it->second.erase(it2++);
			else
				it2++;
		}
		if (it->second.empty())
			ced.happensBeforePoints.erase(it++);
		else
			it++;
	}
}

