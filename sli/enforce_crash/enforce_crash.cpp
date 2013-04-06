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
#include "reorder_bdd.hpp"

extern FILE *bubble_plot_log;

#ifndef NDEBUG
static bool debug_expr_slice = false;
#else
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

struct expr_slice {
	std::set<const IRExprHappensBefore *> trueSlice;
	std::set<const IRExprHappensBefore *> falseSlice;
	const reorder_bbdd *leftOver;

	expr_slice(const std::set<const IRExprHappensBefore *> &_trueSlice,
		   const std::set<const IRExprHappensBefore *> &_falseSlice,
		   const reorder_bbdd *_leftOver)
		: trueSlice(_trueSlice), falseSlice(_falseSlice),
		  leftOver(_leftOver)
	{}

	bool operator<(const expr_slice &o) const {
		if (leftOver < o.leftOver) {
			return true;
		} else if (leftOver > o.leftOver) {
			return false;
		} else if (trueSlice < o.trueSlice) {
			return true;
		} else if (trueSlice > o.trueSlice) {
			return false;
		} else {
			return falseSlice < o.falseSlice;
		}
	}

	bool simplifyAndCheckForContradiction();
};

bool
expr_slice::simplifyAndCheckForContradiction()
{
	if (leftOver->isLeaf && !leftOver->leaf) {
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
	fprintf(bubble_plot_log, "%f: start determine input availability\n", now());
	std::set<input_expression> neededExpressions;
	enumerateNeededExpressions(c.leftOver, neededExpressions);
	fprintf(bubble_plot_log, "%f: stop determine input availability\n", now());

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
	if (TIMEOUT) {
		return false;
	}
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
	for (auto it = slice.falseSlice.begin(); it != slice.falseSlice.end(); it++) {
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
				case Iex_Associative: {
					auto l = (IRExprAssociative *)ieb->arg1;
					auto r = (IRExprAssociative *)ieb->arg2;
					if (l->op != r->op ||
					    l->nr_arguments != r->nr_arguments ||
					    l->nr_arguments != 2 ||
					    l->contents[0]->tag != Iex_Const ||
					    l->contents[0] != r->contents[0]) {
						break;
					}
					IRExprConst *c = (IRExprConst *)l->contents[0];
					switch (l->op) {
					case Iop_Mul64:
						/* Multiplication by a
						   small constant
						   doesn't usually
						   overflow. */
						if (c->Ico.content.U64 >= 1024)
							break;
						ieb = IRExprBinop::mk(ieb->op, l->contents[1], r->contents[1]);
						goto retry;
					default:
						break;
					}
					break;
				}

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
					bbdd::var(scope, cond, bdd_ordering::rank_hint::Near(e)),
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

class only_hb_evaluatable : public reorder_evaluatable {
public:
	bool operator()(IRExpr *const &ex) const {
		return ex->tag == Iex_HappensBefore;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "HB only");
	}
};

template <typename t> static void
print_expr_set(FILE *f, const std::set<t *> &what)
{
	fprintf(f, "{");
	for (auto it = what.begin(); it != what.end(); it++) {
		if (it != what.begin()) {
			fprintf(f, ", ");
		}
		ppIRExpr(*it, f);
	}
	fprintf(f, "}");
}

static void
enumHbOrderings(const reorder_bbdd *what,
		const std::set<const IRExprHappensBefore *> &trueExprs,
		const std::set<const IRExprHappensBefore *> &falseExprs,
		std::set<expr_slice> &acc)
{
	if (TIMEOUT) {
		return;
	}
	if (what->isLeaf || !what->cond.evaluatable) {
		if (debug_expr_slice) {
			printf("Found an HB ordering.  True: ");
			print_expr_set(stdout, trueExprs);
			printf(", False: ");
			print_expr_set(stdout, falseExprs);
			printf("\nLeftover:\n");
			pp_reorder(what);
		}

		expr_slice candidate(trueExprs, falseExprs, what);
		if (candidate.simplifyAndCheckForContradiction()) {
			return;
		}
		if (consistentOrdering(candidate)) {
			if (debug_expr_slice) {
				printf("Consistent ordering -> reject\n");
			}
			return;
		}
		if (debug_expr_slice) {
			printf("Accept\n");
		}
		acc.insert(expr_slice(trueExprs, falseExprs, what));
		return;
	}
	assert(what->cond.cond->tag == Iex_HappensBefore);
	std::set<const IRExprHappensBefore *> aT(trueExprs);
	aT.insert((IRExprHappensBefore *)what->cond.cond);
	enumHbOrderings(what->trueBranch, aT, falseExprs, acc);

	std::set<const IRExprHappensBefore *> aF(falseExprs);
	aF.insert((IRExprHappensBefore *)what->cond.cond);
	enumHbOrderings(what->falseBranch, trueExprs, aF, acc);
}

static void
slice_by_hb(bbdd *expr, std::set<expr_slice> &out)
{
	only_hb_evaluatable ohb;
	auto r_expr = reorder_bbdd::from_bbdd(expr, ohb);
	if (debug_expr_slice) {
		printf("slice_by_hb; expression:\n");
		pp_reorder(r_expr);
	}

	std::set<const IRExprHappensBefore *> empty;
	enumHbOrderings(r_expr, empty, empty, out);

	if (debug_expr_slice) {
		std::map<const reorder_bbdd *, std::set<expr_slice> > inverted;
		for (auto it = out.begin(); it != out.end(); it++) {
			inverted[it->leftOver].insert(*it);
		}

		for (auto it = inverted.begin(); it != inverted.end(); it++) {
			if (it != inverted.begin()) {
				printf("------------------------\n");
			}
			printf("Leftover:\n");
			pp_reorder(it->first);
			printf("Options:\n");
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				printf("\tTrue: ");
				print_expr_set(stdout, it2->trueSlice);
				printf("; False: ");
				print_expr_set(stdout, it2->falseSlice);
				printf("\n");
			}
		}
	}
}

crashEnforcementData
enforceCrashForMachine(const SummaryId &summaryId,
		       VexPtr<CrashSummary, &ir_heap> summary,
		       VexPtr<Oracle> &oracle,
		       ThreadAbstracter &abs,
		       int &next_hb_id)
{
	fprintf(bubble_plot_log, "%f: start prepare summary\n", now());
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

	{
		std::map<bbdd *, bbdd *> memo;
		requirement = heuristicSimplify(&summary->scopes->bools, requirement, memo);
	}

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

	fprintf(_logfile, "After free variable removal:\n");
	requirement->prettyPrint(_logfile);
	fprintf(_logfile, "\n");
	if (TIMEOUT) {
		fprintf(_logfile, "Killed by a timeout during simplification\n");
		exit(1);
	}

	fprintf(bubble_plot_log, "%f: stop prepare summary\n", now());
	fprintf(bubble_plot_log, "%f: start slice by hb\n", now());
	std::set<expr_slice> sliced_by_hb;
	{
		TimeoutTimer tmr;
		tmr.timeoutAfterSeconds(60);
		slice_by_hb(requirement, sliced_by_hb);
		tmr.cancel();
	}
	fprintf(bubble_plot_log, "%f: stop slice by hb\n", now());

	if (TIMEOUT) {
		fprintf(bubble_plot_log, "%f: failed slice by hb\n", now());
		return crashEnforcementData();
	}

	crashEnforcementData accumulator;
	for (auto it = sliced_by_hb.begin(); !TIMEOUT && it != sliced_by_hb.end(); it++) {
		crashEnforcementData tmp;
		if (buildCED(summaryId, *it, rootsCfg, summary, &tmp, abs, next_hb_id, oracle->ms->addressSpace)) {
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

