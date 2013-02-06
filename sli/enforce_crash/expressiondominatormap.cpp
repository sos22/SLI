#include "sli.h"
#include "enforce_crash.hpp"

#ifndef NDEBUG
static bool debug_edm = false;
#else
#define debug_edm false
#endif

static bool
evaluatable(const IRExpr *e, const std::set<input_expression> &availExprs)
{
	struct foo {
		static visit_result Get(const std::set<input_expression> *state,
					const IRExprGet *ieg)
		{
			if (state->count(input_expression::registr(ieg))) {
				return visit_continue;
			} else {
				return visit_abort;
			}
		}
		static visit_result EntryPoint(const std::set<input_expression> *state,
					       const IRExprEntryPoint *ieg)
		{
			if (state->count(input_expression::entry_point(ieg))) {
				return visit_continue;
			} else {
				return visit_abort;
			}
		}
		static visit_result ControlFlow(const std::set<input_expression> *state,
						const IRExprControlFlow *ieg)
		{
			if (state->count(input_expression::control_flow(ieg))) {
				return visit_continue;
			} else {
				return visit_abort;
			}
		}
		static visit_result HappensBefore(const std::set<input_expression> *state,
						  const IRExprHappensBefore *ieg)
		{
			if (state->count(input_expression::happens_before(ieg))) {
				return visit_continue;
			} else {
				return visit_abort;
			}
		}
	};
	static irexpr_visitor<const std::set<input_expression> > visitor;
	visitor.Get = foo::Get;
	visitor.EntryPoint = foo::EntryPoint;
	visitor.ControlFlow = foo::ControlFlow;
	visitor.HappensBefore = foo::HappensBefore;
	return visit_irexpr(&availExprs, &visitor, e) == visit_continue;
}

expressionDominatorMapT::expressionDominatorMapT(DNF_Conjunction &c,
						 expressionStashMapT &stash,
						 instructionDominatorMapT &idom,
						 predecessorMapT &pred,
						 happensAfterMapT &happensBefore)
{
	if (debug_edm) {
		printf("Build expression dominator map.\n");
		printf("Conjunction: ");
		c.prettyPrint(stdout, " || ");
	}

	/* First, figure out where the various expressions could in
	   principle be evaluated. */
	expressionDominatorMapT evalable;
	for (instructionDominatorMapT::iterator it = idom.begin();
	     it != idom.end();
	     it++) {
		evalable[it->first].clear();
		std::set<input_expression> availExprs;
		for (auto it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			Instruction<ThreadCfgLabel> *dominating = *it2;
			const std::set<input_expression> &stashed(stash[dominating->rip]);
			for (auto it = stashed.begin();
			     it != stashed.end();
			     it++)
				availExprs.insert(*it);
		}
		if (debug_edm) {
			printf("\nAvailable at %s: ", it->first->label.name());
			for (auto it = availExprs.begin();
			     it != availExprs.end();
			     it++) {
				if (it != availExprs.begin()) {
					printf(", ");
				}
				printf("%s", it->name());
			}
			printf("\n");
		}
		for (unsigned x = 0; x < c.size(); x++) {
			if (evaluatable(c[x].second, availExprs)) {
				if (debug_edm) {
					printf("%s -> evalable\n", nameIRExpr(c[x].second));
				}
				evalable[it->first].insert(c[x]);
			} else {
				if (debug_edm) {
					printf("%s -> not evalable\n", nameIRExpr(c[x].second));
				}
			}
		}
	}

	if (debug_edm) {
		printf("evalable map:\n");
		for (auto it = evalable.begin();
		     it != evalable.end();
		     it++) {
			printf("%s -> ", it->first->label.name());
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				if (it2 != it->second.begin()) {
					printf(", ");
				}
				printf("%s (%s)",
				       nameIRExpr(it2->second),
				       it2->first ? "true" : "false");
			}
			printf("\n");
		}
	}

	/* Just find all of the things which are evaluatable at X but
	   not at some of X's predecessors, for any instruction X.  I'm
	   not entirely convinced that that's *precisely* what we're
	   after, but it's a pretty reasonable approximation. */
	for (auto it = evalable.begin();
	     it != evalable.end();
	     it++) {
		auto i = it->first;
		std::set<std::pair<bool, IRExpr *> > &theoreticallyEvaluatable(evalable[i]);
		std::set<std::pair<bool, IRExpr *> > &actuallyEvalHere((*this)[i]);
		std::set<Instruction<ThreadCfgLabel> *> &predecessors(pred[i]);
		std::set<Instruction<ThreadCfgLabel> *> *orderingPredecessors = NULL;

		if (happensBefore.happensBefore.count(i))
			orderingPredecessors = &happensBefore.happensBefore[i];
		for (std::set<std::pair<bool, IRExpr *> >::iterator it2 = theoreticallyEvaluatable.begin();
		     it2 != theoreticallyEvaluatable.end();
		     it2++) {
			bool takeIt = false;
			for (auto it3 = predecessors.begin();
			     !takeIt && it3 != predecessors.end();
			     it3++) {
				auto *predecessor = *it3;
				if (!evalable[predecessor].count(*it2))
					takeIt = true;
			}
			if (predecessors.empty())
				takeIt = true;
			/* If it's evaluatable at *any* happens-before
			   predecessor then we don't want to take it,
			   because happens-before edges are always
			   satisfied and it's therefore certain that
			   it will have already been evaluated. */
			if (takeIt && orderingPredecessors) {
				for (auto it3 = orderingPredecessors->begin();
				     takeIt && it3 != orderingPredecessors->end();
				     it3++) {
					if (evalable[*it3].count(*it2))
						takeIt = false;
				}
			}
			if (takeIt) {
				printf("Eval ");
				ppIRExpr(it2->second, stdout);
				printf(" at %s\n", i->rip.name());
				actuallyEvalHere.insert(*it2);
			}
		}
	}
}

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

void
expressionDominatorMapT::prettyPrint(FILE *f) const
{
	for (auto it = begin(); it != end(); it++) {
		fprintf(f, "%s -> {", it->first->label.name());
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			if (it2->first)
				fprintf(f, "!");
			ppIRExpr(it2->second, f);
		}
		fprintf(f, "}\n");
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
