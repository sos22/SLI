/* Idea here is to eliminate Phi nodes by replacing them with muxes
 * wherever possible.  Basic approach is to enumerate all paths to the
 * Phi and classify each according to which input that path selects,
 * then look at conditions on the path to try to figure out some
 * discriminant which'll tell us what we need. */
#include <math.h>

#include "sli.h"
#include "state_machine.hpp"
#include "offline_analysis.hpp"
#include "sat_checker.hpp"
#include "control_domination_map.hpp"
#include "allowable_optimisations.hpp"

#ifndef NDEBUG
static bool debug_build_paths = false;
static bool debug_toplevel = false;
static bool debug_simplify = false;
static bool debug_build_mux = false;
#else
#define debug_build_paths false
#define debug_toplevel false
#define debug_simplify false
#define debug_build_mux false
#endif
#define any_debug (debug_build_paths || debug_toplevel || debug_simplify || debug_build_mux)

namespace _phi_elimination {

struct path {
	std::set<IRExpr *> trueExprs;
	std::set<IRExpr *> falseExprs;
	int result; /* an index into the phi's input vector, or -1 if
		     * we don't have one yet. */
	path()
		: result(-1)
	{}
	void prettyPrint(FILE *f) const {
		if (!trueExprs.empty()) {
			fprintf(f, "True: {");
			for (auto it = trueExprs.begin();
			     it != trueExprs.end();
			     it++) {
				if (it != trueExprs.begin())
					fprintf(f, ", ");
				ppIRExpr(*it, f);
			}
			fprintf(f, "}\n");
		}
		if (!falseExprs.empty()) {
			fprintf(f, "False: {");
			for (auto it = falseExprs.begin();
			     it != falseExprs.end();
			     it++) {
				if (it != falseExprs.begin())
					fprintf(f, ", ");
				ppIRExpr(*it, f);
			}
			fprintf(f, "}\n");
		}
		fprintf(f, "Result: %d\n", result);
	}

	/* Return true on success or false if we find a
	 * contradiction. */
	bool addTrue(IRExpr *e, internIRExprTable &table);
	bool addFalse(IRExpr *e, internIRExprTable &table);
};

bool
path::addTrue(IRExpr *e, internIRExprTable &intern)
{
	e = internIRExpr(e, intern);
	if (trueExprs.count(e))
		return true;
	if (falseExprs.count(e))
		return false;
	if (e->tag == Iex_Unop && ((IRExprUnop *)e)->op == Iop_Not1)
		return addFalse(((IRExprUnop *)e)->arg, intern);
	if (e->tag == Iex_Associative &&
	    ((IRExprAssociative *)e)->op == Iop_And1) {
		IRExprAssociative *a = (IRExprAssociative *)e;
		for (int i = 0; i < a->nr_arguments; i++)
			if (!addTrue(a->contents[i], intern))
				return false;
		return true;
	}
	if (e->tag == Iex_EntryPoint) {
		IRExprEntryPoint *iee = (IRExprEntryPoint *)e;
		for (auto it = trueExprs.begin(); it != trueExprs.end(); it++) {
			if ( (*it)->tag != Iex_EntryPoint )
				continue;
			IRExprEntryPoint *other = (IRExprEntryPoint *)*it;
			if (other->thread == iee->thread) {
				assert(other->label != iee->label);
				return false;
			}
		}
	}
	if (e->tag == Iex_ControlFlow) {
		IRExprControlFlow *iec = (IRExprControlFlow *)e;
		for (auto it = trueExprs.begin(); it != trueExprs.end(); it++) {
			if ( (*it)->tag != Iex_ControlFlow )
				continue;
			IRExprControlFlow *other = (IRExprControlFlow *)*it;
			if (other->thread == iec->thread &&
			    other->cfg1 == iec->cfg1) {
				assert(other->cfg2 != iec->cfg2);
				return false;
			}
		}
	}

	trueExprs.insert(e);
	return true;
}

bool
path::addFalse(IRExpr *e, internIRExprTable &intern)
{
	e = internIRExpr(e, intern);
	if (falseExprs.count(e))
		return true;
	if (trueExprs.count(e))
		return false;
	if (e->tag == Iex_Unop && ((IRExprUnop *)e)->op == Iop_Not1)
		return addTrue(((IRExprUnop *)e)->arg, intern);
	if (e->tag == Iex_Associative &&
	    ((IRExprAssociative *)e)->op == Iop_Or1) {
		IRExprAssociative *a = (IRExprAssociative *)e;
		for (int i = 0; i < a->nr_arguments; i++)
			if (!addFalse(a->contents[i], intern))
				return false;
		return true;
	}
	if (e->tag == Iex_EntryPoint) {
		IRExprEntryPoint *iee = (IRExprEntryPoint *)e;
		for (auto it = trueExprs.begin(); it != trueExprs.end(); it++) {
			if ( (*it)->tag != Iex_EntryPoint )
				continue;
			IRExprEntryPoint *other = (IRExprEntryPoint *)*it;
			if (other->thread == iee->thread) {
				assert(other->label != iee->label);
				return true;
			}
		}
	}
	if (e->tag == Iex_ControlFlow) {
		IRExprControlFlow *iec = (IRExprControlFlow *)e;
		for (auto it = trueExprs.begin(); it != trueExprs.end(); it++) {
			if ( (*it)->tag != Iex_ControlFlow )
				continue;
			IRExprControlFlow *other = (IRExprControlFlow *)*it;
			if (other->thread == iec->thread &&
			    other->cfg1 == iec->cfg1) {
				assert(other->cfg2 != iec->cfg2);
				return true;
			}
		}
	}

	falseExprs.insert(e);
	return true;
}

struct path_set {
	path_set()
		: nr_possible_results(-1)
	{}
	std::vector<path> content;
	int nr_possible_results;
	path_set(StateMachine *sm, StateMachineSideEffectPhi *phi,
		 internIRExprTable &intern,
		 std::map<const StateMachineState *, int> &labels);
	void simplify(bool is_canonical);
	IRExpr *build_mux(StateMachineSideEffectPhi *, IRType);
	void prettyPrint(FILE *f) const {
		fprintf(f, "Path set:\n");
		for (auto it = content.begin(); it != content.end(); it++) {
			if (it != content.begin())
				fprintf(f, "--------------------------\n");
			it->prettyPrint(f);
		}
	}
	void case_split(IRExpr *on, path_set *true_out, path_set *false_out);
	void canonicalise(internIRExprTable &intern);
	double entropy() const;
};

path_set::path_set(StateMachine *sm, StateMachineSideEffectPhi *phi,
		   internIRExprTable &intern,
		   std::map<const StateMachineState *, int> &labels)
	: nr_possible_results(phi->generations.size())
{
	std::set<StateMachineState *> mightReachPhi;
	{
		std::vector<StateMachineState *> allStates;
		enumStates(sm, &allStates);
		bool progress = true;
		while (progress) {
			progress = false;
			for (auto it = allStates.begin(); it != allStates.end(); it++) {
				if (mightReachPhi.count(*it))
					continue;
				if ( (*it)->getSideEffect() == phi ) {
					mightReachPhi.insert(*it);
					progress = true;
					continue;
				}
				std::vector<StateMachineState *> targets;
				(*it)->targets(targets);
				for (auto it2 = targets.begin(); it2 != targets.end(); it2++) {
					if (mightReachPhi.count(*it2)) {
						mightReachPhi.insert(*it);
						progress = true;
						break;
					}
				}
			}
		}
	}

	if (debug_build_paths) {
		printf("Phi-reaching states: {");
		for (auto it = mightReachPhi.begin();
		     it != mightReachPhi.end();
		     it++) {
			if (it != mightReachPhi.begin())
				printf(", ");
			printf("l%d", labels[*it]);
		}
		printf("}\n");
	}

	typedef std::pair<StateMachineState *, path> q_entry;
	std::vector<q_entry> queue;
	queue.push_back(q_entry(sm->root, path()));

	/* Do we have a gen -1 entry in the input set? */
	for (unsigned x = 0; x != phi->generations.size(); x++) {
		const threadAndRegister &tr(phi->generations[x].first);
		if (tr.isReg() && tr.gen() == (unsigned)-1 ) {
			/* Yes; that'll be the result at the root and
			   any other path which doesn't assign to one
			   of the input registers. */
			queue.back().second.result = x;
			break;
		}
	}

	while (!queue.empty()) {
		queue.reserve(queue.size() + 1);
		q_entry &entry(queue.back());
		StateMachineState *s = entry.first;
		if (!mightReachPhi.count(s)) {
			queue.pop_back();
			continue;
		}
		if (s->type == StateMachineState::Bifurcate) {
			auto smb = (StateMachineBifurcate *)s;
			IRExpr *cond = internIRExpr(smb->condition, intern);
			queue.push_back(entry);
			/* Continued use of @entry is valid because of
			   queue.reserve() at top of loop. */
			if (entry.second.addTrue(cond, intern)) {
				entry.first = smb->trueTarget;
			} else {
				entry = queue.back();
				queue.pop_back();
			}
			if (queue.back().second.addFalse(cond, intern)) {
				queue.back().first = smb->falseTarget;
			} else {
				queue.pop_back();
			}
		} else if (s->type == StateMachineState::SideEffecting) {
			auto sme = (StateMachineSideEffecting *)s;
			entry.first = sme->target;
			if (!sme->sideEffect)
				continue;
			if (sme->sideEffect == phi) {
				content.push_back(entry.second);
				queue.pop_back();
				if (debug_build_paths) {
					printf("Found a path to l%d:\n", labels[s]);
					content.back().prettyPrint(stdout);
				}
				continue;
			}
			switch (sme->sideEffect->type) {
			case StateMachineSideEffect::Load:
			case StateMachineSideEffect::Store:
				if (!entry.second.addFalse(
					    IRExpr_Unop(
						    Iop_BadPtr,
						    ((StateMachineSideEffectMemoryAccess *)sme->sideEffect)->addr),
					    intern)) {
					queue.pop_back();
/**/					continue;
				}
				break;
			case StateMachineSideEffect::AssertFalse: {
				StateMachineSideEffectAssertFalse *a =
					(StateMachineSideEffectAssertFalse *)sme->sideEffect;
				if (!entry.second.addFalse(a->value, intern)) {
					queue.pop_back();
/**/					continue;
				}
				break;
			}
			case StateMachineSideEffect::Unreached:
				queue.pop_back();
/**/				continue;
			default:
				break;
			}
			threadAndRegister tr(threadAndRegister::invalid());
			if (sme->sideEffect->definesRegister(tr)) {
				for (unsigned x = 0; x < phi->generations.size(); x++) {
					if (phi->generations[x].first == tr) {
						entry.second.result = x;
						break;
					}
				}
			}
		} else {
			assert(s->isTerminal());
			if (debug_build_paths) {
				printf("Found a path which doesn't reach the phi:\n");
				queue.back().second.prettyPrint(stdout);
			}
			queue.pop_back();
		}
	}
}

void
path_set::simplify(bool is_canonical)
{
	if (content.empty())
		return;

	bool progress;
top:
	progress = false;

	/* We're only interested in expressions which are sometimes
	   true and sometimes false.  If the expressions are in
	   canonical form then we can treat not-present as either true
	   or false, but if it's non-canonical we have to treat it as
	   neither. */
	std::set<IRExpr *> alwaysTrue;
	std::set<IRExpr *> alwaysFalse;
	if (!is_canonical) {
		alwaysTrue = content.begin()->trueExprs;
		alwaysFalse = content.begin()->falseExprs;
		for (unsigned x = 1; x < content.size(); x++) {
			path &p(content[x]);
			alwaysTrue &= p.trueExprs;
			alwaysFalse &= p.falseExprs;
		}
	} else {
		std::set<IRExpr *> allExprs;
		for (auto it = content.begin(); it != content.end(); it++) {
			for (auto it2 = it->trueExprs.begin(); it2 != it->trueExprs.end(); it2++)
				allExprs.insert(*it2);
			for (auto it2 = it->falseExprs.begin(); it2 != it->falseExprs.end(); it2++)
				allExprs.insert(*it2);
		}
		alwaysTrue = allExprs;
		alwaysFalse = allExprs;
		for (unsigned x = 0; x < content.size(); x++) {
			path &p(content[x]);
			for (auto it = p.trueExprs.begin(); it != p.trueExprs.end(); it++)
				alwaysFalse.erase(*it);
			for (auto it = p.falseExprs.begin(); it != p.falseExprs.end(); it++)
				alwaysTrue.erase(*it);
		}
	}
	if (!alwaysTrue.empty() || !alwaysFalse.empty()) {
		if (debug_simplify) {
			printf("Always true: {");
			for (auto it = alwaysTrue.begin();
			     it != alwaysTrue.end();
			     it++) {
				if (it != alwaysTrue.begin())
					printf(", ");
				ppIRExpr(*it, stdout);
			}
			printf("}\nAlways false: {");
			for (auto it = alwaysFalse.begin();
			     it != alwaysFalse.end();
			     it++) {
				if (it != alwaysFalse.begin())
					printf(", ");
				ppIRExpr(*it, stdout);
			}
			printf("}\n");
		}
		for (auto it = content.begin(); it != content.end(); it++) {
			for (auto it2 = alwaysTrue.begin(); it2 != alwaysTrue.end(); it2++)
				progress |= it->trueExprs.erase(*it2);
			for (auto it2 = alwaysFalse.begin(); it2 != alwaysFalse.end(); it2++)
				progress |= it->falseExprs.erase(*it2);
		}
		if (debug_simplify) {
			printf("After elimination of always terms:\n");
			prettyPrint(stdout);
		}
	}

	/* If a term T only appears in paths whose result is N then it
	   doesn't help us very much. */
	std::map<IRExpr *, std::set<int> > appearsWithResult;
	for (auto it = content.begin(); it != content.end(); it++) {
		for (auto it2 = it->trueExprs.begin(); it2 != it->trueExprs.end(); it2++)
			appearsWithResult[*it2].insert(it->result);
		for (auto it2 = it->falseExprs.begin(); it2 != it->falseExprs.end(); it2++)
			appearsWithResult[*it2].insert(it->result);
	}
	std::set<IRExpr *> constantResult;
	for (auto it = appearsWithResult.begin(); it != appearsWithResult.end(); it++)
		if (it->second.size() == 1)
			constantResult.insert(it->first);
	if (!constantResult.empty()) {
		if (debug_simplify) {
			printf("Constant result: {");
			for (auto it = constantResult.begin();
			     it != constantResult.end();
			     it++) {
				if (it != constantResult.begin())
					printf(", ");
				ppIRExpr(*it, stdout);
			}
			printf("}\n");
		}
		for (auto it = content.begin(); it != content.end(); it++) {
			for (auto it2 = alwaysTrue.begin(); it2 != alwaysTrue.end(); it2++)
				progress |= it->trueExprs.erase(*it2);
			for (auto it2 = alwaysFalse.begin(); it2 != alwaysFalse.end(); it2++)
				progress |= it->falseExprs.erase(*it2);
		}
		if (debug_simplify) {
			printf("After elimination of constant-result terms:\n");
			prettyPrint(stdout);
		}
	}

	/* Don't care about any terms T such that for every path P
	   where T is true there is another path P' which is identical
	   to P except for flipping the sense of T. */
	for (unsigned it1 = 0; it1 < content.size(); it1++) {
		const path &path1(content[it1]);
		for (unsigned it2 = it1 + 1; it2 < content.size(); it2++) {
			const path &path2(content[it2]);
			if (path2.result != path1.result)
				continue;
			/* Eliminate dupes while we're here */
			if (path1.falseExprs.size() == path2.falseExprs.size() &&
			    path1.trueExprs == path2.trueExprs &&
			    path1.falseExprs == path2.falseExprs) {
				if (debug_simplify) {
					printf("Eliminate dupe:\n");
					path1.prettyPrint(stdout);
				}
				content.erase(content.begin() + it2);
				it2--;
				progress = true;
				continue;
			}

			/* Do a quick check on size first, since that's fast. */
			bool trueToFalse;
			if (path2.trueExprs.size() == path1.trueExprs.size() + 1 &&
			    path2.falseExprs.size() == path1.falseExprs.size() - 1)
				trueToFalse = false;
			else if (path2.trueExprs.size() == path1.trueExprs.size() - 1 &&
				   path2.falseExprs.size() == path1.falseExprs.size() + 1)
				trueToFalse = true;
			else
				continue;
			/* Sizes match, make sure that it really is a
			   transfer of the desired type. */
			IRExpr *movedExpr = NULL;
			bool failed = false;
			if (trueToFalse) {
				for (auto it = path1.trueExprs.begin();
				     !failed && it != path1.trueExprs.end();
				     it++) {
					if (!path2.trueExprs.count(*it)) {
						if (movedExpr ||
						    !path2.falseExprs.count(*it))
							failed = true;
						else
							movedExpr = *it;
					}
				}
				assert(failed || movedExpr);
				for (auto it = path1.falseExprs.begin();
				     !failed && it != path1.falseExprs.end();
				     it++) {
					if (!path2.falseExprs.count(*it))
						failed = true;
				}
			} else {
				for (auto it = path1.falseExprs.begin();
				     !failed && it != path1.falseExprs.end();
				     it++) {
					if (!path2.falseExprs.count(*it)) {
						if (movedExpr ||
						    !path2.trueExprs.count(*it))
							failed = true;
						else
							movedExpr = *it;
					}
				}
				assert(failed || movedExpr);
				for (auto it = path1.trueExprs.begin();
				     !failed && it != path1.trueExprs.end();
				     it++) {
					if (!path2.trueExprs.count(*it))
						failed = true;
				}
			}
			if (!failed) {
				assert(movedExpr != NULL);
				if (debug_simplify) {
					printf("Merge paths on %s:\n", nameIRExpr(movedExpr));
					path1.prettyPrint(stdout);
					printf("<---->\n");
					path2.prettyPrint(stdout);
				}
				content.erase(content.begin() + it2);
				it2--;
				progress = true;
			}
		}
	}

	if (debug_simplify) {
		printf("After elimination of similar terms:\n");
		prettyPrint(stdout);
	}

	if (progress) {
		if (debug_simplify)
			printf("Made progress, going around again\n");
		goto top;
	}
		
}

/* Some of the simplifications get confused if the things in the
   expression set aren't units i.e. if there are (x || y) expressions
   in a trueExpr set or (x && y) expressions in a falseExpr set.
   Remove them now. */
void
path_set::canonicalise(internIRExprTable &intern)
{
	for (unsigned idx = 0; idx < content.size(); idx++) {
	retry:
		for (auto it = content[idx].trueExprs.begin(); it != content[idx].trueExprs.end(); it++) {
			if ( (*it)->tag != Iex_Associative )
				continue;
			IRExprAssociative *e = (IRExprAssociative *)*it;
			assert(e->op == Iop_Or1);
			path newP(content[idx]);
			newP.trueExprs.erase(e);
			content.resize(content.size() + e->nr_arguments - 1,
				       newP);
			content[idx] = newP;
			content[idx].addTrue(e->contents[0], intern);
			for (int y = 1; y < e->nr_arguments; y++)
				content[content.size() - e->nr_arguments + y].addTrue(e->contents[y], intern);
			goto retry;
		}
		for (auto it = content[idx].falseExprs.begin(); it != content[idx].falseExprs.end(); it++) {
			if ( (*it)->tag != Iex_Associative )
				continue;
			IRExprAssociative *e = (IRExprAssociative *)*it;
			assert(e->op == Iop_And1);
			path newP(content[idx]);
			newP.falseExprs.erase(e);
			content.resize(content.size() + e->nr_arguments - 1,
				       newP);
			content[idx] = newP;
			content[idx].addFalse(e->contents[0], intern);
			for (int y = 1; y < e->nr_arguments; y++)
				content[content.size() - e->nr_arguments + y].addFalse(e->contents[y], intern);
			goto retry;
		}
	}
}

void
path_set::case_split(IRExpr *on, path_set *true_out, path_set *false_out)
{
	true_out->nr_possible_results = nr_possible_results;
	false_out->nr_possible_results = nr_possible_results;
	for (auto it = content.begin(); it != content.end(); it++) {
		if (!it->falseExprs.count(on))
			true_out->content.push_back(*it);
		if (!it->trueExprs.count(on))
			false_out->content.push_back(*it);
	}
	true_out->simplify(true);
	false_out->simplify(true);
}

/* Assume each input variable is independently distributed with a 50%
   chance of being either true or false.  What is the entropy of the
   result of this path set? */   
double
path_set::entropy() const
{
	std::vector<double> prob_of_result;
	double norm = 0;
	prob_of_result.resize(nr_possible_results, 0);
	for (auto it = content.begin(); it != content.end(); it++) {
		assert(it->result >= 0);
		assert(it->result < nr_possible_results);
		double p = pow(0.5, it->trueExprs.size() + it->falseExprs.size());
		prob_of_result[it->result] += p;
		norm += p;
	}
	double acc = 0;
	for (auto it = prob_of_result.begin(); it != prob_of_result.end(); it++) {
		/* zero times log(0) is zero for our purposes, but
		   not in IEEE arithmetic. */
		if (*it == 0)
			continue;
		*it /= norm;
		acc += *it * log(*it);
	}
	return -acc;
}


IRExpr *
path_set::build_mux(StateMachineSideEffectPhi *phi, IRType ty)
{
	if (debug_build_mux) {
		printf("Build mux for ");
		prettyPrint(stdout);
	}

	/* Easy case: if all of the paths produce the same result,
	   that's the answer. */
	assert(!content.empty());
	int result = -2;
	for (auto it = content.begin(); it != content.end(); it++) {
		if (result == -2) {
			result = it->result;
		} else if (result != it->result) {
			result = -3;
		}
	}
	assert(result != -2);
	assert(result != -1);
	if (result != -3) {
		assert(result >= 0);
		assert(result < (int)phi->generations.size());
		/* Everything is the same -> we're done */
		if (debug_build_mux)
			printf("Trivial, result is %d\n", result);
		if (phi->generations[result].second)
			return phi->generations[result].second;
		else
			return IRExpr_Get(phi->generations[result].first, ty);
	}
	std::set<IRExpr *> allExprs;
	for (auto it = content.begin(); it != content.end(); it++) {
		for (auto it2 = it->trueExprs.begin(); it2 != it->trueExprs.end(); it2++)
			allExprs.insert(*it2);
		for (auto it2 = it->falseExprs.begin(); it2 != it->falseExprs.end(); it2++)
			allExprs.insert(*it2);
	}
	/* Now we need to do a case split on one of the inputs.  We
	 * try to pick the one which gives the biggest decrease in
	 * entropy of the final result. */
	while (!allExprs.empty()) {
		IRExpr *best_split = NULL;
		path_set best_t;
		path_set best_f;
		double best_entropy;
		for (auto it = allExprs.begin(); it != allExprs.end(); it++) {
			path_set t, f;
			case_split(*it, &t, &f);
			double entropy = t.entropy() + f.entropy();
			if (best_split == NULL || entropy < best_entropy) {
				best_entropy = entropy;
				best_t = t;
				best_f = f;
				best_split = *it;
			}
		}
		assert(best_split != NULL);
		if (debug_build_mux)
			printf("Try split on %s, entropy %f\n", nameIRExpr(best_split), best_entropy);
		IRExpr *trueExpr = best_t.build_mux(phi, ty);
		IRExpr *falseExpr = trueExpr ? best_f.build_mux(phi, ty) : NULL;
		if (!falseExpr) {
			if (debug_build_mux)
				printf("Failed to build %s sub-condition, go around again\n",
				       trueExpr ? "false" : "true");
			for (auto it = allExprs.begin(); it != allExprs.end(); ) {
				IRExpr *e;
				e = *it;
				allExprs.erase(it++);
				if (e == best_split)
					break;
			}
			continue;
		}
		IRExpr *res = IRExpr_Mux0X(best_split, falseExpr, trueExpr);
		if (debug_build_mux)
			printf("Result %s\n", nameIRExpr(res));
		return res;
	}
	/* Not enough information to disambiguate -> give up */
	if (debug_build_mux)
		printf("Impossible.\n");
	return NULL;
}

static StateMachine *
replaceSideEffects(StateMachine *sm, std::map<StateMachineSideEffect *, StateMachineSideEffect *> &rewrites)
{
	struct : public StateMachineTransformer {
		std::map<StateMachineSideEffect *, StateMachineSideEffect *> *rewrites;
		StateMachineSideEffecting *transformOneState(StateMachineSideEffecting *smse,
							     bool *done_something)
		{
			if (!smse->sideEffect)
				return NULL;
			auto it = rewrites->find(smse->sideEffect);
			if (it == rewrites->end())
				return NULL;
			*done_something = true;
			return new StateMachineSideEffecting(smse, it->second);
		}
		bool rewriteNewStates() const { return true; }
	} doit;
	doit.rewrites = &rewrites;
	return doit.transform(sm);
}

static StateMachine *
phiElimination(StateMachine *sm, bool *done_something)
{
	std::map<const StateMachineState *, int> labels;

	if (any_debug) {
		printf("phiElimination:\n");
		printStateMachine(sm, stdout, labels);
	}

	std::map<StateMachineSideEffect *, StateMachineSideEffect *> replacements;

	std::set<StateMachineSideEffectPhi *> phiEffects;
	internIRExprTable intern;
	enumSideEffects(sm, phiEffects);
	for (auto it = phiEffects.begin(); !TIMEOUT && it != phiEffects.end(); it++) {
		StateMachineSideEffectPhi *phi = *it;

		if (debug_toplevel) {
			printf("Consider side effect ");
			phi->prettyPrint(stdout);
			printf("\n");
		}
		IRType ity = Ity_INVALID;
		for (auto it = phi->generations.begin(); ity == Ity_INVALID && it != phi->generations.end(); it++) {
			if (it->second)
				ity = it->second->type();
		}
		if (ity == Ity_INVALID) {
			if (debug_toplevel)
				printf("Failed: unknown type\n");
			continue;
		}
		path_set paths(sm, phi, intern, labels);
		if (TIMEOUT)
			break;
		paths.simplify(false);
		paths.canonicalise(intern);
		paths.simplify(true);
		IRExpr *e = paths.build_mux(phi, ity);
		if (e) {
			if (debug_toplevel)
				printf("Replace side effect with %s\n", nameIRExpr(e));
			replacements[phi] = new StateMachineSideEffectCopy(
				phi->reg, e);
		} else {
			if (debug_toplevel)
				printf("Failed to build mux expression\n");
		}
	}

	if (replacements.empty()) {
		if (debug_toplevel)
			printf("Nothing to do\n");
		return sm;
	}
	if (debug_toplevel) {
		printf("Replacements:\n");
		for (auto it = replacements.begin(); it != replacements.end(); it++) {
			it->first->prettyPrint(stdout);
			printf("\t--->\t");
			it->second->prettyPrint(stdout);
			printf("\n");
		}
	}
	*done_something = true;
	return replaceSideEffects(sm, replacements);
}

/* End of namespace */
};

StateMachine *
phiElimination(StateMachine *sm, bool *done_something)
{
	return _phi_elimination::phiElimination(sm, done_something);
}
