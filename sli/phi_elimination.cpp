/* Idea here is to eliminate Phi nodes by replacing them with muxes
 * wherever possible.  Basic approach is to enumerate all paths to the
 * Phi and classify each according to which input that path selects,
 * then look at conditions on the path to try to figure out some
 * discriminant which'll tell us what we need. */
#include <math.h>

#include "sli.h"
#include "state_machine.hpp"
#include "offline_analysis.hpp"
#include "bdd.hpp"

#ifndef NDEBUG
static bool debug_build_paths = false;
static bool debug_control_dependence = false;
static bool debug_toplevel = false;
#else
#define debug_build_paths false
#define debug_control_dependence false
#define debug_toplevel false
#endif

namespace _phi_elimination {

class predecessor_map {
	std::map<StateMachineState *, std::set<StateMachineState *> > content;
public:
	predecessor_map(StateMachine *sm);
	void getPredecessors(StateMachineState *s, std::vector<StateMachineState *> &out) const {
		auto i = content.find(s);
		assert(i != content.end());
		out.insert(out.end(), i->second.begin(), i->second.end());
	}
};

predecessor_map::predecessor_map(StateMachine *sm)
{
	std::set<StateMachineState *> s;
	enumStates(sm, &s);
	for (auto it = s.begin(); it != s.end(); it++) {
		std::vector<StateMachineState *> ss;
		(*it)->targets(ss);
		for (auto it2 = ss.begin(); it2 != ss.end(); it2++)
			content[*it2].insert(*it);
	}
}

class control_dependence_graph {
	std::map<StateMachineState *, bbdd *> content;
public:
	control_dependence_graph(StateMachine *sm, bbdd_scope *scope,
				 std::map<const StateMachineState *, int> &labels);
	bbdd *domOf(StateMachineState *s) const {
		auto i = content.find(s);
		assert(i != content.end());
		return i->second;
	}
	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const;
};

control_dependence_graph::control_dependence_graph(StateMachine *sm,
						   bbdd_scope *scope,
						   std::map<const StateMachineState *, int> &labels)
{
	content[sm->root] = bbdd::cnst(true);
	std::vector<StateMachineState *> pending;
	pending.push_back(sm->root);

	struct {
		std::vector<StateMachineState *> *pending;
		bbdd_scope *scope;
		void operator()(bbdd *&slot,
				bbdd *newPath,
				StateMachineState *owner) {
			if (slot) {
				bbdd *n = bbdd::Or(scope, slot, newPath);
				if (n != slot)
					pending->push_back(owner);
				slot = n;
			} else {
				slot = newPath;
				pending->push_back(owner);
			}
		}
	} addPath;
#warning this would work better with a consistent advance structure rather than a fixed point iteration.
	addPath.pending = &pending;
	addPath.scope = scope;
	while (!pending.empty()) {
		StateMachineState *s = pending.back();
		pending.pop_back();
		bbdd *dom = content[s];
		assert(dom);
		if (debug_control_dependence) {
			printf("Redo control dependence of state l%d; current = \n", labels[s]);
			dom->prettyPrint(stdout);
		}
		switch (s->type) {
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
			bbdd *cond = bbdd::var(scope, smb->condition);
			bbdd *trueCond = bbdd::And(scope, dom, cond);
			bbdd *falseCond = bbdd::And(scope, dom, bbdd::invert(scope, cond));
			addPath(content[smb->trueTarget],
				trueCond,
				smb->trueTarget);
			addPath(content[smb->falseTarget],
				falseCond,
				smb->falseTarget);
			if (debug_control_dependence) {
				printf("Convert %s to BBDD ->\n", nameIRExpr(smb->condition));
				cond->prettyPrint(stdout);
				printf("Combine with dom constraint\n");
				dom->prettyPrint(stdout);
				printf("-> true\n");
				trueCond->prettyPrint(stdout);
				printf("-> false\n");
				falseCond->prettyPrint(stdout);

				printf("Update l%d to:\n", labels[smb->trueTarget]);
				content[smb->trueTarget]->prettyPrint(stdout);
				printf("Update l%d to:\n", labels[smb->falseTarget]);
				content[smb->falseTarget]->prettyPrint(stdout);
			}
			break;
		}
		case StateMachineState::SideEffecting: {
			StateMachineSideEffecting *sme = (StateMachineSideEffecting *)s;
			addPath(content[sme->target],
				dom,
				sme->target);
			if (debug_control_dependence) {
				printf("Update l%d to:\n", labels[sme->target]);
				content[sme->target]->prettyPrint(stdout);
			}
			break;
		}
		case StateMachineState::Terminal:
			break;
		}
	}
}

void
control_dependence_graph::prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const
{
	fprintf(f, "CDG:\n");
	for (auto it = content.begin(); it != content.end(); it++) {
		fprintf(f, "l%d:\n", labels[it->first]);
		it->second->prettyPrint(f);
	}
}

static intbdd *
build_selection_bdd(StateMachine *sm,
		    StateMachineSideEffectPhi *phi,
		    std::map<const StateMachineState *, int> &labels,
		    std::map<unsigned, unsigned> &canonResult,
		    intbdd_scope *iscope)
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

	std::set<StateMachineSideEffecting *> sideEffecting;
	enumStates(sm, &sideEffecting);

	bbdd_scope scope;
	predecessor_map pm(sm);
	control_dependence_graph cdg(sm, &scope, labels);

	if (debug_build_paths)
		cdg.prettyPrint(stdout, labels);

	/* Map from states to an intbdd which provides the result if
	   we issue the phi immediately after that state. */
	std::map<StateMachineState *, intbdd *> m;

	/* States whose success entries in @m might need updating */
	std::queue<StateMachineState *> toUpdate;

	/* Set up initial map */
	for (unsigned x = 0; x < phi->generations.size(); x++) {
		const threadAndRegister &tr(phi->generations[x].reg);
		if (tr.isReg() && tr.gen() == (unsigned)-1 ) {
			/* gen -1; that'll be the result at the root
			   and any other path which doesn't assign to
			   one of the input registers. */
			m[sm->root] = intbdd::cnst(iscope, canonResult[x]);
			toUpdate.push(sm->root);
			break;
		} else {
			/* Non-gen -1; need to plop this in at all of
			   the places which define this register. */
			bool found = false;
			for (auto it2 = sideEffecting.begin();
			     it2 != sideEffecting.end();
			     it2++) {
				StateMachineSideEffect *sr = (*it2)->sideEffect;
				if (!sr)
					continue;
				threadAndRegister def(threadAndRegister::invalid());
				if (sr->definesRegister(def) && def == tr) {
					assert(!m.count(*it2));
					m[*it2] = intbdd::cnst(iscope, canonResult[x]);
					toUpdate.push(*it2);
					found = true;
				}
			}
		}
	}

	if (debug_build_paths) {
		printf("Initial map:\n");
		for (auto it = m.begin(); it != m.end(); it++) {
			printf("l%d: ", labels[it->first]);
			it->second->prettyPrint(stdout);
		}
	}

	/* Expand the map to get the final result. */
	while (!toUpdate.empty()) {
		StateMachineState *s = toUpdate.front();
		toUpdate.pop();
		assert(m.count(s));

		if (debug_build_paths) {
			printf("Extend from l%d\n", labels[s]);
			m[s]->prettyPrint(stdout);
		}

		std::vector<StateMachineState *> ss;
		s->targets(ss);
		for (auto it = ss.begin();
		     it != ss.end();
		     it++) {
			StateMachineState *state = *it;
			if (!mightReachPhi.count(state) || m.count(state))
				continue;
			if (debug_build_paths)
				printf("Consider extending to l%d\n", labels[state]);
			std::vector<StateMachineState *> pred;
			pm.getPredecessors(state, pred);
			assert(!pred.empty());
			bool missing = false;
			for (auto it2 = pred.begin(); !missing && it2 != pred.end(); it2++) {
				if (!m.count(*it2)) {
					if (debug_build_paths)
						printf("No extend; predecessor l%d missing\n",
						       labels[*it2]);
					missing = true;
				}
			}
			if (missing)
				continue;
			std::map<bbdd *, intbdd *> enabling;
			bbdd *assumption = cdg.domOf(state);
			bool failed = false;
			for (auto it = pred.begin(); !failed && it != pred.end(); it++) {
				bbdd *condition = bbdd::assume(&scope, cdg.domOf(*it), assumption);
				intbdd *res = intbdd::assume(iscope, m[*it], assumption);
#warning Should be more cunning if the predecessor state is a bifurcate
				if (enabling.count(condition) && enabling[condition] != res) {
					failed = true;
				} else {
					enabling[condition] = res;
				}
			}
			if (failed) {
				if (debug_build_paths)
					printf("Failed to build initial enabling table\n");
				return NULL;
			}
			if (debug_build_paths) {
				printf("Enabling table:\n");
				for (auto it = enabling.begin();
				     it != enabling.end();
				     it++) {
					if (it != enabling.begin())
						printf("------------------\n");
					printf("Cond:\n");
					it->first->prettyPrint(stdout);
					printf("Result:\n");
					it->second->prettyPrint(stdout);
				}
			}
			intbdd *flattened = intbdd::from_enabling(iscope, enabling);
			if (!flattened) {
				if (debug_build_paths)
					printf("Failed to flatten enabling table\n");
				return NULL;
			}

			if (debug_build_paths) {
				printf("Mux for l%d is:\n", labels[state]);
				flattened->prettyPrint(stdout);
			}
			if (state->getSideEffect() == phi) {
				if (debug_build_paths)
					printf("...and that's the end of the analysis.\n");
				return flattened;
			}
			m[state] = flattened;
			toUpdate.push(state);
		}
	}

	if (debug_build_paths)
		printf("Mux builder failed?\n");

	return NULL;
}

static IRExpr *
build_mux(StateMachineSideEffectPhi *phi,
	  IRType ty,
	  bdd<int> *from,
	  std::map<bdd<int> *, IRExpr *> &memo)
{
	if (memo.count(from))
		return memo[from];

	IRExpr *res;
	if (from->isLeaf) {
		int idx = from->content.leaf;
		if (phi->generations[idx].val)
			res = coerceTypes(ty, phi->generations[idx].val);
		else
			res = IRExpr_Get(phi->generations[idx].reg, ty);
	} else {
		res = IRExpr_Mux0X(
			from->content.condition,
			build_mux(phi, ty, from->content.falseBranch, memo),
			build_mux(phi, ty, from->content.trueBranch, memo));
	}
	memo[from] = res;
	return res;
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

	if (debug_build_paths || debug_toplevel) {
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
		IRType ity = phi->ty;
		std::map<unsigned, unsigned> resultCanoniser;
		for (unsigned x = 0; x < phi->generations.size(); x++) {
			IRExpr *expr = phi->generations[x].val;
			if (expr) {
				bool found_one = false;
				for (unsigned y = 0; !found_one && y < x; y++) {
					if (phi->generations[y].val == expr) {
						resultCanoniser[x] = y;
						found_one = true;
					}
				}
				if (!found_one)
					resultCanoniser[x] = x;
			} else {
				bool found_one = false;
				for (unsigned y = 0; !found_one && y < x; y++) {
					if (phi->generations[y].reg == 
					    phi->generations[x].reg) {
						resultCanoniser[x] = y;
						found_one = true;
					}
				}
				if (!found_one)
					resultCanoniser[x] = x;
			}
		}
		intbdd_scope iscope;
		intbdd *sel_bdd = build_selection_bdd(sm, phi, labels, resultCanoniser, &iscope);
		if (!sel_bdd) {
			if (debug_toplevel)
				printf("Failed to build bdd!\n");
			continue;
		}
		std::map<bdd<int> *, IRExpr *> memo;
		IRExpr *e = build_mux(phi, ity, sel_bdd, memo);
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
