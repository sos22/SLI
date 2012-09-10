#include "sli.h"
#include "state_machine.hpp"
#include "offline_analysis.hpp"
#include "sat_checker.hpp"
#include "control_domination_map.hpp"

namespace _phi_elimination {

typedef std::map<const StateMachineState *, int> stateLabelT;

#ifndef NDEBUG
static bool debug_reg_domination = false;
static bool debug_use_domination = false;
#else
#define debug_reg_domination false
#define debug_use_domination false
#endif
#define any_debug (debug_reg_domination || debug_use_domination)

static StateMachine *
phiElimination(StateMachine *sm,
	       const AllowableOptimisations &opt,
	       const ControlDominationMap &dominatingExpressions,
	       bool *done_something)
{
	/* We're only really interested in registers which are input
	   to Phi expressions. */
	std::set<threadAndRegister> phiRegs;
	struct _2 : public StateMachineTransformer {
		std::set<threadAndRegister> &phiRegs;
		StateMachineSideEffectPhi *transformOneSideEffect(
			StateMachineSideEffectPhi *p, bool *done_something) {
			for (auto it = p->generations.begin(); it != p->generations.end(); it++)
				phiRegs.insert(it->first);
			return StateMachineTransformer::transformOneSideEffect(p, done_something);
		}
		IRExpr *transformIRExpr(IRExpr *e, bool *) {
			return e;
		}
		bool rewriteNewStates() const { return false; }
		_2(std::set<threadAndRegister> &_phiRegs)
			: phiRegs(_phiRegs)
		{}
	} buildPhiRegs(phiRegs);
	buildPhiRegs.transform(sm);
	if (phiRegs.empty() || TIMEOUT)
		return sm;

	stateLabelT stateLabels;
	if (any_debug) {
		printf("%s, input:\n", __func__);
		printStateMachine(sm, stdout, stateLabels);
		printf("Phi regs: ");
		for (auto it = phiRegs.begin(); it != phiRegs.end(); it++) {
			if (it != phiRegs.begin())
				printf(", ");
			printf("%s", it->name());
		}
		printf("\n");
	}

	std::set<StateMachineSideEffecting *> states;
	enumStates(sm, &states);

	/* Now build the register dominator map.  This is a map from
	   registers in the Phi set to expressions which must be true
	   if we ever assign to that register. */
	std::map<threadAndRegister, IRExpr *> regDominators;
	for (auto it = states.begin(); it != states.end(); it++) {
		StateMachineSideEffect *s = (*it)->getSideEffect();
		if (!s)
			continue;
		threadAndRegister tr(threadAndRegister::invalid());
		if (!s->definesRegister(tr))
			continue;
		if (!phiRegs.count(tr))
			continue;
		assert(!regDominators.count(tr));
		regDominators[tr] = dominatingExpressions.get(*it);
	}
	if (debug_reg_domination) {
		printf("Register domination table:\n");
		for (auto it = regDominators.begin(); it != regDominators.end(); it++)
			printf("%s: %s\n", it->first.name(), nameIRExpr(it->second));
	}

	/* Finally we can actually use the dominator maps. */
	bool progress = false;
	for (auto it = states.begin(); it != states.end(); it++) {
		StateMachineSideEffectPhi *s;
		{
			StateMachineSideEffect *sp = (*it)->getSideEffect();
			if (!sp || sp->type != StateMachineSideEffect::Phi)
				continue;
			s = (StateMachineSideEffectPhi *)sp;
		}
		IRType ty = Ity_INVALID;
		for (unsigned x = 0; x < s->generations.size() && ty == Ity_INVALID; x++)
			if (s->generations[x].second)
				ty = s->generations[x].second->type();
		if (ty == Ity_INVALID)
			continue;
		bool failed = false;
		for (unsigned x = 0; x < s->generations.size() && !failed; x++)
			if (s->generations[x].second &&
			    ty != s->generations[x].second->type())
				failed = true;
		if (failed) {
			if (debug_use_domination)
				printf("Cannot reduce phi state l%d due to type conflict\n",
				       stateLabels[*it]);
			continue;
		}
		if (debug_use_domination)
			printf("Consider reducing phi state l%d\n", stateLabels[*it]);

		/* Remove any possible inputs whose assignment has been lost. */
		std::vector<std::pair<threadAndRegister, IRExpr *> > newGens;
		newGens.reserve(s->generations.size());
		for (auto it2 = s->generations.begin(); it2 != s->generations.end(); it2++) {
			if (regDominators.count(it2->first) || it2->first.gen() == (unsigned)-1) {
				newGens.push_back(*it2);
			} else {
				if (debug_use_domination)
					printf("Lost input generation %s\n", it2->first.name());
				progress = true;
			}
		}

		assert(newGens.size() > 0);
		if (newGens.size() == 1) {
			if (debug_use_domination)
				printf("Reduced to a simple copy\n");
			(*it)->sideEffect =
				new StateMachineSideEffectCopy(
					s->reg,
					IRExpr_Get(newGens[0].first, ty));
			progress = true;
			continue;
		}

		IRExpr *stateDominator =
			simplifyIRExpr(
				simplify_via_anf(dominatingExpressions.get(*it)),
				opt);
		assert(stateDominator != NULL);
		std::vector<IRExpr *> pRegDominators;
		pRegDominators.resize(newGens.size());
		threadAndRegister genM1(threadAndRegister::invalid());
		for (unsigned x = 0; x < newGens.size(); x++) {
			if (newGens[x].first.gen() == (unsigned)-1) {
				assert(!genM1.isValid());
				genM1 = newGens[x].first;
			} else {
				pRegDominators[x] =
					simplifyIRExpr(
						simplify_via_anf(
							optimiseAssuming(
								regDominators[newGens[x].first],
								stateDominator)),
						opt);
			}
		}
		if (debug_use_domination) {
			printf("State domination: %s\n", nameIRExpr(stateDominator));
			printf("Register dominators:\n");
			for (unsigned x = 0; x < newGens.size(); x++)
				printf("%s -> %s\n", newGens[x].first.name(),
				       pRegDominators[x] ? nameIRExpr(pRegDominators[x]) : "genM1");
			if (genM1.isValid())
				printf("Gen M1: %s\n", genM1.name());
		}

		/* In order for this to be valid, we need to be able
		   to show that precisely one of the reg dominators is
		   true at any given time.  That means doing the full
		   n(n-1)/2 comparison.  Fortunately, n is usually 2,
		   and basically never more than about 4, so it's not
		   too bad. */
		/* First: at most one can be true at any time. */
		bool ambiguous_resolution = false;
		for (unsigned i = 0;
		     !ambiguous_resolution && i < newGens.size();
		     i++) {
			if (newGens[i].first.gen() == (unsigned)-1)
				continue;
			for (unsigned j = i + 1;
			     !ambiguous_resolution && j < newGens.size();
			     j++) {
				if (newGens[j].first.gen() == (unsigned)-1)
					continue;
				if (satisfiable(
					    IRExpr_Binop(
						    Iop_And1,
						    pRegDominators[i],
						    pRegDominators[j]),
					    opt)) {
					if (debug_use_domination)
						printf("Ambiguous resolution: %s vs %s\n",
						       nameIRExpr(pRegDominators[i]),
						       nameIRExpr(pRegDominators[j]));
					ambiguous_resolution = true;
				}
			}
		}
		if (ambiguous_resolution) {
			if (newGens.size() < s->generations.size()) {
				if (debug_use_domination)
					printf("Replace with simpler Phi\n");
				(*it)->sideEffect = new StateMachineSideEffectPhi(
					s, newGens);
			}
			continue;
		}
		/* Next: at least one must always be true, unless we have gen -1 */
		if (genM1.isInvalid()) {
			IRExprAssociative *checker =
				IRExpr_Associative(
					newGens.size(),
					Iop_Or1);
			for (unsigned x = 0; x < newGens.size(); x++)
				checker->contents[x] = pRegDominators[x];
			checker->nr_arguments = newGens.size();
			IRExpr *c = IRExpr_Binop(
				Iop_And1,
				stateDominator,
				IRExpr_Unop(Iop_Not1, checker));
			if (satisfiable(c, opt)) {
				if (debug_use_domination)
					printf("Potentially null resolution: %s is satisfiable\n",
					       nameIRExpr(c));
				if (newGens.size() < s->generations.size()) {
					if (debug_use_domination)
						printf("Replace with simpler Phi\n");
					(*it)->sideEffect = new StateMachineSideEffectPhi(
						s, newGens);
				}
				continue;
			}
		}

		/* So now we know that precisely one of the dominator
		   expressions will always be true, so we can replace
		   this Phi with a simple Mux and copy.  Do so. */
		IRExpr *acc = NULL;
		if (genM1.isValid())
			acc = IRExpr_Get(genM1, ty);
		for (unsigned x = 0; x < newGens.size(); x++) {
			IRExpr *component;
			if (newGens[x].first.gen() == (unsigned)-1)
				continue;
			if (newGens[x].second)
				component = newGens[x].second;
			else
				component = IRExpr_Get(newGens[x].first, ty);
			if (acc)
				acc = IRExpr_Mux0X(pRegDominators[x], acc, component);
			else
				acc = component;
		}
		assert(acc != NULL);

		if (debug_use_domination)
			printf("Built mux expression %s\n", nameIRExpr(acc));
		(*it)->sideEffect = new StateMachineSideEffectCopy(s->reg, acc);
		progress = true;
	}

	*done_something |= progress;
	if (debug_use_domination) {
		if (progress) {
			printf("Result machine:\n");
			printStateMachine(sm, stdout);
		} else {
			printf("Achieved nothing\n");
		}
	}

	return sm;
}

/* End of namespace */
};

StateMachine *
phiElimination(StateMachine *sm, const AllowableOptimisations &opt,
	       const ControlDominationMap &dominatingExpressions,
	       bool *done_something)
{
	return _phi_elimination::phiElimination(sm, opt, dominatingExpressions, done_something);
}
