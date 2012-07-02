#include "sli.h"
#include "state_machine.hpp"
#include "offline_analysis.hpp"
#include "sat_checker.hpp"

namespace _phi_elimination {

typedef std::map<const StateMachineState *, int> stateLabelT;

#ifndef NDEBUG
static bool debug_state_domination = false;
static bool debug_reg_domination = false;
static bool debug_use_domination = false;
#else
#define debug_state_domination false
#define debug_reg_domination false
#define debug_use_domination false
#endif
#define any_debug (debug_state_domination || debug_reg_domination || debug_use_domination)

static void
computeMaxDistanceMap(StateMachine *sm, std::map<StateMachineState *, int> &distanceMap)
{
	std::priority_queue<std::pair<int, StateMachineState *> > pending;
	pending.push(std::pair<int, StateMachineState *>(0, sm->root));
	while (!pending.empty()) {
		std::pair<int, StateMachineState *> p(pending.top());
		pending.pop();
		auto it_did_insert = distanceMap.insert(std::pair<StateMachineState *, int>(p.second, p.first));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (!did_insert && it->second >= p.first)
			continue;
		it->second = p.first;
		std::vector<StateMachineState *> targets;
		p.second->targets(targets);
		for (auto it = targets.begin(); it != targets.end(); it++)
			pending.push(std::pair<int, StateMachineState *>(p.first + 1, *it));
	}
}

static StateMachine *
phiElimination(StateMachine *sm, const AllowableOptimisations &opt,
	       bool *done_something)
{
	/* We're only really interested in registers which are input
	   to Phi expressions. */
	std::set<threadAndRegister, threadAndRegister::fullCompare> phiRegs;
	struct _2 : public StateMachineTransformer {
		std::set<threadAndRegister, threadAndRegister::fullCompare> &phiRegs;
		StateMachineSideEffectPhi *transformOneSideEffect(
			StateMachineSideEffectPhi *p, bool *done_something) {
			for (auto it = p->generations.begin(); it != p->generations.end(); it++)
				phiRegs.insert(p->reg.setGen(it->first));
			return StateMachineTransformer::transformOneSideEffect(p, done_something);
		}
		IRExpr *transformIRExpr(IRExpr *e, bool *) {
			return e;
		}
		bool rewriteNewStates() const { return false; }
		_2(std::set<threadAndRegister, threadAndRegister::fullCompare> &_phiRegs)
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

	/* First figure out the expressions which are definitely true
	   at each state due to control flow, because the state must
	   be reachable from the root state.  States which aren't
	   present in this map definitely aren't reachable (once we've
	   finished building it) i.e. default is 0.  These expressions
	   definitely hold at the *start* of the state. */
	/* (There's a converse optimisation to this one which looks
	 * backwards from terminal nodes, because we're only
	 * interested in machines which might conceivably reach
	 * <crash>, but that's a bit harder to think about, and we
	 * don't implement it.) */

	/* We try to process states so that we pick whatever is
	 * ``closest'' to the root first, where we measure distance
	 * according to the *longest* path from the root to the state.
	 * This means that by the time we want to calculate the
	 * condition for a state all of its inputs are available and
	 * we never have to do any recomputation, which helps to make
	 * things a bit faster. */
	std::map<StateMachineState *, int> stateDistances;
	computeMaxDistanceMap(sm, stateDistances);

	std::map<StateMachineState *, IRExpr *> dominatingExpressions;
	/* States whose successors might need updating. The first
	   argument is just a depth argument to make sure we handle
	   states in the right order. */
	typedef std::pair<int, StateMachineState *> needsUpdateEntryT;
	std::priority_queue<needsUpdateEntryT> needsUpdate;
	dominatingExpressions[sm->root] = IRExpr_Const(IRConst_U1(1));
	needsUpdate.push(needsUpdateEntryT(0, sm->root));
	struct _ {
		const AllowableOptimisations &opt;
		std::map<StateMachineState *, IRExpr *> &dominatingExpressions;
		std::map<StateMachineState *, int> &stateDistances;
		std::priority_queue<needsUpdateEntryT> &needsUpdate;
		void operator()(StateMachineState *s, IRExpr *cond) {
			cond = simplifyIRExpr(cond, opt);
			auto it_did_insert = dominatingExpressions.insert(
				std::pair<StateMachineState *, IRExpr *>(s, cond));
			auto it = it_did_insert.first;
			auto did_insert = it_did_insert.second;
			if (did_insert) {
				needsUpdate.push(needsUpdateEntryT(-stateDistances[s], s));
				return;
			}
			IRExpr *oldCond = it->second;
			it->second = IRExpr_Binop(Iop_Or1,
						  oldCond,
						  cond);
			it->second = simplify_via_anf(simplifyIRExpr(it->second, opt));
			if (!definitelyEqual(it->second, oldCond, opt))
				needsUpdate.push(needsUpdateEntryT(-stateDistances[s], s));
		}
		_(const AllowableOptimisations &_opt,
		  std::map<StateMachineState *, IRExpr *> &_dominatingExpressions,
		  std::map<StateMachineState *, int> &_stateDistances,
		  std::priority_queue<needsUpdateEntryT> &_needsUpdate)
			: opt(_opt),
			  dominatingExpressions(_dominatingExpressions),
			  stateDistances(_stateDistances),
			  needsUpdate(_needsUpdate)
		{}
	} discoverPathToState(opt, dominatingExpressions, stateDistances, needsUpdate);

	while (!needsUpdate.empty() && !TIMEOUT) {
		StateMachineState *s = needsUpdate.top().second;
		needsUpdate.pop();
		/* Build the exprAtExit starting from the expression
		   at entry to the state. */
		if (debug_state_domination)
			printf("Recompute domination condition for l%d\n",
			       stateLabels[s]);
		IRExpr *exprAtEntry = dominatingExpressions[s];
		assert(exprAtEntry); /* should definitely have been
					populated by now */
		switch (s->type) {
		case StateMachineState::Unreached:
		case StateMachineState::Crash:
		case StateMachineState::NoCrash:
		case StateMachineState::Stub:
			/* No exit states, so it doesn't matter what
			 * the exprAtExit is. */
			break;
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
			IRExpr *trueCond = IRExpr_Binop(
				Iop_And1,
				smb->condition,
				exprAtEntry);
			IRExpr *falseCond = IRExpr_Binop(
				Iop_And1,
				IRExpr_Unop(Iop_Not1, smb->condition),
				exprAtEntry);
			discoverPathToState(smb->trueTarget, trueCond);
			discoverPathToState(smb->falseTarget, falseCond);
			break;
		}
		case StateMachineState::SideEffecting: {
			/* The side effect can also tell us something
			   interesting about what happens next. */
			StateMachineSideEffecting *effecting = (StateMachineSideEffecting *)s;
			IRExpr *exprAtExit = exprAtEntry;
			if (effecting->sideEffect) {
				switch (effecting->sideEffect->type) {
				case StateMachineSideEffect::Load:
				case StateMachineSideEffect::Store: {
					StateMachineSideEffectMemoryAccess *m = (StateMachineSideEffectMemoryAccess *)effecting->sideEffect;
					exprAtExit = IRExpr_Binop(
						Iop_And1,
						IRExpr_Unop(
							Iop_Not1,
							IRExpr_Unop(
								Iop_BadPtr,
								m->addr)),
						exprAtEntry);
					break;
				}
				case StateMachineSideEffect::Unreached:
					exprAtExit = IRExpr_Const(IRConst_U1(0));
					break;
				case StateMachineSideEffect::AssertFalse: {
					StateMachineSideEffectAssertFalse *a = (StateMachineSideEffectAssertFalse *)effecting->sideEffect;
					exprAtExit = IRExpr_Binop(
						Iop_And1,
						IRExpr_Unop(
							Iop_Not1,
							a->value),
						exprAtEntry);
					break;
				}
				case StateMachineSideEffect::Copy:
				case StateMachineSideEffect::Phi:
				case StateMachineSideEffect::StartAtomic:
				case StateMachineSideEffect::EndAtomic:
				case StateMachineSideEffect::StartFunction:
				case StateMachineSideEffect::EndFunction:
					break;
				}
			}
			discoverPathToState(effecting->target, exprAtExit);
			break;
		}
		}
	}
	if (TIMEOUT)
		return sm;

	if (debug_state_domination) {
		printf("State domination table:\n");
		for (auto it = dominatingExpressions.begin();
		     it != dominatingExpressions.end();
		     it++)
			printf("l%d: %s\n", stateLabels[it->first], nameIRExpr(it->second));
	}

	std::set<StateMachineSideEffecting *> states;
	enumStates(sm, &states);

	/* Now build the register dominator map.  This is a map from
	   registers in the Phi set to expressions which must be true
	   if we ever assign to that register. */
	std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> regDominators;
	for (auto it = states.begin(); it != states.end(); it++) {
		StateMachineSideEffect *s = (*it)->getSideEffect();
		if (!s)
			continue;
		threadAndRegister tr(threadAndRegister::invalid());
		if (!s->definesRegister(tr))
			continue;
		if (!phiRegs.count(tr))
			continue;
		assert(dominatingExpressions.count(*it));
		assert(!regDominators.count(tr));
		regDominators[tr] = dominatingExpressions[*it];
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
		if (debug_use_domination)
			printf("Consider reducing phi state l%d\n", stateLabels[*it]);
		IRExpr *stateDominator =
			simplifyIRExpr(
				simplify_via_anf(dominatingExpressions[*it]),
				opt);
		assert(stateDominator != NULL);
		std::vector<IRExpr *> pRegDominators;
		pRegDominators.resize(s->generations.size());
		bool haveGenM1 = false;
		for (unsigned x = 0; x < s->generations.size(); x++) {
			if (s->generations[x].first == (unsigned)-1) {
				assert(!haveGenM1);
				haveGenM1 = true;
			} else {
				pRegDominators[x] =
					simplifyIRExpr(
						simplify_via_anf(
							optimiseAssuming(
								regDominators[s->reg.setGen(s->generations[x].first)],
								stateDominator)),
						opt);
			}
		}
		if (debug_use_domination) {
			printf("State domination: %s\n", nameIRExpr(stateDominator));
			printf("Register dominators:\n");
			for (unsigned x = 0; x < s->generations.size(); x++)
				printf("%d -> %s\n", s->generations[x].first, nameIRExpr(pRegDominators[x]));
			if (haveGenM1)
				printf("Have gen m1\n");
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
		     !ambiguous_resolution && i < s->generations.size();
		     i++) {
			if (s->generations[i].first == (unsigned)-1)
				continue;
			for (unsigned j = i + 1;
			     !ambiguous_resolution && j < s->generations.size();
			     j++) {
				if (s->generations[j].first == (unsigned)-1)
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
		if (ambiguous_resolution)
			continue;
		/* Next: at least one must always be true, unless we have gen -1 */
		if (!haveGenM1) {
			IRExprAssociative *checker =
				IRExpr_Associative(
					s->generations.size(),
					Iop_Or1);
			for (unsigned x = 0; x < s->generations.size(); x++)
				checker->contents[x] = pRegDominators[x];
			checker->nr_arguments = s->generations.size();
			IRExpr *c = IRExpr_Binop(
				Iop_And1,
				stateDominator,
				IRExpr_Unop(Iop_Not1, checker));
			if (satisfiable(c, opt)) {
				if (debug_use_domination)
					printf("Potentially null resolution: %s is not satisfiable\n",
					       nameIRExpr(c));
				continue;
			}
		}

		/* So now we know that precisely one of the dominator
		   expressions will always be true, so we can replace
		   this Phi with a simple Mux and copy.  Do so. */
		IRExpr *acc = NULL;
		if (haveGenM1)
			acc = IRExpr_Get(s->reg.setGen(-1), ty);
		for (unsigned x = 0; x < s->generations.size(); x++) {
			IRExpr *component;
			if (s->generations[x].first == (unsigned)-1)
				continue;
			if (s->generations[x].second)
				component = s->generations[x].second;
			else
				component = IRExpr_Get(s->reg.setGen(s->generations[x].first), ty);
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
	       bool *done_something)
{
	return _phi_elimination::phiElimination(sm, opt, done_something);
}
