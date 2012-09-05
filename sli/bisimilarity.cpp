/* Optimisation which tries to merge states which are identical except
   for variable renaming. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "state_machine.hpp"
#include "alloc_mai.hpp"

#ifndef NDEBUG
static bool debug_build_similarity_map = false;
static bool debug_build_replacements = false;
static bool debug_build_unifiers = false;
#else
#define debug_build_similarity_map false
#define debug_build_replacements false
#define debug_build_unifiers false
#endif
#define debug_any (debug_build_similarity_map || debug_build_replacements || debug_build_unifiers)

namespace _bisimilarity {

static bool
equalModuloVariables(const IRExpr *a, const IRExpr *b)
{
	if (a == b)
		return true;
	if (a->tag != b->tag)
		return false;
	switch (a->tag) {
	case Iex_Get:
		return true;
#define hdr(name)							\
	case Iex_ ## name : {						\
		const IRExpr ## name *a1 =				\
			(const IRExpr ## name *)a;			\
		const IRExpr ## name *b1 =				\
			(const IRExpr ## name *)b
	hdr(GetI);
		return a1->descr == b1->descr &&
			a1->bias == b1->bias &&
			a1->tid == b1->tid &&
			equalModuloVariables(a1->ix, b1->ix);
#define footer }
	footer;
	hdr(Qop);
		return a1->op == b1->op &&
			equalModuloVariables(a1->arg1, b1->arg1) &&
			equalModuloVariables(a1->arg2, b1->arg2) &&
			equalModuloVariables(a1->arg3, b1->arg3) &&
			equalModuloVariables(a1->arg4, b1->arg4);
	footer;
	hdr(Triop);
		return a1->op == b1->op &&
			equalModuloVariables(a1->arg1, b1->arg1) &&
			equalModuloVariables(a1->arg2, b1->arg2) &&
			equalModuloVariables(a1->arg3, b1->arg3);
	footer;
	hdr(Binop);
		return a1->op == b1->op &&
			equalModuloVariables(a1->arg1, b1->arg1) &&
			equalModuloVariables(a1->arg2, b1->arg2);
	footer;
	hdr(Unop);
		return a1->op == b1->op &&
			equalModuloVariables(a1->arg, b1->arg);
	footer;
	hdr(Load);
		return equalModuloVariables(a1->addr, b1->addr);
	footer;
	case Iex_Const:
		return false; /* If they were equal then a == b would have caught it */
	hdr(CCall);
		if (a1->cee != b1->cee || a1->retty != b1->retty)
			return false;
		int i;
		for (i = 0; a1->args[i] && b1->args[i]; i++)
			if (!equalModuloVariables(a1->args[i], b1->args[i]))
				return false;
		if (a1->args[i] || b1->args[i])
			return false;
		return true;
	footer;
	hdr(Mux0X);
		return equalModuloVariables(a1->expr0, b1->expr0) &&
			equalModuloVariables(a1->exprX, b1->exprX) &&
			equalModuloVariables(a1->cond, b1->cond);
	footer;
	hdr(Associative);
		if (a1->op != b1->op || a1->nr_arguments != b1->nr_arguments)
			return false;
		for (int i = 0; i < a1->nr_arguments; i++)
			if (!equalModuloVariables(a1->contents[i], b1->contents[i]))
				return false;
		return true;
	footer;
	case Iex_HappensBefore:
		/* No variables, so if they were sufficiently equal
		   internment would make them pointer-equal. */
		return false;
	case Iex_FreeVariable:
		/* Variables here means assignable registers, so
		   these, like HappensBefore, have no variables. */
		return false;
#undef hdr
#undef footer
	}

	abort();
}

static bool
equalModuloVariables(const StateMachineSideEffect *smse1,
		     const StateMachineSideEffect *smse2)
{
	if (smse1 == NULL || smse2 == NULL)
		return false;
	if (smse1->type != smse2->type)
		return false;
	switch (smse1->type) {
	case StateMachineSideEffect::Store:
		/* Later stages of the analysis get confused if they
		   have to unify two input expressions in the same
		   state e.g. data and address, so just don't generate
		   similarity sets for store states. */
		return false;
	case StateMachineSideEffect::Load: {
		const StateMachineSideEffectLoad *smsel1 =
			dynamic_cast<const StateMachineSideEffectLoad *>(smse1);
		const StateMachineSideEffectLoad *smsel2 =
			dynamic_cast<const StateMachineSideEffectLoad *>(smse2);
		return smsel1->type == smsel2->type &&
			smsel1->rip.tid == smsel2->rip.tid &&
			equalModuloVariables(smsel1->addr, smsel2->addr);
	}
	case StateMachineSideEffect::Copy: {
		const StateMachineSideEffectCopy *smsec1 =
			dynamic_cast<const StateMachineSideEffectCopy *>(smse1);
		const StateMachineSideEffectCopy *smsec2 =
			dynamic_cast<const StateMachineSideEffectCopy *>(smse2);
		return smsec1->value->type() == smsec2->value->type() &&
			equalModuloVariables(smsec1->value, smsec2->value);
	}
	case StateMachineSideEffect::AssertFalse:
	case StateMachineSideEffect::StartFunction:
	case StateMachineSideEffect::EndFunction:
	case StateMachineSideEffect::PointerAliasing:
	case StateMachineSideEffect::StackLayout:
	case StateMachineSideEffect::StartAtomic:
	case StateMachineSideEffect::EndAtomic:
	case StateMachineSideEffect::Unreached:
		/* Not *strictly* true, but other passes can handle
		   these more cheaply, and doing it here as well is
		   just a waste of time. */
		return false;
	case StateMachineSideEffect::Phi:
		/* Too confusing to deal with here. */
		return false;
	}
	abort();
}

static bool
extendUnifier(std::map<threadAndRegister, threadAndRegister> &unifier,
	      const IRExpr *a,
	      const IRExpr *b)
{
	if (a == b)
		return true;
	assert(a->tag == b->tag);
	switch (a->tag) {
#define hdr(name)							\
	case Iex_ ## name : {						\
		const IRExpr ## name *a1 =				\
			(const IRExpr ## name *)a;			\
		const IRExpr ## name *b1 =				\
			(const IRExpr ## name *)b
#define footer }
	hdr(Get);
		if (a1->reg == b1->reg)
			return true;
		if (unifier.count(b1->reg) && unifier[b1->reg] != a1->reg)
			return false;
		unifier[b1->reg] = a1->reg;
		return true;
	footer;
	hdr(GetI);
		return extendUnifier(unifier, a1->ix, b1->ix);
	footer;
	hdr(Qop);
		return extendUnifier(unifier, a1->arg1, b1->arg1) &&
			extendUnifier(unifier, a1->arg2, b1->arg2) &&
			extendUnifier(unifier, a1->arg3, b1->arg3) &&
			extendUnifier(unifier, a1->arg4, b1->arg4);
	footer;
	hdr(Triop);
		return extendUnifier(unifier, a1->arg1, b1->arg1) &&
			extendUnifier(unifier, a1->arg2, b1->arg2) &&
			extendUnifier(unifier, a1->arg3, b1->arg3);
	footer;
	hdr(Binop);
		return extendUnifier(unifier, a1->arg1, b1->arg1) &&
			extendUnifier(unifier, a1->arg2, b1->arg2);
	footer;
	hdr(Unop);
		return extendUnifier(unifier, a1->arg, b1->arg);
	footer;
	hdr(Load);
		return extendUnifier(unifier, a1->addr, b1->addr);
	footer;
	case Iex_Const:
		abort();
	hdr(CCall);
		int i;
		for (i = 0; a1->args[i] && b1->args[i]; i++)
			if (!extendUnifier(unifier, a1->args[i], b1->args[i]))
				return false;
		assert(!a1->args[i] && !b1->args[i]);
		return true;
	footer;
	hdr(Mux0X);
		return extendUnifier(unifier, a1->expr0, b1->expr0) &&
			extendUnifier(unifier, a1->exprX, b1->exprX) &&
			extendUnifier(unifier, a1->cond, b1->cond);
	footer;
	hdr(Associative);
		for (int i = 0; i < a1->nr_arguments; i++)
			if (!extendUnifier(unifier, a1->contents[i], b1->contents[i]))
				return false;
		return true;
	footer;
	case Iex_HappensBefore:
		/* No variables, so if they were sufficiently equal
		   internment would make them pointer-equal. */
		abort();
	case Iex_FreeVariable:
		/* Variables here means assignable registers, so
		   these, like HappensBefore, have no variables. */
		abort();
#undef hdr
#undef footer
	}
	abort();
}

static bool
unifyExpressions(const std::set<std::pair<StateMachineState *, IRExpr *> > inputExpressions,
		 const VexRip &vr,
		 StateMachineState ***suffix,
		 IRExpr **result,
		 StateMachineState **fragmentHead)
{
	/* First build a register->register map which will map all of
	   the expressions to the first one.  Such a thing must exist
	   because of the way the similarity sets are constructed. */
	std::map<threadAndRegister, threadAndRegister> unifier;

	auto it = inputExpressions.begin();
	IRExpr *ref = it->second;
	for (it++; it != inputExpressions.end(); it++) {
		if (!extendUnifier(unifier, ref, it->second)) {
			if (debug_build_unifiers)
				printf("Cannot unify %s and %s\n",
				       nameIRExpr(ref), nameIRExpr(it->second));
			return false;
		}
	}

	if (debug_build_unifiers) {
		printf("Unifier for {");
		for (auto it = inputExpressions.begin(); it != inputExpressions.end(); it++) {
			if (it != inputExpressions.begin())
				printf(", ");
			ppIRExpr(it->second, stdout);
		}
		printf("}:\n");
		for (auto it = unifier.begin(); it != unifier.end(); it++)
			printf("\t%s -> %s\n", it->first.name(), it->second.name());
	}

	if (unifier.empty()) {
		if (debug_build_unifiers)
			printf("Trivial unifier!\n");
		*result = ref;
		StateMachineSideEffecting *smse = new StateMachineSideEffecting(
			vr,
			NULL,
			NULL);
		*suffix = &smse->target;
		*fragmentHead = smse;
		return true;
	}
			
#warning write me

	return false;
}

static StateMachineState *
unifyOutputs(const threadAndRegister &reg1, IRType ty, const std::set<threadAndRegister> &otherRegs, StateMachineState *next)
{
	for (auto it = otherRegs.begin(); it != otherRegs.end(); it++)
		next = new StateMachineSideEffecting(
			next->dbg_origin,
			new StateMachineSideEffectCopy(
				*it,
				IRExpr_Get(reg1, ty)),
			next);
	return next;
}
		 
static StateMachine *
bisimilarityReduction(StateMachine *sm, MaiMap &mai, bool *done_something)
{
	std::map<const StateMachineState *, int> stateLabels;

	if (debug_any) {
		printf("bisimilaritityReduction:\n");
		printStateMachine(sm, stdout, stateLabels);
	}

	/* First, figure out what the bisimilarity sets are. */
	std::vector<std::set<StateMachineState *> > similaritySets;

	std::set<StateMachineState *> unassignedStates;
	enumStates(sm, &unassignedStates);

	bool haveNonTrivialSets = false;

	for (auto it = unassignedStates.begin(); it != unassignedStates.end(); ) {
		StateMachineState *s = *it;
		unassignedStates.erase(it++);

		bool assigned = false;
		for (unsigned x = 0; !assigned && x < similaritySets.size(); x++) {
			std::set<StateMachineState *> &candidateSet(similaritySets[x]);
			assert(!candidateSet.count(s));
			assert(!candidateSet.empty());
			StateMachineState *other = *candidateSet.begin();

			if (other->type != s->type)
				continue;
			switch (s->type) {
			case StateMachineState::Unreached:
			case StateMachineState::Crash:
			case StateMachineState::NoCrash:
				/* These are singletons, but we seem
				   to have found multiple
				   instances. */
				abort();
			case StateMachineState::Bifurcate: {
				StateMachineBifurcate *s2 = (StateMachineBifurcate *)s;
				StateMachineBifurcate *o2 = (StateMachineBifurcate *)other;
				if (s2->trueTarget == o2->trueTarget &&
				    s2->falseTarget == o2->falseTarget &&
				    equalModuloVariables(s2->condition, o2->condition))
					assigned = true;
				break;
			}
			case StateMachineState::SideEffecting: {
				StateMachineSideEffecting *s2 = (StateMachineSideEffecting *)s;
				StateMachineSideEffecting *o2 = (StateMachineSideEffecting *)other;
				if (s2->target == o2->target &&
				    equalModuloVariables(s2->sideEffect, o2->sideEffect))
					assigned = true;
				break;
			}
			}
			if (assigned) {
				candidateSet.insert(s);
				haveNonTrivialSets = true;
			}
		}
		if (!assigned) {
			std::set<StateMachineState *> t;
			similaritySets.push_back(t);
			similaritySets.back().insert(s);
		}
	}

	if (!haveNonTrivialSets) {
		if (debug_build_similarity_map)
			printf("All similarity sets trivial\n");
		return sm;
	}

	/* Only keep sets which are non-trivial. */
	{
		std::vector<std::set<StateMachineState *> > similaritySets2;
		for (auto it = similaritySets.begin(); it != similaritySets.end(); it++)
			if (it->size() > 1)
				similaritySets2.push_back(*it);
		similaritySets = similaritySets2;
		assert(!similaritySets.empty());
	}

	if (debug_build_similarity_map) {
		printf("State similarity sets:\n");
		for (unsigned x = 0; x < similaritySets.size(); x++) {
			printf("%d: {", x);
			for (auto it = similaritySets[x].begin();
			     it != similaritySets[x].end();
			     it++) {
				if (it != similaritySets[x].begin())
					printf(", ");
				printf("l%d", stateLabels[*it]);
			}
			printf("}\n");
		}
	}

	/* Now go and build the substitution fragments for each
	 * similarity set. */
	std::vector<StateMachineState *> replacementFragments;
	for (auto it = similaritySets.begin(); it != similaritySets.end(); it++) {
		std::set<StateMachineState *> &set(*it);
		assert(!set.empty());
		StateMachineState *representative = *set.begin();
		StateMachineState *replacement;
		switch (representative->type) {
		case StateMachineState::Unreached:
		case StateMachineState::Crash:
		case StateMachineState::NoCrash:
			abort();
		case StateMachineState::Bifurcate: {
			std::set<std::pair<StateMachineState *, IRExpr *> > conditions;
			for (auto it2 = set.begin(); it2 != set.end(); it2++)
				conditions.insert(
					std::pair<StateMachineState *, IRExpr *>
					(*it2, ((StateMachineBifurcate *)*it2)->condition ));
			StateMachineState **suffix;
			IRExpr *unifiedCondition;
			StateMachineState *replacementHead;
			if (unifyExpressions(conditions, representative->dbg_origin, &suffix, &unifiedCondition, &replacementHead)) {
				*suffix = new StateMachineBifurcate(
					representative->dbg_origin,
					unifiedCondition,
					((StateMachineBifurcate *)representative)->trueTarget,
					((StateMachineBifurcate *)representative)->falseTarget);
				replacement = replacementHead;
			} else {
				replacement = NULL;
			}
			break;
		}
		case StateMachineState::SideEffecting: {
			StateMachineSideEffecting *rep = (StateMachineSideEffecting *)representative;
			assert(rep->sideEffect);
			switch (rep->sideEffect->type) {
			case StateMachineSideEffect::Load: {
				std::set<std::pair<StateMachineState *, IRExpr *> > addr;
				std::set<threadAndRegister> outputRegs;
				std::set<MemoryAccessIdentifier> mais;
				for (auto it2 = set.begin();
				     it2 != set.end();
				     it2++) {
					StateMachineSideEffecting *o = (StateMachineSideEffecting *)*it2;
					StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)o->sideEffect;
					addr.insert(std::pair<StateMachineState *, IRExpr *>(o, l->addr));
					mais.insert(l->rip);
					if (o != representative)
						outputRegs.insert(l->target);
				}
				StateMachineState **suffix;
				IRExpr *unifiedAddr;
				StateMachineState *replacementHead;
				if (unifyExpressions(addr, representative->dbg_origin, &suffix, &unifiedAddr, &replacementHead)) {
					StateMachineSideEffectLoad *l =
						(StateMachineSideEffectLoad *)rep->sideEffect;
					MemoryAccessIdentifier newMai(mai.merge(l->rip.tid, mais));
					*suffix = new StateMachineSideEffecting(
						representative->dbg_origin,
						new StateMachineSideEffectLoad(
							l->target,
							unifiedAddr,
							newMai,
							l->type),
						unifyOutputs(l->target, l->type, outputRegs, rep->target));
					replacement = replacementHead;
				} else {
					replacement = NULL;
				}
				break;
			}
			case StateMachineSideEffect::Copy: {
				std::set<std::pair<StateMachineState *, IRExpr *> > value;
				std::set<threadAndRegister> outputRegs;
				for (auto it2 = set.begin();
				     it2 != set.end();
				     it2++) {
					StateMachineSideEffecting *o = (StateMachineSideEffecting *)*it2;
					StateMachineSideEffectCopy *c = (StateMachineSideEffectCopy *)o->sideEffect;
					value.insert(std::pair<StateMachineState *, IRExpr *>(o, c->value));
					if (o != representative)
						outputRegs.insert(c->target);
				}
				StateMachineState **suffix;
				IRExpr *unifiedValue;
				StateMachineState *replacementHead;
				if (unifyExpressions(value, representative->dbg_origin, &suffix, &unifiedValue, &replacementHead)) {
					StateMachineSideEffectCopy *c =
						(StateMachineSideEffectCopy *)rep->sideEffect;
					*suffix = new StateMachineSideEffecting(
						representative->dbg_origin,
						new StateMachineSideEffectCopy(
							c->target,
							unifiedValue),
						unifyOutputs(c->target, unifiedValue->type(), outputRegs, rep->target));
					replacement = replacementHead;
				} else {
					replacement = NULL;
				}
				break;
			}

			default:
				abort();
			}
		}
		}
		replacementFragments.push_back(replacement);
	}

	if (debug_build_replacements) {
		printf("Replacement table:\n");
		for (unsigned x = 0; x < replacementFragments.size(); x++) {
			if (x != 0)
				printf("---------------------------------\n");
			if (replacementFragments[x]) {
				printf("%d:\n", x);
				printStateMachine(replacementFragments[x], stdout);
			} else {
				printf("%d: NULL\n", x);
			}
		}
	}

	/* Convert that to a rewrite table. */
	std::map<const StateMachineState *, StateMachineState *> rewriteTable;
	for (unsigned x = 0; x < replacementFragments.size(); x++) {
		if (replacementFragments[x] == NULL)
			continue;
		for (auto it = similaritySets[x].begin(); it != similaritySets[x].end(); it++)
			rewriteTable[*it] = replacementFragments[x];
	}

	if (rewriteTable.empty()) {
		if (debug_build_replacements)
			printf("Rewrite table is empty!\n");
		return sm;
	}

	std::queue<StateMachineState *> toRewrite;
	std::set<StateMachineState *> rewritten;
	toRewrite.push(sm->root);
	while (!toRewrite.empty()) {
		StateMachineState *s = toRewrite.front();
		toRewrite.pop();
		if (!rewritten.insert(s).second)
			continue;
		std::vector<StateMachineState **> succ;
		s->targets(succ);
		for (auto it = succ.begin(); it != succ.end(); it++) {
			auto it2 = rewriteTable.find(**it);
			if (it2 != rewriteTable.end()) {
				*done_something = true;
				**it = it2->second;
			}
			toRewrite.push(**it);
		}
	}

	if (debug_any) {
		printf("Result:\n");
		printStateMachine(sm, stdout);
	}
	return sm;
}

}

StateMachine *
bisimilarityReduction(StateMachine *sm, MaiMap &mai, bool *done_something)
{
	return _bisimilarity::bisimilarityReduction(sm, mai, done_something);
}

