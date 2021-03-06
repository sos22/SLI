/* Compare two (canonicalised) crash summaries and try to guess
   whether they represent the same underlying bug. */
#include <dirent.h>
#include <errno.h>

#include "sli.h"
#include "oracle.hpp"
#include "allowable_optimisations.hpp"
#include "state_machine.hpp"
#include "simplify_irexpr.hpp"
#include "inferred_information.hpp"
#include "libvex_prof.hpp"

static bool
localSimilarity(IRExpr *a, IRExpr *b)
{
	return a->type() == b->type() &&
		definitelyEqual(a, b, AllowableOptimisations::defaultOptimisations);
}

template <typename t> static bool
_bddSimilarity(t *a, t *b)
{
	if (a == b)
		return true;
	if (a->isLeaf() || b->isLeaf())
		return false;
	return localSimilarity(a->internal().condition, b->internal().condition) &&
		_bddSimilarity(a->internal().trueBranch, b->internal().trueBranch) &&
		_bddSimilarity(a->internal().falseBranch, b->internal().falseBranch);
}

static bool
bddSimilarity(bbdd *a, bbdd *b)
{
	return _bddSimilarity(a, b);
}
static bool
bddSimilarity(smrbdd *a, smrbdd *b)
{
	return _bddSimilarity(a, b);
}
static bool
bddSimilarity(exprbdd *a, exprbdd *b)
{
	if (a == b) {
		return true;
	}
	if (a->isLeaf() && b->isLeaf()) {
		return localSimilarity(a->leaf(), b->leaf());
	}
	if (a->isLeaf() || b->isLeaf()) {
		return false;
	}
	return localSimilarity(a->internal().condition, b->internal().condition) &&
		bddSimilarity(a->internal().trueBranch, b->internal().trueBranch) &&
		bddSimilarity(a->internal().falseBranch, b->internal().falseBranch);
}

static bool
localSimilarity2(StateMachineSideEffectLoad *smsel1, StateMachineSideEffectLoad *smsel2)
{
	return bddSimilarity(smsel1->addr, smsel2->addr) &&
		smsel1->target == smsel2->target &&
		smsel1->type == smsel2->type;
}

static bool
localSimilarity2(StateMachineSideEffectStore *smsel1, StateMachineSideEffectStore *smsel2)
{
	return bddSimilarity(smsel1->addr, smsel2->addr) &&
		bddSimilarity(smsel1->data, smsel2->data);
}

static bool
localSimilarity2(StateMachineSideEffectCopy *smsel1, StateMachineSideEffectCopy *smsel2)
{
	return bddSimilarity(smsel1->value, smsel2->value) &&
		smsel1->target == smsel2->target;
}

static bool
localSimilarity2(StateMachineSideEffectAssertFalse *smsel1, StateMachineSideEffectAssertFalse *smsel2)
{
	return bddSimilarity(smsel1->value, smsel2->value) &&
		smsel1->reflectsActualProgram == smsel2->reflectsActualProgram;
}

static bool
localSimilarity2(StateMachineSideEffectStartAtomic *, StateMachineSideEffectStartAtomic *)
{
	return true;
}

static bool
localSimilarity2(StateMachineSideEffectEndAtomic *, StateMachineSideEffectEndAtomic *)
{
	return true;
}

static bool
localSimilarity2(StateMachineSideEffectUnreached *, StateMachineSideEffectUnreached *)
{
	return true;
}

static bool
localSimilarity2(StateMachineSideEffectPhi *e1, StateMachineSideEffectPhi *e2)
{
	if (e1->reg != e2->reg)
		return false;
	if (e1->generations.size() != e2->generations.size())
		return false;
	for (auto it1 = e1->generations.begin(); it1 != e1->generations.end(); it1++) {
		bool found_one = false;
		for (auto it2 = e2->generations.begin(); !found_one && it2 != e2->generations.end(); it2++)
			found_one = it1->reg == it2->reg;
		if (!found_one)
			return false;
	}
	for (auto it1 = e2->generations.begin(); it1 != e2->generations.end(); it1++) {
		bool found_one = false;
		for (auto it2 = e1->generations.begin(); !found_one && it2 != e1->generations.end(); it2++)
			found_one = it1->reg == it2->reg;
		if (!found_one)
			return false;
	}
	return true;
}

static bool
localSimilarity2(StateMachineSideEffectImportRegister *smsesf1, StateMachineSideEffectImportRegister *smsesf2)
{
	return *smsesf1 == *smsesf2;
}

#if !CONFIG_NO_STATIC_ALIASING
static bool
localSimilarity2(StateMachineSideEffectStartFunction *smsesf1, StateMachineSideEffectStartFunction *smsesf2)
{
	return bddSimilarity(smsesf1->rsp, smsesf2->rsp);
}

static bool
localSimilarity2(StateMachineSideEffectEndFunction *smsesf1, StateMachineSideEffectEndFunction *smsesf2)
{
	return bddSimilarity(smsesf1->rsp, smsesf2->rsp);
}

static bool
localSimilarity2(StateMachineSideEffectStackLayout *smsesf1, StateMachineSideEffectStackLayout *smsesf2)
{
	return *smsesf1 == *smsesf2;
}
#endif

static bool
localSimilarity(StateMachineSideEffect *smse1, StateMachineSideEffect *smse2)
{
	if (smse1->type != smse2->type)
		return false;
	switch (smse1->type) {
#define do_case(n)							\
		case StateMachineSideEffect::n:				\
			return localSimilarity2( (StateMachineSideEffect ## n *)smse1, \
						 (StateMachineSideEffect ## n *)smse2 );
		all_side_effect_types(do_case);
#undef do_case
	}
	abort();
}

static bool
localSimilarity(StateMachineTerminal *a, StateMachineTerminal *b)
{
	return bddSimilarity(a->res, b->res);
}

static bool
localSimilarity(StateMachineSideEffecting *sm1, StateMachineSideEffecting *sm2)
{
	if (!sm1->sideEffect && !sm2->sideEffect)
		return true;
	if (!sm1->sideEffect || !sm2->sideEffect)
		return false;
	return localSimilarity(sm1->sideEffect, sm2->sideEffect);
}

static bool
localSimilarity(StateMachineBifurcate *sm1, StateMachineBifurcate *sm2)
{
	return bddSimilarity(sm1->condition, sm2->condition);
}

static bool
stateMachineStatesTheSame(std::set<std::pair<StateMachineState *, StateMachineState *> > &memo,
			  StateMachineState *sm1,
			  StateMachineState *sm2)
{
	if (!memo.insert(std::pair<StateMachineState *, StateMachineState *>(sm1, sm2)).second)
		return true;
	if (sm1->type != sm2->type)
		return false;
	switch (sm1->type) {
#define do_state_type(t)						\
		case StateMachineState:: t :				\
			if (!localSimilarity((StateMachine ## t *)sm1,	\
					     (StateMachine ## t *)sm2))	\
				return false;				\
			break;
		all_state_types(do_state_type)
#undef do_state_type
	}
	std::vector<StateMachineState *> targets1;
	std::vector<StateMachineState *> targets2;
	sm1->targets(targets1);
	sm2->targets(targets2);
	if (targets1.size() != targets2.size())
		return false;
	for (unsigned x = 0; x < targets1.size(); x++)
		if (!stateMachineStatesTheSame(memo, targets1[x], targets2[x]))
			return false;
	return true;
}

static bool
stateMachinesTheSame(StateMachine *sm1, StateMachine *sm2)
{
	std::set<std::pair<StateMachineState *, StateMachineState *> > memo;
	return stateMachineStatesTheSame(memo, sm1->root, sm2->root);
}

static bool
crashSummariesTheSame(CrashSummary *summary1,
		      CrashSummary *summary2)
{
	return stateMachinesTheSame(summary1->loadMachine, summary2->loadMachine) &&
		stateMachinesTheSame(summary1->storeMachine, summary2->storeMachine) &&
		bddSimilarity(summary1->inferredAssumption, summary2->inferredAssumption) &&
		bddSimilarity(summary1->crashCondition, summary2->crashCondition) &&
		summary1->aliasing == summary2->aliasing;
}

int
main(int argc, char *argv[])
{
	init_sli();

	__set_profiling(root);

	if (argc == 3) {
		CrashSummary *summary1, *summary2;
		SMScopes scope1;
		summary1 = readBugReport(&scope1, argv[1], NULL);
		SMScopes scope2;
		summary2 = readBugReport(&scope2, argv[2], NULL);

		if (crashSummariesTheSame(summary1, summary2)){
			printf("The same\n");
			return 0;
		} else {
			printf("Different\n");
			return 1;
		}
	}

	std::vector<std::pair<char *, CrashSummary *> > summaries;
	DIR *d = opendir(".");
	if (!d)
		err(1, "opening ./");
	while (1) {
		errno = 0;
		struct dirent *de = readdir(d);
		if (!de) {
			if (errno)
				err(1, "reading current directory");
			break;
		}
		if (!strcmp(de->d_name, ".") || !strcmp(de->d_name, ".."))
			continue;
		SMScopes scope1;
		CrashSummary *summary = readBugReport(&scope1, de->d_name, NULL);
		bool found_dupe = false;
		for (auto it = summaries.begin(); !found_dupe && it != summaries.end(); it++) {
			if (crashSummariesTheSame(summary, it->second)) {
				printf("%s is a dupe of %s\n", de->d_name, it->first);
				unlink(de->d_name);
				found_dupe = true;
			}
		}
		if (!found_dupe) {
			printf("%s is unique\n", de->d_name);
			summaries.push_back(std::pair<char *, CrashSummary *>(strdup(de->d_name), summary));
		}
	}
	return 0;	
}
