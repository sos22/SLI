/* Compare two (canonicalised) crash summaries and try to guess
   whether they represent the same underlying bug. */
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
	return definitelyEqual(a, b, AllowableOptimisations::defaultOptimisations);
}

static bool
localSimilarity2(StateMachineSideEffectLoad *smsel1, StateMachineSideEffectLoad *smsel2)
{
	return localSimilarity(smsel1->addr, smsel2->addr) &&
		threadAndRegister::fullEq(smsel1->target, smsel2->target) &&
		smsel1->type == smsel2->type;
}

static bool
localSimilarity2(StateMachineSideEffectStore *smsel1, StateMachineSideEffectStore *smsel2)
{
	return localSimilarity(smsel1->addr, smsel2->addr) &&
		localSimilarity(smsel1->data, smsel2->data);
}

static bool
localSimilarity2(StateMachineSideEffectCopy *smsel1, StateMachineSideEffectCopy *smsel2)
{
	return localSimilarity(smsel1->value, smsel2->value) &&
		threadAndRegister::fullEq(smsel1->target, smsel2->target);
}

static bool
localSimilarity2(StateMachineSideEffectAssertFalse *smsel1, StateMachineSideEffectAssertFalse *smsel2)
{
	return localSimilarity(smsel1->value, smsel2->value) &&
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
	if (!threadAndRegister::fullEq(e1->reg, e2->reg))
		return false;
	if (e1->generations.size() != e2->generations.size())
		return false;
	for (auto it1 = e1->generations.begin(); it1 != e1->generations.end(); it1++) {
		bool found_one = false;
		for (auto it2 = e2->generations.begin(); !found_one && it2 != e2->generations.end(); it2++)
			found_one = it1->first == it2->first;
		if (!found_one)
			return false;
	}
	for (auto it1 = e2->generations.begin(); it1 != e2->generations.end(); it1++) {
		bool found_one = false;
		for (auto it2 = e1->generations.begin(); !found_one && it2 != e1->generations.end(); it2++)
			found_one = it1->first == it2->first;
		if (!found_one)
			return false;
	}
	return true;
}

static bool
localSimilarity(StateMachineSideEffect *smse1, StateMachineSideEffect *smse2)
{
	if (smse1->type != smse2->type)
		return false;
	switch (smse1->type) {
#define do_case(n)							\
		case StateMachineSideEffect::n:				\
			return localSimilarity2( (StateMachineSideEffect ## n *)smse1, \
						 (StateMachineSideEffect ## n *)smse2 )
		do_case(Load);
		do_case(Store);
		do_case(Copy);
		do_case(Unreached);
		do_case(AssertFalse);
		do_case(Phi);
		do_case(StartAtomic);
		do_case(EndAtomic);
#undef do_case
	}
}

static bool
localSimilarity(StateMachineUnreached *, StateMachineUnreached *)
{
	return true;
}

static bool
localSimilarity(StateMachineCrash *, StateMachineCrash *)
{
	return true;
}

static bool
localSimilarity(StateMachineNoCrash *, StateMachineNoCrash *)
{
	return true;
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
	return localSimilarity(sm1->condition, sm2->condition);
}

static bool
localSimilarity(StateMachineNdChoice *, StateMachineNdChoice *)
{
	return true;
}

static bool
localSimilarity(StateMachineStub *sm1, StateMachineStub *sm2)
{
	return sm1->target == sm2->target;
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
	if (!stateMachinesTheSame(summary1->loadMachine, summary2->loadMachine))
		return false;
	for (auto it = summary1->storeMachines.begin();
	     it != summary1->storeMachines.end();
	     it++) {
		bool found_one = false;
		for (auto it2 = summary2->storeMachines.begin();
		     !found_one && it2 != summary2->storeMachines.end();
		     it2++) {
			if (stateMachinesTheSame((*it)->machine, (*it2)->machine))
				found_one = true;
		}
		if (!found_one)
			return false;
	}
	for (auto it = summary2->storeMachines.begin();
	     it != summary2->storeMachines.end();
	     it++) {
		bool found_one = false;
		for (auto it2 = summary1->storeMachines.begin();
		     !found_one && it2 != summary1->storeMachines.end();
		     it2++) {
			if (stateMachinesTheSame((*it)->machine, (*it2)->machine))
				found_one = true;
		}
		if (!found_one)
			return false;
	}
	return true;
}

static CrashSummary *
read_crash_summary(const char *name)
{
	__set_profiling(read_crash_summary);

	int fd = open(name, O_RDONLY);
	if (fd < 0)
		err(1, "opening %s", name);
	char *content = readfile(fd);

	/* First line is metadata */
	char *real_start = strchr(content, '\n');
	if (!real_start)
		errx(1, "%s is empty", name);
	real_start++;
	/* And use the rest */
	CrashSummary *res;
	if (!parseCrashSummary(&res, real_start, (const char **)&real_start))
		errx(1, "cannot parse %s as crash summary", name);
	free(content);
	return res;
}

int
main(int argc, char *argv[])
{
	init_sli();

	__set_profiling(root);

	CrashSummary *summary1, *summary2;

	summary1 = read_crash_summary(argv[1]);
	summary2 = read_crash_summary(argv[2]);

	if (crashSummariesTheSame(summary1, summary2))
		printf("The same\n");
	else
		printf("Different\n");

	return 0;
}
