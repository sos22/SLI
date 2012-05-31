#include "sli.h"
#include "state_machine.hpp"
#include "allowable_optimisations.hpp"
#include "inferred_information.hpp"
#include "libvex_prof.hpp"
#include "oracle.hpp"
#include "offline_analysis.hpp"

static bool
localSimilarity(IRExpr *a, IRExpr *b, Oracle *)
{
	return definitelyEqual(a, b, AllowableOptimisations::defaultOptimisations);
}

static bool
localSimilarity2(StateMachineSideEffectLoad *smsel1, StateMachineSideEffectLoad *smsel2, Oracle *oracle)
{
	return localSimilarity(smsel1->addr, smsel2->addr, oracle) &&
		threadAndRegister::fullEq(smsel1->target, smsel2->target) &&
		smsel1->type == smsel2->type;
}

static bool
localSimilarity2(StateMachineSideEffectStore *smsel1, StateMachineSideEffectStore *smsel2, Oracle *oracle)
{
	return localSimilarity(smsel1->addr, smsel2->addr, oracle) &&
		localSimilarity(smsel1->data, smsel2->data, oracle);
}

static bool
localSimilarity2(StateMachineSideEffectCopy *smsel1, StateMachineSideEffectCopy *smsel2, Oracle *oracle)
{
	return localSimilarity(smsel1->value, smsel2->value, oracle) &&
		threadAndRegister::fullEq(smsel1->target, smsel2->target);
}

static bool
localSimilarity2(StateMachineSideEffectAssertFalse *smsel1, StateMachineSideEffectAssertFalse *smsel2, Oracle *oracle)
{
	return localSimilarity(smsel1->value, smsel2->value, oracle) &&
		smsel1->reflectsActualProgram == smsel2->reflectsActualProgram;
}

static bool
localSimilarity2(StateMachineSideEffectStartAtomic *, StateMachineSideEffectStartAtomic *, Oracle *)
{
	return true;
}

static bool
localSimilarity2(StateMachineSideEffectEndAtomic *, StateMachineSideEffectEndAtomic *, Oracle *)
{
	return true;
}

static bool
localSimilarity2(StateMachineSideEffectUnreached *, StateMachineSideEffectUnreached *, Oracle *)
{
	return true;
}

static bool
localSimilarity2(StateMachineSideEffectPhi *e1, StateMachineSideEffectPhi *e2, Oracle *)
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
localSimilarity(StateMachineSideEffect *smse1, StateMachineSideEffect *smse2, Oracle *oracle)
{
	if (smse1->type != smse2->type)
		return false;
	switch (smse1->type) {
#define do_case(n)							\
		case StateMachineSideEffect::n:				\
			return localSimilarity2( (StateMachineSideEffect ## n *)smse1, \
						 (StateMachineSideEffect ## n *)smse2, \
						 oracle )
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
localSimilarity(StateMachineUnreached *, StateMachineUnreached *, Oracle *)
{
	return true;
}

static bool
localSimilarity(StateMachineCrash *, StateMachineCrash *, Oracle *)
{
	return true;
}

static bool
localSimilarity(StateMachineNoCrash *, StateMachineNoCrash *, Oracle *)
{
	return true;
}

static bool
localSimilarity(StateMachineSideEffecting *sm1, StateMachineSideEffecting *sm2, Oracle *oracle)
{
	if (!sm1->sideEffect && !sm2->sideEffect)
		return true;
	if (!sm1->sideEffect || !sm2->sideEffect)
		return false;
	return localSimilarity(sm1->sideEffect, sm2->sideEffect, oracle);
}

static bool
localSimilarity(StateMachineBifurcate *sm1, StateMachineBifurcate *sm2, Oracle *oracle)
{
	return localSimilarity(sm1->condition, sm2->condition, oracle);
}

static bool
localSimilarity(StateMachineNdChoice *, StateMachineNdChoice *, Oracle *)
{
	return true;
}

static bool
localSimilarity(StateMachineStub *sm1, StateMachineStub *sm2, Oracle *)
{
	return sm1->target == sm2->target;
}

static bool
stateMachineStatesTheSame(std::set<std::pair<StateMachineState *, StateMachineState *> > &memo,
			  StateMachineState *sm1,
			  StateMachineState *sm2,
			  Oracle *oracle)
{
	if (!memo.insert(std::pair<StateMachineState *, StateMachineState *>(sm1, sm2)).second)
		return true;
	if (sm1->type != sm2->type)
		return false;
	switch (sm1->type) {
#define do_state_type(t)						\
		case StateMachineState:: t :				\
			if (!localSimilarity((StateMachine ## t *)sm1,	\
					     (StateMachine ## t *)sm2,	\
					     oracle))			\
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
		if (!stateMachineStatesTheSame(memo, targets1[x], targets2[x], oracle))
			return false;
	return true;
}

static bool
stateMachinesTheSame(StateMachine *sm1, StateMachine *sm2, Oracle *oracle)
{
	std::set<std::pair<StateMachineState *, StateMachineState *> > memo;
	return stateMachineStatesTheSame(memo, sm1->root, sm2->root, oracle);
}

static bool
crashSummariesTheSame(VexPtr<CrashSummary, &ir_heap> &summary1,
		      VexPtr<CrashSummary, &ir_heap> &summary2,
		      Oracle *oracle,
		      GarbageCollectionToken )
{
	if (!stateMachinesTheSame(summary1->loadMachine, summary2->loadMachine, oracle))
		return false;
	for (auto it = summary1->storeMachines.begin();
	     it != summary1->storeMachines.end();
	     it++) {
		bool found_one = false;
		for (auto it2 = summary2->storeMachines.begin();
		     !found_one && it2 != summary2->storeMachines.end();
		     it2++) {
			if (stateMachinesTheSame((*it)->machine, (*it2)->machine, oracle))
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
			if (stateMachinesTheSame((*it)->machine, (*it2)->machine, oracle))
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
	int fd = open(name, O_RDONLY);
	if (fd < 0)
		err(1, "opening %s", name);
	char *content = readfile(fd);
	/* Discard first line */
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

class RegisterCanonicaliser : public StateMachineTransformer {
	std::map<threadAndRegister, threadAndRegister, threadAndRegister::partialCompare> canonTable;
	std::map<unsigned, unsigned> next_temp_id;
	unsigned alloc_temp_id(unsigned tid) {
		auto it_did_insert = next_temp_id.insert(std::pair<unsigned, unsigned>(tid, 1));
		auto it = it_did_insert.first;
		it->second++;
		return it->second;
	}
	threadAndRegister canon_reg(const threadAndRegister &input)
	{
		auto it_did_insert = canonTable.insert(std::pair<threadAndRegister, threadAndRegister>(input.setGen(0), input.setGen(0)));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert)
			it->second = threadAndRegister::temp(input.tid(), alloc_temp_id(input.tid()), 0);
		return it->second.setGen(input.gen());
	}

	IRExpr *transformIex(IRExprGet *ieg) {
		return IRExpr_Get(canon_reg(ieg->reg), ieg->ty);
	}
	StateMachineSideEffectLoad *transformOneSideEffect(
		StateMachineSideEffectLoad *smsel, bool *done_something)
	{
		StateMachineSideEffectLoad *smsel2 = StateMachineTransformer::transformOneSideEffect(smsel, done_something);
		if (smsel2)
			smsel = smsel2;
		*done_something = true;
		return new StateMachineSideEffectLoad(
			canon_reg(smsel->target),
			smsel->addr,
			smsel->rip,
			smsel->type);
	}
	StateMachineSideEffectCopy *transformOneSideEffect(
		StateMachineSideEffectCopy *smsec, bool *done_something)
	{
		StateMachineSideEffectCopy *smsec2 = StateMachineTransformer::transformOneSideEffect(smsec, done_something);
		if (smsec2)
			smsec = smsec2;
		*done_something = true;
		return new StateMachineSideEffectCopy(
			canon_reg(smsec->target),
			smsec->value);
	}
	StateMachineSideEffectPhi *transformOneSideEffect(
		StateMachineSideEffectPhi *smsep, bool *done_something)
	{
		StateMachineSideEffectPhi *smsep2 = StateMachineTransformer::transformOneSideEffect(smsep, done_something);
		if (smsep2)
			smsep2 = smsep;
		*done_something = true;
		return new StateMachineSideEffectPhi(
			canon_reg(smsep->reg),
			smsep->generations);
	}
};

class SplitSsaGenerations : public StateMachineTransformer {
	std::set<threadAndRegister, threadAndRegister::fullCompare> &phiRegs;
	std::map<threadAndRegister, threadAndRegister, threadAndRegister::fullCompare> canonTable;
	std::map<unsigned, unsigned> next_temp_id;
	unsigned alloc_temp_id(unsigned tid) {
		auto it_did_insert = next_temp_id.insert(std::pair<unsigned, unsigned>(tid, 1));
		auto it = it_did_insert.first;
		it->second++;
		return it->second;
	}
	threadAndRegister canon_reg(const threadAndRegister &input)
	{
		if (phiRegs.count(input))
			return input;
		auto it_did_insert = canonTable.insert(std::pair<threadAndRegister, threadAndRegister>(input, input));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert)
			it->second = threadAndRegister::temp(input.tid(), alloc_temp_id(input.tid()), 0);
		return it->second;
	}

	IRExpr *transformIex(IRExprGet *ieg) {
		return IRExpr_Get(canon_reg(ieg->reg), ieg->ty);
	}
	StateMachineSideEffectLoad *transformOneSideEffect(
		StateMachineSideEffectLoad *smsel, bool *done_something)
	{
		StateMachineSideEffectLoad *smsel2 = StateMachineTransformer::transformOneSideEffect(smsel, done_something);
		if (smsel2)
			smsel = smsel2;
		*done_something = true;
		return new StateMachineSideEffectLoad(
			canon_reg(smsel->target),
			smsel->addr,
			smsel->rip,
			smsel->type);
	}
	StateMachineSideEffectCopy *transformOneSideEffect(
		StateMachineSideEffectCopy *smsec, bool *done_something)
	{
		StateMachineSideEffectCopy *smsec2 = StateMachineTransformer::transformOneSideEffect(smsec, done_something);
		if (smsec2)
			smsec = smsec2;
		*done_something = true;
		return new StateMachineSideEffectCopy(
			canon_reg(smsec->target),
			smsec->value);
	}
public:
	SplitSsaGenerations(std::set<threadAndRegister, threadAndRegister::fullCompare> &_phiRegs)
		: phiRegs(_phiRegs)
	{}
};

static CrashSummary *
canonicalise_crash_summary(CrashSummary *input)
{
	struct : public StateMachineTransformer {
		std::set<threadAndRegister, threadAndRegister::fullCompare> res;
		IRExpr *transformIexPhi(IRExprPhi *phi) {
			for (auto it = phi->generations.begin();
			     it != phi->generations.end();
			     it++)
				res.insert(phi->reg.setGen(*it));
			return IRExprTransformer::transformIex(phi);
		}
		StateMachineSideEffectPhi *trasnformOneSideEffect(
			StateMachineSideEffectPhi *smsep, bool *done_something)
		{
			for (auto it = smsep->generations.begin();
			     it != smsep->generations.end();
			     it++)
				res.insert(smsep->reg.setGen(it->first));
			res.insert(smsep->reg);
			return StateMachineTransformer::transformOneSideEffect(smsep, done_something);
		}
	} phiRegs;
	phiRegs.transform(input->loadMachine);
	for (auto it = input->storeMachines.begin();
	     it != input->storeMachines.end();
	     it++) {
		phiRegs.doit((*it)->assumption);
		phiRegs.transform((*it)->machine);
	}

	SplitSsaGenerations splitter(phiRegs.res);
	input->loadMachine = splitter.transform(input->loadMachine);
	for (auto it = input->storeMachines.begin();
	     it != input->storeMachines.end();
	     it++) {
		(*it)->assumption = splitter.doit((*it)->assumption);
		(*it)->machine = splitter.transform((*it)->machine);
	}

	RegisterCanonicaliser canon;
	input->loadMachine = canon.transform(input->loadMachine);
	for (auto it = input->storeMachines.begin();
	     it != input->storeMachines.end();
	     it++) {
		(*it)->assumption = canon.doit((*it)->assumption);
		(*it)->machine = canon.transform((*it)->machine);
	}
	return input;
}

int
main(int argc, char *argv[])
{
	init_sli();

	__set_profiling(root);

	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(argv[1]);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, argv[2]);
	}
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	VexPtr<CrashSummary, &ir_heap> summary1;
	VexPtr<CrashSummary, &ir_heap> summary2;

	summary1 = read_crash_summary(argv[4]);
	summary2 = read_crash_summary(argv[5]);

	summary1 = canonicalise_crash_summary(summary1);
	summary2 = canonicalise_crash_summary(summary2);

	if (crashSummariesTheSame(summary1, summary2, oracle, ALLOW_GC)) {
		printf("The same\n");
	} else {
		printf("Different\n");
	}
	return 0;
}
