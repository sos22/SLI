/* Try to convert crash summaries into a more canonical form.  At the
   moment, that pretty much means normalising variable identifiers. */
#include "sli.h"
#include "state_machine.hpp"
#include "allowable_optimisations.hpp"
#include "inferred_information.hpp"
#include "libvex_prof.hpp"
#include "oracle.hpp"
#include "offline_analysis.hpp"
#include "intern.hpp"

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
	std::map<IRExprLoad *, threadAndRegister> canonLoadTable;
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
	threadAndRegister canon_load(IRExprLoad *iel)
	{
		auto it_did_insert = canonLoadTable.insert(std::pair<IRExprLoad *, threadAndRegister>(iel, threadAndRegister::invalid()));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert)
			it->second = threadAndRegister::temp(-1, alloc_temp_id(-1), 0);
		return it->second;
	}

	IRExpr *transformIex(IRExprGet *ieg) {
		return IRExpr_Get(canon_reg(ieg->reg), ieg->ty);
	}
	IRExpr *transformIex(IRExprLoad *iel) {
		return IRExpr_Get(canon_load(iel), iel->ty);
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
	internStateMachineTable t;
	input->loadMachine = internStateMachine(input->loadMachine, t);
	for (auto it = input->storeMachines.begin();
	     it != input->storeMachines.end();
	     it++) {
		(*it)->assumption = internIRExpr((*it)->assumption, t);
		(*it)->machine = internStateMachine((*it)->machine, t);
	}

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

	CrashSummary *summary;
	char *first_line;

	summary = readBugReport(argv[1], &first_line);

	summary = canonicalise_crash_summary(summary);

	FILE *f = fopen(argv[2], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);

	return 0;
}
