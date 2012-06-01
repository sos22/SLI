/* Try to convert crash summaries into a more canonical form.  At the
   moment, that pretty much means normalising variable identifiers. */
#include "sli.h"
#include "state_machine.hpp"
#include "allowable_optimisations.hpp"
#include "inferred_information.hpp"
#include "libvex_prof.hpp"
#include "oracle.hpp"
#include "offline_analysis.hpp"

static CrashSummary *
read_crash_summary(const char *name, char **first_line)
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
	*real_start = 0;
	*first_line = strdup(content);

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

	CrashSummary *summary;
	char *first_line;

	summary = read_crash_summary(argv[1], &first_line);

	summary = canonicalise_crash_summary(summary);

	FILE *f = fopen(argv[2], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);

	return 0;
}
