/* Try to convert crash summaries into a more canonical form.  At the
   moment, that pretty much means normalising variable identifiers and
   converting the verification condition to CNF. */
#include "sli.h"
#include "state_machine.hpp"
#include "allowable_optimisations.hpp"
#include "inferred_information.hpp"
#include "libvex_prof.hpp"
#include "oracle.hpp"
#include "offline_analysis.hpp"
#include "intern.hpp"
#include "sat_checker.hpp"
#include "nf.hpp"

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
	bool rewriteNewStates() const { return false; }
};

static bool
expressionIsClosed(IRExpr *a)
{
	struct : public IRExprTransformer {
		bool res;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (!ieg->reg.isReg() &&
			    ieg->reg.tid() != (unsigned)-1) {
				res = false;
				abortTransform();
			}
			return IRExprTransformer::transformIex(ieg);
		}
	} doit;
	doit.res = true;
	doit.doit(a);
	return doit.res;
}

class SplitSsaGenerations : public StateMachineTransformer {
	std::set<threadAndRegister, threadAndRegister::fullCompare> &phiRegs;
	std::map<threadAndRegister, threadAndRegister, threadAndRegister::fullCompare> canonTable;
	std::map<IRExprLoad *, threadAndRegister> canonLoadTable;
	std::map<IRConst *, threadAndRegister> canonConstTable;
	std::map<unsigned, unsigned> next_temp_id;
	internIRExprTable &internTable;

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
	threadAndRegister canon_const(IRConst *iec)
	{
		auto it_did_insert = canonConstTable.insert(std::pair<IRConst *, threadAndRegister>(iec, threadAndRegister::invalid()));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert)
			it->second = threadAndRegister::temp(-2, alloc_temp_id(-2), 0);
		return it->second;
	}

	IRExpr *transformIex(IRExprGet *ieg) {
		return IRExpr_Get(canon_reg(ieg->reg), ieg->ty);
	}
	IRExpr *transformIex(IRExprLoad *iel) {
		if (expressionIsClosed(iel->addr))
			return IRExpr_Get(canon_load(iel), iel->ty);
		else
			return IRExprTransformer::transformIex(iel);
	}
	IRExpr *transformIex(IRExprConst *iec) {
		switch (iec->con->tag) {
		case Ico_U1:
			return iec;
#define do_type(n)						\
			case Ico_U ## n :			\
				if (iec->con->Ico.U ## n  == 0)	\
					return iec;		\
				break
			do_type(8);
			do_type(16);
			do_type(32);
			do_type(64);
#undef do_type
		case Ico_F64:
		case Ico_F64i:
		case Ico_V128:
			break;
		}
		return IRExpr_Get(canon_const(iec->con), iec->type());
	}
	IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
		IRExpr *res = IRExprTransformer::transformIRExpr(e, done_something);
		if (!res)
			return NULL;
		return internIRExpr(res, internTable);
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
	bool rewriteNewStates() const { return false; }
public:
	SplitSsaGenerations(
		std::set<threadAndRegister, threadAndRegister::fullCompare> &_phiRegs,
		internIRExprTable &_internTable)
		: phiRegs(_phiRegs), internTable(_internTable)
	{}
};

class CanonicaliseThreadIds : public StateMachineTransformer {
	std::map<unsigned, unsigned> canon;
	unsigned next_id;
public:
	unsigned canonTid(unsigned tid) {
		auto it_did_insert = canon.insert(std::pair<unsigned, unsigned>(tid, next_id));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert)
			next_id++;
		assert(it->second != 0);
		return it->second;
	}
private:
	ThreadRip canon_threadrip(const ThreadRip &tr)
	{
		return ThreadRip::mk(canonTid(tr.thread), tr.rip);
	}
	MemoryAccessIdentifier canon_memoryaccessidentifier(const MemoryAccessIdentifier &mai)
	{
		return MemoryAccessIdentifier(canon_threadrip(mai.rip), mai.generation);
	}
	threadAndRegister canon_reg(const threadAndRegister &input)
	{
		if (!input.isValid())
			return input;
		if (input.isTemp())
			return threadAndRegister::temp(canonTid(input.tid()),
						       input.asTemp(),
						       input.gen());
		assert(input.isReg());
		return threadAndRegister::reg(canonTid(input.tid()),
					      input.asReg(),
					      input.gen());
	}
	IRExpr *transformIex(IRExprGet *ieg)
	{
		return IRExpr_Get(canon_reg(ieg->reg), ieg->ty);
	}
	IRExpr *transformIex(IRExprPhi *iep)
	{
		return IRExpr_Phi(canon_reg(iep->reg), iep->generations, iep->ty);
	}
	IRExpr *transformIex(IRExprClientCall *iec)
	{
		int nr_args;
		for (nr_args = 0; iec->args[nr_args]; nr_args++)
			;
		IRExpr **args = alloc_irexpr_array(nr_args + 1);
		for (int i = 0; i < nr_args; i++) {
			bool ign;
			args[i] = transformIRExpr(iec->args[i], &ign);
			if (!args[i])
				args[i] = iec->args[i];
		}
		return IRExpr_ClientCall(iec->calledRip, canon_threadrip(iec->callSite), args);
	}
	IRExpr *transformIex(IRExprLoad *iel)
	{
		bool ign;
		IRExpr *arg = transformIRExpr(iel->addr, &ign);
		if (!arg)
			arg = iel->addr;
		return IRExpr_Load(iel->ty, arg, canon_memoryaccessidentifier(iel->rip));
	}
	IRExpr *transformIex(IRExprHappensBefore *ieh)
	{
		return IRExpr_HappensBefore(
			canon_memoryaccessidentifier(ieh->before),
			canon_memoryaccessidentifier(ieh->after));
	}
	IRExpr *transformIex(IRExprFreeVariable *ief)
	{
		return new IRExprFreeVariable(
			canon_memoryaccessidentifier(ief->id),
			ief->ty,
			ief->isUnique);
	}
	StateMachineSideEffectLoad *transformOneSideEffect(
		StateMachineSideEffectLoad *l, bool *done_something)
	{
		bool ign;
		IRExpr *addr = doit(l->addr, &ign);
		if (!addr)
			addr = l->addr;
		*done_something = true;
		return new StateMachineSideEffectLoad(
			canon_reg(l->target),
			addr,
			canon_memoryaccessidentifier(l->rip),
			l->type);
	}
	StateMachineSideEffectStore *transformOneSideEffect(
		StateMachineSideEffectStore *l, bool *done_something)
	{
		bool ign;
		IRExpr *addr = doit(l->addr, &ign);
		if (!addr)
			addr = l->addr;
		IRExpr *data = doit(l->data, &ign);
		if (!data)
			data = l->data;
		*done_something = true;
		return new StateMachineSideEffectStore(
			addr,
			data,
			canon_memoryaccessidentifier(l->rip));
	}
	StateMachineSideEffectCopy *transformOneSideEffect(
		StateMachineSideEffectCopy *l, bool *done_something)
	{
		bool ign;
		IRExpr *value = doit(l->value, &ign);
		if (!value)
			value = l->value;
		*done_something = true;
		return new StateMachineSideEffectCopy(
			canon_reg(l->target),
			value);
	}
	StateMachineSideEffectPhi *transformOneSideEffect(
		StateMachineSideEffectPhi *p, bool *done_something)
	{
		StateMachineSideEffectPhi *p2 = StateMachineTransformer::transformOneSideEffect(p, done_something);
		if (p2)
			p = p2;
		*done_something = true;
		return new StateMachineSideEffectPhi(
			canon_reg(p->reg),
			p->generations);
	}
	bool rewriteNewStates() const { return false; };
public:
	CanonicaliseThreadIds()
		: next_id(1)
	{}
};

static CrashSummary *
transformCrashSummary(CrashSummary *input, StateMachineTransformer &trans)
{
	input->loadMachine = trans.transform(input->loadMachine);
	input->storeMachine = trans.transform(input->storeMachine);
	input->verificationCondition = trans.doit(input->verificationCondition);
	return input;
}

static IRExpr *
canonicaliseIRExpr(IRExpr *input)
{
	input = simplify_via_anf(input);
	IRExpr *inp2 = convert_to_cnf(input);
	if (inp2)
		return inp2;
	else
		return input;
}

static CrashSummary *
canonicalise_crash_summary(CrashSummary *input)
{
	input->verificationCondition = canonicaliseIRExpr(input->verificationCondition);

	CanonicaliseThreadIds thread_canon;
	for (auto it = input->loadMachine->origin.begin(); it != input->loadMachine->origin.end(); it++)
		it->first = thread_canon.canonTid(it->first);
	for (auto it = input->storeMachine->origin.begin(); it != input->storeMachine->origin.end(); it++)
		it->first = thread_canon.canonTid(it->first);
	input = transformCrashSummary(input, thread_canon);

	struct : public StateMachineTransformer {
		std::set<threadAndRegister, threadAndRegister::fullCompare> res;
		IRExpr *transformIex(IRExprPhi *phi) {
			for (auto it = phi->generations.begin();
			     it != phi->generations.end();
			     it++)
				res.insert(phi->reg.setGen(*it));
			return IRExprTransformer::transformIex(phi);
		}
		StateMachineSideEffectPhi *transformOneSideEffect(
			StateMachineSideEffectPhi *smsep, bool *done_something)
		{
			for (auto it = smsep->generations.begin();
			     it != smsep->generations.end();
			     it++)
				res.insert(smsep->reg.setGen(it->first));
			res.insert(smsep->reg);
			return StateMachineTransformer::transformOneSideEffect(smsep, done_something);
		}
		bool rewriteNewStates() const { return false; }
	} phiRegs;
	phiRegs.transform(input->loadMachine);
	phiRegs.transform(input->storeMachine);
	phiRegs.doit(input->verificationCondition);

	internStateMachineTable t;
	input->loadMachine = internStateMachine(input->loadMachine, t);
	input->storeMachine = internStateMachine(input->storeMachine, t);
	input->verificationCondition = internIRExpr(input->verificationCondition, t);

	SplitSsaGenerations splitter(phiRegs.res, t);
	input = transformCrashSummary(input, splitter);

	RegisterCanonicaliser reg_canon;
	input = transformCrashSummary(input, reg_canon);

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
