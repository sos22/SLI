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
		IRExpr *addr = smsel->addr;
		if (addr->tag != Iex_Get) {
			auto it = freshVariables.find(addr);
			if (it != freshVariables.end()) {
				addr = IRExpr_Get(it->second, Ity_I64);
			} else {
				threadAndRegister r(threadAndRegister::temp(smsel2->target.tid(),
									    alloc_temp_id(smsel2->target.tid()),
									    0));
				freshVariables.insert(std::pair<IRExpr *,threadAndRegister>(addr, r));
				addr = IRExpr_Get(r, Ity_I64);
			}
		}
		return new StateMachineSideEffectLoad(
			canon_reg(smsel->target),
			addr,
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
	StateMachineSideEffectStore *transformOneSideEffect(
		StateMachineSideEffectStore *store, bool *done_something)
	{
		StateMachineSideEffectStore *store2 = StateMachineTransformer::transformOneSideEffect(store, done_something);
		if (!store2)
			store2 = store;
		if (store2->addr->tag != Iex_Get) {
			*done_something = true;
			IRExpr *addr;
			auto it = freshVariables.find(store2->addr);
			if (it != freshVariables.end()) {
				addr = IRExpr_Get(it->second, Ity_I64);
			} else {
				threadAndRegister r(threadAndRegister::temp(store2->rip.tid,
									    alloc_temp_id(store2->rip.tid),
									    0));
				freshVariables.insert(std::pair<IRExpr *, threadAndRegister>(store2->addr, r));
				addr = IRExpr_Get(r, Ity_I64);
			}
			return new StateMachineSideEffectStore(
				addr,
				store2->data,
				store2->rip);
		}
		return store2;
	}

	bool rewriteNewStates() const { return false; }
public:
	std::map<IRExpr *, threadAndRegister> freshVariables;
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

/* Caution: this is done partly in-place. */
class SplitSsaGenerations : public StateMachineTransformer {
	std::set<threadAndRegister> &phiRegs;
	std::set<threadAndRegister> &generatedRegisters;
	std::map<threadAndRegister, threadAndRegister> canonTable;
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
	StateMachineSideEffectPhi *transformOneSideEffect(
		StateMachineSideEffectPhi *smsep, bool *done_something)
	{
		StateMachineSideEffectPhi *smsep2 = StateMachineTransformer::transformOneSideEffect(smsep, done_something);
		if (smsep2)
			smsep = smsep2;
		for (auto it = smsep->generations.begin(); it != smsep->generations.end(); ) {
			if (!generatedRegisters.count( smsep->reg.setGen(it->first) ) ) {
				*done_something = true;
				it = smsep->generations.erase(it);
			} else {
				it++;
			}
		}
		return smsep;
	}
	bool rewriteNewStates() const { return false; }
public:
	SplitSsaGenerations(
		std::set<threadAndRegister> &_phiRegs,
		std::set<threadAndRegister> &_generatedRegisters,
		internIRExprTable &_internTable)
		: phiRegs(_phiRegs),
		  generatedRegisters(_generatedRegisters),
		  internTable(_internTable)
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
		return MemoryAccessIdentifier(mai.where, canonTid(mai.tid), mai.generation);
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
	IRExpr *transformIex(IRExprLoad *iel)
	{
		bool ign;
		IRExpr *arg = transformIRExpr(iel->addr, &ign);
		if (!arg)
			arg = iel->addr;
		return IRExpr_Load(iel->ty, arg);
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

static void
canonicaliseAliasingInformation(CrashSummary *cs)
{
	if (cs->aliasing.empty())
		return;

	std::set<StateMachineSideEffectLoad *> loadLoads;
	std::set<StateMachineSideEffectLoad *> storeLoads;
	std::set<StateMachineSideEffectStore *> loadStores;
	std::set<StateMachineSideEffectStore *> storeStores;
	enumSideEffects(cs->loadMachine, loadLoads);
	enumSideEffects(cs->storeMachine, storeLoads);
	enumSideEffects(cs->loadMachine, loadStores);
	enumSideEffects(cs->storeMachine, storeStores);
	std::set<std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier> > aliases
		(cs->aliasing.begin(), cs->aliasing.end());
	std::set<std::pair<IRExpr *, IRExpr *> > definitelyNotEqual;

#define do_set(s)							\
	for (auto it2 = s.begin(); it2 != s.end(); it2++) {		\
		if ( (*it)->rip == (*it2)->rip )			\
			continue;					\
		std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier> p \
			(std::min( (*it)->rip, (*it2)->rip),		\
			 std::max( (*it)->rip, (*it2)->rip));		\
		if (!aliases.count(p))					\
			definitelyNotEqual.insert(			\
				std::pair<IRExpr *, IRExpr *>(		\
					(*it)->addr,			\
					(*it2)->addr));			\
	}

	for (auto it = loadStores.begin(); it != loadStores.end(); it++) {
		do_set(loadLoads);
	}
	for (auto it = storeStores.begin(); it != storeStores.end(); it++) {
		do_set(loadLoads);
		do_set(loadStores);
		do_set(storeLoads);
		do_set(storeStores);
	}
#undef do_set

	if (!definitelyNotEqual.empty()) {
		IRExprAssociative *assoc = IRExpr_Associative(
			definitelyNotEqual.size() + 1,
			Iop_And1);
		for (auto it = definitelyNotEqual.begin();
		     it != definitelyNotEqual.end();
		     it++) {
			assoc->contents[assoc->nr_arguments++] =
				IRExpr_Unop(
					Iop_Not1,
					IRExpr_Binop(
						Iop_CmpEQ64,
						it->first,
						it->second));
		}
		assoc->contents[assoc->nr_arguments++] =
			cs->verificationCondition;
		cs->verificationCondition = assoc;
	}

	cs->aliasing.clear();
}

static CrashSummary *
canonicalise_crash_summary(CrashSummary *input)
{
	canonicaliseAliasingInformation(input);
	input->verificationCondition = canonicaliseIRExpr(input->verificationCondition);

	CanonicaliseThreadIds thread_canon;
	input = transformCrashSummary(input, thread_canon);

	struct : public StateMachineTransformer {
		std::set<threadAndRegister> res;
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

	std::set<threadAndRegister> generatedRegisters;
	std::set<StateMachineSideEffect *> sideEffects;
	enumSideEffects(input->loadMachine, sideEffects);
	enumSideEffects(input->storeMachine, sideEffects);
	for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
		threadAndRegister r(threadAndRegister::invalid());
		if ((*it)->definesRegister(r))
			generatedRegisters.insert(r);
	}

	SplitSsaGenerations splitter(phiRegs.res, generatedRegisters, t);
	input = transformCrashSummary(input, splitter);

	RegisterCanonicaliser reg_canon;
	input = transformCrashSummary(input, reg_canon);
	if (!reg_canon.freshVariables.empty()) {
		IRExprAssociative *newCond = IRExpr_Associative(reg_canon.freshVariables.size() + 1,
								Iop_And1);
		for (auto it = reg_canon.freshVariables.begin();
		     it != reg_canon.freshVariables.end();
		     it++) {
			newCond->contents[newCond->nr_arguments++] =
				IRExpr_Binop(
					Iop_CmpEQ64,
					IRExpr_Get(it->second, Ity_I64),
					it->first);
		}
		newCond->contents[newCond->nr_arguments++] = input->verificationCondition;
		input->verificationCondition = newCond;
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
