#include "sli.h"
#include "eval_state_machine.hpp"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "inferred_information.hpp"
#include "allowable_optimisations.hpp"
#include "sat_checker.hpp"
#include "nf.hpp"
#include "offline_analysis.hpp"
#include "timers.hpp"

typedef std::set<threadAndRegister, threadAndRegister::fullCompare> reg_set_t;

class TimeoutTimer : public Timer {
public:
	void fired() {
		_timed_out = true;
	}
};
static TimeoutTimer timeoutTimer;

class DummyOracle : public OracleInterface {
	CrashSummary *summary;
	void visit(HeapVisitor &hv) {
		hv(summary);
	}
	bool memoryAccessesMightAlias(const MemoryAccessIdentifier &mai1,
				      const MemoryAccessIdentifier &mai2)
	{
		if (summary->aliasing.empty())
			return true;
		for (auto it = summary->aliasing.begin(); it != summary->aliasing.end(); it++) {
			if ((it->first == mai1 && it->second == mai2) ||
			    (it->first == mai2 && it->second == mai1))
				return true;
		}
		return false;
	}

public:
	DummyOracle(CrashSummary *_summary)
		: summary(_summary)
	{}
	bool memoryAccessesMightAlias(const AllowableOptimisations &, StateMachineSideEffectLoad *l1, StateMachineSideEffectLoad *l2) {
		return memoryAccessesMightAlias(l1->rip, l2->rip);
	}
	bool memoryAccessesMightAlias(const AllowableOptimisations &, StateMachineSideEffectLoad *l1, StateMachineSideEffectStore *l2) {
		return memoryAccessesMightAlias(l1->rip, l2->rip);
	}
	bool memoryAccessesMightAlias(const AllowableOptimisations &, StateMachineSideEffectStore *l1, StateMachineSideEffectStore *l2) {
		return memoryAccessesMightAlias(l1->rip, l2->rip);
	}
	bool memoryAccessesMightAliasCrossThread(const DynAnalysisRip &load, const DynAnalysisRip &store) {
		if (summary->aliasing.empty())
			return true;
		for (auto it = summary->aliasing.begin();
		     it != summary->aliasing.end();
		     it++) {
			if ((load == DynAnalysisRip(it->first.rip.rip) && store == DynAnalysisRip(it->second.rip.rip)) ||
			    (store == DynAnalysisRip(it->first.rip.rip) && load == DynAnalysisRip(it->second.rip.rip)))
				return true;
		}
		return false;
	}
        bool memoryAccessesMightAliasCrossThread(const VexRip &load, const VexRip &store) {
		return memoryAccessesMightAliasCrossThread(DynAnalysisRip(load),
							   DynAnalysisRip(store));
	}
	bool hasConflictingRemoteStores(const AllowableOptimisations &, StateMachineSideEffectMemoryAccess *) {
		return true;
	}
};

static void
enumRegisters(const IRExpr *input, reg_set_t *out)
{
	struct : public IRExprTransformer {
		reg_set_t *out;
		IRExpr *transformIex(IRExprGet *ieg) {
			out->insert(ieg->reg);
			return ieg;
		}
	} doit;
	doit.out = out;
	doit.doit(const_cast<IRExpr *>(input));
}

template <typename t, typename compare>
class lazySetIntersection {
public:
	const std::set<t, compare> &a;
	const std::set<t, compare> &b;
	lazySetIntersection(const std::set<t, compare> &_a,
			    const std::set<t, compare> &_b)
		: a(_a), b(_b)
	{}
	bool empty() const {
		auto it1 = a.begin();
		auto it2 = b.begin();
		compare c;
		while (it1 != a.end() && it2 != b.end()) {
			if (c(*it1, *it2))
				it1++;
			else if (c(*it2, *it1))
				it2++;
			else
				return false;
		}
		return true;
	}
};

template <typename t, typename comp>
static lazySetIntersection<t, comp>
operator &(const std::set<t, comp> &a, const std::set<t, comp> &b)
{
	return lazySetIntersection<t, comp>(a, b);
}

template <typename t, typename comp>
static void
operator |=(std::set<t, comp> &out, const std::set<t, comp> &a)
{
	auto it1 = out.begin();
	for (auto it2 = a.begin(); it2 != a.end(); it2++)
		it1 = out.insert(it1, *it2);
}

template <typename t, typename comp>
static void
operator -=(std::set<t, comp> &out, const std::set<t, comp> &a)
{
	for (auto it = a.begin(); it != a.end(); it++)
		out.erase(*it);
}

static int
findRegisterMultiplicity(const IRExpr *iex, const threadAndRegister &r)
{
	struct _ : public IRExprTransformer {
		const threadAndRegister &r;
		int multiplicity;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (threadAndRegister::fullEq(ieg->reg, r))
				multiplicity++;
			return ieg;
		}
		_(const threadAndRegister &_r)
			: r(_r), multiplicity(0)
		{}
	} doit(r);
	doit.doit(const_cast<IRExpr *>(iex));
	return doit.multiplicity;
}

static IRExpr *
removeRedundantClauses(IRExpr *verificationCondition,
		       internIRExprTable &intern,
		       const reg_set_t &targetRegisters,
		       bool *done_something)
{
	verificationCondition = simplify_via_anf(verificationCondition);
	verificationCondition = convert_to_cnf(verificationCondition);
	if (!verificationCondition) {
		fprintf(stderr, "can't convert verification constraint to CNF\n");
		return verificationCondition;
	}

	verificationCondition = internIRExpr(verificationCondition, intern);
	if (verificationCondition->tag != Iex_Associative ||
	    ((IRExprAssociative *)verificationCondition)->op != Iop_And1)
		verificationCondition = IRExpr_Associative(Iop_And1, verificationCondition, NULL);

	/* First rule: we only want to keep clauses which interfere
	   with the the target variables in some sense. */
	int nr_verification_clauses = ((IRExprAssociative *)verificationCondition)->nr_arguments;
	IRExpr **verification_clauses = ((IRExprAssociative *)verificationCondition)->contents;
	bool precious[nr_verification_clauses];
	for (int i = 0; i < nr_verification_clauses; i++)
		precious[i] = false;
	reg_set_t preciousVariables;
	preciousVariables = targetRegisters;
	int nr_kept = 0;
	bool progress;
	progress = true;
	while (progress && !TIMEOUT) {
		progress = false;
		for (int i = 0; i < nr_verification_clauses; i++) {
			if (precious[i])
				continue;
			reg_set_t vars;
			enumRegisters(verification_clauses[i], &vars);
			if (!(vars & preciousVariables).empty()) {
				precious[i] = true;
				preciousVariables |= vars;
				progress = true;
				nr_kept++;
			}
		}
	}

#ifndef NDEBUG
	{
		int n = 0;
		for (int i = 0; i < nr_verification_clauses; i++)
			if (precious[i])
				n++;
		assert(n == nr_kept);
	}
#endif

	if (nr_kept != nr_verification_clauses)
		*done_something = true;

	if (nr_kept == 0) {
		return IRExpr_Const(IRConst_U1(1));
	} else if (nr_kept == 1) {
		for (int i = 0; i < nr_verification_clauses; i++)
			if (precious[i])
				return verification_clauses[i];
		abort();
	} else if (nr_kept != nr_verification_clauses) {
		IRExprAssociative *k = IRExpr_Associative(nr_kept, Iop_And1);
		for (int i = 0; i < nr_verification_clauses; i++)
			if (precious[i])
				k->contents[k->nr_arguments++] = verification_clauses[i];
		return k;
	} else {
		return verificationCondition;
	}
}

/* Returns true if the expression could be anything at all.  The idea
 * is that if a variable only appears once in the verification
 * condition, and the operators used are appropriate, we can make the
 * value of the expression be anything we want by setting the variable
 * as appropriate.  If a clause in the verification condition is
 * underspecified in this way then it's not actually telling us
 * anything, and so we might as well remove it. */
static bool
clauseUnderspecified(IRExpr *clause,
		     const std::map<threadAndRegister, int, threadAndRegister::fullCompare> &mult)
{
	switch (clause->tag) {
	case Iex_Unop: {
		IRExprUnop *ieu = (IRExprUnop *)clause;
		switch (ieu->op) {
		case Iop_Not1:
		case Iop_Not8:
		case Iop_Not16:
		case Iop_Not32:
		case Iop_Not64:
		case Iop_Neg8:
		case Iop_Neg16:
		case Iop_Neg32:
		case Iop_Neg64:
		case Iop_BadPtr:
			return clauseUnderspecified(ieu->arg, mult);
		case Iop_32Uto64:
			return false;
		default:
			abort();
		}
	}
	case Iex_Binop: {
		IRExprBinop *ieb = (IRExprBinop *)clause;
		switch (ieb->op) {
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
		case Iop_CmpLT8U:
		case Iop_CmpLT16U:
		case Iop_CmpLT32U:
		case Iop_CmpLT64U:
			return clauseUnderspecified(ieb->arg1, mult) ||
				clauseUnderspecified(ieb->arg2, mult);
		case Iop_Shl64:
			return clauseUnderspecified(ieb->arg1, mult) &&
				clauseUnderspecified(ieb->arg2, mult);
		default:
			abort();
		}
	}
	case Iex_Associative: {
		IRExprAssociative *iea = (IRExprAssociative *)clause;
		bool acc;
		if (iea->nr_arguments == 0)
			return false;
		switch (iea->op) {
		case Iop_Add8:
		case Iop_Add16:
		case Iop_Add32:
		case Iop_Add64:
			acc = false;
			for (int i = 0; i < iea->nr_arguments; i++)
				acc |= clauseUnderspecified(iea->contents[i], mult);
			break;
		case Iop_And1:
		case Iop_And8:
		case Iop_And16:
		case Iop_And32:
		case Iop_And64:
		case Iop_Or1:
		case Iop_Or8:
		case Iop_Or16:
		case Iop_Or32:
		case Iop_Or64:
			acc = true;
			for (int i = 0; i < iea->nr_arguments; i++)
				acc &= clauseUnderspecified(iea->contents[i], mult);
			break;
		default:
			abort();
		}
		return acc;
	}
	case Iex_Get: {
		IRExprGet *ieg = (IRExprGet *)clause;
		auto it = mult.find(ieg->reg);
		assert(it != mult.end());
		assert(it->second != 0);
		return it->second == 1;
	}
	default:
		return false;
	}
	abort();
}

static IRExpr *
removeUnderspecifiedClauses(IRExpr *input,
			    internIRExprTable &intern,
			    const reg_set_t &targetRegisters,
			    bool *done_something)
{
	std::map<threadAndRegister, int, threadAndRegister::fullCompare> mult;
	reg_set_t allRegisters;
	enumRegisters(input, &allRegisters);
	for (auto it = allRegisters.begin(); it != allRegisters.end(); it++)
		mult[*it] = findRegisterMultiplicity(input, *it);
	for (auto it = targetRegisters.begin(); it != targetRegisters.end(); it++)
		mult[*it]++;

	int nr_clauses;
	IRExpr **clauses;
	if (input->tag == Iex_Associative &&
	    ((IRExprAssociative *)input)->op == Iop_And1) {
		nr_clauses = ((IRExprAssociative *)input)->nr_arguments;
		clauses = ((IRExprAssociative *)input)->contents;
	} else {
		nr_clauses = 1;
		clauses = &input;
	}

	int nr_killed = 0;
	for (int i = 0; i < nr_clauses; i++) {
		if (clauseUnderspecified(clauses[i], mult)) {
			printf("Kill underspecified clause ");
			ppIRExpr(clauses[i], stdout);
			printf("\n");
			clauses[i] = NULL;
			nr_killed++;
		}
	}
	if (nr_killed == 0)
		return input;
	*done_something = true;
	if (nr_killed == nr_clauses)
		return IRExpr_Const(IRConst_U1(1));
	assert(nr_clauses != 1);
	if (nr_killed == nr_clauses - 1) {
		for (int i = 0; i < nr_clauses; i++)
			if (clauses[i])
				return clauses[i];
		abort();
	}
	int i = 0;
	int j = 0;
	while (j < nr_clauses) {
		while (j < nr_clauses && !clauses[j])
			j++;
		clauses[i++] = clauses[j++];
	}
	((IRExprAssociative *)input)->nr_arguments = i;
	return internIRExpr(input, intern);
}
	
static bool
findTargetRegisters(CrashSummary *summary,
		    OracleInterface *oracle,
		    internIRExprTable &intern,
		    reg_set_t *targetRegisters)
{
	IRExpr *reducedSurvivalConstraint =
		crossProductSurvivalConstraint(
			summary->loadMachine,
			summary->storeMachine,
			oracle,
			IRExpr_Const(IRConst_U1(1)),
			AllowableOptimisations::defaultOptimisations,
			ALLOW_GC);
	if (!reducedSurvivalConstraint) {
		fprintf(stderr, "can't build cross product survival constraint\n");
		return false;
	}

	reducedSurvivalConstraint = simplify_via_anf(reducedSurvivalConstraint);
	reducedSurvivalConstraint = convert_to_cnf(reducedSurvivalConstraint);
	if (!reducedSurvivalConstraint) {
		fprintf(stderr, "can't convert reduced survival constraint to CNF\n");
		return false;
	}
	reducedSurvivalConstraint = internIRExpr(reducedSurvivalConstraint, intern);

	enumRegisters(reducedSurvivalConstraint, targetRegisters);

	return true;
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<CrashSummary, &ir_heap> summary;
	char *first_line;

	timeoutTimer.nextDue = now() + 30;
	timeoutTimer.schedule();

	summary = readBugReport(argv[1], &first_line);
	OracleInterface *oracle = new DummyOracle(summary);

	internIRExprTable intern;
	std::set<threadAndRegister, threadAndRegister::fullCompare> targetRegisters;
	if (findTargetRegisters(summary, oracle, intern, &targetRegisters)) {
		bool progress;
		progress = true;
		while (progress) {
			progress = false;
			summary->verificationCondition =
				removeRedundantClauses(
					summary->verificationCondition,
					intern,
					targetRegisters,
					&progress);
			summary->verificationCondition =
				removeUnderspecifiedClauses(
					summary->verificationCondition,
					intern,
					targetRegisters,
					&progress);
		}
	}

	if (TIMEOUT)
		fprintf(stderr, "timeout processing %s\n", argv[1]);

	FILE *f = fopen(argv[2], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);
	
	return 0;
}
