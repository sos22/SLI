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

static IRExpr *
removeRedundantClauses(IRExpr *verificationCondition,
		       internIRExprTable &intern,
		       const reg_set_t &targetRegisters)
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
		summary->verificationCondition =
			removeRedundantClauses(summary->verificationCondition,
					       intern,
					       targetRegisters);
	}

	if (TIMEOUT)
		fprintf(stderr, "timeout processing %s\n", argv[1]);

	FILE *f = fopen(argv[2], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);
	
	return 0;
}
