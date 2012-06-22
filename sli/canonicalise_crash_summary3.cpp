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
#include "intern.hpp"

#ifndef NDEBUG
static bool debug_subst_equalities = false;
#else
#define debug_subst_equalities false
#endif

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

struct _findRegisterMultiplicity : public StateMachineTransformer {
	const threadAndRegister &r;
	int multiplicity;
	IRExpr *transformIex(IRExprGet *ieg) {
		if (threadAndRegister::fullEq(ieg->reg, r))
			multiplicity++;
		return ieg;
	}
	bool rewriteNewStates() const { return false; }
	_findRegisterMultiplicity(const threadAndRegister &_r)
		: r(_r), multiplicity(0)
	{}
};

static int
findRegisterMultiplicity(const IRExpr *iex, const threadAndRegister &r)
{
	_findRegisterMultiplicity doit(r);
	doit.doit(const_cast<IRExpr *>(iex));
	return doit.multiplicity;
}


static int
findRegisterMultiplicity(const CrashSummary *sm, const threadAndRegister &r)
{
	_findRegisterMultiplicity doit(r);
	transformCrashSummary(const_cast<CrashSummary *>(sm), doit);
	return doit.multiplicity;
}

static IRExpr *
removeRedundantClauses(IRExpr *verificationCondition,
		       const reg_set_t &targetRegisters,
		       bool *done_something)
{
	if (verificationCondition->tag == Iex_Const)
		return verificationCondition;

	verificationCondition = simplify_via_anf(verificationCondition);
	verificationCondition = convert_to_cnf(verificationCondition);
	if (!verificationCondition) {
		fprintf(stderr, "can't convert verification constraint to CNF\n");
		return verificationCondition;
	}

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

	int nr_kept = 0;
	IRExpr *kept[nr_clauses];
	for (int i = 0; i < nr_clauses; i++) {
		if (!clauseUnderspecified(clauses[i], mult))
			kept[nr_kept++] = clauses[i];
	}
	if (nr_kept == nr_clauses)
		return input;
	*done_something = true;
	if (nr_kept == 0)
		return IRExpr_Const(IRConst_U1(1));
	assert(nr_clauses != 1);
	if (nr_kept == 1) {
		return kept[0];
	}
	IRExprAssociative *res = IRExpr_Associative(nr_kept, Iop_And1);
	memcpy(res->contents, kept, sizeof(IRExpr *) * nr_kept);
	res->nr_arguments = nr_kept;
	return res;
}
	
static bool
findTargetRegisters(const VexPtr<CrashSummary, &ir_heap> &summary,
		    const VexPtr<OracleInterface> &oracle,
		    reg_set_t *targetRegisters,
		    GarbageCollectionToken token)
{
	IRExpr *reducedSurvivalConstraint =
		crossProductSurvivalConstraint(
			summary->loadMachine,
			summary->storeMachine,
			oracle,
			IRExpr_Const(IRConst_U1(1)),
			AllowableOptimisations::defaultOptimisations,
			token);
	if (!reducedSurvivalConstraint) {
		fprintf(stderr, "can't build cross product survival constraint\n");
		return false;
	}

	reducedSurvivalConstraint = simplify_via_anf(reducedSurvivalConstraint);
	if (!reducedSurvivalConstraint) {
		fprintf(stderr, "can't convert reduced survival constraint to CNF\n");
		return false;
	}

	enumRegisters(reducedSurvivalConstraint, targetRegisters);

	return true;
}

static CrashSummary *
substituteEqualities(CrashSummary *input,
		     bool *progress)
{
	if (debug_subst_equalities) {
		printf("Input to substituteEqualities:\n");
		printCrashSummary(input, stdout);
	}

	IRExpr *verificationCondition = input->verificationCondition;
	int nr_clauses;
	IRExpr *const *clauses;
	if (verificationCondition->tag == Iex_Associative &&
	    ((IRExprAssociative *)verificationCondition)->op == Iop_And1) {
		nr_clauses = ((IRExprAssociative *)verificationCondition)->nr_arguments;
		clauses = ((IRExprAssociative *)verificationCondition)->contents;		
	} else {
		nr_clauses = 1;
		clauses = &verificationCondition;
	}

	/* Now we see if there are any equalities we can use to remove
	   some variables. */
	reg_set_t things_we_can_remove;
	for (int i = 0; i < nr_clauses; i++) {
		if (clauses[i]->tag != Iex_Binop)
			continue;
		IRExprBinop *clause = (IRExprBinop *)clauses[i];
		if (clause->op != Iop_CmpEQ64)
			continue;
		/* We assume that the expression is of the form
		   const == x + y + z + ....  We can then eliminate
		   R1 if one of the things on the right is R1 and
		   R1 occurs precisely once on the RHS. */
		reg_set_t topLevelRegisters;
		struct {
			bool f(IRExpr *a, reg_set_t &out) {
				if (a->tag == Iex_Get) {
					out.insert( ((IRExprGet *)a)->reg );
					return true;
				} else if (a->tag == Iex_Unop &&
					   ((IRExprUnop *)a)->op == Iop_Neg64 &&
					   ((IRExprUnop *)a)->arg->tag == Iex_Get) {
					out.insert( ((IRExprGet *)((IRExprUnop *)a)->arg)->reg );
					return true;
				} else {
					return false;
				}
			}
			void operator()(IRExpr *a, reg_set_t &out) {
				if (f(a, out))
					return;
				if (a->tag == Iex_Associative &&
				    ((IRExprAssociative *)a)->op == Iop_Add64) {
					IRExprAssociative *aa = (IRExprAssociative *)a;
					for (int i = 0; i < aa->nr_arguments; i++)
						f(aa->contents[i], out);
				}
			}
		} findTopLevelRegisters;
		findTopLevelRegisters(clause->arg1, topLevelRegisters);
		findTopLevelRegisters(clause->arg2, topLevelRegisters);
		for (auto it = topLevelRegisters.begin(); it != topLevelRegisters.end(); ) {
			int multiplicity = findRegisterMultiplicity(clause, *it);
			assert(multiplicity != 0);
			if (multiplicity != 1) {
				topLevelRegisters.erase(it++);
			} else {
				it++;
			}
		}
		things_we_can_remove |= topLevelRegisters;
	}

	if (debug_subst_equalities) {
		printf("Things we can remove: {");
		for (auto it = things_we_can_remove.begin();
		     it != things_we_can_remove.end();
		     it++) {
			if (it != things_we_can_remove.begin())
				printf(", ");
			printf("%s", it->name());
		}
		printf("}\n");
	}
	if (things_we_can_remove.empty()) {
		if (debug_subst_equalities)
			printf("Cannot remove anything.\n");
		return input;
	}

	printf("Calc multiplicities:\n");
	auto it = things_we_can_remove.begin();
	threadAndRegister bestReg(*it);
	int bestMultiplicity = findRegisterMultiplicity(input, bestReg);
	if (debug_subst_equalities)
		printf("\t%s -> %d\n", bestReg.name(), bestMultiplicity);
	it++;
	while (it != things_we_can_remove.end()) {
		int m = findRegisterMultiplicity(input, *it);
		if (debug_subst_equalities)
			printf("\t%s -> %d\n", it->name(), m);
		if (m > bestMultiplicity) {
			bestReg = *it;
			bestMultiplicity = m;
		}
		it++;
	}
	if (debug_subst_equalities)
		printf("Best register: %s, with mult %d\n",
		       bestReg.name(), bestMultiplicity);

	IRExpr *rewriteResult = NULL;
	IRExpr *rewriteClause = NULL;
	for (int i = 0; i < nr_clauses; i++) {
		if (clauses[i]->tag != Iex_Binop ||
		    ((IRExprBinop *)clauses[i])->op != Iop_CmpEQ64)
			continue;
		if (findRegisterMultiplicity(clauses[i], bestReg) != 1)
			continue;
		IRExprBinop *clause = (IRExprBinop *)clauses[i];
		int nr_left_terms;
		int nr_right_terms;
		IRExpr **left_terms;
		IRExpr **right_terms;
		if (clause->arg1->tag == Iex_Associative &&
		    ((IRExprAssociative *)clause->arg1)->op == Iop_Add64) {
			nr_left_terms = ((IRExprAssociative *)clause->arg1)->nr_arguments;
			left_terms = ((IRExprAssociative *)clause->arg1)->contents;
		} else {
			nr_left_terms = 1;
			left_terms = &clause->arg1;
		}
		if (clause->arg2->tag == Iex_Associative &&
		    ((IRExprAssociative *)clause->arg2)->op == Iop_Add64) {
			nr_right_terms = ((IRExprAssociative *)clause->arg2)->nr_arguments;
			right_terms = ((IRExprAssociative *)clause->arg2)->contents;
		} else {
			nr_right_terms = 1;
			right_terms = &clause->arg2;
		}

		bool targetIsOnLeft = false;
		bool targetIsOnRight = false;
		for (int i = 0; i < nr_left_terms; i++) {
			if (left_terms[i]->tag == Iex_Get &&
			    threadAndRegister::fullEq(((IRExprGet *)left_terms[i])->reg, bestReg)) {
				assert(!targetIsOnLeft);
				targetIsOnLeft = true;
			}
			if (left_terms[i]->tag == Iex_Unop &&
			    ((IRExprUnop *)left_terms[i])->op == Iop_Neg64 &&
			    ((IRExprUnop *)left_terms[i])->arg->tag == Iex_Get &&
			    threadAndRegister::fullEq(((IRExprGet *)((IRExprUnop *)left_terms[i])->arg)->reg, bestReg)) {
				assert(!targetIsOnRight);
				targetIsOnRight = true;
			}
		}
		for (int i = 0; i < nr_right_terms; i++) {
			if (right_terms[i]->tag == Iex_Get &&
			    threadAndRegister::fullEq(((IRExprGet *)right_terms[i])->reg, bestReg)) {
				assert(!targetIsOnRight);
				targetIsOnRight = true;
			}
			if (right_terms[i]->tag == Iex_Unop &&
			    ((IRExprUnop *)right_terms[i])->op == Iop_Neg64 &&
			    ((IRExprUnop *)right_terms[i])->arg->tag == Iex_Get &&
			    threadAndRegister::fullEq(((IRExprGet *)((IRExprUnop *)right_terms[i])->arg)->reg, bestReg)) {
				assert(!targetIsOnLeft);
				targetIsOnLeft = true;
			}
		}
		assert(targetIsOnLeft == !targetIsOnRight);

		rewriteClause = clause;
		IRExprAssociative *res = IRExpr_Associative(nr_left_terms + nr_right_terms, Iop_Add64);
		for (int i = 0; i < nr_left_terms; i++) {
			if (left_terms[i]->tag == Iex_Get &&
			    threadAndRegister::fullEq(((IRExprGet *)left_terms[i])->reg, bestReg))
				continue;
			if (left_terms[i]->tag == Iex_Unop &&
			    ((IRExprUnop *)left_terms[i])->op == Iop_Neg64 &&
			    ((IRExprUnop *)left_terms[i])->arg->tag == Iex_Get &&
			    threadAndRegister::fullEq(((IRExprGet *)((IRExprUnop *)left_terms[i])->arg)->reg, bestReg))
				continue;
			res->contents[res->nr_arguments++] =
				targetIsOnLeft ?
				IRExpr_Unop(Iop_Neg64, left_terms[i]) :
				left_terms[i];
		}
		for (int i = 0; i < nr_right_terms; i++) {
			if (right_terms[i]->tag == Iex_Get &&
			    threadAndRegister::fullEq(((IRExprGet *)right_terms[i])->reg, bestReg))
				continue;
			if (right_terms[i]->tag == Iex_Unop &&
			    ((IRExprUnop *)right_terms[i])->op == Iop_Neg64 &&
			    ((IRExprUnop *)right_terms[i])->arg->tag == Iex_Get &&
			    threadAndRegister::fullEq(((IRExprGet *)((IRExprUnop *)right_terms[i])->arg)->reg, bestReg))
				continue;
			res->contents[res->nr_arguments++] =
				!targetIsOnLeft ?
				IRExpr_Unop(Iop_Neg64, right_terms[i]) :
				right_terms[i];
		}

		rewriteResult = res;
		break;
	}
	assert(rewriteResult != NULL);
	assert(rewriteClause != NULL);
	if (debug_subst_equalities) {
		printf("Rewrite clause: ");
		ppIRExpr(rewriteClause, stdout);
		printf("\n");
		printf("Rewrite result: ");
		ppIRExpr(rewriteResult, stdout);
		printf("\n");
	}
	rewriteResult = simplifyIRExpr(rewriteResult, AllowableOptimisations::defaultOptimisations);

	if (debug_subst_equalities) {
		printf("Rewrite result after optimisation: ");
		ppIRExpr(rewriteResult, stdout);
		printf("\n");
	}
	struct _ : public StateMachineTransformer {
		IRExpr *rewriteClause;
		IRExpr *rewriteResult;
		const threadAndRegister &rewriteReg;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (threadAndRegister::fullEq(ieg->reg, rewriteReg))
				return rewriteResult;
			return ieg;
		}
		IRExpr *transformIRExpr(IRExpr *e, bool *done_something)
		{
			if (e == rewriteClause)
				return e;
			return StateMachineTransformer::transformIRExpr(e, done_something);
		}
		bool rewriteNewStates() const { return false; }
		_(IRExpr *_rewriteClause,
		  IRExpr *_rewriteResult,
		  const threadAndRegister &_rewriteReg)
			: rewriteClause(_rewriteClause),
			  rewriteResult(_rewriteResult),
			  rewriteReg(_rewriteReg)
		{}
	} doit(rewriteClause, rewriteResult, bestReg);

	input = transformCrashSummary(input, doit, progress);
	input->verificationCondition = simplifyIRExpr(
		input->verificationCondition,
		AllowableOptimisations::defaultOptimisations);
	if (debug_subst_equalities) {
		printf("Result of rewrite:\n");
		printCrashSummary(input, stdout);
		printf("\n");
	}
	return input;
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
	VexPtr<OracleInterface> oracle(new DummyOracle(summary));

	bool progress;
	progress = true;
	while (!TIMEOUT && progress) {
		progress = false;
		reg_set_t targetRegisters;
		bool p;
		if (findTargetRegisters(summary, oracle, &targetRegisters, ALLOW_GC)) {
			p = true;
			while (p) {
				p = false;
				summary->verificationCondition =
					removeRedundantClauses(
						summary->verificationCondition,
						targetRegisters,
						&p);
				summary->verificationCondition =
					removeUnderspecifiedClauses(
						summary->verificationCondition,
						targetRegisters,
						&p);
				progress |= p;
			}
		}
		p = true;
		while (p) {
			p = false;
			summary =
				substituteEqualities(
					summary,
					&p);
			progress |= p;
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
