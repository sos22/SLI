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
#include "alloc_mai.hpp"
#include "dummy_oracle.hpp"
#include "MachineAliasingTable.hpp"

#ifndef NDEBUG
static bool debug_subst_equalities = false;
static bool debug_simplify_assuming_survive = false;
static bool debug_functional_underspecification = false;
#else
#define debug_subst_equalities false
#define debug_simplify_assuming_survive false
#define debug_functional_underspecification false
#endif

#define underspecExpression ((IRExpr *)3)

class reg_or_free_var : public Named {
	char *mkName() const {
		if (is_reg)
			return strdup(reg.name());
		else
			return strdup(fv.name());
	}
public:
	bool is_reg;
	threadAndRegister reg;
	MemoryAccessIdentifier fv;
	reg_or_free_var(const threadAndRegister &_reg)
		: is_reg(true), reg(_reg), fv(MemoryAccessIdentifier::uninitialised())
	{}
	reg_or_free_var(const MemoryAccessIdentifier &_fv)
		: is_reg(false), reg(threadAndRegister::invalid()), fv(_fv)
	{}
	bool operator<(const reg_or_free_var &o) const {
		if (is_reg < o.is_reg)
			return true;
		if (o.is_reg < is_reg)
			return false;
		if (is_reg)
			return reg < o.reg;
		else
			return fv < o.fv;
	}
};
static bool
operator==(const IRExpr *a, const reg_or_free_var &b)
{
	if (a->tag == Iex_Get && b.is_reg && ((IRExprGet *)a)->reg == b.reg)
		return true;
	if (a->tag == Iex_FreeVariable && !b.is_reg && ((IRExprFreeVariable *)a)->id == b.fv)
		return true;
	return false;
}

typedef std::set<reg_or_free_var> reg_set_t;

class TimeoutTimer : public Timer {
public:
	void fired() {
		_timed_out = true;
	}
};
static TimeoutTimer timeoutTimer;

static void
enumRegisters(const IRExpr *input, reg_set_t *out)
{
	struct : public IRExprTransformer {
		reg_set_t *out;
		IRExpr *transformIex(IRExprGet *ieg) {
			out->insert(reg_or_free_var(ieg->reg));
			return ieg;
		}
		IRExpr *transformIex(IRExprFreeVariable *ieg) {
			out->insert(reg_or_free_var(ieg->id));
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
	const reg_or_free_var &r;
	int multiplicity;
	IRExpr *transformIex(IRExprGet *ieg) {
		if (ieg == r)
			multiplicity++;
		return ieg;
	}
	IRExpr *transformIex(IRExprFreeVariable *ieg) {
		if (ieg == r)
			multiplicity++;
		return ieg;
	}
	bool rewriteNewStates() const { return false; }
	_findRegisterMultiplicity(const reg_or_free_var &_r)
		: r(_r), multiplicity(0)
	{}
};

static int
findRegisterMultiplicity(const IRExpr *iex, const reg_or_free_var &r)
{
	_findRegisterMultiplicity doit(r);
	doit.doit(const_cast<IRExpr *>(iex));
	return doit.multiplicity;
}


static int
findRegisterMultiplicity(const CrashSummary *sm, const reg_or_free_var &r)
{
	_findRegisterMultiplicity doit(r);
	transformCrashSummary(const_cast<CrashSummary *>(sm), doit);
	return doit.multiplicity;
}

static bool
mentionsHBEdge(IRExpr *a)
{
	struct : public IRExprTransformer {
		bool res;
		IRExpr *transformIex(IRExprHappensBefore *hb) {
			res = true;
			abortTransform();
			return hb;
		}
	} doit;
	doit.res = false;
	doit.doit(a);
	return doit.res;
}

static IRExpr *
removeRedundantClauses(IRExpr *verificationCondition,
		       const reg_set_t &targetRegisters,
		       bool *done_something)
{
	if (verificationCondition->tag == Iex_Const)
		return verificationCondition;

	verificationCondition = simplify_via_anf(verificationCondition);
	{
		IRExpr *v;
		v = convert_to_cnf(verificationCondition);
		if (!v) {
			fprintf(stderr, "can't convert verification constraint to CNF\n");
			return verificationCondition;
		}
		verificationCondition = v;
	}
	if (verificationCondition->tag == Iex_Const)
		return verificationCondition;

	if (verificationCondition->tag != Iex_Associative ||
	    ((IRExprAssociative *)verificationCondition)->op != Iop_And1)
		verificationCondition = IRExpr_Associative(Iop_And1, verificationCondition, NULL);

	/* First rule: we only want to keep clauses which interfere
	   with the the target variables in some sense or which
	   contain HB edges. */
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
			if (mentionsHBEdge(verification_clauses[i]) ||
			    !(vars & preciousVariables).empty()) {
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
		     const std::map<reg_or_free_var, int> &mult)
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
		case Iop_128HIto64:
		case Iop_16to8:
		case Iop_32to1:
		case Iop_32to8:
		case Iop_32to16:
		case Iop_64to1:
		case Iop_64to8:
		case Iop_64to16:
		case Iop_64to32:
		case Iop_128to64:
			return clauseUnderspecified(ieu->arg, mult);
		case Iop_1Uto8:
		case Iop_1Uto32:
		case Iop_1Uto64:
		case Iop_8Uto16:
		case Iop_8Uto32:
		case Iop_8Uto64:
		case Iop_16Uto32:
		case Iop_16Uto64:
		case Iop_32Uto64:
		case Iop_8Sto16:
		case Iop_8Sto32:
		case Iop_8Sto64:
		case Iop_16Sto32:
		case Iop_16Sto64:
		case Iop_32Sto64:
			return false;
		default:
			break;
		}
		break;
	}
	case Iex_Binop: {
		IRExprBinop *ieb = (IRExprBinop *)clause;
		switch (ieb->op) {
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			return clauseUnderspecified(ieb->arg1, mult) ||
				clauseUnderspecified(ieb->arg2, mult);
		case Iop_Shr32:
		case Iop_Shl64:
		case Iop_Shr64:
		case Iop_Sar64:
		case Iop_MullU64:
		case Iop_Mul64:
		case Iop_Mul32:
		case Iop_DivModU128to64:
		case Iop_DivModS128to64:
		case Iop_64HLto128:
		case Iop_CmpLT8U:
		case Iop_CmpLT16U:
		case Iop_CmpLT32U:
		case Iop_CmpLT64U:
		case Iop_CmpLT8S:
		case Iop_CmpLT16S:
		case Iop_CmpLT32S:
		case Iop_CmpLT64S:
		case Iop_CmpLE32U:
		case Iop_CmpLE64U:
			return clauseUnderspecified(ieb->arg1, mult) &&
				clauseUnderspecified(ieb->arg2, mult);
		default:
			break;
		}
		break;
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
		case Iop_Xor8:
		case Iop_Xor16:
		case Iop_Xor32:
		case Iop_Xor64:
			acc = false;
			for (int i = 0; i < iea->nr_arguments; i++)
				acc |= clauseUnderspecified(iea->contents[i], mult);
			return acc;
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
			return acc;
		default:
			break;
		}
		break;
	}
	case Iex_Get: {
		IRExprGet *ieg = (IRExprGet *)clause;
		auto it = mult.find(reg_or_free_var(ieg->reg));
		assert(it != mult.end());
		assert(it->second != 0);
		return it->second == 1;
	}
	case Iex_FreeVariable: {
		IRExprFreeVariable *ieg = (IRExprFreeVariable *)clause;
		auto it = mult.find(reg_or_free_var(ieg->id));
		assert(it != mult.end());
		assert(it->second != 0);
		return it->second == 1;
	}
	case Iex_Const:
	case Iex_GetI:
		return false;
	case Iex_Qop:
		break;
	case Iex_Triop:
		break;
	case Iex_Mux0X: {
		IRExprMux0X *m = (IRExprMux0X *)clause;
#warning could do better here if either argument is underspec and the condition is as well.
		return clauseUnderspecified(m->expr0, mult) &&
			clauseUnderspecified(m->exprX, mult);
	}
	case Iex_CCall:
		return false;
	case Iex_Load:
		return false;
	case Iex_HappensBefore:
		return false;
	case Iex_EntryPoint:
		return false;
	case Iex_ControlFlow:
		return false;
	}
	fprintf(stderr, "%s: ", __func__);
	ppIRExpr(clause, stderr);
	fprintf(stderr, "\n");
	abort();
}

static IRExpr *
removeUnderspecifiedClauses(IRExpr *input,
			    const reg_set_t &targetRegisters,
			    IRExpr *underspecifiedResult,
			    bool *done_something)
{
	std::map<reg_or_free_var, int> mult;
	reg_set_t allRegisters;
	enumRegisters(input, &allRegisters);
	for (auto it = allRegisters.begin(); it != allRegisters.end(); it++)
		mult[*it] = findRegisterMultiplicity(input, *it);
	for (auto it = targetRegisters.begin(); it != targetRegisters.end(); it++)
		mult[*it]++;

	if (TIMEOUT) {
		/* Need to check here because if we've timed out then
		   mult will be wrong, which will then screw up
		   clauseUnderspecified. */
		return input;
	}

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
		return underspecifiedResult;
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
			summary->mai,
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
			if (TIMEOUT)
				return input;
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

	if (debug_subst_equalities)
		printf("Calc multiplicities:\n");
	auto it = things_we_can_remove.begin();
	reg_or_free_var bestReg(*it);
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
			if (left_terms[i] == bestReg) {
				assert(!targetIsOnLeft);
				targetIsOnLeft = true;
			}
			if (left_terms[i]->tag == Iex_Unop &&
			    ((IRExprUnop *)left_terms[i])->op == Iop_Neg64 &&
			    ((IRExprUnop *)left_terms[i])->arg == bestReg) {
				assert(!targetIsOnRight);
				targetIsOnRight = true;
			}
		}
		for (int i = 0; i < nr_right_terms; i++) {
			if (right_terms[i] == bestReg) {
				assert(!targetIsOnRight);
				targetIsOnRight = true;
			}
			if (right_terms[i]->tag == Iex_Unop &&
			    ((IRExprUnop *)right_terms[i])->op == Iop_Neg64 &&
			    ((IRExprUnop *)right_terms[i])->arg == bestReg) {
				assert(!targetIsOnLeft);
				targetIsOnLeft = true;
			}
		}
		if (!targetIsOnLeft && !targetIsOnRight)
			continue;
		assert(!targetIsOnLeft || !targetIsOnRight);

		rewriteClause = clause;
		IRExprAssociative *res = IRExpr_Associative(nr_left_terms + nr_right_terms, Iop_Add64);
		for (int i = 0; i < nr_left_terms; i++) {
			if (left_terms[i] == bestReg)
				continue;
			if (left_terms[i]->tag == Iex_Unop &&
			    ((IRExprUnop *)left_terms[i])->op == Iop_Neg64 &&
			    ((IRExprUnop *)left_terms[i])->arg == bestReg)
				continue;
			res->contents[res->nr_arguments++] =
				targetIsOnLeft ?
				IRExpr_Unop(Iop_Neg64, left_terms[i]) :
				left_terms[i];
		}
		for (int i = 0; i < nr_right_terms; i++) {
			if (right_terms[i] == bestReg)
				continue;
			if (right_terms[i]->tag == Iex_Unop &&
			    ((IRExprUnop *)right_terms[i])->op == Iop_Neg64 &&
			    ((IRExprUnop *)right_terms[i])->arg == bestReg)
				continue;
			res->contents[res->nr_arguments++] =
				!targetIsOnLeft ?
				IRExpr_Unop(Iop_Neg64, right_terms[i]) :
				right_terms[i];
		}

		rewriteResult = res;
		break;
	}
	if (TIMEOUT)
		return input;

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
		const reg_or_free_var &rewriteReg;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (ieg == rewriteReg)
				return coerceTypes(ieg->ty, rewriteResult);
			return ieg;
		}
		IRExpr *transformIex(IRExprFreeVariable *ieg) {
			if (ieg == rewriteReg)
				return coerceTypes(ieg->ty, rewriteResult);
			return ieg;
		}
		IRExpr *transformIRExpr(IRExpr *e, bool *done_something)
		{
			if (e == rewriteClause) {
				*done_something = true;
				return IRExpr_Const(IRConst_U1(1));
			}
			return StateMachineTransformer::transformIRExpr(e, done_something);
		}
		bool rewriteNewStates() const { return false; }
		_(IRExpr *_rewriteClause,
		  IRExpr *_rewriteResult,
		  const reg_or_free_var &_rewriteReg)
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

static void
extractDefinitelyTrueFalse(std::set<IRExpr *> *definitelyTrue,
			   std::set<IRExpr *> *definitelyFalse,
			   bool exprIsTrue,
			   IRExpr *expr)
{
	if (expr->tag == Iex_Unop &&
	    ((IRExprUnop *)expr)->op == Iop_Not1) {
		extractDefinitelyTrueFalse(definitelyTrue,
					   definitelyFalse,
					   !exprIsTrue,
					   ((IRExprUnop *)expr)->arg);
		return;
	}
	if (expr->tag == Iex_Associative &&
	    ((IRExprAssociative *)expr)->op == (exprIsTrue ? Iop_And1 : Iop_Or1) ) {
		IRExprAssociative *a = (IRExprAssociative *)expr;
		for (int i = 0; i < a->nr_arguments; i++)
			extractDefinitelyTrueFalse(definitelyTrue,
						   definitelyFalse,
						   exprIsTrue,
						   a->contents[i]);
		return;
	}

	if (expr->tag == Iex_Const) {
		assert(((IRExprConst *)expr)->con->Ico.U1 == exprIsTrue);
		return;
	}

	if (exprIsTrue)
		definitelyTrue->insert(expr);
	else
		definitelyFalse->insert(expr);
}

static IRExpr *
simplifyAssuming(IRExpr *expr,
		 IRExpr *assumption,
		 bool debug,
		 bool isTrue,
		 bool *progress)
{
	std::set<IRExpr *> definitelyTrue;
	std::set<IRExpr *> definitelyFalse;
	extractDefinitelyTrueFalse(&definitelyTrue,
				   &definitelyFalse,
				   isTrue,
				   assumption);

	if (debug) {
		printf("Definitely true:");
		for (auto it = definitelyTrue.begin(); it != definitelyTrue.end(); it++) {
			printf("\n\t");
			ppIRExpr(*it, stdout);
		}
		printf("\nDefinitely false:");
		for (auto it = definitelyFalse.begin(); it != definitelyFalse.end(); it++) {
			printf("\n\t");
			ppIRExpr(*it, stdout);
		}
		printf("\n");
	}

	struct _ : public IRExprTransformer {
		const std::set<IRExpr *> &definitelyTrue;
		const std::set<IRExpr *> &definitelyFalse;
		IRExpr *transformIRExpr(IRExpr *what, bool *done_something) {
			if (definitelyTrue.count(what)) {
				*done_something = true;
				return IRExpr_Const(IRConst_U1(1));
			}
			if (definitelyFalse.count(what)) {
				*done_something = true;
				return IRExpr_Const(IRConst_U1(0));
			}
			return IRExprTransformer::transformIRExpr(what, done_something);
		}
		_(const std::set<IRExpr *> &_definitelyTrue,
		  const std::set<IRExpr *> &_definitelyFalse)
			: definitelyTrue(_definitelyTrue),
			  definitelyFalse(_definitelyFalse)
		{}
	} doit(definitelyTrue, definitelyFalse);

	return doit.doit(expr, progress);
}

static IRExpr *
simplifyAssumingMachineSurvives(const VexPtr<MaiMap, &ir_heap> &mai,
				const VexPtr<StateMachine, &ir_heap> &machine,
				bool doesSurvive,
				const VexPtr<IRExpr, &ir_heap> &expr,
				const VexPtr<OracleInterface> &oracle,
				bool *progress,
				GarbageCollectionToken token)
{
	if (debug_simplify_assuming_survive) {
		printf("%s input:\nmachine = ", __func__);
		printStateMachine(machine, stdout);
		printf("doesSurvive = %s\n", doesSurvive ? "true" : "false");
		printf("expr = ");
		ppIRExpr(expr, stdout);
		printf("\n");
	}

	IRExpr *survival_constraint;
	if (doesSurvive) {
		survival_constraint = survivalConstraintIfExecutedAtomically(
			mai,
			machine,
			IRExpr_Const(IRConst_U1(1)),
			oracle,
			false,
			AllowableOptimisations::defaultOptimisations,
			token);
	} else {
		survival_constraint = crashingConstraintIfExecutedAtomically(
			mai,
			machine,
			IRExpr_Const(IRConst_U1(1)),
			oracle,
			true,
			AllowableOptimisations::defaultOptimisations,
			token);
	}
	if (!survival_constraint) {
		printf("Cannot derive survival constraint for %s\n", __func__);
		return expr;
	}

	if (debug_simplify_assuming_survive) {
		printf("survival_constraint: ");
		ppIRExpr(survival_constraint, stdout);
		printf("\n");
	}

	internIRExprTable intern;
	IRExpr *expri = internIRExpr(expr.get(), intern);
	survival_constraint = internIRExpr(survival_constraint, intern);

	IRExpr *res = simplifyAssuming(expri, survival_constraint,
				       debug_simplify_assuming_survive,
				       true, progress);
	if (debug_simplify_assuming_survive) {
		printf("Final result: ");
		ppIRExpr(res, stdout);
		printf("\n");
	}
	return res;
}

static IRExpr *
simplifyUsingUnderspecification(
	IRExpr *expr,
	const reg_set_t &targetRegisters,
	IRExpr *underspecified_result,
	bool *progress)
{
	bool p;
	p = true;
	while (!TIMEOUT && p && expr != underspecified_result) {
		p = false;
		expr = removeRedundantClauses(
			expr,
			targetRegisters,
			&p);
		expr = removeUnderspecifiedClauses(
			expr,
			targetRegisters,
			underspecified_result,
			&p);
		*progress |= p;
	}
	return expr;
}

static void
findBooleanMultiplicity(IRExpr *input, std::map<IRExpr *, int> &r)
{
	assert(input->type() == Ity_I1);
	assert(input->tag != Iex_Const);
	if (input->tag == Iex_Associative) {
		IRExprAssociative *iex = (IRExprAssociative *)input;
		assert(iex->op == Iop_And1 || iex->op == Iop_Or1);
		for (int i = 0; i < iex->nr_arguments; i++)
			findBooleanMultiplicity(iex->contents[i], r);
		return;
	} else if (input->tag == Iex_Unop) {
		IRExprUnop *iex = (IRExprUnop *)input;
		if (iex->op == Iop_Not1) {
			findBooleanMultiplicity(iex->arg, r);
			return;
		}
	}
	r[input]++;
}

/* Try to simplify @input a bit by re-expressing it as a nested set of
 * functions. */
/* i.e. pick some variable in @input, say Q, and perform a case split
 * on Q.  That'll give us a version of @input assuming Q is true, call
 * it T, and another version assuming it's false, call it F.  We then
 * rewrite @input to be (Q && T) || (!Q && F).
 */
static IRExpr *
functionalUnderspecification(IRExpr *input,
			     internIRExprTable &intern,
			     const reg_set_t &targetRegisters,
			     int depth)
{
	if (debug_functional_underspecification) {
		printf("%d: %s(", depth, __func__);
		ppIRExpr(input, stdout);
		printf(", {");
		for (auto it = targetRegisters.begin(); it != targetRegisters.end(); it++) {
			if (it != targetRegisters.begin())
				printf(", ");
			printf("%s", it->name());
		}
		printf("})\n");
	}

	if (input->tag == Iex_Const) {
		/* Can't really do anything if we already have a
		 * constant. */
		if (debug_functional_underspecification)
			printf("%d: Input is constant -> nothing to do\n", depth);
		return input;
	}

	input = internIRExpr(input, intern);

	/* Decide what we're going to case split on. */
	IRExpr *splitOn;
	{
		std::map<IRExpr *, int> booleanMultiplicity;
		findBooleanMultiplicity(input, booleanMultiplicity);
		if (debug_functional_underspecification) {
			printf("%d: Multiplicities:\n", depth);
			for (auto it = booleanMultiplicity.begin();
			     it != booleanMultiplicity.end();
			     it++)
				printf("%d: \t%s\t -> %d\n", depth, nameIRExpr(it->first), it->second);
		}
		assert(!booleanMultiplicity.empty());
		if (booleanMultiplicity.size() == 1) {
			/* No point in doing a case split if we only
			 * have one input clause. */
			if (debug_functional_underspecification)
				printf("%d: Input has single variable -> nothing to do\n", depth);
			return input;
		}
		IRExpr *bestExpr;
		bestExpr = (IRExpr *)0xf001; /* Shut the compiler up */
		int bestMultiplicity = -1;
		for (auto it = booleanMultiplicity.begin();
		     it != booleanMultiplicity.end();
		     it++) {
			if (it->second > bestMultiplicity) {
				bestExpr = it->first;
				bestMultiplicity = it->second;
			}
		}
		assert(bestMultiplicity > 0);
		if (debug_functional_underspecification)
			printf("%d: Split on %s, mult %d\n",
			       depth,
			       nameIRExpr(bestExpr), bestMultiplicity);
		splitOn = bestExpr;
	}

	/* splitOn is now Q.  Calculate T and F expressions */
	bool p;
	IRExpr *assumingTrue = simplifyAssuming(input, splitOn, false, true, &p);
	IRExpr *assumingFalse = simplifyAssuming(input, splitOn, false, false, &p);

	if (debug_functional_underspecification)
		printf("%d: T = %s, F = %s\n",
		       depth, nameIRExpr(assumingTrue), nameIRExpr(assumingFalse));

	/* We can now do the full underspecification analysis on each
	   one independently, treating the thing we just split on as
	   being fully specified. */
	reg_set_t newTargets(targetRegisters);
	enumRegisters(splitOn, &newTargets);
	assumingTrue = simplifyUsingUnderspecification(
		assumingTrue,
		newTargets,
		underspecExpression,
		&p);
	assumingFalse = simplifyUsingUnderspecification(
		assumingFalse,
		newTargets,
		underspecExpression,
		&p);

	if (TIMEOUT) {
		if (debug_functional_underspecification)
			printf("%d: Timed out!\n", depth);
		return input;
	}

	if (assumingTrue == underspecExpression ||
	    assumingFalse == underspecExpression) {
		if (assumingFalse == underspecExpression &&
		    assumingTrue == underspecExpression) {
			/* We're going to turn input into
			   (Q && T) || (~Q && F), and
			   we can set T and F to whatever the
			   hell we like.  That means that we can
			   make the final result be whatever
			   we like, so we get a nice
			   underspecification. */
			if (debug_functional_underspecification)
				printf("%d: Result is underspecified\n", depth);
			return underspecExpression;
		}

		/* We're going to expression the input as
		   (Q && T) || (~Q && F), and one of T and F
		   are underspecified, so we can set it to be
		   whatever we want.  Suppose that T is
		   underspecified and F is fully specified.
		   Then we set T = F, and get the
		   result (Q && F) || (~Q && F) i.e.
		   just F. */
		IRExpr *i = assumingTrue;
		if (i == underspecExpression)
			i = assumingFalse;
		assert(i != underspecExpression);

		if (debug_functional_underspecification)
			printf("%d: %s underspecified; take %s\n",
			       depth,
			       i == assumingTrue ? "F" : "T",
			       nameIRExpr(i));

		i = functionalUnderspecification(i,
						 intern,
						 newTargets,
						 depth + 1);

		if (debug_functional_underspecification)
			printf("%d: After recursive simplify: %s\n",
			       depth, nameIRExpr(i));
		i = simplifyIRExpr(i, AllowableOptimisations::defaultOptimisations);
		if (debug_functional_underspecification)
			printf("%d: After final simplify: %s\n",
			       depth, nameIRExpr(i));
		return i;
	}
	if (debug_functional_underspecification)
		printf("%d: After first simplify: T = %s, F = %s\n",
		       depth, nameIRExpr(assumingTrue), nameIRExpr(assumingFalse));

	/* Recursively consider doing another case split. */
	assumingTrue = functionalUnderspecification(assumingTrue,
						    intern,
						    newTargets,
						    depth + 1);
	assumingFalse = functionalUnderspecification(assumingFalse,
						     intern,
						     newTargets,
						     depth + 1);

	if (debug_functional_underspecification)
		printf("%d: After second simplify: T = %s, F = %s\n",
		       depth, nameIRExpr(assumingTrue), nameIRExpr(assumingFalse));

	IRExpr *res = IRExpr_Binop(
		Iop_Or1,
		IRExpr_Binop(
			Iop_And1,
			splitOn,
			assumingTrue),
		IRExpr_Binop(
			Iop_And1,
			IRExpr_Unop(
				Iop_Not1,
				splitOn),
			assumingFalse));
	res = internIRExpr(
		simplifyIRExpr(res, AllowableOptimisations::defaultOptimisations),
		intern);

	if (debug_functional_underspecification)
		printf("%d: Final result: %s\n\n", depth, nameIRExpr(res));

	return res;
}

static CrashSummary *
nonFunctionalSimplifications(
	VexPtr<CrashSummary, &ir_heap> summary,
	const VexPtr<OracleInterface> &oracle,
	GarbageCollectionToken token)
{
	bool progress;
	progress = true;
	while (!TIMEOUT && progress) {
		progress = false;
		bool p;
		p = true;
		while (!TIMEOUT && p) {
			p = false;
			summary =
				substituteEqualities(
					summary,
					&p);
			progress |= p;
		}
		p = true;
		while (!TIMEOUT && p) {
			p = false;
			summary->verificationCondition =
				simplifyAssumingMachineSurvives(
					summary->mai,
					summary->loadMachine,
					true,
					summary->verificationCondition,
					oracle,
					&p,
					token);
			summary->verificationCondition =
				simplifyAssumingMachineSurvives(
					summary->mai,
					summary->storeMachine,
					false,
					summary->verificationCondition,
					oracle,
					&p,
					token);
			progress |= p;
		}
		reg_set_t targetRegisters;
		if (findTargetRegisters(summary, oracle, &targetRegisters, token)) {
			summary->verificationCondition =
				simplifyUsingUnderspecification(
					summary->verificationCondition,
					targetRegisters,
					IRExpr_Const(IRConst_U1(1)),
					&progress);
		}
	}

	return summary;
}

static CrashSummary *
functionalSimplifications(const VexPtr<CrashSummary, &ir_heap> &summary,
			  const VexPtr<OracleInterface> &oracle,
			  GarbageCollectionToken token)
{
	reg_set_t targetRegisters;
	if (findTargetRegisters(summary, oracle, &targetRegisters, token)) {
		internIRExprTable intern;
		IRExpr *e = 
			functionalUnderspecification(
				summary->verificationCondition,
				intern,
				targetRegisters,
				1);
		if (e == underspecExpression)
			summary->verificationCondition = IRExpr_Const(IRConst_U1(1));
		else
			summary->verificationCondition = simplify_via_anf(e);
	}
	return summary;
}

class LoadCanonicaliser : public GarbageCollected<LoadCanonicaliser, &ir_heap> {
	std::vector<std::pair<IRExprLoad *, IRExprFreeVariable *> > canonMap;

	StateMachine *canonicalise(StateMachine *sm);
	IRExpr *canonicalise(IRExpr *iex);
	StateMachine *decanonicalise(StateMachine *sm);
	IRExpr *decanonicalise(IRExpr *iex);
	class canon_transformer : public StateMachineTransformer {
		LoadCanonicaliser *_this;
		IRExpr *transformIex(IRExprLoad *e) {
			for (auto it = _this->canonMap.begin();
			     it != _this->canonMap.end();
			     it++)
				if (it->first == e)
					return it->second;
			return StateMachineTransformer::transformIex(e);
		}
		bool rewriteNewStates() const { return false; }
	public:
		canon_transformer(LoadCanonicaliser *__this)
			: _this(__this)
		{}
	};
	class decanon_transformer : public StateMachineTransformer {
		LoadCanonicaliser *_this;
		IRExpr *transformIex(IRExprFreeVariable *e) {
			for (auto it = _this->canonMap.begin();
			     it != _this->canonMap.end();
			     it++)
				if (it->second == e)
					return it->first;
			return StateMachineTransformer::transformIex(e);
		}
		bool rewriteNewStates() const { return false; }
	public:
		decanon_transformer(LoadCanonicaliser *__this)
			: _this(__this)
		{}
	};
public:
	LoadCanonicaliser(CrashSummary *cs);
	CrashSummary *canonicalise(CrashSummary *cs);
	CrashSummary *decanonicalise(CrashSummary *cs);

	void visit(HeapVisitor &hv) {
		for (auto it = canonMap.begin();
		     it != canonMap.end();
		     it++) {
			hv(it->first);
			hv(it->second);
		}
	}
	NAMED_CLASS
};

/* Should be anonymous and local to
   LoadCanonicaliser::LoadCanonicaliser(), but that triggers bugs in
   gdb and then the debugger crashes. */
struct LCPrivateTransformer : public StateMachineTransformer {
	std::set<std::pair<StateMachineState *, IRExprLoad *> > res;
	StateMachineState *currentState;
	IRExpr *transformIex(IRExprLoad *iex) {
		res.insert(std::pair<StateMachineState *, IRExprLoad *>(currentState, iex));
		return StateMachineTransformer::transformIex(iex);
	}
	StateMachineState *transformState(StateMachineState *s, bool *d) {
		assert(currentState == NULL);
		assert(!*d);
		currentState = s;
		StateMachineState *s2 = StateMachineTransformer::transformState(s, d);
		assert(s2 == NULL);
		assert(!*d);
		assert(currentState == s);
		currentState = NULL;
		return s2;
	}
	bool rewriteNewStates() const { return false; }
	LCPrivateTransformer()
		: currentState(NULL)
	{}
};

LoadCanonicaliser::LoadCanonicaliser(CrashSummary *cs)
{
	LCPrivateTransformer findAllLoads;
	findAllLoads.currentState = NULL;
	transformCrashSummary(cs, findAllLoads);

	MachineAliasingTable mat;
	mat.initialise(cs->storeMachine);
	mat.initialise(cs->loadMachine);

	/* We can degrade a load X to a free variable if we can
	 * disambiguate every LD wrt X.  i.e. a LD X can be converted
	 * to a free variable if, for every other LD Y, either X
	 * definitely aliases with Y (in which case X and Y must have
	 * the same free variable) or X and Y definitely don't alias.
	 */
	std::set<std::pair<StateMachineState *, IRExprLoad *> > pendingLoads(findAllLoads.res);
	while (!pendingLoads.empty()) {
		std::pair<StateMachineState *, IRExprLoad *> k = *pendingLoads.begin();

		bool allowSubst = true;
		std::set<std::pair<StateMachineState *, IRExprLoad *> > definitelyAliasLds;
		definitelyAliasLds.insert(k);
		for (auto it = findAllLoads.res.begin();
		     allowSubst && it != findAllLoads.res.end();
		     it++) {
			if (*it == k)
				continue;
			if (it->second->ty == k.second->ty &&
			    definitelyEqual(k.second->addr, it->second->addr, AllowableOptimisations::defaultOptimisations.enableassumePrivateStack())) {
				assert(!definitelyAliasLds.count(*it));
				definitelyAliasLds.insert(*it);
				assert(it->second->ty == k.second->ty);
			} else if (mat.ptrsMightAlias(k.first, k.second->addr, it->first, it->second->addr,
						      AllowableOptimisations::defaultOptimisations.enableassumePrivateStack()) &&
				   !definitelyNotEqual(k.second->addr, it->second->addr, AllowableOptimisations::defaultOptimisations.enableassumePrivateStack())) {
				allowSubst = false;
				/* If *it and k might alias then
				   neither *it nor k can be converted
				   to free variables. */
				pendingLoads.erase(*it);
				pendingLoads.erase(k);
			}
		}
		if (!allowSubst)
			continue;
		IRExprFreeVariable *fv = new IRExprFreeVariable(
			(*cs->mai)(-1, NULL), k.second->ty, false);
		for (auto it = definitelyAliasLds.begin();
		     it != definitelyAliasLds.end();
		     it++) {
			pendingLoads.erase(*it);
			canonMap.push_back(std::pair<IRExprLoad *, IRExprFreeVariable *>(k.second, fv));
		}
	}
}

StateMachine *
LoadCanonicaliser::canonicalise(StateMachine *sm)
{
	canon_transformer t(this);
	return t.transform(sm);
}

IRExpr *
LoadCanonicaliser::canonicalise(IRExpr *iex)
{
	canon_transformer t(this);
	return t.doit(iex);
}

StateMachine *
LoadCanonicaliser::decanonicalise(StateMachine *sm)
{
	decanon_transformer t(this);
	return t.transform(sm);
}

IRExpr *
LoadCanonicaliser::decanonicalise(IRExpr *iex)
{
	decanon_transformer t(this);
	return t.doit(iex);
}

CrashSummary *
LoadCanonicaliser::canonicalise(CrashSummary *cs)
{
	StateMachine *loadM = canonicalise(cs->loadMachine);
	StateMachine *storeM = canonicalise(cs->storeMachine);
	IRExpr *cond = canonicalise(cs->verificationCondition);
	return new CrashSummary(loadM,
				storeM,
				cond,
				cs->macroSections,
				cs->aliasing,
				cs->mai);
}

CrashSummary *
LoadCanonicaliser::decanonicalise(CrashSummary *cs)
{
	return new CrashSummary(decanonicalise(cs->loadMachine),
				decanonicalise(cs->storeMachine),
				decanonicalise(cs->verificationCondition),
				cs->macroSections,
				cs->aliasing,
				cs->mai);
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
	MachineState *ms = MachineState::readELFExec(argv[2]);
	Thread *thr = ms->findThread(ThreadId(1));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[3]));

	summary = internCrashSummary(summary);

	VexPtr<LoadCanonicaliser, &ir_heap> lc(new LoadCanonicaliser(summary));
	summary = lc->canonicalise(summary);
	VexPtr<OracleInterface> oracleI(oracle);
	summary = nonFunctionalSimplifications(summary, oracleI, ALLOW_GC);
	if (!TIMEOUT)
		summary = functionalSimplifications(summary, oracleI, ALLOW_GC);
	if (!TIMEOUT)
		summary = nonFunctionalSimplifications(
			summary,
			oracleI,
			ALLOW_GC);
	summary = lc->decanonicalise(summary);

	if (TIMEOUT)
		fprintf(stderr, "timeout processing %s\n", argv[1]);

	FILE *f = fopen(argv[4], "w");
	fprintf(f, "%s\n", first_line);
	printCrashSummary(summary, f);
	fclose(f);
	
	return 0;
}
