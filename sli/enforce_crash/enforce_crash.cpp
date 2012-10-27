#include <sys/fcntl.h>
#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "offline_analysis.hpp"
#include "intern.hpp"
#include "genfix.hpp"
#include "dnf.hpp"
#include "simplify_ordering.hpp"
#include "enforce_crash.hpp"
#include "allowable_optimisations.hpp"
#include "alloc_mai.hpp"
#include "sat_checker.hpp"

#ifndef NDEBUG
static bool debug_declobber_instructions = false;
#else
#define debug_declobber_instructuions false
#endif

unsigned long
__trivial_hash_function(const VexRip &vr)
{
	return vr.hash();
}

void
instrToInstrSetMap::print(FILE *f) const
{
	for (auto it = begin(); it != end(); it++) {
		fprintf(f, "%s -> {", it->first->label.name());
		for (auto it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			fprintf(f, "%s", (*it2)->label.name());
		}
		fprintf(f, "}\n");
	}
}

static bool
exprUsesRegister(IRExpr *e, const IRExpr *e2)
{
	struct : public IRExprTransformer {
		const IRExpr *needle;
		bool res;
		IRExpr *transformIex(IRExprGet *ieg) {
			if (ieg == needle) {
				res = true;
				abortTransform();
			}
			return ieg;
		}
		IRExpr *transformIex(IRExprEntryPoint *ieg) {
			if (ieg == needle) {
				res = true;
				abortTransform();
			}
			return ieg;
		}
	} doit;
	doit.needle = e2;
	doit.res = false;
	doit.doit(e);
	return doit.res;
}

static bool
instrUsesExpr(Instruction<ThreadCfgLabel> *instr, IRExpr *expr, crashEnforcementData &ced)
{
	{
		auto it = ced.happensBeforePoints.find(instr->rip);
		if (it != ced.happensBeforePoints.end()) {
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				happensBeforeEdge *hbe = *it2;
				if (hbe->before->rip == instr->rip) {
					for (auto it3 = hbe->content.begin();
					     it3 != hbe->content.end();
					     it3++) {
						if (*it3 == expr)
							return true;
					}
				}
			}
		}
	}

	{
		auto it = ced.expressionEvalPoints.find(instr->rip);
		if (it != ced.expressionEvalPoints.end()) {
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				if (exprUsesRegister(it2->e, expr))
					return true;
			}
		}
	}
	return false;
}

static void
optimiseHBContent(crashEnforcementData &ced)
{
	std::set<happensBeforeEdge *> hbEdges;
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
	     it++)
		hbEdges.insert(it->second.begin(), it->second.end());
	bool progress = true;
	while (progress) {
		progress = false;
		for (auto it = hbEdges.begin(); it != hbEdges.end(); it++) {
			happensBeforeEdge *hbe = *it;
			for (unsigned x = 0; x < hbe->content.size(); ) {
				bool must_keep = false;
				std::queue<Instruction<ThreadCfgLabel> *> pending;
				pending.push(hbe->after);
				while (!must_keep && !pending.empty()) {
					Instruction<ThreadCfgLabel> *l = pending.front();
					pending.pop();
					if (instrUsesExpr(l, hbe->content[x], ced))
						must_keep = true;
					for (unsigned y = 0; y < l->successors.size(); y++)
						pending.push(l->successors[y].instr);
				}
				if (must_keep) {
					x++;
				} else {
					hbe->content.erase(hbe->content.begin() + x);
					progress = true;
				}
			}
		}
	}
}

static bool
buildCED(const SummaryId &summaryId,
	 DNF_Conjunction &c,
	 std::map<ConcreteThread, std::set<CfgLabel> > &rootsCfg,
	 CrashSummary *summary,
	 crashEnforcementData *out,
	 ThreadAbstracter &abs,
	 int &next_hb_id,
	 AddressSpace *as)
{
	/* Figure out what we actually need to keep track of */
	std::set<IRExpr *> neededExpressions;
	for (unsigned x = 0; x < c.size(); x++)
		enumerateNeededExpressions(c[x].second, neededExpressions);

	*out = crashEnforcementData(summaryId, *summary->mai, neededExpressions, abs, rootsCfg, c, next_hb_id, summary, as);
	optimiseHBContent(*out);
	return true;
}

static bool
analyseHbGraph(DNF_Conjunction &c, CrashSummary *summary)
{
	std::set<IRExprHappensBefore *, HBOrdering> hb;
	std::set<IRExprHappensBefore *, HBOrdering> assumption;

	extractImplicitOrder(summary->loadMachine, assumption);
	extractImplicitOrder(summary->storeMachine, assumption);
	for (unsigned x = 0; x < c.size(); x++) {
		if (c[x].second->tag == Iex_HappensBefore) {
			IRExprHappensBefore *g = (IRExprHappensBefore *)c[x].second;
			IRExprHappensBefore *h;
			if (c[x].first) {
				h = (IRExprHappensBefore *)IRExpr_HappensBefore(g->after, g->before);
			} else {
				h = g;
			}
			hb.insert(h);
		}
	}

	if (!simplifyOrdering(hb, assumption)) {
		/* Contradiction, get out */
		return false;
	}

	/* Build the results */
	DNF_Conjunction out;
	for (unsigned x = 0; x < c.size(); x++)
		if (c[x].second->tag != Iex_HappensBefore)
			out.push_back(c[x]);
	for (auto it = hb.begin();
	     it != hb.end();
	     it++)
		out.push_back(NF_Atom(false, *it));

	c = out;

	return true;
}

/* Check whether the ordering in @c is consistent with a total
   ordering over threads.  Those don't actually enforce any
   concurrency, so aren't very interesting. */
static bool
consistentOrdering(DNF_Conjunction &c)
{
	int thread_a;
	int thread_b;
	bool found_a_thread;
	for (auto it = c.begin(); it != c.end(); it++) {
		if (it->second->tag == Iex_HappensBefore) {
			IRExprHappensBefore *e = (IRExprHappensBefore *)it->second;
			if (!found_a_thread) {
				thread_a = e->before.tid;
				thread_b = e->after.tid;
				found_a_thread = true;
			} else {
				if (thread_a != e->before.tid ||
				    thread_b != e->after.tid)
					return false;
			}
		}
	}
	return true;
}

/* Munge a side condition to make it easier to evaluate.  This is
   allowed to slightly change the value of the condition if that makes
   the eval much easier, but shouldn't push things too far. */
/* Generally, taking a true expression and making it false is more
   dangerous than taking a false expression and making it true */
static IRExpr *
heuristicSimplify(IRExpr *e)
{
	bool done_something = false;
	if (e->tag != Iex_Binop ||
	    ((IRExprBinop *)e)->op != Iop_CmpEQ64)
		return e;

	/* First rule: 0 == a - b -> a == b */
	IRExprBinop *ieb = (IRExprBinop *)e;
	if (ieb->arg1->tag == Iex_Const &&
	    ((IRExprConst *)ieb->arg1)->con->Ico.U64 == 0 &&
	    ieb->arg2->tag == Iex_Associative &&
	    ((IRExprAssociative *)ieb->arg2)->op == Iop_Add64 &&
	    ((IRExprAssociative *)ieb->arg2)->nr_arguments == 2 &&
	    ((IRExprAssociative *)ieb->arg2)->contents[1]->tag == Iex_Unop &&
	    ((IRExprUnop *)((IRExprAssociative *)ieb->arg2)->contents[1])->op == Iop_Neg64) {
		ieb->arg1 = ((IRExprAssociative *)ieb->arg2)->contents[0];
		ieb->arg2 = ((IRExprUnop *)((IRExprAssociative *)ieb->arg2)->contents[1])->arg;
		done_something = true;
	}

	/* Second rule: f(a) == f(b) -> a == b, if f is sufficiently
	   injective. */
	if (ieb->arg1->tag == ieb->arg2->tag) {
		switch (ieb->arg1->tag) {
		case Iex_Binop: {
			IRExprBinop *l = (IRExprBinop *)ieb->arg1;
			IRExprBinop *r = (IRExprBinop *)ieb->arg2;
			if (l->op != r->op)
				break;
			switch (l->op) {
			case Iop_Shl64: /* x << k is treated as
					 * injective if k is a small
					 * constant, because most of
					 * the time you don't get
					 * overflow. */
				if (r->arg2->tag == Iex_Const &&
				    l->arg2->tag == Iex_Const &&
				    ((IRExprConst *)r->arg2)->con->Ico.U8 ==
				         ((IRExprConst *)l->arg2)->con->Ico.U8 &&
				    ((IRExprConst *)l->arg2)->con->Ico.U8 < 8) {
					ieb->arg1 = l->arg1;
					ieb->arg2 = r->arg1;
					done_something = true;
				}
				break;
			default:
				break;
			}
			break;
		}
		case Iex_Unop: {
			IRExprUnop *l = (IRExprUnop *)ieb->arg1;
			IRExprUnop *r = (IRExprUnop *)ieb->arg2;
			if (l->op != r->op)
				break;
			switch (l->op) {
			case Iop_32Sto64:
				/* This one actually is injective */
				ieb->arg1 = l->arg;
				ieb->arg2 = r->arg;
				done_something = true;
				break;
			default:
				break;
			}
			break;
		}
		default:
			break;
		}
	}

	if (done_something)
		return heuristicSimplify(e);
	return e;
}

/* We're allowed to make errors where the approximation returns 1 and
   the true value is 0 */
#define ERROR_POSITIVE 1
/* Allow errors where the approximation returns 0 and the true value
   is 1. */
#define ERROR_NEGATIVE 2

/* We can't get at the values of free variables from the run-time
   enforcer, so we might as well remove them now. */
/* Return value is either NULL, if we can't compute any approximation
   to @what with the desired error types, or an expression which
   approximates @what.  In the latter case, *@errors_produced will be
   set to a mask of the types of errors introduced. */
static IRExpr *
removeFreeVariables(IRExpr *what, int errors_allowed, int *errors_produced)
{
	if (errors_allowed == (ERROR_POSITIVE | ERROR_NEGATIVE))
		return NULL;
	if (errors_allowed != 0) {
		assert(errors_produced != NULL);
		*errors_produced = 0;
	}
	switch (what->tag) {
	case Iex_Get: {
		auto *i = (IRExprGet *)what;
		/* Interpreters can only get at the ``normal'' integer
		   registers, plus FS_ZERO, so we need to treat the
		   other ones as being free. */
		if (i->reg.isReg() &&
		    (unsigned)i->reg.asReg() > offsetof(VexGuestAMD64State, guest_R15) &&
		    (unsigned)i->reg.asReg() != offsetof(VexGuestAMD64State, guest_FS_ZERO))
			return NULL;
		return what;
	}
	case Iex_GetI: {
		auto *i = (IRExprGetI *)what;
		IRExpr *ix = removeFreeVariables(i->ix, 0, NULL);
		if (!ix)
			return NULL;
		if (ix == i->ix)
			return i;
		return IRExpr_GetI(i->descr, ix,  i->bias, i->tid);
	}
	case Iex_Qop: {
		abort();
		auto *i = (IRExprQop *)what;
		auto arg1 = removeFreeVariables(i->arg1, 0, NULL);
		if (!arg1)
			return NULL;
		auto arg2 = removeFreeVariables(i->arg2, 0, NULL);
		if (!arg2)
			return NULL;
		auto arg3 = removeFreeVariables(i->arg3, 0, NULL);
		if (!arg3)
			return NULL;
		auto arg4 = removeFreeVariables(i->arg4, 0, NULL);
		if (!arg4)
			return NULL;
		if (arg1 == i->arg1 && arg2 == i->arg2 && arg3 == i->arg3 && arg4 == i->arg4)
			return i;
		return IRExpr_Qop(
			i->op, arg1, arg2, arg3, arg4);
	}
	case Iex_Triop: {
		abort();
		auto *i = (IRExprTriop *)what;
		auto arg1 = removeFreeVariables(i->arg1, 0, NULL);
		if (!arg1)
			return NULL;
		auto arg2 = removeFreeVariables(i->arg2, 0, NULL);
		if (!arg2)
			return NULL;
		auto arg3 = removeFreeVariables(i->arg3, 0, NULL);
		if (!arg3)
			return NULL;
		if (arg1 == i->arg1 && arg2 == i->arg2 && arg3 == i->arg3)
			return i;
		return IRExpr_Triop(
			i->op, arg1, arg2, arg3);
	}
	case Iex_Binop: {
		auto i = (IRExprBinop *)what;
		if (i->op == Iop_CmpF32 || i->op == Iop_CmpF64 ||
		    i->op == Iop_64HLtoV128)
			return NULL;
		auto arg1 = removeFreeVariables(i->arg1, 0, NULL);
		auto arg2 = removeFreeVariables(i->arg2, 0, NULL);
		if (arg1 == i->arg1 && arg2 == i->arg2)
			return what;
		if (arg1 && arg2)
			return IRExpr_Binop(i->op, arg1, arg2);
		switch (i->op) {
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
		case Iop_CmpLT8U:
		case Iop_CmpLT16U:
		case Iop_CmpLT32U:
		case Iop_CmpLT64U:
		case Iop_Shr64:
			return NULL;
		default:
			abort();
		}
		break;
	}
	case Iex_Unop: {
		auto i = (IRExprUnop *)what;
		if (i->op == Iop_V128to64 || i->op == Iop_ReinterpI32asF32)
			return NULL;
		int errors2;
		int errors3;
		switch (errors_allowed) {
		case 0:
			errors2 = 0;
			break;
		case ERROR_POSITIVE:
			errors2 = ERROR_NEGATIVE;
			break;
		case ERROR_NEGATIVE:
			errors2 = ERROR_POSITIVE;
			break;
		default:
			abort();
		}
		auto arg = removeFreeVariables(i->arg, errors2, &errors3);
		if (!arg)
			return NULL;
		if (arg == i->arg)
			return i;
		if (errors_produced) {
			*errors_produced = 0;
			if (errors3 & ERROR_NEGATIVE)
				*errors_produced |= ERROR_POSITIVE;
			if (errors3 & ERROR_POSITIVE)
				*errors_produced |= ERROR_NEGATIVE;
		}
		return IRExpr_Unop(i->op, arg);
	}
	case Iex_Load: {
		auto i = (IRExprLoad *)what;
		auto addr = removeFreeVariables(i->addr, 0, NULL);
		if (!addr)
			return NULL;
		if (addr == i->addr)
			return what;
		return IRExpr_Load(i->ty, addr);
	}
	case Iex_Const:
		return what;
	case Iex_CCall:
		/* The interpreter can't evaluate these, so might as
		   well get rid of them as well. */
		return NULL;
	case Iex_Mux0X: {
		/* mux0x is unevaluatable if any of the arguments are
		   unevaluatable.  That's not ideal; it'd be better to
		   try to preserve whichever arguments are eval-able.
		   The problem is that we don't have any ``preferred''
		   value at this stage, so we can't put in a sensible
		   default for the other one. */
		auto i = (IRExprMux0X *)what;
		auto cond = removeFreeVariables(i->cond, 0, NULL);
		int err0, errX;
		auto expr0 = removeFreeVariables(i->expr0, errors_allowed, &err0);
		auto exprX = removeFreeVariables(i->exprX, errors_allowed, &errX);
		if (cond == i->cond && expr0 == i->expr0 && exprX == i->exprX)
			return i;
		if (errors_allowed == 0 && (expr0 == NULL || exprX == NULL || cond == NULL))
			return NULL;
		if (!expr0 && !exprX)
			return NULL;
		*errors_produced = err0 | errX;
		if (errors_allowed && (!expr0 || !exprX) && expr0->type() == Ity_I1) {
			IRExpr *def;
			if (errors_allowed & ERROR_POSITIVE) {
				def = IRExpr_Const(IRConst_U1(1));
				*errors_produced |= ERROR_POSITIVE;
			} else {
				def = IRExpr_Const(IRConst_U1(0));
				*errors_produced |= ERROR_NEGATIVE;
			}
			if (!expr0)
				expr0 = def;
			if (!exprX)
				exprX = def;
			
		}
		if (!cond && expr0->type() == Ity_I1) {
			/* mux0x(cond, expr0, exprx) = (cond && exprX) || (!cond && expr0).
			   If cond is unknown then that can be approximated to
			   either exprX && expr0 or exprX || expr0, depending on
			   the type of error allowed. */
			if (errors_allowed & ERROR_NEGATIVE) {
				*errors_produced |= ERROR_NEGATIVE;
				return IRExpr_Binop(
					Iop_And1,
					expr0,
					exprX);
			} else {
				*errors_produced |= ERROR_POSITIVE;
				return IRExpr_Binop(
					Iop_Or1,
					expr0,
					exprX);
			}
		}
		
		if (!cond || !expr0 || !exprX) {
			/* Out of ideas */
			return NULL;
		}

		return IRExpr_Mux0X(cond, expr0, exprX);
	}
	case Iex_Associative: {
		auto i = (IRExprAssociative *)what;
		int idx;
		IRExpr *a;
		int err_a;
		for (idx = 0; idx < i->nr_arguments; idx++) {
			a = removeFreeVariables(i->contents[idx], errors_allowed, &err_a);
			if (a != i->contents[idx])
				break;
		}
		if (idx == i->nr_arguments)
			return i;
		IRExprAssociative *newI = (IRExprAssociative *)IRExpr_Associative(i->nr_arguments, i->op);
		int idx2 = idx;
		memcpy(newI->contents, i->contents, idx * sizeof(IRExpr *));
		goto l1;

		while (idx < i->nr_arguments) {
			a = removeFreeVariables(i->contents[idx], errors_allowed, &err_a);
		l1:
			if (!a || err_a) {
				switch (i->op) {
				case Iop_Add8:
				case Iop_Add16:
				case Iop_Add32:
				case Iop_Add64:
					/* k + x, where x is
					 * completely unknown, is
					 * itself unknown. */
					return NULL;
				case Iop_And1:
				case Iop_And8:
				case Iop_And16:
				case Iop_And32:
				case Iop_And64:
					if (!a) {
						/* k & x, where x is
						 * completely unknown.
						 * Approximate it by
						 * just k with a
						 * positive error. */
						if (errors_allowed & ERROR_POSITIVE)
							*errors_produced |= ERROR_POSITIVE;
						else
							return NULL;
					} else {
						assert(err_a == errors_allowed);
						*errors_produced |= err_a;
						newI->contents[idx2] = a;
						idx2++;
					}
					break;
				case Iop_Or1:
				case Iop_Or8:
				case Iop_Or16:
				case Iop_Or32:
				case Iop_Or64:
					if (!a) {
						/* k | x, where x is
						 * completely unknown.
						 * Approximate it by
						 * just k with a
						 * negative error. */
						if (errors_allowed & ERROR_NEGATIVE)
							*errors_produced |= ERROR_NEGATIVE;
						else
							return NULL;
					} else {
						assert(err_a == errors_allowed);
						*errors_produced |= err_a;
						newI->contents[idx2] = a;
						idx2++;
					}
					break;
				default:
					abort();
				}
			} else {
				newI->contents[idx2] = a;
				idx2++;
			}
			idx++;
		}
		if (idx2 == 0)
			return NULL;
		newI->nr_arguments = idx2;
		return newI;
	}
	case Iex_HappensBefore:
		return what;
	case Iex_FreeVariable:
		return NULL;
	case Iex_EntryPoint:
		return what;
	case Iex_ControlFlow:
		return what;
	}
	abort();
}

static bool
simplifyControlExpressions(DNF_Conjunction &d)
{
	std::set<std::pair<bool, IRExprControlFlow *> > exprs;
	for (auto it = d.begin(); it != d.end(); it++)
		if ( it->second->tag == Iex_ControlFlow )
			exprs.insert( std::pair<bool, IRExprControlFlow *>(it->first, (IRExprControlFlow *)it->second) );

	std::set<std::pair<unsigned, CfgLabel> > setExit;

	/* First rule: if we have both A->B and A->C edges, where B !=
	   C, we have a contradiction. */
	for (auto it1 = exprs.begin(); it1 != exprs.end(); it1++) {
		if (it1->first)
			continue;
		IRExprControlFlow *e1 = it1->second;
		setExit.insert(std::pair<unsigned, CfgLabel>(e1->thread, e1->cfg1));
		auto it2 = it1;
		it2++;
		for (; it2 != exprs.end(); it2++) {
			if (it2->first)
				continue;
			IRExprControlFlow *e2 = it2->second;
			if (e1->thread == e2->thread &&
			    e1->cfg1 == e2->cfg1) {
				/* By the internment property */
				assert(e1->cfg2 != e2->cfg2);
				return false;
			}
		}
	}

	/* Second rule: if we have Control(t1:cfg1->cfg2) &&
	 * !Control(t1:cfg1->cfg3) then we can turn it into just
	 * Control(t1:cfg1->cfg2) */
	for (auto it = exprs.begin(); it != exprs.end(); it++) {
		if (it->first) {
			IRExprControlFlow *e = it->second;
			if (setExit.count(std::pair<unsigned, CfgLabel>(e->thread, e->cfg1)))
				d.remove(NF_Atom(it->first, it->second));
		}
	}
	return true;
}

static crashEnforcementData
enforceCrashForMachine(const SummaryId &summaryId,
		       VexPtr<CrashSummary, &ir_heap> summary,
		       VexPtr<Oracle> &oracle,
		       GarbageCollectionToken token,
		       ThreadAbstracter &abs,
		       int &next_hb_id)
{
	summary = internCrashSummary(summary);
	if (TIMEOUT) {
		fprintf(_logfile, "Timeout while interning summary\n");
		exit(1);
	}

	printf("Machines to enforce:\n");
	printCrashSummary(summary, stdout);

	VexPtr<OracleInterface> oracleI(oracle);

	IRExpr *requirement = summary->verificationCondition;
	int ignore;
	requirement = removeFreeVariables(requirement, ERROR_POSITIVE, &ignore);
	requirement = internIRExpr(simplify_via_anf(simplifyIRExpr(requirement, AllowableOptimisations::defaultOptimisations)));
	fprintf(_logfile, "After free variable removal:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");
	if (TIMEOUT) {
		fprintf(_logfile, "Killed by a timeout during simplification\n");
		exit(1);
	}
	DNF_Disjunction d;
	if (!dnf(requirement, d)) {
		fprintf(_logfile, "failed to convert to DNF\n");
		exit(1);
	}

	for (unsigned x = 0; x < d.size(); x++)
		for (unsigned y = 0; y < d[x].size(); y++)
			d[x][y].second = heuristicSimplify(d[x][y].second);

	for (unsigned x = 0; x < d.size(); ) {
		if (analyseHbGraph(d[x], summary) &&
		    !consistentOrdering(d[x])) {
			x++;
		} else {
			d.erase(d.begin() + x);
		}
	}

	for (unsigned x = 0; x < d.size(); ) {
		if (simplifyControlExpressions(d[x]))
			x++;
		else
			d.erase(d.begin() + x);
	}

	printDnf(d, _logfile);

	if (d.size() == 0)
		return crashEnforcementData();

	std::map<ConcreteThread, std::set<CfgLabel> > rootsCfg;
	for (auto it = summary->loadMachine->cfg_roots.begin();
	     it != summary->loadMachine->cfg_roots.end();
	     it++)
		rootsCfg[ConcreteThread(summaryId, it->first)].insert(it->second->label);
	for (auto it = summary->storeMachine->cfg_roots.begin();
	     it != summary->storeMachine->cfg_roots.end();
	     it++)
		rootsCfg[ConcreteThread(summaryId, it->first)].insert(it->second->label);

	crashEnforcementData accumulator;
	for (unsigned x = 0; x < d.size(); x++) {
		crashEnforcementData tmp;
		if (buildCED(summaryId, d[x], rootsCfg, summary, &tmp, abs, next_hb_id, oracle->ms->addressSpace)) {
			printf("Intermediate CED:\n");
			tmp.prettyPrint(stdout, true);
			accumulator |= tmp;
		}
	}
	return accumulator;
}

/* Try to delay stashing registers until we actually need to do so.
   We start off trying to stash them at the roots of the CFG and we
   can delay if:

   -- The node doesn't modify the register
   -- We don't try to eval anything at the node.
   -- The node isn't the before end of a happens-before edge
*/
static void
optimiseStashPoints(crashEnforcementData &ced, Oracle *oracle)
{
	expressionStashMapT newMap;
	for (auto it = ced.exprStashPoints.begin();
	     it != ced.exprStashPoints.end();
	     it++) {
		const ThreadCfgLabel &label(it->first);
		typedef std::pair<Instruction<ThreadCfgLabel> *, IRExpr *> entryT;
		std::set<entryT> frozenStashPoints;
		std::set<entryT> unfrozenStashPoints;

		{
			Instruction<ThreadCfgLabel> *n = ced.crashCfg.findInstr(label);
			const std::set<IRExpr *> &exprsToStash(it->second);
			assert(n);
			for (auto it = exprsToStash.begin(); it != exprsToStash.end(); it++)
				unfrozenStashPoints.insert(entryT(n, *it));
		}
		while (!unfrozenStashPoints.empty()) {
			Instruction<ThreadCfgLabel> *node;
			IRExprGet *expr;
			{
				auto it = unfrozenStashPoints.begin();
				node = it->first;
				IRExpr *e = it->second;
				unfrozenStashPoints.erase(it);

				if (e->tag == Iex_EntryPoint ||
				    e->tag == Iex_ControlFlow) {
					/* Can never advance stash of
					 * entry point expressions. */
					frozenStashPoints.insert(entryT(node, e));
					continue;
				}
				assert(e->tag == Iex_Get);
				expr = (IRExprGet *)e;
			}
			const ThreadCfgLabel &label(node->rip);

			/* Can't be an eval point */
			if (ced.expressionEvalPoints.count(label)) {
				frozenStashPoints.insert(entryT(node, expr));
				continue;
			}

			/* Can't be a happens-before before point */
			{
				auto it2 = ced.happensBeforePoints.find(label);
				if (it2 != ced.happensBeforePoints.end()) {
					bool b = false;
					for (auto it3 = it2->second.begin();
					     !b && it3 != it2->second.end();
					     it3++)
						if ((*it3)->before->rip == label)
							b = true;
					if (b) {
						frozenStashPoints.insert(entryT(node, expr));
						continue;
					}
				}
			}


			/* Can't stash a register which this
			 * instruction might modify */
			const AbstractThread &absThread(node->rip.thread);
			ConcreteThread concThread(ced.roots.lookupAbsThread(absThread));
			ConcreteCfgLabel concCfgLabel(concThread.summary(), node->rip.label);
			const VexRip &vr(ced.crashCfg.labelToRip(concCfgLabel));
			IRSB *irsb = oracle->ms->addressSpace->getIRSBForAddress(ThreadRip(Oracle::STATIC_THREAD, vr), true);
			bool modifies = false;
			for (int x = 0; !modifies && x < irsb->stmts_used && irsb->stmts[x]->tag != Ist_IMark; x++) {
				if (irsb->stmts[x]->tag == Ist_Put &&
				    ((IRStmtPut *)irsb->stmts[x])->target == expr->reg)
					modifies = true;
			}
			if (modifies) {
				frozenStashPoints.insert(entryT(node, expr));
				continue;
			}

			/* Advance this stash point */
			for (auto it2 = node->successors.begin(); it2 != node->successors.end(); it2++)
				unfrozenStashPoints.insert(entryT(it2->instr, expr));
		}

		for (auto it2 = frozenStashPoints.begin(); it2 != frozenStashPoints.end(); it2++) {
			auto node = it2->first;
			auto expr = it2->second;
			ThreadCfgLabel label(it->first.thread, node->label);
			newMap[label].insert(expr);
		}
	}

	ced.exprStashPoints = newMap;
}

/* We sometimes find that the CFG has a prefix which is completely
   irrelevant.  Try to remove it. */
static void
optimiseCfg(crashEnforcementData &ced)
{
	struct {
		crashEnforcementData *ced;
		bool operator()(const ThreadCfgLabel &label) {
			return ced->exprStashPoints.count(label) != 0 ||
				ced->happensBeforePoints.count(label) != 0 ||
				ced->expressionEvalPoints.count(label) != 0;
		}
	} hasSideEffect = {&ced};
	crashEnforcementRoots newRoots;
	for (auto it = ced.roots.begin(); !it.finished(); it.advance()) {
		const AbstractThread thread(it.get().thread);
		auto root = ced.crashCfg.findInstr(it.get());
		while (1) {
			/* We can advance a root if it has a single
			   successor, and it has no stash points, and
			   it has no HB points, and it has no eval
			   points, and it isn't an exit point. */
			if (root->successors.size() != 1)
                               break;
			ThreadCfgLabel l(thread, root->label);
			if (hasSideEffect(l))
				break;
			root = root->successors[0].instr;
		}

		/* If all of the paths forwards from root N issue
		   their first side-effect at node N' then N can be
		   replaced by N'. */
		bool haveFirstSideEffect = false;
		bool failed = false;
		ThreadCfgLabel firstSideEffect;
		std::set<const Instruction<ThreadCfgLabel> *> visited;
		std::queue<const Instruction<ThreadCfgLabel> *> pending;
		pending.push(root);
		while (!failed && !pending.empty()) {
			auto n = pending.front();
			pending.pop();
			ThreadCfgLabel l(thread, n->label);

			if (hasSideEffect(l)) {
				if (haveFirstSideEffect) {
					if (firstSideEffect != l)
						failed = true;
				} else {
					firstSideEffect = l;
					haveFirstSideEffect = true;
				}
			} else {
				for (auto it = n->successors.begin();
				     it != n->successors.end();
				     it++)
					pending.push(it->instr);
			}
		}
		if (haveFirstSideEffect) {
			if (failed)
				newRoots.insert(it.concrete_tid(), it.get());
			else
				newRoots.insert(it.concrete_tid(), firstSideEffect);
		}
	}
	ced.roots = newRoots;

	/* Anything which isn't reachable from a root can be removed
	 * from the CFG. */
	std::set<Instruction<ThreadCfgLabel> *> retain;
	std::queue<Instruction<ThreadCfgLabel> *> pending;
	for (auto it = ced.roots.begin(); !it.finished(); it.advance())
		pending.push(ced.crashCfg.findInstr(it.get()));
	while (!pending.empty()) {
		auto n = pending.front();
		pending.pop();
		if (!retain.insert(n).second)
			continue;
		for (auto it = n->successors.begin(); it != n->successors.end(); it++)
			pending.push(it->instr);
	}
	ced.crashCfg.removeAllBut(retain);
}

/* This function is responsible for setting up the patch point list
   and the force interpret list.  The preceding phases of the analysis
   have given us a set of instructions I and we must arrange that
   we're in the interpreter whenever the program executes an
   instruction from I.  The challenge is that the only way of gaining
   control is through a jump instruction, which is five bytes, and
   some of the instructions in I might themselves be smaller than five
   bytes, and so directly patching one of them might clobber something
   important.  That is itself fine *provided* that the program is
   definitely in the interpreter when it executes the instruction
   which you clobbered, which might then require us to add new entry
   points.

   Define some notation first:

   -- MustInterpret(X) means that we must be in the interpreter when we
   run instruction X.
   -- DoesInterpret(X) means that the patched program definitely will
   be in the interpreter when in runs X.
   -- Clobber(X, Y) means that trying to patch X into an entry point
   will clobber Y.
   -- Patch(X) means that we're going to replace X with an entry point.
   -- Cont(X) means that if the interpreter hits X it should continue
   interpreting.
   -- Predecessor(X, Y) is true precisely when there's some control-flow
   edge from Y to X i.e. when Y is a predecessor of X.
   -- External(X) is true if there might be some control-flow edge which
   we don't know about which ends at X.

   We control Patch and Cont; everything else is set for us in advance
   by the oracle and the CED.

   Assumptions:

   Patch(X) => DoesInterpret(X)
   !External(X) && Cont(X) && forall Y.(Predecessor(X, Y) => DoesInterpret(Y)) => DoesInterpret(X)

   In the final configuration, we need:

   Patch(X) => Cont(X)
   MustInterpret(X) => DoesInterpret(X)
   Patch(X) && Clobber(X, Y) => DoesInterpret(Y)
   Patch(X) && Clobber(X, Y) => !External(Y)

   For performance reasons, we'd also like to minimise the size of the
   Cont set.

   We treat this as an exhaustive search problem, using two possible
   maneuvers:

   -- Create a new patch point at X.  That's only valid if doing so
      wouldn't clobber an external function.  Doing this then moves
      you to a new state in which MustInterpret() contains all of the
      instructions which are clobbered by X.
   -- Use a continue point instead: set Cont(X) and then set
      MustInterpret for all of X's predecessors.
*/

struct patchStrategy {
	std::set<unsigned long> MustInterpret;
	std::set<unsigned long> Patch;
	std::set<unsigned long> Cont;
	unsigned size() const {
		return MustInterpret.size() + Cont.size();
	}
	bool operator<(const patchStrategy &o) const {
		return size() > o.size();
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "MI: {");
		for (auto it = MustInterpret.begin(); it != MustInterpret.end(); it++) {
			if (it != MustInterpret.begin())
				fprintf(f, ",");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "}; P {");
		for (auto it = Patch.begin(); it != Patch.end(); it++) {
			if (it != Patch.begin())
				fprintf(f, ",");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "}; C {");
		for (auto it = Cont.begin(); it != Cont.end(); it++) {
			if (it != Cont.begin())
				fprintf(f, ",");
			fprintf(f, "0x%lx", *it);
		}
		fprintf(f, "}\n");
	}
};

static bool
patchSearch(Oracle *oracle,
	    const patchStrategy &input,
	    std::priority_queue<patchStrategy> &thingsToTry)
{
	if (input.MustInterpret.empty())
		return true;

	input.prettyPrint(stdout);
	unsigned long needed = *input.MustInterpret.begin();

	printf("\tLook at %lx\n", needed);
	patchStrategy c(input);
	/* @needed is definitely going to be interpreted after
	 * this. */
	c.Cont.insert(needed);
	c.MustInterpret.erase(needed);

	/* Decide which maneuver to use here.  We need to either patch
	   @needed itself or bring all of its predecessors into the
	   patch. */

	/* Figure out which instructions might get clobbered by the
	 * patch */
	std::set<unsigned long> clobbered_by_patch;
	unsigned offset = 0;
	offset += getInstructionSize(oracle->ms->addressSpace, StaticRip(needed));
	while (offset < 5) {
		clobbered_by_patch.insert(needed + offset);
		offset += getInstructionSize(oracle->ms->addressSpace, StaticRip(needed + offset));
	}

	/* Can't use patch if that would clobber an external. */
	bool can_use_patch = true;
	for (auto it = clobbered_by_patch.begin(); can_use_patch && it != clobbered_by_patch.end(); it++) {
		if (oracle->isFunctionHead(StaticRip(*it)))
			can_use_patch = false;
	}
	/* Can't use patch if that would clobber/be clobbered by an
	   existing patch point. */
	for (auto it = input.Patch.begin(); can_use_patch && it != input.Patch.end(); it++) {
		if (needed > *it - 5 && needed < *it + 5)
			can_use_patch = false;
	}

	if (can_use_patch) {
		/* Try using a patch. */
		patchStrategy patched(c);
		patched.Patch.insert(needed);
		for (auto it = clobbered_by_patch.begin();
		     it != clobbered_by_patch.end();
		     it++) {
			std::set<unsigned long> predecessors;
			oracle->findPredecessors(*it, predecessors);
			for (unsigned long y = needed; y < *it; y++)
				predecessors.erase(y);
			patched.Cont.insert(*it);
			patched.MustInterpret.erase(*it);
			patched.MustInterpret.insert(predecessors.begin(), predecessors.end());
		}
		thingsToTry.push(patched);
		printf("Patch to: ");
		patched.prettyPrint(stdout);
	}

	/* Try expanding to predecessors. */
	std::set<unsigned long> predecessors;
	oracle->findPredecessors(needed, predecessors);
	c.MustInterpret.insert(predecessors.begin(), predecessors.end());
	thingsToTry.push(c);
	printf("Unpatched: ");
	c.prettyPrint(stdout);
	return false;
}

static void
buildPatchStrategy(crashEnforcementData &ced, Oracle *oracle)
{
	patchStrategy initPs;

	for (auto it = ced.roots.begin(); !it.finished(); it.advance()) {
		Instruction<ThreadCfgLabel> *instr = ced.crashCfg.findInstr(it.get());
		assert(instr);
		const AbstractThread &absThread(instr->rip.thread);
		ConcreteThread concThread(ced.roots.lookupAbsThread(absThread));
		ConcreteCfgLabel concCfgLabel(concThread.summary(), instr->rip.label);
		const VexRip &vr(ced.crashCfg.labelToRip(concCfgLabel));

		unsigned long r = vr.unwrap_vexrip();
		if (debug_declobber_instructions)
			printf("%lx is a root\n", r);
		initPs.MustInterpret.insert(r);
	}

	std::priority_queue<patchStrategy> pses;
	pses.push(initPs);
	while (!pses.empty()) {
		patchStrategy next(pses.top());
		pses.pop();
		if (patchSearch(oracle, next, pses)) {
			/* We have a solution. */
			ced.patchPoints = next.Patch;
			ced.interpretInstrs = next.Cont;

			/* Minor optimisation: anything within five bytes of a patch
			   point is implicitly cont, so remove them. */
			for (auto it = ced.patchPoints.begin(); it != ced.patchPoints.end(); it++)
				for (unsigned x = 0; x < 5; x++)
					ced.interpretInstrs.erase(*it + x);
			return;
		}
	}
	errx(1, "Cannot solve patch problem");
}

static void
optimiseHBEdges(crashEnforcementData &ced)
{
	/* If an instruction receives a message from thread X then it
	   then binds to thread X and from that point on can only ever
	   send or receive with X.  That allows us to eliminate some
	   message operations. */
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
	     it++) {
		std::set<AbstractThread> mightReceiveFrom;
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			const happensBeforeEdge *hbe = *it2;
			if (hbe->after->rip == it->first)
				mightReceiveFrom.insert(hbe->before->rip.thread);
		}
		if (mightReceiveFrom.empty())
			continue;
		/* Now we know that we've definitely received from one
		   of the threads in @mightReceiveFrom, so we can only
		   send to them.  Kill off any other edges. */
		for (auto it2 = it->second.begin(); it2 != it->second.end(); ) {
			const happensBeforeEdge *hbe = *it2;
			if (hbe->before->rip == it->first &&
			    !mightReceiveFrom.count(hbe->after->rip.thread))
				it->second.erase(it2++);
			else
				it2++;
		}
	}

	/* And now get rid of any messages which are sent but never
	   received or received but never sent. */
	std::set<unsigned> sent;
	std::set<unsigned> received;
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
	     it++) {
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			if ((*it2)->before->rip == it->first)
				sent.insert( (*it2)->msg_id);
			else
				received.insert( (*it2)->msg_id);
		}
	}
	for (auto it = ced.happensBeforePoints.begin();
	     it != ced.happensBeforePoints.end();
		) {
		for (auto it2 = it->second.begin(); it2 != it->second.end(); ) {
			unsigned id = (*it2)->msg_id;
			if (!sent.count(id) || !received.count(id))
				it->second.erase(it2++);
			else
				it2++;
		}
		if (it->second.empty())
			ced.happensBeforePoints.erase(it++);
		else
			it++;
	}
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	int next_hb_id = 0xaabb;

	ThreadAbstracter abs;
	crashEnforcementData accumulator;
	for (int i = 5; i < argc; i++) {
		VexPtr<CrashSummary, &ir_heap> summary(readBugReport(argv[i], NULL));
		crashEnforcementData acc = enforceCrashForMachine(SummaryId(i - 4), summary, oracle, ALLOW_GC, abs, next_hb_id);
		optimiseHBEdges(acc);
		optimiseStashPoints(acc, oracle);
		optimiseCfg(acc);
		accumulator |= acc;
	}

	buildPatchStrategy(accumulator, oracle);

	FILE *f = fopen(argv[4], "w");
	accumulator.prettyPrint(f);
	accumulator.prettyPrint(stdout);
	fclose(f);

	return 0;
}


/* For the compiler to instantiate CFG<ThreadRip>::print, so that it's
   available in gdb. */
void
force_compilation(CFG<ThreadRip> *r)
{
	r->print(stdout);
}
