#include <stdlib.h>

#include "sli.h"
#include "state_machine.hpp"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"
#include "simplify_irexpr.hpp"
#include "eval_state_machine.hpp"
#include "alloc_mai.hpp"
#include "sat_checker.hpp"
#include "simplify_irexpr.hpp"

#include "../VEX/priv/guest_generic_bb_to_IR.h"
#include "../VEX/priv/guest_amd64_defs.h"

class evalRes : public Named {
	int val;
	char *mkName() const {
		switch (val) {
		case 0:
			return strdup("unreached");
		case 1:
			return strdup("crash");
		case 2:
			return strdup("survive");
		default:
			abort();
		}
	}
	evalRes(int _val)
		: val(_val)
	{}
public:
	static evalRes unreached() { return evalRes(0); }
	static evalRes crash() { return evalRes(1); }
	static evalRes survive() { return evalRes(2); }
	bool operator==(const evalRes &o) {
		return val == o.val;
	}
	bool operator!=(const evalRes &o) {
		return val != o.val;
	}
};

class evalExprRes : public Named {
	bool _failed;
	unsigned long val;
	char *mkName() const {
		if (_failed)
			return strdup("<failed>");
		else
			return my_asprintf("0x%lx", val);
	}
	evalExprRes()
		: _failed(true), val(0xf001dead)
	{}
	evalExprRes(unsigned long v)
		: _failed(false), val(v)
	{}
public:
	static evalExprRes failed() {
		return evalExprRes();
	}
	static evalExprRes success(unsigned long v) {
		return evalExprRes(v);
	}
	bool unpack(unsigned long *v) {
		if (_failed) {
			return false;
		} else {
			*v = val;
			return true;
		}
	}
	bool valid() { return !_failed; }
};

class EvalState {
public:
	std::map<threadAndRegister, unsigned long> regs;
	std::map<MemoryAccessIdentifier, unsigned long> freeVars;
	std::map<unsigned long, unsigned long> memory;
	std::set<unsigned long> badPtrs;
	void prettyPrint(FILE *f) const {
		fprintf(f, "Regs:\n");
		for (auto it = regs.begin(); it != regs.end(); it++)
			fprintf(f, "\t%s -> 0x%lx\n", it->first.name(), it->second);
		fprintf(f, "freeVars:\n");
		for (auto it = freeVars.begin(); it != freeVars.end(); it++)
			fprintf(f, "\t%s -> 0x%lx\n", it->first.name(), it->second);
		fprintf(f, "memory:\n");
		for (auto it = memory.begin(); it != memory.end(); it++)
			fprintf(f, "\t0x%lx -> 0x%lx\n", it->first, it->second);
		fprintf(f, "badPtrs:\n");
		for (auto it = badPtrs.begin(); it != badPtrs.end(); it++)
			fprintf(f, "\t0x%lx\n", *it);
	}
	void clear() {
		regs.clear();
		freeVars.clear();
		memory.clear();
		badPtrs.clear();
	}
};

class EvalCtxt {
public:
	EvalState currentState;
	std::vector<threadAndRegister> regOrder;
	EvalCtxt(EvalState &_initialState)
		: currentState(_initialState)
	{}
	unsigned long eval(IRExpr *e);
	bool eval(StateMachineSideEffect *effect);
	evalRes eval(VexPtr<StateMachineState, &ir_heap> state,
		     GarbageCollectionToken token);
};

static unsigned long
genRandomUlong()
{
	unsigned long res;
	res = random() + random() * RAND_MAX + random() * RAND_MAX * RAND_MAX;
	return res;
}

static IRExpr *mk_const(unsigned long val, IRType ty)
{
	IRConst *c;
	switch (ty) {
	case Ity_I8:
		c = IRConst_U8(val);
		break;
	case Ity_I16:
		c = IRConst_U16(val);
		break;
	case Ity_I32:
		c = IRConst_U32(val);
		break;
	case Ity_I64:
		c = IRConst_U64(val);
		break;
	default:
		abort();
	}
	return IRExpr_Const(c);
}

static evalExprRes evalExpr(EvalState &ctxt, IRExpr *what, bool *usedRandom);

unsigned long
EvalCtxt::eval(IRExpr *e)
{
	bool b;
	unsigned long l;
	evalExprRes res(evalExpr(currentState, e, &b));
	if (!res.unpack(&l))
		abort();
	return l;
}

bool
EvalCtxt::eval(StateMachineSideEffect *effect)
{
	switch (effect->type) {
	case StateMachineSideEffect::Load: {
		auto *l = (StateMachineSideEffectLoad *)effect;
		unsigned long addr = eval(l->addr);
		unsigned long res;
		if (currentState.memory.count(addr)) {
			res = currentState.memory[addr];
		} else if (currentState.badPtrs.count(addr)) {
			return false;
		} else {
			res = genRandomUlong();
			currentState.memory[addr] = res;
		}
		currentState.regs[l->target] = res;
		regOrder.push_back(l->target);
		return true;
	}
	case StateMachineSideEffect::Store: {
		auto *s = (StateMachineSideEffectStore *)effect;
		unsigned long addr = eval(s->addr);
		unsigned long data = eval(s->data);
		currentState.memory[addr] = data;
		return true;
	}
	case StateMachineSideEffect::Copy: {
		auto *c = (StateMachineSideEffectCopy *)effect;
		unsigned long val = eval(c->value);
		currentState.regs[c->target] = val;
		regOrder.push_back(c->target);
		return true;
	}
	case StateMachineSideEffect::Unreached:
		return false;
	case StateMachineSideEffect::AssertFalse: {
		auto *a = (StateMachineSideEffectAssertFalse *)effect;
		unsigned long v = eval(a->value);
		if (v == 0)
			return true;
		else
			return false;
	}
	case StateMachineSideEffect::Phi: {
		auto *p = (StateMachineSideEffectPhi *)effect;
		for (auto it = regOrder.rbegin(); it != regOrder.rend(); it++) {
			for (auto it2 = p->generations.begin(); it2 != p->generations.end(); it2++) {
				if (it2->first == *it) {
					assert(currentState.regs.count(it2->first));
					if (it2->second) {
						assert(eval(it2->second) == currentState.regs[it2->first]);
					}
					currentState.regs[p->reg] = currentState.regs[it2->first];
					regOrder.push_back(p->reg);
					return true;
				}
			}
		}
		/* Okay, so we have no assignments, so it must be an
		 * initial value Phi. */
#ifndef NDEBUG
		{
			int nr_gen_m1 = 0;
			for (auto it = p->generations.begin(); it != p->generations.end(); it++)
				if (it->first.gen() == (unsigned)-1)
					nr_gen_m1++;
			assert(nr_gen_m1 == 1);
		}
#endif
		for (auto it = p->generations.begin(); it != p->generations.end(); it++) {
			if (it->first.gen() == (unsigned)-1) {
				if (!currentState.regs.count(it->first))
					currentState.regs[it->first] = genRandomUlong();
				currentState.regs[p->reg] = currentState.regs[it->first];
				regOrder.push_back(p->reg);
				return true;
			}
		}
		abort();
	}
	case StateMachineSideEffect::StartAtomic:
	case StateMachineSideEffect::EndAtomic:
	case StateMachineSideEffect::StartFunction:
	case StateMachineSideEffect::EndFunction:
	case StateMachineSideEffect::PointerAliasing:
	case StateMachineSideEffect::StackLayout:
		return true;
	}
	abort();
}

evalRes
EvalCtxt::eval(VexPtr<StateMachineState, &ir_heap> state,
	       GarbageCollectionToken token)
{
top:
	LibVEX_maybe_gc(token);
	switch (state->type) {
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)state.get();
		if (eval(smb->condition))
			state = smb->trueTarget;
		else
			state = smb->falseTarget;
		goto top;
	}
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)state.get();
		if (sme->sideEffect && !eval(sme->sideEffect))
			return evalRes::unreached();
		state = sme->target;
		goto top;
	}
	case StateMachineState::Unreached:
		return evalRes::unreached();
	case StateMachineState::Crash:
		return evalRes::crash();
	case StateMachineState::NoCrash:
		return evalRes::survive();
	}
	abort();
}

template <typename t, Heap *h>
class gc_vector : public std::vector<t *>, public GcCallback<h> {
	void runGc(HeapVisitor &hv) {
		for (auto it = this->begin(); it != this->end(); it++)
			hv(*it);
	}
};

static evalExprRes
evalExpr(EvalState &ctxt, IRExpr *what, bool *usedRandom)
{
	struct : public IRExprTransformer {
		EvalState *ctxt;
		bool *usedRandom;
		IRExpr *mk_const(unsigned long val, IRType ty) {
			IRConst *c;
			switch (ty) {
			case Ity_I1:
				c = IRConst_U1(val);
				break;
			case Ity_I8:
				c = IRConst_U8(val);
				break;
			case Ity_I16:
				c = IRConst_U16(val);
				break;
			case Ity_I32:
				c = IRConst_U32(val);
				break;
			case Ity_I64:
				c = IRConst_U64(val);
				break;
			default:
				abort();
			}
			return IRExpr_Const(c);
		}
		IRExpr *transformIex(IRExprGet *ieg) {
			if (!ctxt->regs.count(ieg->reg) &&
			    usedRandom) {
				*usedRandom = true;
				ctxt->regs[ieg->reg] = genRandomUlong();
			}
			if (ctxt->regs.count(ieg->reg))
				return mk_const(ctxt->regs[ieg->reg], ieg->type());
			return ieg;
		}
		IRExpr *transformIex(IRExprGetI *) {
			abort();
		}
		IRExpr *transformIex(IRExprLoad *e) {
			bool b;
			IRExpr *addr = transformIRExpr(e->addr, &b);
			if (!addr)
				addr = e->addr;
			addr = simplifyIRExpr(addr, AllowableOptimisations::defaultOptimisations);
			if (addr->tag != Iex_Const)
				return IRExpr_Load(e->ty, addr);
			assert(addr->tag == Iex_Const);
			assert(addr->type() == Ity_I64);
			unsigned long address = ((IRExprConst *)addr)->con->Ico.U64;
			if (ctxt->memory.count(address))
				return mk_const(ctxt->memory[address], e->type());
			if (usedRandom) {
				*usedRandom = true;
				ctxt->memory[address] = genRandomUlong();
				return mk_const(ctxt->memory[address], e->type());
			}
			return IRExpr_Load(e->ty, addr);
		}
		IRExpr *transformIex(IRExprHappensBefore *) {
			abort();
		}
		IRExpr *transformIex(IRExprFreeVariable *e) {
			if (ctxt->freeVars.count(e->id))
				return mk_const(ctxt->freeVars[e->id], e->ty);
			if (usedRandom) {
				*usedRandom = true;
				ctxt->freeVars[e->id] = genRandomUlong();
				return mk_const(ctxt->freeVars[e->id], e->ty);
			}
			return e;
		}
		IRExpr *transformIex(IRExprUnop *e) {
			bool b;
			IRExpr *arg = transformIRExpr(e->arg, &b);
			if (!arg)
				arg = e->arg;
			if (aborted)
				return e;
			if (e->op != Iop_BadPtr)
				return IRExpr_Unop(e->op, arg);
			arg = simplifyIRExpr(arg, AllowableOptimisations::defaultOptimisations);
			if (arg->tag != Iex_Const)
				return IRExpr_Unop(e->op, arg);
			assert(arg->tag == Iex_Const);
			assert(arg->type() == Ity_I64);
			unsigned long address = ((IRExprConst *)arg)->con->Ico.U64;
			if (ctxt->badPtrs.count(address)) {
				return mk_const(1, Ity_I1);
			} else if (ctxt->memory.count(address)) {
				return mk_const(0, Ity_I1);
			} else if (usedRandom) {
				*usedRandom = true;
				ctxt->memory[address] = genRandomUlong();
				return mk_const(0, Ity_I1);
			}
			return IRExpr_Unop(Iop_BadPtr, arg);
		}
		IRExpr *transformIex(IRExprCCall *e) {
			if (!strcmp(e->cee->name, "amd64g_calculate_condition") &&
			    e->args[1]->tag == Iex_Get) {
				/* Special case: make sure we produce
				   something which is nice and easy to
				   constant-fold here. */
				IRExprGet *ieg = (IRExprGet *)e->args[1];
				if (!ctxt->regs.count(ieg->reg))
					ctxt->regs[ieg->reg] = AMD64G_CC_OP_SUBQ;
			}

			return IRExprTransformer::transformIex(e);
		}
	} trans;
	trans.ctxt = &ctxt;
	trans.usedRandom = usedRandom;
	IRExpr *a = trans.doit(what);
	a = simplifyIRExpr(a, AllowableOptimisations::defaultOptimisations);
	if (a->tag == Iex_Const)
		return evalExprRes::success(((IRExprConst *)a)->con->Ico.U64);
	else
		return evalExprRes::failed();
}

static bool makeEq(EvalState &res, IRExpr *arg1, IRExpr *arg2, bool wantTrue, bool *usedRandom);

static bool
makeEqConst(EvalState &res, unsigned long cnst, IRExpr *what, bool wantTrue, bool *usedRandom)
{
	switch (what->tag) {
	case Iex_FreeVariable: {
		auto *ief = (IRExprFreeVariable *)what;
		if (res.freeVars.count(ief->id)) {
			if (res.freeVars[ief->id] == cnst)
				return wantTrue;
			else
				return !wantTrue;
		}
		if (wantTrue)
			res.freeVars[ief->id] = cnst;
		else
			res.freeVars[ief->id] = cnst + 128;
		return true;
	}
	case Iex_Get: {
		auto *ieg = (IRExprGet *)what;
		if (res.regs.count(ieg->reg)) {
			if (res.regs[ieg->reg] == cnst)
				return wantTrue;
			else
				return !wantTrue;
		}
		if (wantTrue)
			res.regs[ieg->reg] = cnst;
		else
			res.regs[ieg->reg] = cnst + 128;
		return true;
	}
	case Iex_Load: {
		auto *iel = (IRExprLoad *)what;
		evalExprRes addr(evalExpr(res, iel->addr, usedRandom));
		unsigned long addr_c;
		if (!addr.unpack(&addr_c))
			return false;
		if (res.badPtrs.count(addr_c))
			return false;
		if (res.memory.count(addr_c)) {
			if (res.memory[addr_c] == cnst)
				return wantTrue;
			else
				return !wantTrue;
		}
		if (wantTrue)
			res.memory[addr_c] = cnst;
		else
			res.memory[addr_c] = cnst + 128;
		return true;
	}
	case Iex_CCall: {
		auto iec = (IRExprCCall *)what;
		if (strcmp(iec->cee->name, "amd64g_calculate_condition"))
			abort();
		IRExpr *cond, *cc_op, *dep1, *dep2;
		cond = iec->args[0];
		cc_op = iec->args[1];
		dep1 = iec->args[2];
		dep2 = iec->args[3];
		evalExprRes cond_eval(evalExpr(res, cond, NULL));
		evalExprRes cc_op_eval(evalExpr(res, cc_op, NULL));
		unsigned long cond_c;
		if (!cond_eval.unpack(&cond_c) ||
		    cc_op_eval.valid())
			abort();
		if (!cnst)
			cond_c ^= 1;
		switch (cond_c) {
		case AMD64CondZ:
		case AMD64CondLE:
			return makeEqConst(res, AMD64G_CC_OP_SUBQ, cc_op, true, usedRandom) &&
				makeEq(res, dep1, dep2, wantTrue, usedRandom);
		case AMD64CondNZ:
			return makeEqConst(res, AMD64G_CC_OP_SUBQ, cc_op, true, usedRandom) &&
				makeEq(res, dep1, dep2, !wantTrue, usedRandom);
		case AMD64CondNLE:
			if (wantTrue) {
				return makeEqConst(res, AMD64G_CC_OP_SUBQ, cc_op, true, usedRandom) &&
					makeEqConst(res, 128, dep1, true, usedRandom) &&
					makeEqConst(res, 0, dep2, true, usedRandom);
			} else {
				return makeEqConst(res, AMD64G_CC_OP_SUBQ, cc_op, true, usedRandom) &&
					makeEqConst(res, 128, dep2, true, usedRandom) &&
					makeEqConst(res, 0, dep1, true, usedRandom);
			}
		default:
			abort();
		}
		abort();
	}
	case Iex_Associative: {
		auto *iea = (IRExprAssociative *)what;
		switch (iea->op) {
		case Iop_Add64: {
			if (iea->nr_arguments != 2)
				abort();
			evalExprRes res1(evalExpr(res, iea->contents[0], NULL));
			evalExprRes res2(evalExpr(res, iea->contents[1], NULL));
			unsigned long res1c, res2c;
			if (res1.unpack(&res1c))
				return makeEqConst(res, cnst - res1c, iea->contents[1], wantTrue, usedRandom);
			if (res2.unpack(&res2c))
				return makeEqConst(res, cnst - res2c, iea->contents[0], wantTrue, usedRandom);
			res1 = evalExpr(res, iea->contents[0], usedRandom);
			return makeEqConst(res, cnst - res1c, iea->contents[1], wantTrue, usedRandom);
		}
		default:
			abort();
		}
	}
	case Iex_Unop: {
		auto *ieu = (IRExprUnop *)what;
		switch (ieu->op) {
		case Iop_Neg64:
			return makeEqConst(res, -cnst, ieu->arg, wantTrue, usedRandom);
		default:
			abort();
		}
	}
	default:
		abort();
	}
}

static bool
makeEq(EvalState &res, IRExpr *arg1, IRExpr *arg2, bool wantTrue, bool *usedRandom)
{
	if (arg1->tag == Iex_Const)
		return makeEqConst(res, ((IRExprConst *)arg1)->con->Ico.U64, arg2, wantTrue, usedRandom);
	else if (arg2->tag == Iex_Const)
		return makeEqConst(res, ((IRExprConst *)arg2)->con->Ico.U64, arg1, wantTrue, usedRandom);
	else
		return makeEqConst(res, 0, arg1, true, usedRandom) &&
			makeEqConst(res, 0, arg2, wantTrue, usedRandom);

}

static bool
makeTrue(EvalState &res, IRExpr *expr, bool wantTrue, bool *usedRandom)
{
	switch (expr->tag) {
	case Iex_Binop: {
		auto *ieb = (IRExprBinop *)expr;
		switch (ieb->op) {
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			return makeEq(res, ieb->arg1, ieb->arg2, wantTrue, usedRandom);
			/* Cheat a little bit and ignore overflow here */
		case Iop_CmpLT8U:
		case Iop_CmpLT16U:
		case Iop_CmpLT32U:
		case Iop_CmpLT64U:
			return makeTrue(
				res,
				simplifyIRExpr(
					IRExpr_Binop(
						(IROp)(Iop_CmpEQ8 + ieb->op - Iop_CmpLT8U),
						IRExpr_Binop(
							(IROp)(Iop_Sub8 + ieb->op - Iop_CmpLT8U),
							ieb->arg1,
							mk_const(1, ieb->arg1->type())),
						ieb->arg2),
					AllowableOptimisations::defaultOptimisations),
				wantTrue,
				usedRandom);
		default:
			abort();
		}
		break;
	}
	case Iex_Unop: {
		auto *ieu = (IRExprUnop *)expr;
		switch (ieu->op) {
		case Iop_64to1:
			return makeEqConst(res, wantTrue, ieu->arg, true, usedRandom);
		case Iop_BadPtr: {
			evalExprRes addr(evalExpr(res, ieu->arg, usedRandom));
			unsigned long addr_c;
			if (!addr.unpack(&addr_c))
				return false;
			if (res.memory.count(addr_c))
				return !wantTrue;
			if (wantTrue) {
				res.badPtrs.insert(addr_c);
			} else {
				if (res.badPtrs.count(addr_c))
					return false;
				if (usedRandom) {
					res.memory[addr_c] = genRandomUlong();
					*usedRandom = true;
					return true;
				} else {
					return false;
				}
			}
			return true;
		}
		default:
			abort();
		}
		break;
	}
	default:
		abort();
	}
}

static bool
generateConcreteSatisfier(EvalState &res, const satisfier &abstract_sat, bool *usedRandom)
{
	std::set<IRExpr *> truePrimaries;
	std::set<IRExpr *> falsePrimaries;
	for (auto it = abstract_sat.memo.begin(); it != abstract_sat.memo.end(); it++) {
		if (!it->second.second)
			continue;
		if (it->second.first)
			truePrimaries.insert(it->first);
		else
			falsePrimaries.insert(it->first);
	}

	/* True primaries tend to be easier to deal with, so do them
	 * first. */
	for (auto it = truePrimaries.begin(); it != truePrimaries.end(); it++) {
		if (!makeTrue(res, *it, true, usedRandom))
			return false;
	}
	for (auto it = falsePrimaries.begin(); it != falsePrimaries.end(); it++) {
		if (!makeTrue(res, *it, false, usedRandom))
			return false;
	}
	return true;
}

static bool
addSatisfier(std::vector<EvalState> &initialCtxts, IRExpr *a)
{
	bool done = false;
	for (auto sat = sat_enumerator(a);
	     !done && !sat.finished();
	     sat.advance()) {
		EvalState ctxt;
		bool random = false;
		bool res;
		res = generateConcreteSatisfier(ctxt, sat.get(), &random);
		if (res) {
			initialCtxts.push_back(ctxt);
			done = true;
		} else if (random) {
			for (int i = 0; !done && i < 100; i++) {
				random = false;
				ctxt.clear();
				res = generateConcreteSatisfier(ctxt, sat.get(), &random);
				assert(random);
				if (res) {
					initialCtxts.push_back(ctxt);
					done = true;
				}
			}
		}
	}
	return done;
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<Oracle> oracle;
	{
		MachineState *ms = MachineState::readELFExec(argv[1]);
		Thread *thr = ms->findThread(ThreadId(1));
		oracle = new Oracle(ms, thr, argv[2]);
	}
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	VexPtr<OracleInterface> oracleI(oracle);
	VexPtr<StateMachine, &ir_heap> machine1(readStateMachine(argv[4]));
	VexPtr<MaiMap, &ir_heap> mai1(MaiMap::fromFile(machine1, argv[5]));
	VexPtr<StateMachine, &ir_heap> machine2(readStateMachine(argv[6]));
	VexPtr<MaiMap, &ir_heap> mai2(MaiMap::fromFile(machine2, argv[7]));
	gc_vector<IRExpr, &ir_heap> constraints;
	collectConstraints(mai1, machine1, oracleI, constraints, ALLOW_GC);

	printf("Constraints:\n");
	for (auto it = constraints.begin(); it != constraints.end(); it++)
		printf("\t%s\n", nameIRExpr(*it));

	std::vector<EvalState> initialCtxts;
	for (auto it = constraints.begin(); it != constraints.end(); it++) {
		/* Find some concrete configuration which satisfies
		 * this constraint. */

		/* First check whether we've already got one. */
		bool have_satisfying = false;
		for (auto it2 = initialCtxts.begin();
		     !have_satisfying && it2 != initialCtxts.end();
		     it2++) {
			auto res = evalExpr(*it2, *it, NULL);
			unsigned long v;
			if (res.unpack(&v) && v)
				have_satisfying = true;
		}

		if (have_satisfying) {
			/* No point in doing anything more with this
			 * condition. */
			continue;
		}

		IRExpr *a = sat_simplify(*it, AllowableOptimisations::defaultOptimisations);
		if (!addSatisfier(initialCtxts, a))
			fprintf(stderr, "WARNING: Cannot generate concrete satisfier for %s\n", nameIRExpr(a));
	}

	/* Should also try to make all of the conditions be
	 * non-satisfied at least once. */
	for (auto it = constraints.begin(); it != constraints.end(); it++) {
		IRExpr *a = sat_simplify(IRExpr_Unop(Iop_Not1, *it), AllowableOptimisations::defaultOptimisations);

		bool found_one = false;
		for (auto it2 = initialCtxts.begin();
		     !found_one && it2 != initialCtxts.end();
		     it2++) {
			auto res = evalExpr(*it2, a, NULL);
			unsigned long v;
			if (res.unpack(&v) && v)
				found_one = true;
		}

		if (found_one)
			continue;

		dbg_break("Need explicit non-satisfier\n");

		printf("Need explicit non-satisfier for %s...\n", nameIRExpr(a));
		if (!addSatisfier(initialCtxts, a))
			fprintf(stderr, "WARNING: Cannot generate concrete non-satisfier for %s\n", nameIRExpr(a));
	}

	printf("Concrete conditions to consider:\n");
	for (auto it = initialCtxts.begin(); it != initialCtxts.end(); it++) {
		if (it != initialCtxts.begin())
			printf("-----------\n");
		it->prettyPrint(stdout);
	}

	int nr_crash = 0;
	int nr_nocrash = 0;
	int nr_escape = 0;

	int nr_failed = 0;
	int cntr = 0;
	for (auto it = initialCtxts.begin(); it != initialCtxts.end(); it++) {
		EvalCtxt ctxt1(*it);
		evalRes machine1res = ctxt1.eval(machine1->root, ALLOW_GC);
		int i;
		for (i = 0; i < 100 && machine1res == evalRes::unreached(); i++) {
			ctxt1.currentState = *it;
			machine1res = ctxt1.eval(machine1->root, ALLOW_GC);
		}
		EvalCtxt ctxt2(*it);
		evalRes machine2res = ctxt2.eval(machine2->root, ALLOW_GC);
		for (i = 0; i < 100 && machine2res == evalRes::unreached(); i++) {
			ctxt2.currentState = *it;
			machine2res = ctxt1.eval(machine2->root, ALLOW_GC);
		}
		
		if (machine1res != machine2res) {
			printf("Failed: machine1res(%s) != machine2res(%s)\n", machine1res.name(), machine2res.name());
			it->prettyPrint(stdout);
			dbg_break("Failed");
			nr_failed++;
		} else {
			if (machine1res == evalRes::unreached())
				nr_escape++;
			else if (machine1res == evalRes::crash())
				nr_crash++;
			else if (machine2res == evalRes::survive())
				nr_nocrash++;
			else
				abort();
		}
		cntr++;
	}
	if (nr_failed != 0) {
		printf("Result: failed %d/%d\n", nr_failed, cntr);
		return 1;
	} else {
		printf("Result: passed %d (%d escape, %d survive, %d crash)\n",
		       cntr, nr_escape, nr_nocrash, nr_crash);
		return 0;
	}
}

