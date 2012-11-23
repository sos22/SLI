/* This pass takes advantage of variable undefinedness to simplify
   machines.  The idea is that we arrange that uninitialised variables
   can never influence the result of a machine, but that doesn't imply
   that they will never be referenced.  You might, for instance, find
   that you have an expression like ``x && <something_complicated>''.
   If x is definitely uninitialised at that point then it can't
   influence the outcome of the machine, so <something_complicated>
   must definitely be zero, and hence the whole expression must be
   zero. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"

#define UNDEFINED_EXPR ((IRExpr *)3)
#define UNDEFINED_BBDD ((bbdd *)5)
#define UNDEFINED_SMRBDD ((smrbdd *)7)
#define UNDEFINED_EXPRBDD ((exprbdd *)9)

#ifndef NDEBUG
static bool debug_undefinedness = false;
#else
#define debug_undefinedness false
#endif

namespace _undefinedness {

class VariableDefinednessMap {
	typedef std::set<threadAndRegister> entryT ;
	std::map<StateMachineState *, entryT> content;
public:
	void prettyPrint(FILE *f, const std::map<const StateMachineState *, int> &labels) const {
		for (auto it = content.begin(); it != content.end(); it++) {
			auto it2 = labels.find(it->first);
			fprintf(f, "l%d: ", it2 == labels.end() ? -1 : it2->second);
			for (auto it3 = it->second.begin(); it3 != it->second.end(); it3++) {
				if (it3 != it->second.begin())
					fprintf(f, ", ");
				fprintf(f, "%s", it3->name());
			}
			fprintf(f, "\n");
		}
	}
	bool isUndefined(StateMachineState *sm, const threadAndRegister &tr) const {
		if (tr.gen() == (unsigned)-1)
			return false;
		auto it = content.find(sm);
		assert(it != content.end());
		return it->second.count(tr) == 0;
	}
	void init(StateMachine *sm);
};

void
VariableDefinednessMap::init(StateMachine *sm)
{
	content.insert(std::pair<StateMachineState *, entryT>(sm->root, entryT()));
	std::queue<StateMachineState *> pending;
	pending.push(sm->root);
	while (!pending.empty()) {
		StateMachineState *p = pending.front();
		pending.pop();
		const entryT &entrySet(content[p]);
		entryT exitSet(entrySet);
		StateMachineSideEffect *se = p->getSideEffect();
		threadAndRegister tr(threadAndRegister::invalid());
		if (se && se->definesRegister(tr))
			exitSet.insert(tr);
		std::vector<StateMachineState *> succ;
		p->targets(succ);
		for (auto it = succ.begin(); it != succ.end(); it++) {
			auto it2_did_insert = content.insert(std::pair<StateMachineState *, entryT>(*it, exitSet));
			auto it2 = it2_did_insert.first;
			auto did_insert = it2_did_insert.second;
			if (did_insert || (it2->second |= exitSet))
				pending.push(*it);
		}
	}
}

static IRExpr *
undefinednessExpression(StateMachineState *sm, IRExpr *a, const VariableDefinednessMap &vdm,
			const IRExprOptimisations &opt)
{
	switch (a->tag) {
	case Iex_Get: {
		IRExprGet *ieg = (IRExprGet *)a;
		if (vdm.isUndefined(sm, ieg->reg))
			return UNDEFINED_EXPR;
		return a;
	}
	case Iex_GetI: {
		IRExprGetI *iegi = (IRExprGetI *)a;
		IRExpr *ix = undefinednessExpression(sm, iegi->ix, vdm, opt);
		if (ix == UNDEFINED_EXPR)
			return a;
		if (ix != iegi->ix)
			return IRExpr_GetI(iegi->descr, ix, iegi->bias, iegi->tid);
		return a;
	}
	case Iex_Qop: {
		IRExprQop *i = (IRExprQop *)a;
		IRExpr *a = undefinednessExpression(sm, i->arg1, vdm, opt);
		IRExpr *b = undefinednessExpression(sm, i->arg2, vdm, opt);
		IRExpr *c = undefinednessExpression(sm, i->arg3, vdm, opt);
		IRExpr *d = undefinednessExpression(sm, i->arg4, vdm, opt);
		if (a == UNDEFINED_EXPR)
			a = i->arg1;
		if (b == UNDEFINED_EXPR)
			b = i->arg2;
		if (c == UNDEFINED_EXPR)
			c = i->arg3;
		if (d == UNDEFINED_EXPR)
			d = i->arg4;
		if (a == i->arg1 && b == i->arg2 && c == i->arg3 && d == i->arg4)
			return i;
		return IRExpr_Qop(i->op, a, b, c, d);
	}
	case Iex_Triop: {
		IRExprTriop *i = (IRExprTriop *)a;
		IRExpr *a = undefinednessExpression(sm, i->arg1, vdm, opt);
		IRExpr *b = undefinednessExpression(sm, i->arg2, vdm, opt);
		IRExpr *c = undefinednessExpression(sm, i->arg3, vdm, opt);
		if (a == UNDEFINED_EXPR)
			a = i->arg1;
		if (b == UNDEFINED_EXPR)
			b = i->arg2;
		if (c == UNDEFINED_EXPR)
			c = i->arg3;
		if (a == i->arg1 && b == i->arg2 && c == i->arg3)
			return i;
		return IRExpr_Triop(i->op, a, b, c);
	}
	case Iex_Binop: {
		IRExprBinop *i = (IRExprBinop *)a;
		if (CONFIG_DISCARD_FLOATING_POINT) {
			if (i->op >= Iop_AddF64 && i->op <= Iop_RoundF64toInt)
				return UNDEFINED_EXPR;
		}
		IRExpr *a = undefinednessExpression(sm, i->arg1, vdm, opt);
		IRExpr *b = undefinednessExpression(sm, i->arg2, vdm, opt);
		if (a == UNDEFINED_EXPR || b == UNDEFINED_EXPR) {
			if (i->op >= Iop_CmpEQ8 && i->op <= Iop_CmpEQ64)
				return UNDEFINED_EXPR;
		}
		if (a == UNDEFINED_EXPR)
			a = i->arg1;
		if (b == UNDEFINED_EXPR)
			b = i->arg2;
		if (a == i->arg1 && b == i->arg2)
			return i;
		return IRExpr_Binop(i->op, a, b);
	}
	case Iex_Unop: {
		IRExprUnop *ieu = (IRExprUnop *)a;
		if (CONFIG_DISCARD_FLOATING_POINT) {
			switch (ieu->op) {
			case Iop_F32toF64:
				return UNDEFINED_EXPR;
			default:
				break;
			}
		}
		IRExpr *arg = undefinednessExpression(sm, ieu->arg, vdm, opt);
		if (arg == UNDEFINED_EXPR) {
			switch (ieu->op) {
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
			case Iop_F32toF64:
				return ieu;
			case Iop_BadPtr:
			case Iop_Not1:
			case Iop_Not8:
			case Iop_Not16:
			case Iop_Not32:
			case Iop_Not64:
			case Iop_Neg8:
			case Iop_Neg16:
			case Iop_Neg32:
			case Iop_Neg64:
			case Iop_64to8:
			case Iop_64to16:
			case Iop_64to32:
			case Iop_32to1:
			case Iop_32to8:
			case Iop_32to16:
			case Iop_16to8:
			case Iop_ReinterpF64asI64:
				return UNDEFINED_EXPR;
			default:
				printIRExpr(a);
				abort();
			}
		}
		if (arg != ieu->arg)
			return IRExpr_Unop(ieu->op, arg);
		return a;
	}
	case Iex_Load: {
		IRExprLoad *iel = (IRExprLoad *)a;
		IRExpr *addr = undefinednessExpression(sm, iel->addr, vdm, opt);
		if (addr == UNDEFINED_EXPR)
			return UNDEFINED_EXPR;
		if (addr->tag == Iex_Const) {
			unsigned long addrc = ((IRExprConst *)addr)->Ico.U64;
			bool isAcc;
			if (opt.addressAccessible(addrc, &isAcc) && !isAcc)
				return UNDEFINED_EXPR;
		}
		if (addr == iel->addr)
			return a;
		return IRExpr_Load(iel->ty, addr);
	}

	case Iex_Const:
	case Iex_HappensBefore:
	case Iex_FreeVariable:
	case Iex_EntryPoint:
	case Iex_ControlFlow:
		return a;

	case Iex_CCall: {
		IRExprCCall *i = (IRExprCCall *)a;
		IRExpr *v;
		int j;
		for (j = 0; i->args[j]; j++) {
			v = undefinednessExpression(sm, i->args[j], vdm, opt);
			if (v != i->args[j] && v != UNDEFINED_EXPR)
				break;
		}
		if (!i->args[j])
			return a;
		IRExpr **newArgs;
		int nr_args;
		for (nr_args = j + 1; i->args[nr_args]; nr_args++)
			;
		newArgs = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_args + 1);
		memcpy(newArgs, i->args, sizeof(newArgs[0]) * j);
		newArgs[j] = v;
		for (j++; i->args[j]; j++) {
			v = undefinednessExpression(sm, i->args[j], vdm, opt);
			if (v == UNDEFINED_EXPR)
				newArgs[j] = i->args[j];
			else
				newArgs[j] = v;
		}
		newArgs[j] = NULL;
		return IRExpr_CCall(i->cee, i->retty, newArgs);
	}

	case Iex_Mux0X: {
		IRExprMux0X *i = (IRExprMux0X *)a;
		IRExpr *c = undefinednessExpression(sm, i->cond, vdm, opt);
		IRExpr *z = undefinednessExpression(sm, i->expr0, vdm, opt);
		IRExpr *x = undefinednessExpression(sm, i->exprX, vdm, opt);

		if (c == UNDEFINED_EXPR) {
			if (z == UNDEFINED_EXPR || x == UNDEFINED_EXPR)
				return UNDEFINED_EXPR;
			return z;
		}
		if (z == UNDEFINED_EXPR)
			return x;
		if (x == UNDEFINED_EXPR)
			return z;
		if (c == i->cond && z == i->expr0 && x == i->exprX)
			return a;
		return IRExpr_Mux0X(c, z, x);
	}

	case Iex_Associative: {
		IRExprAssociative *i = (IRExprAssociative *)a;
		int x = 0;
		IRExpr *newE = (IRExpr *)0xf001dead; /* shut compiler up */
		while (x < i->nr_arguments) {
			newE = undefinednessExpression(sm, i->contents[x], vdm, opt);
			if (newE != i->contents[x]) {
				if (newE == UNDEFINED_EXPR)
					goto undefined;
				break;
			}
			x++;
		}
		if (x == i->nr_arguments)
			return a;
		{
			IRExprAssociative *r = (IRExprAssociative *)IRExpr_Associative(i);
			r->contents[x] = newE;
			for (x++; x < i->nr_arguments; x++) {
				r->contents[x] = undefinednessExpression(sm, i->contents[x], vdm, opt);
				if (r->contents[x] == UNDEFINED_EXPR)
					goto undefined;
				
			}
			return r;
		}

		undefined:
		switch (i->op) {
		case Iop_And1:
			return IRExpr_Const_U1(false);
		case Iop_And8:
			return IRExpr_Const_U8(0);
		case Iop_And16:
			return IRExpr_Const_U16(0);
		case Iop_And32:
			return IRExpr_Const_U32(0);
		case Iop_And64:
			return IRExpr_Const_U64(0);
		case Iop_Or1:
			return IRExpr_Const_U1(true);
		case Iop_Or8:
			return IRExpr_Const_U8(0xff);
		case Iop_Or16:
			return IRExpr_Const_U16(0xffff);
		case Iop_Or32:
			return IRExpr_Const_U32(~0u);
		case Iop_Or64:
			return IRExpr_Const_U64(~0ul);
		case Iop_Add8: case Iop_Add16: case Iop_Add32: case Iop_Add64:
		case Iop_Xor8: case Iop_Xor16: case Iop_Xor32: case Iop_Xor64:
			return UNDEFINED_EXPR;
		default:
			abort();
		}
	}
	}
	abort();
}

static bbdd *
undefinednessBBDD(bbdd::scope *scope,
		  StateMachineState *sm,
		  bbdd *what,
		  const VariableDefinednessMap &vdm,
		  const IRExprOptimisations &opt)
{
	if (what->isLeaf)
		return what;
	IRExpr *c = undefinednessExpression(sm, what->content.condition, vdm, opt);
	if (c == UNDEFINED_EXPR)
		return UNDEFINED_BBDD;
	bbdd *trueB = undefinednessBBDD(scope, sm, what->content.trueBranch, vdm, opt);
	bbdd *falseB = undefinednessBBDD(scope, sm, what->content.falseBranch, vdm, opt);
	if (trueB == UNDEFINED_BBDD)
		return falseB;
	if (falseB == UNDEFINED_BBDD)
		return trueB;
	return scope->makeInternal(c, trueB, falseB);
}

static smrbdd *
undefinednessSmrBDD(smrbdd::scope *scope,
		    StateMachineState *sm,
		    smrbdd *what,
		    const VariableDefinednessMap &vdm,
		    const IRExprOptimisations &opt)
{
	if (what->isLeaf)
		return what;
	IRExpr *c = undefinednessExpression(sm, what->content.condition, vdm, opt);
	if (c == UNDEFINED_EXPR)
		return UNDEFINED_SMRBDD;
	smrbdd *trueB = undefinednessSmrBDD(scope, sm, what->content.trueBranch, vdm, opt);
	smrbdd *falseB = undefinednessSmrBDD(scope, sm, what->content.falseBranch, vdm, opt);
	if (trueB == UNDEFINED_SMRBDD)
		return falseB;
	if (falseB == UNDEFINED_SMRBDD)
		return trueB;
	return scope->makeInternal(c, trueB, falseB);
}

static exprbdd *
undefinednessExprBDD(exprbdd::scope *scope,
		     bbdd::scope *bscope,
		     StateMachineState *sm,
		     exprbdd *what,
		     const VariableDefinednessMap &vdm,
		     const IRExprOptimisations &opt)
{
	if (what->isLeaf)
		return what;
	IRExpr *c = undefinednessExpression(sm, what->content.condition, vdm, opt);
	if (c == UNDEFINED_EXPR)
		return UNDEFINED_EXPRBDD;
	exprbdd *trueB = undefinednessExprBDD(scope, bscope, sm, what->content.trueBranch, vdm, opt);
	exprbdd *falseB = undefinednessExprBDD(scope, bscope, sm, what->content.falseBranch, vdm, opt);
	if (trueB == UNDEFINED_EXPRBDD)
		return falseB;
	if (falseB == UNDEFINED_EXPRBDD)
		return trueB;
	return exprbdd::ifelse(
		scope,
		bbdd::var(bscope, c),
		trueB,
		falseB);
}

static StateMachine *
undefinednessSimplification(SMScopes *scopes,
			    StateMachine *sm,
			    const IRExprOptimisations &opt,
			    bool *done_something)
{
	std::map<const StateMachineState *, int> stateLabels;
	if (debug_undefinedness) {
		printf("undefinednessSimplification:\n");
		printStateMachine(sm, stdout, stateLabels);
	}
	VariableDefinednessMap vdm;
	vdm.init(sm);
	if (debug_undefinedness) {
		printf("Variable definedness:\n");
		vdm.prettyPrint(stdout, stateLabels);
	}
	std::set<StateMachineState *> allStates;
	enumStates(sm, &allStates);
	for (auto it = allStates.begin(); it != allStates.end(); it++) {
		StateMachineState *sm = *it;
		switch (sm->type) {
		case StateMachineState::Terminal: {
			StateMachineTerminal *smt = (StateMachineTerminal *)sm;
			smrbdd *res = undefinednessSmrBDD(&scopes->smrs, sm, smt->res, vdm, opt);
			if (res != smt->res) {
				*done_something = true;
				if (res == UNDEFINED_SMRBDD) {
					if (debug_undefinedness)
						printf("l%d: terminal on undefined expression\n",
						       stateLabels[sm]);
					smt->res = scopes->smrs.cnst(smr_unreached);
				} else {
					if (debug_undefinedness) {
						printf("l%d: terminal changed from:",
						       stateLabels[sm]);
						smt->res->prettyPrint(stdout);
						printf("l%d: terminal changed to:",
						       stateLabels[sm]);
						res->prettyPrint(stdout);
					}
					smt->res = res;
				}
			}
			break;
		}
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)sm;
			bbdd *e = undefinednessBBDD(&scopes->bools, sm, smb->condition, vdm, opt);
			if (e != smb->condition) {
				*done_something = true;
				if (e == UNDEFINED_BBDD) {
					if (debug_undefinedness)
						printf("l%d: bifurcation on undefined value\n",
						       stateLabels[sm]);
					smb->falseTarget = smb->trueTarget =
						new StateMachineTerminal(
							smb->dbg_origin,
							scopes->smrs.cnst(smr_unreached));
				} else {
					if (debug_undefinedness) {
						printf("l%d: condition changed from:\n",
						       stateLabels[sm]);
						smb->condition->prettyPrint(stdout);
						printf("l%d: condition changed to:\n",
						       stateLabels[sm]);
						e->prettyPrint(stdout);
					}
					smb->condition = e;
				}
			}
			break;
		}
		case StateMachineState::SideEffecting: {
			StateMachineSideEffecting *smse = (StateMachineSideEffecting *)sm;
			if (smse->sideEffect) {
				StateMachineSideEffect *newSe = smse->sideEffect;
				switch (smse->sideEffect->type) {
				case StateMachineSideEffect::Load: {
					StateMachineSideEffectLoad *l = (StateMachineSideEffectLoad *)newSe;
					IRExpr *addr = undefinednessExpression(sm, l->addr, vdm, opt);
					if (addr != l->addr) {
						if (addr == UNDEFINED_EXPR) {
							newSe = StateMachineSideEffectUnreached::get();
						} else {
							newSe = new StateMachineSideEffectLoad(
								l, addr);
						}
					}
					break;
				}
				case StateMachineSideEffect::Store: {
					auto *s = (StateMachineSideEffectStore *)newSe;
					IRExpr *addr = undefinednessExpression(sm, s->addr, vdm, opt);
					exprbdd *data = undefinednessExprBDD(&scopes->exprs, &scopes->bools, sm, s->data, vdm, opt);
					if (addr != s->addr || data != s->data) {
						if (addr == UNDEFINED_EXPR || data == UNDEFINED_EXPRBDD)
							newSe = StateMachineSideEffectUnreached::get();
						else
							newSe = new StateMachineSideEffectStore(
								s, addr, data);
					}
					break;
				}
				case StateMachineSideEffect::Copy: {
					auto *c = (StateMachineSideEffectCopy *)newSe;
					exprbdd *v = undefinednessExprBDD(&scopes->exprs, &scopes->bools, sm, c->value, vdm, opt);
					if (v != c->value) {
						if (v == UNDEFINED_EXPRBDD)
							newSe = NULL;
						else
							newSe = new StateMachineSideEffectCopy(
								c->target, v);
					}
					break;
				}
				case StateMachineSideEffect::AssertFalse: {
					auto *a = (StateMachineSideEffectAssertFalse *)newSe;
					IRExpr *v = undefinednessExpression(sm, a->value, vdm, opt);
					if (v != a->value) {
						if (v == UNDEFINED_EXPR)
							newSe = StateMachineSideEffectUnreached::get();
						else
							newSe = new StateMachineSideEffectAssertFalse(
								v, a->reflectsActualProgram);
					}
					break;
				}
				case StateMachineSideEffect::StartAtomic:
				case StateMachineSideEffect::EndAtomic:
				case StateMachineSideEffect::PointerAliasing:
				case StateMachineSideEffect::StackLayout:
				case StateMachineSideEffect::Unreached:
					break;
				case StateMachineSideEffect::Phi: {
					auto *p = (StateMachineSideEffectPhi *)newSe;
					unsigned inIdx;
					unsigned outIdx;
					exprbdd *v = NULL;
					for (inIdx = 0; inIdx < p->generations.size(); inIdx++) {
						v = undefinednessExprBDD(&scopes->exprs, &scopes->bools, sm, p->generations[inIdx].val, vdm, opt);
						if (v != p->generations[inIdx].val)
							break;
					}
					if (inIdx == p->generations.size())
						break;
					std::vector<StateMachineSideEffectPhi::input> newGen;
					newGen.reserve(p->generations.size());
					newGen.resize(inIdx);
					for (outIdx = 0; outIdx < inIdx; outIdx++)
						newGen[outIdx] = p->generations[outIdx];

					goto middle_of_loop;
					while (inIdx < newGen.size()) {
						v = undefinednessExprBDD(&scopes->exprs, &scopes->bools, sm, p->generations[inIdx].val, vdm, opt);
					middle_of_loop:
						if (v != UNDEFINED_EXPRBDD)
							newGen[outIdx++].val = v;
						inIdx++;
					}
					newSe = new StateMachineSideEffectPhi(
						p, newGen);
					break;
				}
				case StateMachineSideEffect::StartFunction: {
					auto *s = (StateMachineSideEffectStartFunction *)newSe;
					IRExpr *v = undefinednessExpression(sm, s->rsp, vdm, opt);
					if (v != s->rsp && v != UNDEFINED_EXPR)
						newSe = new StateMachineSideEffectStartFunction(v, s->frame);
					break;
				}
				case StateMachineSideEffect::EndFunction: {
					auto *e = (StateMachineSideEffectEndFunction *)newSe;
					IRExpr *v = undefinednessExpression(sm, e->rsp, vdm, opt);
					if (v != e->rsp && v != UNDEFINED_EXPR)
						newSe = new StateMachineSideEffectEndFunction(v, e->frame);
					break;
				}
				}

				if (newSe != smse->sideEffect) {
					if (debug_undefinedness) {
						printf("l%d: side effect changed from ",
						       stateLabels[sm]);
						smse->sideEffect->prettyPrint(stdout);
						printf(" to ");
						if (newSe)
							newSe->prettyPrint(stdout);
						else
							printf("<no-op>");
						printf("\n");
					}
					*done_something = true;
					smse->sideEffect = newSe;
				}
			}
		}
		}
	}
	return sm;
}

};

StateMachine *
undefinednessSimplification(SMScopes *scopes, StateMachine *sm, const IRExprOptimisations &opt, bool *done_something)
{
	return _undefinedness::undefinednessSimplification(scopes, sm, opt, done_something);
}

