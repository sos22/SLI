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

#define UNDEFINED_EXPR ((IRExpr *)3)

#ifndef NDEBUG
static bool debug_undefinedness = false;
#else
#define debug_undefinedness false
#endif

namespace _undefinedness {

template <typename t, typename s> static bool
operator |=(std::set<t, s> &a, const std::set<t, s> &b)
{
	bool res = false;
	for (auto it = b.begin(); it != b.end(); it++)
		res |= a.insert(*it).second;
	return res;
}

class VariableDefinednessMap {
	typedef std::set<threadAndRegister, threadAndRegister::fullCompare> entryT ;
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
undefinednessExpression(StateMachineState *sm, IRExpr *a, const VariableDefinednessMap &vdm)
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
		IRExpr *ix = undefinednessExpression(sm, iegi->ix, vdm);
		if (ix == UNDEFINED_EXPR)
			return a;
		if (ix != iegi->ix)
			return IRExpr_GetI(iegi->descr, ix, iegi->bias, iegi->tid);
		return a;
	}
	case Iex_Qop: {
		IRExprQop *i = (IRExprQop *)a;
		IRExpr *a = undefinednessExpression(sm, i->arg1, vdm);
		IRExpr *b = undefinednessExpression(sm, i->arg2, vdm);
		IRExpr *c = undefinednessExpression(sm, i->arg3, vdm);
		IRExpr *d = undefinednessExpression(sm, i->arg4, vdm);
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
		IRExpr *a = undefinednessExpression(sm, i->arg1, vdm);
		IRExpr *b = undefinednessExpression(sm, i->arg2, vdm);
		IRExpr *c = undefinednessExpression(sm, i->arg3, vdm);
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
		IRExpr *a = undefinednessExpression(sm, i->arg1, vdm);
		IRExpr *b = undefinednessExpression(sm, i->arg2, vdm);
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
		IRExpr *arg = undefinednessExpression(sm, ieu->arg, vdm);
		if (arg == UNDEFINED_EXPR) {
			switch (ieu->op) {
			case Iop_32Uto64:
				return ieu;
			default:
				abort();
			}
		}
		if (arg != ieu->arg)
			return IRExpr_Unop(ieu->op, arg);
		return a;
	}
	case Iex_Load: {
		IRExprLoad *iel = (IRExprLoad *)a;
		IRExpr *addr = undefinednessExpression(sm, iel->addr, vdm);
		if (addr == UNDEFINED_EXPR)
			return UNDEFINED_EXPR;
		if (addr == iel->addr)
			return a;
		return IRExpr_Load(iel->ty, addr);
	}

	case Iex_Const:
	case Iex_HappensBefore:
	case Iex_FreeVariable:
		return a;

	case Iex_CCall: {
		IRExprCCall *i = (IRExprCCall *)a;
		IRExpr *v;
		int j;
		for (j = 0; i->args[j]; j++) {
			v = undefinednessExpression(sm, i->args[j], vdm);
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
			v = undefinednessExpression(sm, i->args[j], vdm);
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
		IRExpr *c = undefinednessExpression(sm, i->cond, vdm);
		IRExpr *z = undefinednessExpression(sm, i->expr0, vdm);
		IRExpr *x = undefinednessExpression(sm, i->exprX, vdm);

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
			newE = undefinednessExpression(sm, i->contents[x], vdm);
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
				r->contents[x] = undefinednessExpression(sm, i->contents[x], vdm);
				if (r->contents[x] == UNDEFINED_EXPR)
					goto undefined;
				
			}
			return r;
		}

		undefined:
		if (i->op == Iop_And1)
			return IRExpr_Const(IRConst_U1(0));
		else if (i->op == Iop_Or1)
			return IRExpr_Const(IRConst_U1(1));
		else if (i->op == Iop_Add64)
			return UNDEFINED_EXPR;
		else
			abort();
	}
	}
	abort();
}

static StateMachine *
undefinednessSimplification(StateMachine *sm, bool *done_something)
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
		case StateMachineState::Unreached:
		case StateMachineState::Crash:
		case StateMachineState::NoCrash:
			break;
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)sm;
			IRExpr *e = undefinednessExpression(sm, smb->condition, vdm);
			if (e != smb->condition) {
				*done_something = true;
				if (e == UNDEFINED_EXPR) {
					if (debug_undefinedness)
						printf("l%d: bifurcation on undefined value\n",
						       stateLabels[sm]);
					smb->trueTarget = StateMachineUnreached::get();
					smb->falseTarget = StateMachineUnreached::get();
				} else {
					if (debug_undefinedness)
						printf("l%d: condition changed from %s to %s\n",
						       stateLabels[sm],
						       nameIRExpr(smb->condition),
						       nameIRExpr(e));
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
					IRExpr *addr = undefinednessExpression(sm, l->addr, vdm);
					if (addr != l->addr) {
						if (addr == UNDEFINED_EXPR) {
							newSe = NULL;
						} else {
							newSe = new StateMachineSideEffectLoad(
								l, addr);
						}
					}
					break;
				}
				case StateMachineSideEffect::Store: {
					auto *s = (StateMachineSideEffectStore *)newSe;
					IRExpr *addr = undefinednessExpression(sm, s->addr, vdm);
					IRExpr *data = undefinednessExpression(sm, s->data, vdm);
					if (addr != s->addr || data != s->data) {
						if (addr == UNDEFINED_EXPR || data == UNDEFINED_EXPR)
							newSe = NULL;
						else
							newSe = new StateMachineSideEffectStore(
								s, addr, data);
					}
					break;
				}
				case StateMachineSideEffect::Copy: {
					auto *c = (StateMachineSideEffectCopy *)newSe;
					IRExpr *v = undefinednessExpression(sm, c->value, vdm);
					if (v != c->value) {
						if (v == UNDEFINED_EXPR)
							newSe = NULL;
						else
							newSe = new StateMachineSideEffectCopy(
								c->target, v);
					}
					break;
				}
				case StateMachineSideEffect::AssertFalse: {
					auto *a = (StateMachineSideEffectAssertFalse *)newSe;
					IRExpr *v = undefinednessExpression(sm, a->value, vdm);
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
				case StateMachineSideEffect::StackUnescaped:
				case StateMachineSideEffect::PointerAliasing:
				case StateMachineSideEffect::StackLayout:
				case StateMachineSideEffect::Unreached:
					break;
				case StateMachineSideEffect::Phi: {
					auto *p = (StateMachineSideEffectPhi *)newSe;
					unsigned x;
					IRExpr *v = NULL;
					for (x = 0; x < p->generations.size(); x++) {
						if (!p->generations[x].second)
							continue;
						v = undefinednessExpression(sm, p->generations[x].second, vdm);
						if (v == p->generations[x].second)
							continue;
						if (v != UNDEFINED_EXPR)
							break;
					}
					if (x == p->generations.size())
						break;
					std::vector<std::pair<unsigned, IRExpr *> > newGen(p->generations);
					newGen[x].second = v;
					for (x++; x < newGen.size(); x++) {
						if (!newGen[x].second)
							continue;
						v = undefinednessExpression(sm, newGen[x].second, vdm);
						if (v == newGen[x].second)
							continue;
						if (v != UNDEFINED_EXPR)
							newGen[x].second = v;
					}
					newSe = new StateMachineSideEffectPhi(
						p->reg, newGen);
					break;
				}
				case StateMachineSideEffect::StartFunction: {
					auto *s = (StateMachineSideEffectStartFunction *)newSe;
					IRExpr *v = undefinednessExpression(sm, s->rsp, vdm);
					if (v != s->rsp && v != UNDEFINED_EXPR)
						newSe = new StateMachineSideEffectStartFunction(v, s->frame);
					break;
				}
				case StateMachineSideEffect::EndFunction: {
					auto *e = (StateMachineSideEffectEndFunction *)newSe;
					IRExpr *v = undefinednessExpression(sm, e->rsp, vdm);
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
undefinednessSimplification(StateMachine *sm, bool *done_something)
{
	return _undefinedness::undefinednessSimplification(sm, done_something);
}

