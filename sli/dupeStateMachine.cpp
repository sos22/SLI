#include "sli.h"
#include "state_machine.hpp"

namespace _dupeStateMachine {

class duplication_context {
	typedef void *duplicator_t(duplication_context &ctxt,
				   const void *old);

	struct reloc_t {
		void **ptr;
		const void *old;
		duplicator_t *f;
	};
		
	std::map<const void *, void *> transTable;
	std::vector<reloc_t> relocs;

public:
	template <typename t> void operator()(t **out, const t *inp,
					      t *(*rawDupe)(duplication_context &ctxt,
							    const t *old))
	{
		reloc_t r;
		r.ptr = (void **)out;
		r.old = (const void *)inp;
		r.f = (duplicator_t *)rawDupe;
		relocs.push_back(r);
	}

	void doit(void)
	{
		while (!relocs.empty()) {
			reloc_t r = relocs.back();
			relocs.pop_back();
			auto it = transTable.find(r.old);
			if (it != transTable.end()) {
				*r.ptr = it->second;
				continue;
			}
			void *res = r.f(*this, r.old);
			transTable[r.old] = res;
			*r.ptr = res;
		}
	}
};

static IRExpr *rawDupe(duplication_context &ctxt, const IRExpr *inp)
{
	switch (inp->tag) {
	case Iex_Get: {
		const IRExprGet *i = (const IRExprGet *)inp;
		return (IRExprGet *)i;
	}
	case Iex_GetI: {
		const IRExprGetI *i = (const IRExprGetI *)inp;
		IRExprGetI *res = new IRExprGetI(i, NULL);
		ctxt((IRExpr **)&res->ix, i->ix, rawDupe);
		return res;
	}
	case Iex_Qop: {
		const IRExprQop *i = (const IRExprQop *)inp;
		IRExprQop *res = new IRExprQop(i->op);
		ctxt(&res->arg1, i->arg1, rawDupe);
		ctxt(&res->arg2, i->arg2, rawDupe);
		ctxt(&res->arg3, i->arg3, rawDupe);
		ctxt(&res->arg4, i->arg4, rawDupe);
		return res;
	}
	case Iex_Triop: {
		const IRExprTriop *i = (const IRExprTriop *)inp;
		IRExprTriop *res = new IRExprTriop(i->op);
		ctxt(&res->arg1, i->arg1, rawDupe);
		ctxt(&res->arg2, i->arg2, rawDupe);
		ctxt(&res->arg3, i->arg3, rawDupe);
		return res;
	}
	case Iex_Binop: {
		const IRExprBinop *i = (const IRExprBinop *)inp;
		IRExprBinop *res = new IRExprBinop(i->op);
		ctxt(&res->arg1, i->arg1, rawDupe);
		ctxt(&res->arg2, i->arg2, rawDupe);
		return res;
	}
	case Iex_Unop: {
		const IRExprUnop *i = (const IRExprUnop *)inp;
		IRExprUnop *res = new IRExprUnop(i->op);
		ctxt(&res->arg, i->arg, rawDupe);
		return res;
	}
	case Iex_Load: {
		const IRExprLoad *i = (const IRExprLoad *)inp;
		IRExprLoad *res = new IRExprLoad(i->ty);
		ctxt(&res->addr, i->addr, rawDupe);
		return res;
	}
	case Iex_Const:
		return (IRExprConst *)inp;
	case Iex_CCall: {
		const IRExprCCall *i = (const IRExprCCall *)inp;
		IRExprCCall *res = new IRExprCCall();
		res->cee = i->cee;
		res->retty = i->retty;
		int nr_args;
		for (nr_args = 0; i->args[nr_args]; nr_args++)
			;
		res->args = alloc_irexpr_array(nr_args + 1);
		for (nr_args = 0; i->args[nr_args]; nr_args++)
			ctxt(&res->args[nr_args], i->args[nr_args], rawDupe);
		res->args[nr_args] = NULL;
		return res;
	}
	case Iex_Mux0X: {
		const IRExprMux0X *i = (const IRExprMux0X *)inp;
		IRExprMux0X *res = new IRExprMux0X();
		ctxt(&res->cond, i->cond, rawDupe);
		ctxt(&res->expr0, i->expr0, rawDupe);
		ctxt(&res->exprX, i->exprX, rawDupe);
		return res;
	}
	case Iex_Associative: {
		const IRExprAssociative *i = (const IRExprAssociative *)inp;
		IRExprAssociative *res = new IRExprAssociative();
		res->op = i->op;
		res->nr_arguments = i->nr_arguments;
		res->nr_arguments_allocated = i->nr_arguments;
		static libvex_allocation_site __las = {0, __FILE__, __LINE__};		
		res->contents =
			(IRExpr **)__LibVEX_Alloc_Bytes(&ir_heap,
							sizeof(res->contents[0]) * res->nr_arguments,
							&__las);
		for (int j = 0; j < res->nr_arguments; j++)
			ctxt(&res->contents[j], i->contents[j], rawDupe);
		return res;
	}
	case Iex_HappensBefore: {
		const IRExprHappensBefore *i = (const IRExprHappensBefore *)inp;
		return new IRExprHappensBefore(i->before, i->after);
	}
	case Iex_FreeVariable: {
		const IRExprFreeVariable *i = (const IRExprFreeVariable *)inp;
		return new IRExprFreeVariable(i->id, i->ty, i->isUnique);
	}
	case Iex_EntryPoint: {
		const IRExprEntryPoint *i = (const IRExprEntryPoint *)inp;
		return new IRExprEntryPoint(*i);
	}
	case Iex_ControlFlow: {
		const IRExprControlFlow *i = (const IRExprControlFlow *)inp;
		return new IRExprControlFlow(*i);
	}
	}
	abort();
}

static StateMachineSideEffectLoad *
rawDupeS(const StateMachineSideEffectLoad *l)
{
	return new StateMachineSideEffectLoad(l, l->addr);
}

static StateMachineSideEffectStore *
rawDupeS(const StateMachineSideEffectStore *l)
{
	return new StateMachineSideEffectStore(l, l->addr, l->data);
}

static StateMachineSideEffectUnreached *
rawDupeS(const StateMachineSideEffectUnreached *)
{
	return StateMachineSideEffectUnreached::get();
}

static StateMachineSideEffectStartAtomic *
rawDupeS(const StateMachineSideEffectStartAtomic *)
{
	return StateMachineSideEffectStartAtomic::get();
}

static StateMachineSideEffectEndAtomic *
rawDupeS(const StateMachineSideEffectEndAtomic *)
{
	return StateMachineSideEffectEndAtomic::get();
}

static StateMachineSideEffectAssertFalse *
rawDupeS(const StateMachineSideEffectAssertFalse *l)
{
	return new StateMachineSideEffectAssertFalse(l->value, l->reflectsActualProgram);
}

static StateMachineSideEffectCopy *
rawDupeS(const StateMachineSideEffectCopy *l)
{
	return new StateMachineSideEffectCopy(l->target, l->value);
}

static StateMachineSideEffectPhi *
rawDupeS(const StateMachineSideEffectPhi *l)
{
	return new StateMachineSideEffectPhi(l->reg, l->ty, l->generations);
}

static StateMachineSideEffectStartFunction *
rawDupeS(const StateMachineSideEffectStartFunction *l)
{
	return new StateMachineSideEffectStartFunction(l->rsp, l->frame);
}

static StateMachineSideEffectEndFunction *
rawDupeS(const StateMachineSideEffectEndFunction *l)
{
	return new StateMachineSideEffectEndFunction(l->rsp, l->frame);
}

static StateMachineSideEffectImportRegister *
rawDupeS(const StateMachineSideEffectImportRegister *l)
{
	return new StateMachineSideEffectImportRegister(*l);
}

static StateMachineSideEffectStackLayout *
rawDupeS(const StateMachineSideEffectStackLayout *l)
{
	return new StateMachineSideEffectStackLayout(l->functions);
}

static StateMachineSideEffect *
rawDupe(const StateMachineSideEffect *smse)
{
	switch (smse->type) {
#define do_case(n)							\
		case StateMachineSideEffect::n:				\
			return rawDupeS((const StateMachineSideEffect ## n *)smse);
		all_side_effect_types(do_case);
#undef do_case
	}
	abort();
}

static StateMachineState *rawDupe(duplication_context &ctxt, const StateMachineState *inp);

static StateMachineState *
rawDupe(duplication_context &ctxt, const StateMachineState *inp)
{
	switch (inp->type) {
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)inp;
		StateMachineBifurcate *res = new StateMachineBifurcate(smb->dbg_origin, smb->condition, NULL, NULL);
		ctxt(&res->trueTarget, smb->trueTarget, rawDupe);
		ctxt(&res->falseTarget, smb->falseTarget, rawDupe);
		return res;
	}
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)inp;
		StateMachineSideEffecting *res = new StateMachineSideEffecting(sme->dbg_origin,
									       sme->sideEffect ? rawDupe(sme->sideEffect) : NULL,
									       NULL);
		ctxt(&res->target, sme->target, rawDupe);
		return res;
	}
	case StateMachineState::Terminal: {
		StateMachineTerminal *smt = (StateMachineTerminal *)inp;
		return new StateMachineTerminal(smt->dbg_origin, smt->res);
	}
	}
	abort();
}

static StateMachine *
rawDupe(duplication_context &ctxt, const StateMachine *inp)
{
	StateMachine *res = new StateMachine((StateMachine *)inp, NULL);
	ctxt(&res->root, inp->root, rawDupe);
	return res;
}

static StateMachine *
duplicateStateMachine(const StateMachine *inp)
{
	duplication_context ctxt;
	StateMachine *res;
	ctxt(&res, inp, rawDupe);
	ctxt.doit();
	return res;
}

/* End of namespace */
};

StateMachine *
duplicateStateMachine(const StateMachine *inp)
{
	return _dupeStateMachine::duplicateStateMachine(inp);
}

