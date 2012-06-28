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

static IRRegArray *rawDupe(duplication_context &, const IRRegArray *inp)
{
	IRRegArray *res = new IRRegArray();
	res->base = inp->base;
	res->elemTy = inp->elemTy;
	res->nElems = inp->nElems;
	return res;
}

static IRConst *rawDupe(duplication_context &, const IRConst *inp)
{
	IRConst *res = new IRConst();
	res->tag = inp->tag;
	res->Ico = inp->Ico;
	return res;
}

static IRCallee *rawDupe(duplication_context &, const IRCallee *inp)
{
	IRCallee *res = new IRCallee();
	res->regparms = inp->regparms;
	res->name = inp->name;
	res->addr = inp->addr;
	res->mcx_mask = inp->mcx_mask;
	return res;
}

static IRExpr *rawDupe(duplication_context &ctxt, const IRExpr *inp)
{
	switch (inp->tag) {
	case Iex_Get: {
		const IRExprGet *i = (const IRExprGet *)inp;
		return new IRExprGet(i->reg, i->ty);
	}
	case Iex_GetI: {
		const IRExprGetI *i = (const IRExprGetI *)inp;
		IRExprGetI *res = new IRExprGetI();
		ctxt(&res->descr, i->descr, rawDupe);
		ctxt(&res->ix, i->ix, rawDupe);
		res->bias = i->bias;
		res->tid = i->tid;
		return res;
	}
	case Iex_Qop: {
		const IRExprQop *i = (const IRExprQop *)inp;
		IRExprQop *res = new IRExprQop();
		res->op = i->op;
		ctxt(&res->arg1, i->arg1, rawDupe);
		ctxt(&res->arg2, i->arg2, rawDupe);
		ctxt(&res->arg3, i->arg3, rawDupe);
		ctxt(&res->arg4, i->arg4, rawDupe);
		return res;
	}
	case Iex_Triop: {
		const IRExprTriop *i = (const IRExprTriop *)inp;
		IRExprTriop *res = new IRExprTriop();
		res->op = i->op;
		ctxt(&res->arg1, i->arg1, rawDupe);
		ctxt(&res->arg2, i->arg2, rawDupe);
		ctxt(&res->arg3, i->arg3, rawDupe);
		return res;
	}
	case Iex_Binop: {
		const IRExprBinop *i = (const IRExprBinop *)inp;
		IRExprBinop *res = new IRExprBinop();
		res->op = i->op;
		ctxt(&res->arg1, i->arg1, rawDupe);
		ctxt(&res->arg2, i->arg2, rawDupe);
		return res;
	}
	case Iex_Unop: {
		const IRExprUnop *i = (const IRExprUnop *)inp;
		IRExprUnop *res = new IRExprUnop();
		res->op = i->op;
		ctxt(&res->arg, i->arg, rawDupe);
		return res;
	}
	case Iex_Load: {
		const IRExprLoad *i = (const IRExprLoad *)inp;
		IRExprLoad *res = new IRExprLoad(i->rip);
		res->ty = i->ty;
		ctxt(&res->addr, i->addr, rawDupe);
		return res;
	}
	case Iex_Const: {
		const IRExprConst *i = (const IRExprConst *)inp;
		IRExprConst *res = new IRExprConst();
		ctxt(&res->con, i->con, rawDupe);
		return res;
	}
	case Iex_CCall: {
		const IRExprCCall *i = (const IRExprCCall *)inp;
		IRExprCCall *res = new IRExprCCall();
		ctxt(&res->cee, i->cee, rawDupe);
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
	case Iex_ClientCall: {
		const IRExprClientCall *i = (const IRExprClientCall *)inp;
		IRExprClientCall *res = new IRExprClientCall();
		res->calledRip = i->calledRip;
		res->callSite = i->callSite;
		int nr_args;
		for (nr_args = 0; i->args[nr_args]; nr_args++)
			;
		res->args = alloc_irexpr_array(nr_args + 1);
		for (nr_args = 0; i->args[nr_args]; nr_args++)
			ctxt(&res->args[nr_args], i->args[nr_args], rawDupe);
		res->args[nr_args] = NULL;
		return res;
	}
	case Iex_ClientCallFailed: {
		const IRExprClientCallFailed *i = (const IRExprClientCallFailed *)inp;
		IRExprClientCallFailed *res = new IRExprClientCallFailed();
		ctxt(&res->target, i->target, rawDupe);
		return res;
	}
	case Iex_HappensBefore: {
		const IRExprHappensBefore *i = (const IRExprHappensBefore *)inp;
		return new IRExprHappensBefore(i->before, i->after);
	}
	case Iex_Phi: {
		const IRExprPhi *i = (const IRExprPhi *)inp;
		return new IRExprPhi(i->reg, i->generations, i->ty);
	}
	case Iex_FreeVariable: {
		const IRExprFreeVariable *i = (const IRExprFreeVariable *)inp;
		return new IRExprFreeVariable(i->id, i->ty, i->isUnique);
	}
	}
	abort();
}

static StateMachineSideEffectLoad *
rawDupeS(duplication_context &ctxt, const StateMachineSideEffectLoad *l)
{
	StateMachineSideEffectLoad *res = new StateMachineSideEffectLoad(l->target,
									 NULL,
									 l->rip,
									 l->type);
	ctxt(&res->addr, l->addr, rawDupe);
	return res;
}

static StateMachineSideEffectStore *
rawDupeS(duplication_context &ctxt, const StateMachineSideEffectStore *l)
{
	StateMachineSideEffectStore *res = new StateMachineSideEffectStore(NULL,
									   NULL,
									   l->rip);
	ctxt(&res->addr, l->addr, rawDupe);
	ctxt(&res->data, l->data, rawDupe);
	return res;
}

static StateMachineSideEffectUnreached *
rawDupeS(duplication_context &, const StateMachineSideEffectUnreached *)
{
	return StateMachineSideEffectUnreached::get();
}

static StateMachineSideEffectStartAtomic *
rawDupeS(duplication_context &, const StateMachineSideEffectStartAtomic *)
{
	return StateMachineSideEffectStartAtomic::get();
}

static StateMachineSideEffectEndAtomic *
rawDupeS(duplication_context &, const StateMachineSideEffectEndAtomic *)
{
	return StateMachineSideEffectEndAtomic::get();
}

static StateMachineSideEffectAssertFalse *
rawDupeS(duplication_context &ctxt, const StateMachineSideEffectAssertFalse *l)
{
	StateMachineSideEffectAssertFalse *res = new StateMachineSideEffectAssertFalse(NULL, l->reflectsActualProgram);
	ctxt(&res->value, l->value, rawDupe);
	return res;
}

static StateMachineSideEffectCopy *
rawDupeS(duplication_context &ctxt, const StateMachineSideEffectCopy *l)
{
	StateMachineSideEffectCopy *res = new StateMachineSideEffectCopy(l->target,
									 NULL);
	ctxt(&res->value, l->value, rawDupe);
	return res;
}

static StateMachineSideEffectPhi *
rawDupeS(duplication_context &ctxt, const StateMachineSideEffectPhi *l)
{
	StateMachineSideEffectPhi *res = new StateMachineSideEffectPhi(l->reg, l->generations);
	for (unsigned x = 0; x < l->generations.size(); x++) {
		if (l->generations[x].second)
			ctxt(&res->generations[x].second, l->generations[x].second, rawDupe);
	}
	return res;
}

static StateMachineSideEffectStartFunction *
rawDupeS(duplication_context &ctxt, const StateMachineSideEffectStartFunction *l)
{
	auto *res = new StateMachineSideEffectStartFunction(NULL);
	ctxt(&res->rsp, l->rsp, rawDupe);
	return res;
}

static StateMachineSideEffectEndFunction *
rawDupeS(duplication_context &ctxt, const StateMachineSideEffectEndFunction *l)
{
	auto *res = new StateMachineSideEffectEndFunction(NULL);
	ctxt(&res->rsp, l->rsp, rawDupe);
	return res;
}

static StateMachineSideEffect *
rawDupe(duplication_context &ctxt, const StateMachineSideEffect *smse)
{
	switch (smse->type) {
#define do_case(n)							\
		case StateMachineSideEffect::n:				\
			return rawDupeS(ctxt,				\
					(const StateMachineSideEffect ## n *)smse);
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
		StateMachineBifurcate *res = new StateMachineBifurcate(smb->origin, NULL, NULL, NULL);
		ctxt(&res->condition, smb->condition, rawDupe);
		ctxt(&res->trueTarget, smb->trueTarget, rawDupe);
		ctxt(&res->falseTarget, smb->falseTarget, rawDupe);
		return res;
	}
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)inp;
		StateMachineSideEffecting *res = new StateMachineSideEffecting(sme->origin,
									       sme->sideEffect ? rawDupe(ctxt, sme->sideEffect) : NULL,
									       NULL);
		ctxt(&res->target, sme->target, rawDupe);
		return res;
	}
	case StateMachineState::NdChoice: {
		StateMachineNdChoice *smnd = (StateMachineNdChoice *)inp;
		std::vector<StateMachineState *> s(smnd->successors);
		StateMachineNdChoice *res = new StateMachineNdChoice(inp->origin, s);
		for (auto it = res->successors.begin(); it != res->successors.end(); it++)
			ctxt(&*it, *it, rawDupe);
		return res;
	}
	case StateMachineState::Unreached:
		return StateMachineUnreached::get();
	case StateMachineState::Crash:
		return StateMachineCrash::get();
	case StateMachineState::NoCrash:
		return StateMachineNoCrash::get();
	case StateMachineState::Stub: {
		StateMachineStub *sms = (StateMachineStub *)inp;
		return new StateMachineStub(sms->origin, sms->target);
	}
	}
	abort();
}

static StateMachine *
rawDupe(duplication_context &ctxt, const StateMachine *inp)
{
	StateMachine *res = new StateMachine(
		NULL,
		inp->origin);
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

