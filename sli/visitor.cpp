#include "sli.h"
#include "visitor.hpp"

visit_result
_visit_irexpr(void *ctxt,
	      const irexpr_visitor<void> *visitor,
	      const IRExpr *expr)
{
	visit_result res = visit_continue;
	switch (expr->tag) {
#define do_head(name)							\
		case Iex_ ## name :					\
			if (visitor->name)				\
				res = visitor->name(			\
					ctxt,				\
					(const IRExpr ## name *)expr);
#define do_child(ty, field)						\
		if (res == visit_continue)				\
			res = _visit_irexpr(				\
				ctxt, visitor,				\
				((IRExpr ## ty *)expr)->field)
		do_head(Get);
		break;

		do_head(GetI);
		do_child(GetI, ix);
		break;

		do_head(Qop);
		do_child(Qop, arg1);
		do_child(Qop, arg2);
		do_child(Qop, arg3);
		do_child(Qop, arg4);
		break;

		do_head(Triop);
		do_child(Triop, arg1);
		do_child(Triop, arg2);
		do_child(Triop, arg3);
		break;

		do_head(Binop);
		do_child(Binop, arg1);
		do_child(Binop, arg2);
		break;

		do_head(Unop);
		do_child(Unop, arg);
		break;

		do_head(Const);
		break;

		do_head(Mux0X);
		do_child(Mux0X, cond);
		do_child(Mux0X, expr0);
		do_child(Mux0X, exprX);
		break;

		do_head(CCall);
		{
			IRExprCCall *cee = (IRExprCCall *)expr;
			for (int i = 0; res == visit_continue && cee->args[i]; i++)
				res = _visit_irexpr(ctxt, visitor, cee->args[i]);
		}
		break;

		do_head(Associative);
		{
			IRExprAssociative *iea = (IRExprAssociative *)expr;
			for (int i = 0; res == visit_continue && i < iea->nr_arguments; i++)
				res = _visit_irexpr(ctxt, visitor, iea->contents[i]);
		}
		break;

		do_head(Load);
		do_child(Load, addr);
		break;

		do_head(HappensBefore);
		break;

		do_head(FreeVariable);
		break;

		do_head(EntryPoint);
		break;

		do_head(ControlFlow);
		break;
#undef do_head
#undef do_child
	}
	return res;
}

visit_result
_visit_side_effect(void *ctxt,
		   const state_machine_visitor<void> *visitor,
		   const StateMachineSideEffect *sme)
{
	visit_result res = visit_continue;
	switch (sme->type) {
	case StateMachineSideEffect::Load: {
		auto l = (const StateMachineSideEffectLoad *)sme;
		if (visitor->Load)
			res = visitor->Load(ctxt, l);
		if (res == visit_continue)
			res = _visit_bdd(ctxt, &visitor->bdd, _visit_irexpr, l->addr);
		return res;
	}
	case StateMachineSideEffect::Store: {
		auto s = (const StateMachineSideEffectStore *)sme;
		if (visitor->Store)
			res = visitor->Store(ctxt, s);
		if (res == visit_continue)
			res = _visit_bdd(ctxt, &visitor->bdd, _visit_irexpr, s->addr);
		if (res == visit_continue)
			res = _visit_bdd(ctxt, &visitor->bdd, _visit_irexpr, s->data);
		return res;
	}
	case StateMachineSideEffect::Copy: {
		auto c = (const StateMachineSideEffectCopy *)sme;
		if (visitor->Copy)
			res = visitor->Copy(ctxt, c);
		if (res == visit_continue)
			res = _visit_bdd(ctxt, &visitor->bdd, _visit_irexpr, c->value);
		return res;
	}
	case StateMachineSideEffect::AssertFalse: {
		auto c = (const StateMachineSideEffectAssertFalse *)sme;
		if (visitor->AssertFalse)
			res = visitor->AssertFalse(ctxt, c);
		if (res == visit_continue)
			res = visit_bdd(ctxt, &visitor->bdd, c->value);
		return res;
	}
	case StateMachineSideEffect::Phi: {
		auto p = (const StateMachineSideEffectPhi *)sme;
		if (visitor->Phi)
			res = visitor->Phi(ctxt, p);
		for (auto it = p->generations.begin();
		     res == visit_continue && it != p->generations.end();
		     it++)
			res = _visit_bdd(ctxt, &visitor->bdd, _visit_irexpr, it->val);
		return res;
	}
#if !CONFIG_NO_STATIC_ALIASING
	case StateMachineSideEffect::StartFunction: {
		auto s = (const StateMachineSideEffectStartFunction *)sme;
		if (visitor->StartFunction)
			res = visitor->StartFunction(ctxt, s);
		if (res == visit_continue)
			res = _visit_bdd(ctxt, &visitor->bdd, _visit_irexpr, s->rsp);
		return res;
	}
	case StateMachineSideEffect::EndFunction: {
		auto s = (const StateMachineSideEffectEndFunction *)sme;
		if (visitor->EndFunction)
			res = visitor->EndFunction(ctxt, s);
		if (res == visit_continue)
			_visit_bdd(ctxt, &visitor->bdd, _visit_irexpr, s->rsp);
		return res;
	}
#endif
#define do_simple(name)							\
		case StateMachineSideEffect::name:			\
			if (visitor->name)				\
				res = visitor->name(			\
					ctxt,				\
					(const StateMachineSideEffect ## name *)sme); \
			return res;
		do_simple(Unreached)
		do_simple(StartAtomic)
		do_simple(EndAtomic)
		do_simple(ImportRegister)
#if !CONFIG_NO_STATIC_ALIASING
		do_simple(StackLayout)
#endif
#undef do_simple
	}
	abort();
}

visit_result
_visit_one_state(void *ctxt,
		 const state_machine_visitor<void> *visitor,
		 const StateMachineState *s)
{
	visit_result res = visit_continue;
	switch (s->type) {
	case StateMachineState::Terminal: {
		auto smt = (const StateMachineTerminal *)s;
		if (visitor->Terminal)
			res = visitor->Terminal(ctxt, smt);
		if (res == visit_continue)
			res = _visit_bdd(ctxt, &visitor->bdd, (visit_result (*)(void *, const irexpr_visitor<void> *, StateMachineRes))NULL, smt->res);
		return res;
	}
	case StateMachineState::Bifurcate: {
		auto smb = (const StateMachineBifurcate *)s;
		if (visitor->Bifurcate)
			res = visitor->Bifurcate(ctxt, smb);
		if (res == visit_continue)
			res = _visit_bdd(ctxt, &visitor->bdd, (visit_result (*)(void *, const irexpr_visitor<void> *, bool))NULL, smb->condition);
		return res;
	}
	case StateMachineState::SideEffecting: {
		auto sme = (const StateMachineSideEffecting *)s;
		if (visitor->SideEffecting)
			res = visitor->SideEffecting(ctxt, sme);
		if (res == visit_continue && sme->sideEffect)
			res = visit_side_effect(ctxt, visitor, sme->sideEffect);
		return res;
	}
	}
	abort();
}

visit_result
_visit_state_machine(void *ctxt,
		     const state_machine_visitor<void> *visitor,
		     const StateMachineState *sm,
		     std::set<const StateMachineState *> &memo)
{
	if (!memo.insert(sm).second)
		return visit_continue;
	visit_result res = visit_continue;
	switch (sm->type) {
	case StateMachineState::Terminal: {
		auto smt = (const StateMachineTerminal *)sm;
		if (visitor->Terminal)
			res = visitor->Terminal(ctxt, smt);
		if (res == visit_continue)
			res = visit_const_bdd(ctxt, &visitor->bdd, smt->res);
		return res;
	}
	case StateMachineState::Bifurcate: {
		auto smb = (const StateMachineBifurcate *)sm;
		if (visitor->Bifurcate)
			res = visitor->Bifurcate(ctxt, smb);
		if (res == visit_continue)
			res = visit_const_bdd(ctxt, &visitor->bdd, smb->condition);
		if (res == visit_continue)
			res = _visit_state_machine(ctxt, visitor, smb->trueTarget, memo);
		if (res == visit_continue)
			res = _visit_state_machine(ctxt, visitor, smb->falseTarget, memo);
		return res;
	}
	case StateMachineState::SideEffecting: {
		auto sme = (const StateMachineSideEffecting *)sm;
		if (visitor->SideEffecting)
			res = visitor->SideEffecting(ctxt, sme);
		if (res == visit_continue && sme->sideEffect)
			res = visit_side_effect(ctxt, visitor, sme->sideEffect);
		if (res == visit_continue)
			res = _visit_state_machine(ctxt, visitor, sme->target, memo);
		return res;
	}
	}
	abort();
}

visit_result
visit_state_machine(void *ctxt,
		    const state_machine_visitor<void> *visitor,
		    const StateMachine *sm)
{
	std::set<const StateMachineState *> memo;
	return _visit_state_machine(ctxt, visitor, sm->root, memo);
}

template <typename constT, typename subtreeT> static visit_result
_visit_bdd(void *ctxt,
	   const bdd_visitor<void> *visitor,
	   visit_result (*visitLeaf)(void *ctxt, const irexpr_visitor<void> *, constT cnst),
	   const subtreeT *bdd,
	   std::set<const subtreeT *> &visited,
	   std::set<bdd_rank> &visitedRanks)
{
	if (!visited.insert(bdd).second)
		return visit_continue;
	visit_result res = visit_continue;
	if (bdd->isLeaf()) {
		if (visitLeaf)
			res = visitLeaf(ctxt, &visitor->irexpr, bdd->leaf());
	} else {
		if (visitedRanks.insert(bdd->internal().rank).second) {
			if (visitor->rank) {
				res = visitor->rank(ctxt, bdd->internal().rank);
			}
			if (res == visit_continue) {
				res = _visit_irexpr(ctxt, &visitor->irexpr, bdd->internal().condition);
			}
		}
		if (res == visit_continue) {
			res = _visit_bdd(ctxt, visitor, visitLeaf, bdd->internal().trueBranch, visited, visitedRanks);
		}
		if (res == visit_continue) {
			res = _visit_bdd(ctxt, visitor, visitLeaf, bdd->internal().falseBranch, visited, visitedRanks);
		}
	}
	return res;
}

template <typename constT, typename subtreeT> visit_result
_visit_bdd(void *ctxt,
	   const bdd_visitor<void> *visitor,
	   visit_result (*visitLeaf)(void *ctxt, const irexpr_visitor<void> *, constT cnst),
	   const subtreeT *bdd)
{
	std::set<const subtreeT *> visited;
	std::set<bdd_rank> visitedRanks;
	return _visit_bdd(ctxt, visitor, visitLeaf, bdd, visited, visitedRanks);
}

template visit_result _visit_bdd<bool, bbdd>(
	void *,
	const bdd_visitor<void> *,
	visit_result (*visitLeaf)(void *, const irexpr_visitor<void> *, bool),
	const bbdd *);
template visit_result _visit_bdd<StateMachineRes, smrbdd>(
	void *,
	const bdd_visitor<void> *,
	visit_result (*visitLeaf)(void *, const irexpr_visitor<void> *, StateMachineRes),
	const smrbdd *);
