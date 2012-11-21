#ifndef VISITOR_HPP__
#define VISITOR_HPP__

#include "state_machine.hpp"
#include "bdd.hpp"

enum visit_result { visit_continue, visit_abort };

template <typename ctxtT> struct irexpr_visitor {
#define iter_type(name)						\
	visit_result (*name)(ctxtT *ctxt, const IRExpr ## name *);
	IREXPR_TYPES(iter_type)
#undef iter_type
};
visit_result _visit_irexpr(void *ctxt, const irexpr_visitor<void> *visitor, const IRExpr *expr);
template <typename ctxtT> static visit_result
visit_irexpr(ctxtT *ctxt,
	     const irexpr_visitor<ctxtT> *visitor,
	     const IRExpr *expr)
{
	return _visit_irexpr( (void *)ctxt, (const irexpr_visitor<void> *)visitor, expr);
}

template <typename constT, typename subtreeT> visit_result _visit_bdd(
	void *ctxt,
	const irexpr_visitor<void> *visitor,
	visit_result (*visitLeaf)(void *ctxt, const irexpr_visitor<void> *, constT cnst),
	const subtreeT *bdd);
template <typename constT, typename subtreeT, typename ctxtT> static visit_result
visit_bdd(ctxtT *ctxt,
	  const irexpr_visitor<ctxtT> *visitor,
	  visit_result (*visitLeaf)(ctxtT *ctxt, const irexpr_visitor<ctxtT> *, constT cnst),
	  const subtreeT *bdd)
{
	return _visit_bdd( (void *)ctxt,
			   (const irexpr_visitor<void> *)visitor,
			   (visit_result(*)(void *, const irexpr_visitor<void> *, constT))visitLeaf,
			   bdd );
}
template <typename subtreeT, typename ctxtT> static visit_result
visit_const_bdd(ctxtT *ctxt,
		const irexpr_visitor<ctxtT> *visitor,
		const subtreeT *bdd)
{
	return _visit_bdd( (void *)ctxt,
			   (const irexpr_visitor<void> *)visitor,
			   (visit_result (*)(void *, const irexpr_visitor<void> *, typename subtreeT::leafT))NULL,
			   bdd );
}

template <typename ctxtT> struct state_machine_visitor {
	struct irexpr_visitor<ctxtT> irexpr;
#define iter_state(name)						\
	visit_result (*name)(ctxtT *ctxt, const StateMachine ## name *);
	all_state_types(iter_state);
#undef iter_state
#define iter_sideeffect(name)						\
	visit_result (*name)(ctxtT *ctxt, const StateMachineSideEffect ## name *);
	all_side_effect_types(iter_sideeffect)
#undef iter_sideeffect
};
visit_result _visit_state_machine(void *ctxt,
				  const state_machine_visitor<void> *visitor,
				  const StateMachineState *sm,
				  std::set<const StateMachineState *> &memo);
template <typename ctxtT> static visit_result
visit_state_machine(ctxtT *ctxt,
		    const state_machine_visitor<ctxtT> *visitor,
		    const StateMachineState *sm,
		    std::set<const StateMachineState *> &memo)
{
	return _visit_state_machine( (void *)ctxt,
				     (const state_machine_visitor<void> *)visitor,
				     sm, memo );
}

visit_result _visit_side_effect(void *ctxt,
				const state_machine_visitor<void> *visitor,
				const StateMachineSideEffect *se);
template <typename ctxtT> static visit_result
visit_side_effect(ctxtT *ctxt,
		  const state_machine_visitor<ctxtT> *visitor,
		  const StateMachineSideEffect *se)
{
	return _visit_side_effect( (void *)ctxt,
				   (const state_machine_visitor<void> *)visitor,
				   se );
}

template <typename ctxtT> static visit_result
visit_state_machine(ctxtT *ctxt,
		    const state_machine_visitor<ctxtT> *visitor,
		    const StateMachineState *sm)
{
	std::set<const StateMachineState *> memo;
	return visit_state_machine(ctxt, visitor, sm, memo);
}
template <typename ctxtT> static visit_result
visit_state_machine(ctxtT *ctxt,
		    const state_machine_visitor<ctxtT> *visitor,
		    const StateMachine *sm,
		    std::set<const StateMachineState *> &memo)
{
	return visit_state_machine(ctxt, visitor, sm->root, memo);
}
template <typename ctxtT> static visit_result
visit_state_machine(ctxtT *ctxt,
		    const state_machine_visitor<ctxtT> *visitor,
		    const StateMachine *sm)
{
	return visit_state_machine(ctxt, visitor, sm->root);
}

template <typename ctxtT> static visit_result
visit_state_machine(ctxtT *ctxt,
		    const irexpr_visitor<ctxtT> *visitor,
		    const StateMachineState *sm,
		    std::set<const StateMachineState *> &memo)
{
	state_machine_visitor<ctxtT> vis = {};
	vis.irexpr = *visitor;
	return visit_state_machine(ctxt, &vis, sm, memo);
}
template <typename ctxtT> static visit_result
visit_state_machine(ctxtT *ctxt,
		    const irexpr_visitor<ctxtT> *visitor,
		    const StateMachineState *sm)
{
	state_machine_visitor<ctxtT> vis = {};
	vis.irexpr = *visitor;
	return visit_state_machine(ctxt, &vis, sm);
}

template <typename ctxtT> static visit_result
visit_state_machine(ctxtT *ctxt,
		    const irexpr_visitor<ctxtT> *visitor,
		    const StateMachine *sm,
		    std::set<const StateMachineState *> &memo)
{
	return visit_state_machine(ctxt, visitor, sm->root, memo);
}
template <typename ctxtT> static visit_result
visit_state_machine(ctxtT *ctxt,
		    const irexpr_visitor<ctxtT> *visitor,
		    const StateMachine *sm)
{
	return visit_state_machine(ctxt, visitor, sm->root);
}

#endif /* !VISITOR_HPP__ */
