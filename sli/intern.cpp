#include <map>

#include "sli.h"
#include "intern.hpp"
#include "simplify_irexpr.hpp"
#include "state_machine.hpp"
#include "libvex_prof.hpp"

struct internStateMachineTable : public internIRExprTable {
	std::map<StateMachineSideEffect *, StateMachineSideEffect *> sideEffects;
	std::map<StateMachineState *, StateMachineState *> states;
	std::set<StateMachineSideEffectStore *> stores;
	std::set<StateMachineSideEffectLoad *> loads;
	std::set<StateMachineSideEffectCopy *> copies;
	std::set<StateMachineSideEffectPhi *> phis;
	std::set<StateMachineSideEffectAssertFalse *> asserts;
	std::set<StateMachineBifurcate *> states_bifurcate;
	std::set<StateMachineStub *> states_stub;
	std::set<StateMachineSideEffecting *> states_side_effect;
	std::set<StateMachineNdChoice *> states_ndchoice;
};

static unsigned
shallow_hash(const IRExpr *e)
{
	switch (e->tag) {
	case Iex_Const:
		return 100242167;
	case Iex_Get:
		return ((IRExprGet *)e)->reg.hash() + 100011943;
	case Iex_GetI:
		return 100013213;
	case Iex_Qop:
		return ((IRExprQop *)e)->op * 100034159 + 100043347;
	case Iex_Triop:
		return ((IRExprTriop *)e)->op * 100046753 + 100050683;
	case Iex_Binop:
		return ((IRExprBinop *)e)->op * 100057339 + 100067581;
	case Iex_Unop:
		return ((IRExprUnop *)e)->op * 100080689 + 100102913;
	case Iex_Load:
		return 100110343;
	case Iex_CCall:
		return 100125853;
	case Iex_Mux0X:
		return 100146091;
	case Iex_Associative:
		return ((IRExprAssociative *)e)->op * 100161727 + ((IRExprAssociative *)e)->nr_arguments * 100268423 + 100176877;
	case Iex_FreeVariable:
		return ((IRExprFreeVariable *)e)->key.val * 100190957;
	case Iex_ClientCallFailed:
		return 100213697;
	case Iex_ClientCall:
		return 100256371 + ((IRExprClientCall *)e)->callSite.rip.hash() * 50013641;
	case Iex_HappensBefore:
		return 100234427;
	case Iex_Phi:
		return 100029499 + ((IRExprPhi *)e)->reg.hash() * 1000014181;
	}
	abort();
}

IRExpr *
internIRExpr(IRExpr *e, internIRExprTable &lookupTable)
{
	if (TIMEOUT)
		return e;
	unsigned h = shallow_hash(e) % internIRExprTable::nr_entries;
	if (lookupTable.lookups[h].count(e))
		return lookupTable.lookups[h][e];
	switch (e->tag) {
	case Iex_Get:
	case Iex_Const:
	case Iex_FreeVariable:
	case Iex_HappensBefore:
	case Iex_Phi:
		break;
	case Iex_GetI:
		((IRExprGetI *)e)->ix = internIRExpr(((IRExprGetI *)e)->ix, lookupTable);
		break;
	case Iex_Qop:
		((IRExprQop *)e)->arg4 = internIRExpr(((IRExprQop *)e)->arg4, lookupTable);
	case Iex_Triop:
		((IRExprQop *)e)->arg3 = internIRExpr(((IRExprQop *)e)->arg3, lookupTable);
	case Iex_Binop:
		((IRExprQop *)e)->arg2 = internIRExpr(((IRExprQop *)e)->arg2, lookupTable);
	case Iex_Unop:
		((IRExprQop *)e)->arg1 = internIRExpr(((IRExprQop *)e)->arg1, lookupTable);
		break;
	case Iex_Load:
		((IRExprLoad *)e)->addr = internIRExpr(((IRExprLoad *)e)->addr, lookupTable);
		break;
	case Iex_CCall:
		for (int x = 0; ((IRExprCCall *)e)->args[x]; x++)
			((IRExprCCall *)e)->args[x] =
				internIRExpr(((IRExprCCall *)e)->args[x], lookupTable);
		break;
	case Iex_Mux0X:
		((IRExprMux0X *)e)->cond = internIRExpr(((IRExprMux0X *)e)->cond, lookupTable);
		((IRExprMux0X *)e)->expr0 = internIRExpr(((IRExprMux0X *)e)->expr0, lookupTable);
		((IRExprMux0X *)e)->exprX = internIRExpr(((IRExprMux0X *)e)->exprX, lookupTable);
		break;
	case Iex_Associative:
		for (int x = 0; x < ((IRExprAssociative *)e)->nr_arguments; x++)
			((IRExprAssociative *)e)->contents[x] =
				internIRExpr(((IRExprAssociative *)e)->contents[x], lookupTable);
		break;
	case Iex_ClientCall:
		for (int x = 0; ((IRExprClientCall *)e)->args[x]; x++)
			((IRExprClientCall *)e)->args[x] =
				internIRExpr(((IRExprClientCall *)e)->args[x], lookupTable);
		break;
	case Iex_ClientCallFailed:
		((IRExprClientCallFailed *)e)->target =
			internIRExpr(((IRExprClientCallFailed *)e)->target, lookupTable);
		break;
	}
	for (std::map<IRExpr *, IRExpr *>::iterator it = lookupTable.lookups[h].begin();
	     it != lookupTable.lookups[h].end();
	     it++) {
		IRExpr *other = it->first;
		if (other->tag != e->tag)
			continue;
		switch (e->tag) {
#define do_field(t, n)							\
			if (((IRExpr ## t *)other)-> n !=		\
			    ((IRExpr ## t *)e)->n)			\
				continue
		case Iex_Get:
			if (!threadAndRegister::fullEq(((IRExprGet *)other)->reg,
						       ((IRExprGet *)e)->reg))
				continue;
			do_field(Get, ty);
			break;
		case Iex_GetI:
			do_field(GetI, descr);
			do_field(GetI, ix);
			do_field(GetI, bias);
			do_field(GetI, tid);
			break;
		case Iex_Qop:
			do_field(Qop, op);
			do_field(Qop, arg1);
			do_field(Qop, arg2);
			do_field(Qop, arg3);
			do_field(Qop, arg4);
			break;
		case Iex_Triop:
			do_field(Triop, op);
			do_field(Triop, arg1);
			do_field(Triop, arg2);
			do_field(Triop, arg3);
			break;
		case Iex_Binop:
			do_field(Binop, op);
			do_field(Binop, arg1);
			do_field(Binop, arg2);
			break;
		case Iex_Unop:
			do_field(Unop, op);
			do_field(Unop, arg);
			break;
		case Iex_Mux0X:
			do_field(Mux0X, cond);
			do_field(Mux0X, expr0);
			do_field(Mux0X, exprX);
			break;
		case Iex_FreeVariable:
			do_field(FreeVariable, key);
			break;
		case Iex_ClientCallFailed:
			do_field(ClientCallFailed, target);
			break;
		case Iex_Load:
			do_field(Load, ty);
			do_field(Load, addr);
			do_field(Load, rip);
			break;
#undef do_field

		case Iex_CCall: {
			bool bad;
			if (((IRExprCCall *)other)->retty != ((IRExprCCall *)e)->retty)
				continue;
			bad = false;
			for (int x = 0; !bad && ((IRExprCCall *)e)->args[x]; x++) {
				if (((IRExprCCall *)e)->args[x] !=
				    ((IRExprCCall *)other)->args[x])
					bad = true;
			}
			if (bad)
				continue;
			break;
		}

		case Iex_Associative: {
			if (((IRExprAssociative *)other)->op != ((IRExprAssociative *)e)->op ||
			    ((IRExprAssociative *)other)->nr_arguments != ((IRExprAssociative *)e)->nr_arguments)
				continue;
			bool bad = false;
			for (int x = 0; !bad && x < ((IRExprAssociative *)e)->nr_arguments; x++)
				if (((IRExprAssociative *)e)->contents[x] !=
				    ((IRExprAssociative *)other)->contents[x])
					bad = true;
			if (bad)
				continue;
			break;
		}

		case Iex_Const:
			if (!physicallyEqual(((IRExprConst *)e)->con,
					     ((IRExprConst *)other)->con))
				continue;
			break;

		case Iex_ClientCall: {
			bool bad;
			if (((IRExprClientCall *)other)->calledRip != ((IRExprClientCall *)e)->calledRip ||
			    ((IRExprClientCall *)other)->callSite != ((IRExprClientCall *)e)->callSite)
				continue;
			bad = false;
			for (int x = 0; !bad; x++) {
				if (((IRExprClientCall *)e)->args[x] != ((IRExprClientCall *)other)->args[x])
					bad = true;
				if (((IRExprClientCall *)e)->args[x] == NULL)
					break;
			}
			if (bad)
				continue;
			break;
		}

		case Iex_HappensBefore:
			if (((IRExprHappensBefore *)e)->before != ((IRExprHappensBefore *)other)->before ||
			    ((IRExprHappensBefore *)e)->after != ((IRExprHappensBefore *)other)->after)
				continue;
			break;

		case Iex_Phi: {
			IRExprPhi *ep = (IRExprPhi *)e;
			IRExprPhi *op = (IRExprPhi *)other;
			if (!threadAndRegister::fullEq(ep->reg, op->reg) ||
			    ep->generations != op->generations || ep->ty != op->ty)
				continue;
			break;
		}
		}

		/* If we get here, they match and we're done. */

		/* If the expressions are equal, then any optimisation
		   which has been applied to one can be assumed to
		   have been applied to the other. */
		e->optimisationsApplied |= it->second->optimisationsApplied;
		it->second->optimisationsApplied |= e->optimisationsApplied;

		lookupTable.lookups[h][e] = it->second;
		return it->second;
	}
	/* No duplicates of this IRExpr found so far */
	lookupTable.lookups[h][e] = e;
	return e;
}

IRExpr *
internIRExpr(IRExpr *x)
{
	__set_profiling(internIRExpr);
	internIRExprTable t;
	return internIRExpr(x, t);
}

static void
internFreeVariables(FreeVariableMap &fvm, internIRExprTable &t)
{
	for (auto it = fvm.content->begin();
	     it != fvm.content->end();
	     it++)
		it.set_value(internIRExpr(it.value(), t));
}

static StateMachineSideEffect *
internStateMachineSideEffect(StateMachineSideEffect *s, internStateMachineTable &t)
{
	if (t.sideEffects.count(s))
		return t.sideEffects[s];
	switch (s->type) {
	case StateMachineSideEffect::Unreached:
		t.sideEffects[s] = s;
		return s;
	case StateMachineSideEffect::Load:
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectMemoryAccess *ma = dynamic_cast<StateMachineSideEffectMemoryAccess *>(s);
		assert(ma);
		ma->addr = internIRExpr(ma->addr, t);
		if (s->type == StateMachineSideEffect::Store) {
			StateMachineSideEffectStore *store = dynamic_cast<StateMachineSideEffectStore *>(ma);
			assert(store);
			store->data = internIRExpr(store->data, t);
			for (auto it = t.stores.begin();
			     it != t.stores.end();
			     it++) {
				StateMachineSideEffectStore *o = *it;
				if (o->addr == store->addr &&
				    o->data == store->data &&
				    o->rip == store->rip) {
					t.sideEffects[s] = o;
					return o;
				}
			}
			t.stores.insert(store);
		} else {
			assert(s->type == StateMachineSideEffect::Load);
			StateMachineSideEffectLoad *load = dynamic_cast<StateMachineSideEffectLoad *>(ma);
			for (auto it = t.loads.begin();
			     it != t.loads.end();
			     it++) {
				StateMachineSideEffectLoad *o = *it;
				if (o->addr == load->addr &&
				    threadAndRegister::fullEq(o->target, load->target) &&
				    o->rip == load->rip) {
					t.sideEffects[s] = o;
					return o;
				}
			}
			t.loads.insert(load);
		}
		t.sideEffects[s] = s;
		return s;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *copy = dynamic_cast<StateMachineSideEffectCopy *>(s);
		assert(copy);
		copy->value = internIRExpr(copy->value, t);
		for (auto it = t.copies.begin(); it != t.copies.end(); it++) {
			StateMachineSideEffectCopy *o = *it;
			if (threadAndRegister::fullEq(o->target, copy->target) &&
			    o->value == copy->value) {
				t.sideEffects[s] = o;
				return o;
			}
		}
		t.sideEffects[s] = s;
		t.copies.insert(copy);
		return s;
	}
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *phi = dynamic_cast<StateMachineSideEffectPhi *>(s);
		assert(phi);
		for (auto it = phi->generations.begin(); it != phi->generations.end(); it++)
			if (it->second)
				it->second = internIRExpr(it->second, t);
		for (auto it = t.phis.begin(); it != t.phis.end(); it++) {
			StateMachineSideEffectPhi *o = *it;
			if (threadAndRegister::fullEq(o->reg, phi->reg)) {
				t.sideEffects[s] = o;
				return o;
			}
		}
		t.sideEffects[s] = s;
		t.phis.insert(phi);
		return s;
	}
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *af = dynamic_cast<StateMachineSideEffectAssertFalse *>(s);
		assert(af);
		af->value = internIRExpr(af->value, t);
		for (auto it = t.asserts.begin(); it != t.asserts.end(); it++) {
			StateMachineSideEffectAssertFalse *o = *it;
			if (o->value == af->value) {
				t.sideEffects[s] = o;
				return o;
			}
		}
		t.sideEffects[s] = s;
		t.asserts.insert(af);
		return s;
	}
	}
	abort();
}

static StateMachineState *internStateMachineState(StateMachineState *start, internStateMachineTable &t);

static StateMachineState *
internStateMachineState(StateMachineState *start, internStateMachineTable &t)
{
	if (t.states.count(start))
		return t.states[start];
	t.states[start] = start; /* Cycle breaking */
	switch (start->type) {
	case StateMachineState::Crash:
	case StateMachineState::NoCrash:
	case StateMachineState::Unreached:
		t.states[start] = start;
		return start;
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *smse = (StateMachineSideEffecting *)start;
		if (smse->sideEffect)
			smse->sideEffect = internStateMachineSideEffect(smse->sideEffect, t);
		smse->target = internStateMachineState(smse->target, t);
		for (auto it = t.states_side_effect.begin();
		     it != t.states_side_effect.end();
		     it++) {
			if ( (*it)->sideEffect == smse->sideEffect &&
			     (*it)->target == smse->target ) {
				t.states[start] = *it;
				return *it;
			}
		}
		t.states[start] = start;
		t.states_side_effect.insert(smse);
		return start;
	}
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)start;
		smb->condition = internIRExpr(smb->condition, t);
		smb->trueTarget = internStateMachineState(smb->trueTarget, t);
		smb->falseTarget = internStateMachineState(smb->falseTarget, t);
		for (auto it = t.states_bifurcate.begin();
		     it != t.states_bifurcate.end();
		     it++) {
			StateMachineBifurcate *o = *it;
			if (o->condition == smb->condition &&
			    o->trueTarget == smb->trueTarget &&
			    o->falseTarget == smb->falseTarget) {
				t.states[start] = o;
				return o;
			}
		}
		t.states[start] = start;
		t.states_bifurcate.insert(smb);
		return start;
	}
	case StateMachineState::Stub: {
		StateMachineStub *sms = (StateMachineStub *)start;
		for (auto it = t.states_stub.begin();
		     it != t.states_stub.end();
		     it++) {
			if (sms->target == (*it)->target) {
				t.states[start] = *it;
				return *it;
			}
		}
		t.states[start] = start;
		t.states_stub.insert(sms);
		return start;
	}
	case StateMachineState::NdChoice: {
		StateMachineNdChoice *smnd = (StateMachineNdChoice *)start;
		for (auto it = smnd->successors.begin(); it != smnd->successors.end(); it++)
			*it = internStateMachineState(*it, t);
		for (auto it = t.states_ndchoice.begin();
		     it != t.states_ndchoice.end();
		     it++) {
			StateMachineNdChoice *o = *it;
			if (smnd->successors == o->successors) {
				t.states[start] = o;
				return o;
			}
		}
		t.states[start] = start;
		t.states_ndchoice.insert(smnd);
		return start;
	}
	}
	abort();
}

StateMachine *
internStateMachine(StateMachine *sm)
{
	__set_profiling(internStateMachine);
	internStateMachineTable t;
	internFreeVariables(sm->freeVariables, t);
	sm->root = internStateMachineState(sm->root, t);
	return sm;
}
