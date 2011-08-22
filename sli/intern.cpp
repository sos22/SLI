#include <map>

#include "sli.h"
#include "intern.hpp"
#include "simplify_irexpr.hpp"
#include "state_machine.hpp"
#include "libvex_prof.hpp"

struct internIRExprTable {
	static const int nr_entries = 17;
	std::map<IRExpr *, IRExpr *> lookups[nr_entries];
};

struct internStateMachineTable : public internIRExprTable {
	std::map<StateMachineSideEffect *, StateMachineSideEffect *> sideEffects;
	std::map<StateMachineEdge *, StateMachineEdge *> edges;
	std::map<StateMachineState *, StateMachineState *> states;
	std::set<StateMachineSideEffectStore *> stores;
	std::set<StateMachineSideEffectLoad *> loads;
	std::set<StateMachineSideEffectCopy *> copies;
	std::set<StateMachineProxy *> states_proxy;
	std::set<StateMachineBifurcate *> states_bifurcate;
	std::set<StateMachineStub *> states_stub;
};

static unsigned
shallow_hash(const IRExpr *e)
{
	switch (e->tag) {
	case Iex_Const:
		return 100242167;
	case Iex_Binder:
		return e->Iex.Binder.binder * 100000393 + 100005469;
	case Iex_Get:
		return e->Iex.Get.offset * 100001029 + 100011943;
	case Iex_GetI:
		return 100013213;
	case Iex_RdTmp:
		return e->Iex.RdTmp.tmp * 100017493 + 100025479;
	case Iex_Qop:
		return e->Iex.Qop.op * 100034159 + 100043347;
	case Iex_Triop:
		return e->Iex.Triop.op * 100046753 + 100050683;
	case Iex_Binop:
		return e->Iex.Binop.op * 100057339 + 100067581;
	case Iex_Unop:
		return e->Iex.Unop.op * 100080689 + 100102913;
	case Iex_Load:
		return 100110343;
	case Iex_CCall:
		return 100125853;
	case Iex_Mux0X:
		return 100146091;
	case Iex_Associative:
		return e->Iex.Associative.op * 100161727 + e->Iex.Associative.nr_arguments * 100268423 + 100176877;
	case Iex_FreeVariable:
		return e->Iex.FreeVariable.key.val * 100190957;
	case Iex_ClientCallFailed:
		return 100213697;
	case Iex_ClientCall:
		return 100256371 + e->Iex.ClientCall.callSite.rip * 50013641;
	case Iex_HappensBefore:
		return 100234427;
	}
	abort();
}

static IRExpr *
internIRExpr(IRExpr *e, internIRExprTable &lookupTable)
{
	unsigned h = shallow_hash(e) % internIRExprTable::nr_entries;
	if (lookupTable.lookups[h].count(e))
		return lookupTable.lookups[h][e];
	switch (e->tag) {
	case Iex_Binder:
	case Iex_Get:
	case Iex_RdTmp:
	case Iex_Const:
	case Iex_FreeVariable:
	case Iex_HappensBefore:
		break;
	case Iex_GetI:
		e->Iex.GetI.ix = internIRExpr(e->Iex.GetI.ix, lookupTable);
		break;
	case Iex_Qop:
		e->Iex.Qop.arg4 = internIRExpr(e->Iex.Qop.arg4, lookupTable);
	case Iex_Triop:
		e->Iex.Qop.arg3 = internIRExpr(e->Iex.Qop.arg3, lookupTable);
	case Iex_Binop:
		e->Iex.Qop.arg2 = internIRExpr(e->Iex.Qop.arg2, lookupTable);
	case Iex_Unop:
		e->Iex.Qop.arg1 = internIRExpr(e->Iex.Qop.arg1, lookupTable);
		break;
	case Iex_Load:
		e->Iex.Load.addr = internIRExpr(e->Iex.Load.addr, lookupTable);
		break;
	case Iex_CCall:
		for (int x = 0; e->Iex.CCall.args[x]; x++)
			e->Iex.CCall.args[x] =
				internIRExpr(e->Iex.CCall.args[x], lookupTable);
		break;
	case Iex_Mux0X:
		e->Iex.Mux0X.cond = internIRExpr(e->Iex.Mux0X.cond, lookupTable);
		e->Iex.Mux0X.expr0 = internIRExpr(e->Iex.Mux0X.expr0, lookupTable);
		e->Iex.Mux0X.exprX = internIRExpr(e->Iex.Mux0X.exprX, lookupTable);
		break;
	case Iex_Associative:
		for (int x = 0; x < e->Iex.Associative.nr_arguments; x++)
			e->Iex.Associative.contents[x] =
				internIRExpr(e->Iex.Associative.contents[x], lookupTable);
		break;
	case Iex_ClientCall:
		for (int x = 0; e->Iex.ClientCall.args[x]; x++)
			e->Iex.ClientCall.args[x] =
				internIRExpr(e->Iex.ClientCall.args[x], lookupTable);
		break;
	case Iex_ClientCallFailed:
		e->Iex.ClientCallFailed.target =
			internIRExpr(e->Iex.ClientCallFailed.target, lookupTable);
		break;
	}
	for (std::map<IRExpr *, IRExpr *>::iterator it = lookupTable.lookups[h].begin();
	     it != lookupTable.lookups[h].end();
	     it++) {
		IRExpr *other = it->first;
		if (other->tag != e->tag)
			continue;
		switch (e->tag) {
			/* For some structures, equality can be
			   checked by bitwise comparison. */
#define do_case(n)							\
			case Iex_ ## n:					\
				if (memcmp(&other->Iex. n,		\
					   &e->Iex. n,			\
					   sizeof(e->Iex. n)))		\
					continue;			\
			break
			do_case(Binder);
			do_case(Get);
			do_case(GetI);
			do_case(RdTmp);
			do_case(Qop);
			do_case(Triop);
			do_case(Binop);
			do_case(Unop);
			do_case(Mux0X);
			do_case(FreeVariable);
			do_case(ClientCallFailed);
#undef do_case
		case Iex_Load:
#define do_field(n)							\
			if (other->Iex.Load. n != e->Iex.Load. n)	\
				continue
			do_field(isLL);
			do_field(end);
			do_field(ty);
			do_field(addr);
			do_field(rip);
#undef do_field
			break;

			/* Others are harder. */
		case Iex_CCall: {
			bool bad;
			if (other->Iex.CCall.retty != e->Iex.CCall.retty)
				continue;
			bad = false;
			for (int x = 0; !bad && e->Iex.CCall.args[x]; x++) {
				if (e->Iex.CCall.args[x] !=
				    other->Iex.CCall.args[x])
					bad = true;
			}
			if (bad)
				continue;
			break;
		}

		case Iex_Associative: {
			if (other->Iex.Associative.op != e->Iex.Associative.op ||
			    other->Iex.Associative.nr_arguments != e->Iex.Associative.nr_arguments)
				continue;
			bool bad = false;
			for (int x = 0; !bad && x < e->Iex.Associative.nr_arguments; x++)
				if (e->Iex.Associative.contents[x] !=
				    other->Iex.Associative.contents[x])
					bad = true;
			if (bad)
				continue;
			break;
		}

		case Iex_Const:
			if (!physicallyEqual(e->Iex.Const.con,
					     other->Iex.Const.con))
				continue;
			break;

		case Iex_ClientCall: {
			bool bad;
			if (other->Iex.ClientCall.calledRip != e->Iex.ClientCall.calledRip ||
			    other->Iex.ClientCall.callSite != e->Iex.ClientCall.callSite)
				continue;
			bad = false;
			for (int x = 0; !bad; x++) {
				if (e->Iex.ClientCall.args[x] != other->Iex.ClientCall.args[x])
					bad = true;
				if (e->Iex.ClientCall.args[x] == NULL)
					break;
			}
			if (bad)
				continue;
			break;
		}

		case Iex_HappensBefore:
			if (e->Iex.HappensBefore.before != other->Iex.HappensBefore.before ||
			    e->Iex.HappensBefore.after != other->Iex.HappensBefore.after)
				continue;
			break;
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

static void
internKnownGoodPointers(knownGoodPointersT &p, internIRExprTable &t)
{
	for (auto it = p.begin(); it != p.end(); it++)
		*it = internIRExpr(*it, t);
}

static StateMachineSideEffect *
internStateMachineSideEffect(StateMachineSideEffect *s, internStateMachineTable &t)
{
	if (t.sideEffects.count(s))
		return t.sideEffects[s];
	if (dynamic_cast<StateMachineSideEffect *>(s)) {
		t.sideEffects[s] = s;
		return s;
	} else if (StateMachineSideEffectMemoryAccess *ma = dynamic_cast<StateMachineSideEffectMemoryAccess *>(s)) {
		ma->addr = internIRExpr(ma->addr, t);
		if (StateMachineSideEffectStore *store = dynamic_cast<StateMachineSideEffectStore *>(ma)) {
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
			t.sideEffects[s] = s;
			t.stores.insert(store);
			return s;
		} else if (StateMachineSideEffectLoad *load = dynamic_cast<StateMachineSideEffectLoad *>(ma)) {
			for (auto it = t.loads.begin();
			     it != t.loads.end();
			     it++) {
				StateMachineSideEffectLoad *o = *it;
				if (o->addr == load->addr &&
				    o->key == load->key &&
				    o->rip == load->rip) {
					t.sideEffects[s] = o;
					return o;
				}
			}
			t.sideEffects[s] = s;
			t.loads.insert(load);
			return s;
		} else {
			abort();
		}
	} else if (StateMachineSideEffectCopy *copy = dynamic_cast<StateMachineSideEffectCopy *>(ma)) {
		copy->value = internIRExpr(copy->value, t);
		for (auto it = t.copies.begin(); it != t.copies.end(); it++) {
			StateMachineSideEffectCopy *o = *it;
			if (o->key == copy->key &&
			    o->value == copy->value) {
				t.sideEffects[s] = o;
				return o;
			}
		}
		t.sideEffects[s] = s;
		t.copies.insert(copy);
		return s;
	} else {
		abort();
	}
}

static StateMachineState *internStateMachineState(StateMachineState *start, internStateMachineTable &t);

static StateMachineEdge *
internStateMachineEdge(StateMachineEdge *start, internStateMachineTable &t)
{
	if (t.edges.count(start))
		return t.edges[start];
	start->target = internStateMachineState(start->target, t);
	for (auto it = start->sideEffects.begin();
	     it != start->sideEffects.end();
	     it++)
		*it = internStateMachineSideEffect(*it, t);
	for (auto it = t.edges.begin(); it != t.edges.end(); it++) {
		StateMachineEdge *o = it->second;
		if (o->target == start->target && o->sideEffects == start->sideEffects) {
			t.edges[start] = o;
			return o;
		}
	}
	t.edges[start] = start;
	return start;
}

static StateMachineState *
internStateMachineState(StateMachineState *start, internStateMachineTable &t)
{
	if (t.states.count(start))
		return t.states[start];
	t.states[start] = start; /* Cycle breaking */
	if (dynamic_cast<StateMachineCrash *>(start) ||
	    dynamic_cast<StateMachineNoCrash *>(start) ||
	    dynamic_cast<StateMachineUnreached *>(start)) {
		t.states[start] = start;
		return start;
	} else if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(start)) {
		smp->target = internStateMachineEdge(smp->target, t);
		for (auto it = t.states_proxy.begin();
		     it != t.states_proxy.end();
		     it++) {
			if ((*it)->target == smp->target) {
				t.states[start] = *it;
				return *it;
			}
		}
		t.states[start] = start;
		t.states_proxy.insert(smp);
		return start;
	} else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(start)) {
		smb->condition = internIRExpr(smb->condition, t);
		smb->trueTarget = internStateMachineEdge(smb->trueTarget, t);
		smb->falseTarget = internStateMachineEdge(smb->falseTarget, t);
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
	} else if (StateMachineStub *sms = dynamic_cast<StateMachineStub *>(start)) {
		sms->target = internIRExpr(sms->target);
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
	} else {
		abort();
	}
}

StateMachine *
internStateMachine(StateMachine *sm)
{
	__set_profiling(internStateMachine);
	internStateMachineTable t;
	internFreeVariables(sm->freeVariables, t);
	internKnownGoodPointers(sm->goodPointers, t);
	sm->root = internStateMachineState(sm->root, t);
	return sm;
}
