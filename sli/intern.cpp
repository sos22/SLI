#include <map>

#include "sli.h"
#include "intern.hpp"
#include "simplify_irexpr.hpp"
#include "state_machine.hpp"
#include "libvex_prof.hpp"

static StateMachineSideEffect *
internStateMachineSideEffect(StateMachineSideEffect *s, internStateMachineTable &t)
{
	if (t.sideEffects.count(s))
		return t.sideEffects[s];
	switch (s->type) {
	case StateMachineSideEffect::Unreached:
	case StateMachineSideEffect::StartAtomic:
	case StateMachineSideEffect::EndAtomic:
		t.sideEffects[s] = s;
		return s;
	case StateMachineSideEffect::Load:
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectMemoryAccess *ma = dynamic_cast<StateMachineSideEffectMemoryAccess *>(s);
		assert(ma);
		if (s->type == StateMachineSideEffect::Store) {
			StateMachineSideEffectStore *store = dynamic_cast<StateMachineSideEffectStore *>(ma);
			assert(store);
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
				    o->target == load->target &&
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
		for (auto it = t.copies.begin(); it != t.copies.end(); it++) {
			StateMachineSideEffectCopy *o = *it;
			if (o->target == copy->target &&
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
		for (auto it = t.phis.begin(); it != t.phis.end(); it++) {
			StateMachineSideEffectPhi *o = *it;
			if (o->ty == phi->ty && o->reg == phi->reg && o->generations == phi->generations) {
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
#define do_search(name) do {						\
			for (auto it = t. name .begin();		\
			     it != t. name .end();			\
			     it++) {					\
				if (*sf == **it) {			\
					t.sideEffects[s] = *it;		\
					return *it;			\
				}					\
			}						\
			t.sideEffects[s] = s;				\
			t.name.insert(sf);				\
			return s;					\
		} while (0)
#if TRACK_FRAMES
	case StateMachineSideEffect::StartFunction: {
		StateMachineSideEffectStartFunction *sf = (StateMachineSideEffectStartFunction *)s;
		do_search(StartFunction);
	}
	case StateMachineSideEffect::EndFunction: {
		StateMachineSideEffectEndFunction *sf = (StateMachineSideEffectEndFunction *)s;
		do_search(EndFunction);
	}
	case StateMachineSideEffect::StackLayout: {
		auto sf = (StateMachineSideEffectStackLayout *)s;
		do_search(StackLayout);
	}
#endif
	case StateMachineSideEffect::ImportRegister: {
		auto sf = (StateMachineSideEffectImportRegister *)s;
		do_search(ImportRegister);
	}
#undef do_search

	}
	abort();
}

static StateMachineState *
internStateMachineState(StateMachineState *start, internStateMachineTable &t)
{
	if (t.states.count(start))
		return t.states[start];
	t.states[start] = start; /* Cycle breaking */
	switch (start->type) {
	case StateMachineState::Terminal: {
		auto smt = (StateMachineTerminal *)start;
		for (auto it = t.states_terminal.begin();
		     it != t.states_terminal.end();
		     it++) {
			if ( (*it)->res == smt->res) {
				t.states[start] = *it;
				return *it;
			}
		}
		t.states[start] = start;
		t.states_terminal.insert(smt);
		return start;
	}
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
	}
	abort();
}

static const CFGNode *
internCFG(const CFGNode *inp, internStateMachineTable &t)
{
	auto it_did_insert = t.cfgNodes.insert(std::pair<const CFGNode *, const CFGNode *>(inp, inp));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;
	/* We modify a const structure here.  That's fine, because the
	   new structure is semantically the same as the old one. */
	for (auto it = inp->successors.begin(); it != inp->successors.end(); it++)
		if (it->instr)
			(const_cast<CFGNode::successor_t *>(&*it))->instr = const_cast<CFGNode *>(internCFG(it->instr, t));
	for (auto it2 = t.cfgNodesS.begin(); it2 != t.cfgNodesS.end(); it2++) {
		const CFGNode *other = *it2;
		if (*other == *inp) {
			it->second = other;
			return other;
		}
	}
	t.cfgNodesS.insert(inp);
	return inp;
}

StateMachine *
internStateMachine(StateMachine *sm, internStateMachineTable &t)
{
	__set_profiling(internStateMachine);
	sm->root = internStateMachineState(sm->root, t);
	return sm;
}

StateMachine *
internStateMachine(StateMachine *sm)
{
	internStateMachineTable t;
	return internStateMachine(sm, t);
}

void
internStateMachineCfg(StateMachine *sm)
{
	internStateMachineTable t;
	for (auto it = sm->cfg_roots.begin(); it != sm->cfg_roots.end(); it++) {
		it->first.node = internCFG(it->first.node, t);
	}
}

void
internStateMachineTable::_runGc(HeapVisitor &hv)
{
#define do_map(typename, fieldname)					\
	do {								\
		std::map<typename, typename> newLookup;			\
		for (auto it = fieldname.begin();			\
		     it != fieldname.end();				\
		     it++) {						\
			if (it->first != it->second)			\
				continue;				\
			typename aa = hv.visited(it->first);		\
			if (!aa)					\
				continue;				\
			newLookup[aa] = aa;				\
		}							\
		fieldname = newLookup;					\
	} while (0)
	do_map(StateMachineSideEffect *, sideEffects);
	do_map(StateMachineState *, states);
	do_map(const CFGNode *, cfgNodes);
#undef do_map
#define do_set(typename, fieldname)			\
	do {						\
		std::set<typename> newSet;		\
		for (auto it = fieldname.begin();	\
		     it != fieldname.end();		\
		     it++) {				\
			typename aa = hv.visited(*it);	\
			if (aa)				\
				newSet.insert(aa);	\
		}					\
		fieldname = newSet;			\
	} while (0)
	do_set(StateMachineSideEffectStore *, stores);
	do_set(StateMachineSideEffectLoad *, loads);
	do_set(StateMachineSideEffectCopy *, copies);
	do_set(StateMachineSideEffectPhi *, phis);
	do_set(StateMachineSideEffectAssertFalse *, asserts);
#define ds(n)					\
	do_set(StateMachineSideEffect ## n *, n)
#if TRACK_FRAMES
	ds(StartFunction);
	ds(EndFunction);
	ds(StackLayout);
#endif
	ds(ImportRegister);
#undef ds
	do_set(StateMachineBifurcate *, states_bifurcate);
	do_set(StateMachineSideEffecting *, states_side_effect);
	do_set(const CFGNode *, cfgNodesS);
#undef do_set
}
