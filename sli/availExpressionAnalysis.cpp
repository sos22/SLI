/* Available expression analysis on memory locations.  This isn't
   included in the normal optimise() operation because it's
   context-sensitive, and therefore isn't allowed to mutate nodes
   in-place. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "libvex_prof.hpp"
#include "allowable_optimisations.hpp"
#include "visitor.hpp"
#include "either.hpp"
#include "stacked_cdf.hpp"

#ifdef NDEBUG
#define debug_avail false
#else
static bool debug_avail = false;
#endif

namespace _availExpressionAnalysis {
/* Unconfuse emacs */
#if 0
}
#endif

class availExprSet {
	bbdd *definitelyTrue;
	std::set<StateMachineSideEffectMemoryAccess *> memory;
	std::map<threadAndRegister, exprbdd *> fixedRegs;

	class SubstRegsTransform : public IRExprTransformer {
		const std::map<threadAndRegister, exprbdd *> &fixedRegs;
		IRExpr *transformIex(IRExprGet *e) {
			auto it = fixedRegs.find(e->reg);
			if (it != fixedRegs.end()) {
				if (it->second->type() >= e->type()) {
					return coerceTypes(e->type(), exprbdd::to_irexpr(it->second));
				}
			}
			return IRExprTransformer::transformIex(e);
		}
	public:
		SubstRegsTransform(const std::map<threadAndRegister, exprbdd *> &_fixedRegs)
			: fixedRegs(_fixedRegs)
		{}
	};
	static visit_result mr_visit_Get(const threadAndRegister *tr,
					 const IRExprGet *ieg) {
		if (ieg->reg == *tr) {
			return visit_abort;
		} else {
			return visit_continue;
		}
	}
	static struct bdd_visitor<const threadAndRegister> mr_visitor;

	static bool mentionsRegister(IRExpr *, const threadAndRegister &);
	static bool mentionsRegister(exprbdd *, const threadAndRegister &);
	static bbdd *bddPurgeRegister(SMScopes *, bbdd *, const threadAndRegister &, sane_map<bbdd *, bbdd *> &);
	static bbdd *bddPurgeRegister(SMScopes *, bbdd *, const threadAndRegister &);

	smrbdd *simplifySmrbdd(SMScopes *, smrbdd *) const;
	bbdd *simplifyBbdd(SMScopes *, bbdd *) const;
	exprbdd *simplifyExprbdd(SMScopes *, exprbdd *) const;
#define mk_proto(name)							\
	StateMachineSideEffect *simplifySE(SMScopes *, StateMachineSideEffect ## name *) const;
	all_side_effect_types(mk_proto)
#undef mk_proto
	StateMachineSideEffect *simplifySideEffect(SMScopes *, StateMachineSideEffect *) const;

public:
	void clear(SMScopes *scopes) {
		definitelyTrue = scopes->bools.cnst(true);
		memory.clear();
	}

	void simplifyState(SMScopes *scopes, StateMachineState *, bool *) const;

	void updateForSideEffect(SMScopes *, OracleInterface *, const MaiMap &m, const AllowableOptimisations &, StateMachineSideEffect *);
	void assertTrue(SMScopes *, bbdd *);
	void assertFalse(SMScopes *, bbdd *);
	void merge(SMScopes *, const availExprSet &o);

	void print() const;
};
struct bdd_visitor<const threadAndRegister> availExprSet::mr_visitor;

bool
availExprSet::mentionsRegister(IRExpr *what, const threadAndRegister &tr)
{
	mr_visitor.irexpr.Get = mr_visit_Get;
	return visit_irexpr(&tr, &mr_visitor.irexpr, what) == visit_abort;
}

bool
availExprSet::mentionsRegister(exprbdd *what, const threadAndRegister &tr)
{
	mr_visitor.irexpr.Get = mr_visit_Get;
	return visit_bdd(&tr, &mr_visitor, visit_irexpr<const threadAndRegister>, what) == visit_abort;
}

bbdd *
availExprSet::bddPurgeRegister(SMScopes *scopes, bbdd *what, const threadAndRegister &reg,
			       sane_map<bbdd *, bbdd *> &memo)
{
	if (what->isLeaf()) {
		return what;
	}
	auto it_did_insert = memo.insert(what, (bbdd *)0xf001);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	auto t = bddPurgeRegister(scopes, what->internal().trueBranch, reg, memo);
	auto f = bddPurgeRegister(scopes, what->internal().falseBranch, reg, memo);
	if (t == f) {
		it->second = t;
	} else if (mentionsRegister(what->internal().condition, reg)) {
		it->second = scopes->bools.cnst(true);
	} else if (t == what->internal().trueBranch &&
		   f == what->internal().falseBranch) {
		it->second = what;
	} else {
		it->second = scopes->bools.node(
			what->internal().condition,
			what->internal().rank,
			t,
			f);
	}
	return it->second;
}

bbdd *
availExprSet::bddPurgeRegister(SMScopes *scopes, bbdd *what, const threadAndRegister &reg)
{
	sane_map<bbdd *, bbdd *> memo;
	return bddPurgeRegister(scopes, what, reg, memo);
}


smrbdd *
availExprSet::simplifySmrbdd(SMScopes *scopes, smrbdd *smr) const
{
	SubstRegsTransform trans(fixedRegs);
	if (definitelyTrue->isLeaf() && !definitelyTrue->leaf()) {
		return scopes->smrs.cnst(smr_unreached);
	}
	return trans.transform_smrbdd(&scopes->bools, &scopes->smrs, smrbdd::assume(&scopes->smrs, smr, definitelyTrue));
}

bbdd *
availExprSet::simplifyBbdd(SMScopes *scopes, bbdd *b) const
{
	SubstRegsTransform trans(fixedRegs);
	return trans.transform_bbdd(&scopes->bools, bbdd::assume(&scopes->bools, b, definitelyTrue));
}

exprbdd *
availExprSet::simplifyExprbdd(SMScopes *scopes, exprbdd *b) const
{
	SubstRegsTransform trans(fixedRegs);
	return trans.transform_exprbdd(&scopes->bools, &scopes->exprs, exprbdd::assume(&scopes->exprs, b, definitelyTrue));
}

StateMachineSideEffect *
availExprSet::simplifySE(SMScopes *scopes, StateMachineSideEffectLoad *l) const
{
	auto b = simplifyExprbdd(scopes, l->addr);
	if (TIMEOUT) {
		return l;
	}
	for (auto it = memory.begin(); it != memory.end(); it++) {
		StateMachineSideEffectMemoryAccess *other = *it;
		if (other->addr == b) {
			exprbdd *exp;
			if (other->type == StateMachineSideEffect::Store) {
				exp = ((StateMachineSideEffectStore *)other)->data;
			} else {
				auto o = (StateMachineSideEffectLoad *)other;
				exp = exprbdd::var(&scopes->exprs, &scopes->bools, IRExpr_Get(o->target, l->type));
			}
			return new StateMachineSideEffectCopy(
				l->target,
				exp);
		}
	}
	if (b == l->addr) {
		return l;
	} else {
		return new StateMachineSideEffectLoad(l, b);
	}
}

StateMachineSideEffect *
availExprSet::simplifySE(SMScopes *scopes, StateMachineSideEffectStore *s) const
{
	auto a = simplifyExprbdd(scopes, s->addr);
	auto d = simplifyExprbdd(scopes, s->data);
	if (TIMEOUT || (a == s->addr && d == s->data)) {
		return s;
	} else {
		return new StateMachineSideEffectStore(s, a, d);
	}
}

StateMachineSideEffect *
availExprSet::simplifySE(SMScopes *scopes, StateMachineSideEffectCopy *c) const
{
	auto d = simplifyExprbdd(scopes, c->value);
	if (TIMEOUT || d == c->value) {
		return c;
	} else {
		return new StateMachineSideEffectCopy(c, d);
	}
}

StateMachineSideEffect *
availExprSet::simplifySE(SMScopes *, StateMachineSideEffectUnreached *c) const
{
	return c;
}

StateMachineSideEffect *
availExprSet::simplifySE(SMScopes *scopes, StateMachineSideEffectAssertFalse *a) const
{
	auto d = simplifyBbdd(scopes, a->value);
	if (TIMEOUT || d == a->value) {
		return a;
	} else {
		return new StateMachineSideEffectAssertFalse(a, d);
	}
}

StateMachineSideEffect *
availExprSet::simplifySE(SMScopes *, StateMachineSideEffectPhi *p) const
{
	/* We could do a little bit better here, but Phi effects in
	   non-SSA machines are so rare that it's not worth worrying
	   about. */
	return p;
}

StateMachineSideEffect *
availExprSet::simplifySE(SMScopes *, StateMachineSideEffectStartAtomic *c) const
{
	return c;
}

StateMachineSideEffect *
availExprSet::simplifySE(SMScopes *, StateMachineSideEffectEndAtomic *c) const
{
	return c;
}

StateMachineSideEffect *
availExprSet::simplifySE(SMScopes *, StateMachineSideEffectImportRegister *c) const
{
	return c;
}

#if TRACK_FRAMES
StateMachineSideEffect *
availExprSet::simplifySE(SMScopes *scopes, StateMachineSideEffectStartFunction *s) const
{
	auto rsp = simplifyExprbdd(scopes, s->rsp);
	if (TIMEOUT || rsp == s->rsp) {
		return s;
	} else {
		return new StateMachineSideEffectStartFunction(s, rsp);
	}
}

StateMachineSideEffect *
availExprSet::simplifySE(SMScopes *scopes, StateMachineSideEffectEndFunction *s) const
{
	auto rsp = simplifyExprbdd(scopes, s->rsp);
	if (TIMEOUT || rsp == s->rsp) {
		return s;
	} else {
		return new StateMachineSideEffectEndFunction(s, rsp);
	}
}

StateMachineSideEffect *
availExprSet::simplifySE(SMScopes *, StateMachineSideEffectStackLayout *c) const
{
	return c;
}
#endif

StateMachineSideEffect *
availExprSet::simplifySideEffect(SMScopes *scopes, StateMachineSideEffect *se) const
{
	if (definitelyTrue->isLeaf() && !definitelyTrue->leaf()) {
		return StateMachineSideEffectUnreached::get();
	}
	switch (se->type) {
#define do_case(name)							\
		case StateMachineSideEffect::name :			\
			return simplifySE(scopes,			\
					  (StateMachineSideEffect ## name *)se);
		all_side_effect_types(do_case)
#undef do_case
	}
	abort();
}

void
availExprSet::simplifyState(SMScopes *scopes, StateMachineState *s, bool *done_something) const
{
	switch (s->type) {
	case StateMachineState::Terminal: {
		auto smt = (StateMachineTerminal *)s;
		auto res = simplifySmrbdd(scopes, smt->res);
		if (!TIMEOUT) {
			if (debug_avail && res != smt->res) {
				printf("Terminal:\n");
				smt->res->prettyPrint(stdout);
				printf("--------->\n");
				res->prettyPrint(stdout);
			}
			*done_something |= smt->set_res(res);
		}
		return;
	}
	case StateMachineState::Bifurcate: {
		auto smb = (StateMachineBifurcate *)s;
		if (definitelyTrue->isLeaf() && !definitelyTrue->leaf()) {
			smb->trueTarget = smb->falseTarget =
				new StateMachineTerminal(
					smb->dbg_origin,
					scopes->smrs.cnst(smr_unreached));
			*done_something = true;
			return;
		}
		auto c = simplifyBbdd(scopes, smb->condition);
		if (!TIMEOUT) {
			if (debug_avail && c != smb->condition) {
				printf("Condition:\n");
				smb->condition->prettyPrint(stdout);
				printf("------------>\n");
				c->prettyPrint(stdout);
			}
			*done_something |= smb->set_condition(c);
		}
		return;
	}
	case StateMachineState::SideEffecting: {
		auto sme = (StateMachineSideEffecting *)s;
		if (!sme->sideEffect) {
			return;
		}
		auto s = simplifySideEffect(scopes, sme->sideEffect);
		if (!TIMEOUT) {
			if (debug_avail && s != sme->sideEffect) {
				printf("Side effect:\n");
				sme->sideEffect->prettyPrint(stdout);
				printf("\n------------>\n");
				s->prettyPrint(stdout);
			}
			*done_something |= s != sme->sideEffect;
			sme->sideEffect = s;
		}
		return;
	}
	}
	abort();
}

void
availExprSet::updateForSideEffect(SMScopes *scopes, OracleInterface *oracle, const MaiMap &decode, const AllowableOptimisations &opt, StateMachineSideEffect *se)
{
	if (!se) {
		return;
	}

	/* Does this kill off any memory accesses? */
	if (se->type == StateMachineSideEffect::Store) {
		auto sms = (StateMachineSideEffectStore *)se;
		for (auto it = memory.begin(); it != memory.end(); ) {
			if (oracle->memoryAccessesMightAlias(decode, opt, *it, (StateMachineSideEffectMemoryAccess *)sms) &&
			    !definitelyNotEqual(sms->addr, (*it)->addr, opt)) {
				memory.erase(it++);
			} else {
				it++;
			}
		}
	}

	/* Does it kill anything by means of changing a register? */
	threadAndRegister definedReg(threadAndRegister::invalid());
	if (se->definesRegister(definedReg)) {
		definitelyTrue = bddPurgeRegister(scopes, definitelyTrue, definedReg);
		for (auto it = memory.begin(); it != memory.end(); ) {
			auto ma = *it;
			bool kill;
			if (ma->type == StateMachineSideEffect::Load) {
				auto l = (StateMachineSideEffectLoad *)ma;
				kill = l->target == definedReg || mentionsRegister(l->addr, definedReg);
			} else {
				auto s = (StateMachineSideEffectStore *)ma;
				kill = mentionsRegister(s->addr, definedReg) ||
					mentionsRegister(s->data, definedReg);
			}
			if (kill) {
				memory.erase(it++);
			} else {
				it++;
			}
		}
		for (auto it = fixedRegs.begin(); it != fixedRegs.end(); ) {
			if (it->first == definedReg ||
			    mentionsRegister(it->second, definedReg)) {
				fixedRegs.erase(it++);
			} else {
				it++;
			}
		}
	}

	/* Make its effects available */
	if (se->type == StateMachineSideEffect::Store ||
	    se->type == StateMachineSideEffect::Load) {
		auto ma = (StateMachineSideEffectMemoryAccess *)se;
		bool doit;
		if (se->type == StateMachineSideEffect::Store) {
			doit = true;
		} else {
			auto l = (StateMachineSideEffectLoad *)ma;
			doit = !mentionsRegister(l->addr, definedReg);
		}
		if (doit) {
			memory.insert(ma);
			definitelyTrue = bbdd::And(
				&scopes->bools,
				definitelyTrue,
				bbdd::invert(
					&scopes->bools,
					exprbdd::to_bbdd(
						&scopes->bools,
						exprbdd::unop(
							&scopes->exprs,
							&scopes->bools,
							Iop_BadPtr,
							ma->addr))));
		}
	}
	if (se->type == StateMachineSideEffect::Copy) {
		auto cp = (StateMachineSideEffectCopy *)se;
		if (!mentionsRegister(cp->value, cp->target)) {
			fixedRegs[cp->target] = cp->value;
		}
	}
	if (se->type == StateMachineSideEffect::AssertFalse) {
		auto af = (StateMachineSideEffectAssertFalse *)se;
		definitelyTrue = bbdd::And(
			&scopes->bools,
			definitelyTrue,
			bbdd::invert(
				&scopes->bools,
				af->value));
	}
}

void
availExprSet::assertTrue(SMScopes *scopes, bbdd *what)
{
	definitelyTrue = bbdd::And(&scopes->bools,
				   what,
				   definitelyTrue);
}

void
availExprSet::assertFalse(SMScopes *scopes, bbdd *what)
{
	definitelyTrue = bbdd::And(&scopes->bools,
				   bbdd::invert(&scopes->bools, what),
				   definitelyTrue);
}

void
availExprSet::merge(SMScopes *scopes, const availExprSet &o)
{
	definitelyTrue = bbdd::Or(&scopes->bools,
				  definitelyTrue,
				  o.definitelyTrue);
	for (auto it = fixedRegs.begin(); it != fixedRegs.end(); ) {
		auto it2 = o.fixedRegs.find(it->first);
		if (it2 == o.fixedRegs.end() || it2->second != it->second) {
			fixedRegs.erase(it++);
		} else {
			it++;
		}
	}
	memory &= o.memory;
}

void
availExprSet::print() const
{
	printf("Definitely true:\n");
	definitelyTrue->prettyPrint(stdout);
	printf("memory:\n");
	for (auto it = memory.begin(); it != memory.end(); it++) {
		printf("\t");
		(*it)->prettyPrint(stdout);
		printf("\n");
	}
	for (auto it = fixedRegs.begin(); it != fixedRegs.end(); it++) {
		printf("Fixed reg %s ->\n", it->first.name());
		it->second->prettyPrint(stdout);
	}
}

static StateMachine *
availExpressionAnalysis(SMScopes *scopes,
			const MaiMap &decode,
			StateMachine *sm,
			const AllowableOptimisations &opt,
			OracleInterface *oracle,
			bool *done_something)
{
	std::map<const StateMachineState *, int> labels;
	if (debug_avail) {
		printf("Avail analysis:\n");
		printStateMachine(sm, stdout, labels);
	}

	std::vector<StateMachineState *> states;
	enumStates(sm, &states);
	std::map<const StateMachineState *, int> nrPredecessors;
	nrPredecessors[sm->root] = 0;
	for (auto it = states.begin(); it != states.end(); it++) {
		std::vector<StateMachineState *> targ;
		(*it)->targets(targ);
		for (auto it2 = targ.begin(); it2 != targ.end(); it2++) {
			nrPredecessors[*it2]++;
		}
	}

	sane_map<StateMachineState *, availExprSet> availMap;
	availMap[sm->root].clear(scopes);

	std::vector<StateMachineState *> pending;
	pending.push_back(sm->root);
	while (!TIMEOUT && !pending.empty()) {
		StateMachineState *s = pending.back();
		pending.pop_back();

		assert(nrPredecessors.count(s));
		assert(nrPredecessors[s] == 0);

		auto it_avail = availMap.find(s);
		assert(it_avail != availMap.end());
		availExprSet availHere(it_avail->second);
		availMap.erase(it_avail);

		if (debug_avail) {
			printf("Consider l%d, entry avail =\n", labels[s]);
			availHere.print();
		}

		availHere.simplifyState(scopes, s, done_something);

		/* Update successor avail sets */
		switch (s->type) {
		case StateMachineState::Terminal:
			/* No successors */
			break;
		case StateMachineState::Bifurcate: {
			auto smb = (StateMachineBifurcate *)s;
			auto t_it_did_insert = availMap.insert(smb->trueTarget, availHere);
			if (t_it_did_insert.second) {
				t_it_did_insert.first->second.assertTrue(scopes, smb->condition);
			} else {
				availExprSet tAvail(availHere);
				tAvail.assertTrue(scopes, smb->condition);
				t_it_did_insert.first->second.merge(scopes, tAvail);
			}
			auto f_it_did_insert = availMap.insert(smb->falseTarget, availHere);
			if (f_it_did_insert.second) {
				f_it_did_insert.first->second.assertFalse(scopes, smb->condition);
			} else {
				availHere.assertFalse(scopes, smb->condition);
				f_it_did_insert.first->second.merge(scopes, availHere);
			}

			if (--nrPredecessors[smb->trueTarget] == 0) {
				pending.push_back(smb->trueTarget);
			}
			if (--nrPredecessors[smb->falseTarget] == 0) {
				pending.push_back(smb->falseTarget);
			}
			break;
		}
		case StateMachineState::SideEffecting: {
			auto sme = (StateMachineSideEffecting *)s;
			auto it_did_insert = availMap.insert(sme->target, availHere);
			if (it_did_insert.second) {
				it_did_insert.first->second.updateForSideEffect(scopes, oracle, decode, opt, sme->sideEffect);
			} else {
				availHere.updateForSideEffect(scopes, oracle, decode, opt, sme->sideEffect);
				it_did_insert.first->second.merge(scopes, availHere);
			}
			assert(nrPredecessors[sme->target] > 0);
			if (--nrPredecessors[sme->target] == 0) {
				pending.push_back(sme->target);
			}
			break;
		}
		}
	}

	return sm;
}

typedef std::map<threadAndRegister, exprbdd *> regDefT;

struct ssa_avail_state {
	SMScopes *scopes;
	bool canEarlyOut;
	regDefT defs;
	sane_map<bbdd *, bbdd *> boolMemo;
	sane_map<smrbdd *, smrbdd *> smrMemo;
	sane_map<exprbdd *, exprbdd *> exprMemo;
};

typedef std::map<threadAndRegister, exprbdd *> substTableT;

struct ssaEnumRegsState {
	ssa_avail_state *s;
	substTableT *out;
};

static void
ssaEnumRegs(ssa_avail_state &state, const IRExpr *what, substTableT &out)
{
	struct {
		static visit_result Get(ssaEnumRegsState *state, const IRExprGet *ieg) {
			if (state->out->count(ieg->reg))
				return visit_continue;
			auto it = state->s->defs.find(ieg->reg);
			if (it == state->s->defs.end())
				return visit_continue;
			(*state->out)[ieg->reg] = it->second;
			return visit_continue;
		}
	} foo;
	static irexpr_visitor<ssaEnumRegsState> visitor;
	visitor.Get = foo.Get;
	ssaEnumRegsState s;
	s.s = &state;
	s.out = &out;
	visit_irexpr(&s, &visitor, what);
}

static IRExpr *
applyLeafSubstTable(const substTableT &table, IRExpr *e)
{
	struct : public IRExprTransformer {
		const substTableT *table;
		IRExpr *transformIex(IRExprGet *ieg) {
			auto it = table->find(ieg->reg);
			if (it == table->end())
				return ieg;
			assert(it->second->isLeaf());
			if (it->second->leaf()->type() < ieg->type())
				return ieg;
			return coerceTypes(ieg->type(), it->second->leaf());
		}
	} trans;
	trans.table = &table;
	return trans.doit(e);
}

/* Take an atomic bool IRExpr and apply the transformation, converting
   to a bbdd as we do so. */
static bbdd *
ssaApplyAvailExprBool(ssa_avail_state &state, const substTableT &t, IRExpr *e,
		      sane_map<std::pair<IRExpr *, substTableT>, bbdd *> &memo)
{
	if (TIMEOUT || (state.canEarlyOut && LibVEX_want_GC())) {
		return NULL;
	}

	auto it_did_insert = memo.insert(std::pair<IRExpr *, substTableT>(e, t),
					 NULL);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		const bdd_rank *bestVar = NULL;
		IRExpr *bestCond = (IRExpr *)0xf001;
		for (auto it2 = t.begin();
		     it2 != t.end();
		     it2++) {
			if ( it2->second->isLeaf() )
				continue;
			if (!bestVar || it2->second->internal().rank < *bestVar) {
				bestCond = it2->second->internal().condition;
				bestVar = &it2->second->internal().rank;
			}
		}
		if (bestVar == NULL) {
			IRExpr *trans = applyLeafSubstTable(t, e);
			it->second = bbdd::var(&state.scopes->bools, trans);
		} else {
			substTableT trueTable(t);
			for (auto it2 = trueTable.begin(); it2 != trueTable.end(); it2++)
				it2->second = it2->second->trueBranch(*bestVar);
			substTableT falseTable(t);
			for (auto it2 = falseTable.begin(); it2 != falseTable.end(); it2++)
				it2->second = it2->second->falseBranch(*bestVar);
			auto tt = ssaApplyAvailExprBool(state, trueTable, e, memo);
			auto ff = ssaApplyAvailExprBool(state, falseTable, e, memo);
			if (tt && ff) {
				it->second = state.scopes->bools.node(
					bestCond,
					*bestVar,
					tt,
					ff);
			} else {
				it->second = NULL;
			}
		}
	}
	return it->second;
}
static either<bbdd *, IRExpr *>
ssaApplyAvailExprBool(ssa_avail_state &state, IRExpr *what)
{
	assert(what->type() == Ity_I1);
	substTableT substTable;
	ssaEnumRegs(state, what, substTable);
	if (substTable.empty())
		return either<bbdd *, IRExpr *>(what);
	sane_map<std::pair<IRExpr *, substTableT>, bbdd *> memo;
	return either<bbdd *, IRExpr *>(ssaApplyAvailExprBool(state, substTable, what, memo));
}

static exprbdd *
ssaApplyAvailExprExpr(ssa_avail_state &state, const substTableT &t, IRExpr *e,
		      sane_map<std::pair<IRExpr *, substTableT>, exprbdd *> &memo)
{
	auto it_did_insert = memo.insert(std::pair<IRExpr *, substTableT>(e, t),
					 NULL);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		const bdd_rank *bestVar = NULL;
		IRExpr *bestCond = (IRExpr *)0xf001;
		for (auto it2 = t.begin();
		     it2 != t.end();
		     it2++) {
			if ( it2->second->isLeaf() )
				continue;
			if (!bestVar || it2->second->internal().rank < *bestVar) {
				bestCond = it2->second->internal().condition;
				bestVar = &it2->second->internal().rank;
			}
		}
		if (bestVar == NULL) {
			IRExpr *trans = applyLeafSubstTable(t, e);
			it->second = exprbdd::var(&state.scopes->exprs, &state.scopes->bools, trans);
		} else {
			substTableT trueTable(t);
			for (auto it2 = trueTable.begin(); it2 != trueTable.end(); it2++)
				it2->second = it2->second->trueBranch(*bestVar);
			substTableT falseTable(t);
			for (auto it2 = falseTable.begin(); it2 != falseTable.end(); it2++)
				it2->second = it2->second->falseBranch(*bestVar);
			it->second = state.scopes->exprs.node(
				bestCond,
				*bestVar,
				ssaApplyAvailExprExpr(state, trueTable, e, memo),
				ssaApplyAvailExprExpr(state, falseTable, e, memo));
		}
	}
	return it->second;
}
static either<exprbdd *, IRExpr *>
ssaApplyAvailExprExpr(ssa_avail_state &state, IRExpr *what)
{
	substTableT substTable;
	ssaEnumRegs(state, what, substTable);
	if (substTable.empty())
		return either<exprbdd *, IRExpr *>(what);
	sane_map<std::pair<IRExpr *, substTableT>, exprbdd *> memo;
	return either<exprbdd *, IRExpr *>(ssaApplyAvailExprExpr(state, substTable, what, memo));
}

static bbdd *
ssaApplyAvail(ssa_avail_state &state, bbdd *inp)
{
	auto it_did_insert = state.boolMemo.insert(inp, NULL);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (inp->isLeaf()) {
			it->second = inp;
		} else {
			auto newCond(ssaApplyAvailExprBool(state, inp->internal().condition));
			if (newCond.isLeft && !newCond.left()) {
				it->second = inp;
			} else {
				bbdd *t = ssaApplyAvail(state, inp->internal().trueBranch);
				bbdd *f = ssaApplyAvail(state, inp->internal().falseBranch);
				if (!newCond.isLeft &&
				    newCond.right() == inp->internal().condition &&
				    t == inp->internal().trueBranch &&
				    f == inp->internal().falseBranch) {
					it->second = inp;
				} else {
					it->second = bbdd::ifelse(
						&state.scopes->bools,
						newCond.isLeft ? newCond.left() : bbdd::var(&state.scopes->bools, newCond.right()),
						t,
						f);
				}
			}
		}
	}
	return it->second;
}

static smrbdd *
ssaApplyAvail(ssa_avail_state &state, smrbdd *inp)
{
	auto it_did_insert = state.smrMemo.insert(inp, NULL);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (inp->isLeaf()) {
			it->second = inp;
		} else {
			auto newCond(ssaApplyAvailExprBool(state, inp->internal().condition));
			if (newCond.isLeft && !newCond.left()) {
				it->second = inp;
			} else {
				smrbdd *t = ssaApplyAvail(state, inp->internal().trueBranch);
				smrbdd *f = ssaApplyAvail(state, inp->internal().falseBranch);
				if (!newCond.isLeft &&
				    newCond.right() == inp->internal().condition &&
				    t == inp->internal().trueBranch &&
				    f == inp->internal().falseBranch) {
					it->second = inp;
				} else {
					it->second = smrbdd::ifelse(
						&state.scopes->smrs,
						newCond.isLeft ? newCond.left() : bbdd::var(&state.scopes->bools, newCond.right()),
						t,
						f);
				}
			}
		}
	}
	return it->second;
}

static exprbdd *
ssaApplyAvail(ssa_avail_state &state, exprbdd *inp)
{
	auto it_did_insert = state.exprMemo.insert(inp, NULL);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (inp->isLeaf()) {
			auto newLeaf(ssaApplyAvailExprExpr(state, inp->leaf()));
			if (!newLeaf.isLeft && newLeaf.right() == inp->leaf())
				it->second = inp;
			else if (newLeaf.isLeft)
				it->second = newLeaf.left();
			else
				it->second = exprbdd::var(
					&state.scopes->exprs,
					&state.scopes->bools,
					newLeaf.right());
		} else {
			auto newCond(ssaApplyAvailExprBool(state, inp->internal().condition));
			if (newCond.isLeft && !newCond.left()) {
				it->second = inp;
			} else {
				exprbdd *t = ssaApplyAvail(state, inp->internal().trueBranch);
				exprbdd *f = ssaApplyAvail(state, inp->internal().falseBranch);
				if (!newCond.isLeft &&
				    newCond.right() == inp->internal().condition &&
				    t == inp->internal().trueBranch &&
				    f == inp->internal().falseBranch) {
					it->second = inp;
				} else {
					it->second = exprbdd::ifelse(
						&state.scopes->exprs,
						newCond.isLeft ? newCond.left() : bbdd::var(&state.scopes->bools, newCond.right()),
						t,
						f);
				}
			}
		}
	}
	return it->second;
}

template <typename t> static void
rewrite_var(ssa_avail_state &state, t *&arg, bool *done_something)
{
	t *n = ssaApplyAvail(state, arg);
	if (TIMEOUT)
		return;
	if (n != arg)
		*done_something = n;
	arg = n;
}

static StateMachineSideEffect *
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectLoad *inp)
{
	exprbdd *addr = ssaApplyAvail(state, inp->addr);
	if (addr == inp->addr)
		return inp;
	return new StateMachineSideEffectLoad(inp, addr);
}
static StateMachineSideEffect *
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectStore *inp)
{
	exprbdd *addr = ssaApplyAvail(state, inp->addr);
	exprbdd *data = ssaApplyAvail(state, inp->data);
	if (addr == inp->addr && data == inp->data)
		return inp;
	return new StateMachineSideEffectStore(inp, addr, data);
}
static StateMachineSideEffect *
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectCopy *inp)
{
	exprbdd *data = ssaApplyAvail(state, inp->value);
	if (data == inp->value)
		return inp;
	return new StateMachineSideEffectCopy(inp, data);
}
static StateMachineSideEffect *
ssaApplyAvailSE(ssa_avail_state &, StateMachineSideEffectUnreached *inp)
{
	return inp;
}
static StateMachineSideEffect *
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectAssertFalse *inp)
{
	bbdd *value = ssaApplyAvail(state, inp->value);
	if (value == inp->value)
		return inp;
	return new StateMachineSideEffectAssertFalse(inp, value);
}
static StateMachineSideEffect *
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectPhi *inp)
{
	unsigned x;
	exprbdd *e;
	x = 0;
	while (x < inp->generations.size()) {
		e = ssaApplyAvail(state, inp->generations[x].val);
		if (e != inp->generations[x].val)
			break;
		x++;
	}
	if (x == inp->generations.size())
		return inp;
	std::vector<StateMachineSideEffectPhi::input> inputs(inp->generations);
	inputs[x].val = e;
	for (x++; x < inp->generations.size(); x++)
		inputs[x].val = ssaApplyAvail(state, inputs[x].val);
	return new StateMachineSideEffectPhi(inp, inputs);
}
static StateMachineSideEffect *
ssaApplyAvailSE(ssa_avail_state &, StateMachineSideEffectStartAtomic *inp)
{
	return inp;
}
static StateMachineSideEffect *
ssaApplyAvailSE(ssa_avail_state &, StateMachineSideEffectEndAtomic *inp)
{
	return inp;
}
#if TRACK_FRAMES
static StateMachineSideEffect *
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectStartFunction *inp)
{
	exprbdd *rsp = ssaApplyAvail(state, inp->rsp);
	if (rsp == inp->rsp)
		return inp;
	return new StateMachineSideEffectStartFunction(inp, rsp);
}
static StateMachineSideEffect *
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectEndFunction *inp)
{
	exprbdd *rsp = ssaApplyAvail(state, inp->rsp);
	if (rsp == inp->rsp)
		return inp;
	return new StateMachineSideEffectEndFunction(inp, rsp);
}
static StateMachineSideEffect *
ssaApplyAvailSE(ssa_avail_state &, StateMachineSideEffectStackLayout *inp)
{
	return inp;
}
#endif
static StateMachineSideEffect *
ssaApplyAvailSE(ssa_avail_state &, StateMachineSideEffectImportRegister *inp)
{
	return inp;
}

static StateMachineSideEffect *
rewrite_side_effect(ssa_avail_state &state, StateMachineSideEffect *inp)
{
	if (!inp)
		return NULL;
	switch (inp->type) {
#define do_type(name)							\
		case StateMachineSideEffect:: name :			\
			return ssaApplyAvailSE(				\
				state,					\
				(StateMachineSideEffect ## name *)inp);
		all_side_effect_types(do_type)
#undef do_type
	}
	abort();
}

/* Avoid applying any definitions which will themselves need to be
 * rewritten later. */
static void
definitionClosure(ssa_avail_state &state)
{
	struct {
		static visit_result Get(ssa_avail_state *s, const IRExprGet *ieg) {
			if (s->defs.count(ieg->reg))
				return visit_abort;
			else
				return visit_continue;
		}
	} foo;
	static bdd_visitor<ssa_avail_state> visitor;
	visitor.irexpr.Get = foo.Get;
	for (auto it = state.defs.begin();
	     it != state.defs.end();
		) {
		if (visit_bdd(&state,
			      &visitor,
			      visit_irexpr<ssa_avail_state>,
			      it->second) == visit_continue)
			it++;
		else
			state.defs.erase(it++);
	}
}

static StateMachine *
ssaAvailAnalysis(SMScopes *scopes, StateMachine *sm, bool canEarlyOut, bool *done_something)
{
	ssa_avail_state state;
	state.scopes = scopes;
	state.canEarlyOut = canEarlyOut;
	std::set<StateMachineSideEffectCopy *> sideEffects;
	enumSideEffects(sm, sideEffects);
	for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
		StateMachineSideEffectCopy *se = *it;
		assert(!state.defs.count(se->target));
		state.defs[se->target] = se->value;
	}
	definitionClosure(state);

	if (state.defs.empty())
		return sm;

	std::vector<StateMachineState *> states;
	enumStates(sm, &states);
	for (auto it = states.begin(); it != states.end(); it++) {
		state.canEarlyOut |= *done_something;
		if (state.canEarlyOut && LibVEX_want_GC()) {
			/* Get out and give the GC a chance to run. */
			break;
		}

		StateMachineState *s = *it;
		switch (s->type) {
		case StateMachineState::Terminal: {
			auto smt = (StateMachineTerminal *)s;
			smrbdd *res = smt->res;
			rewrite_var(state, res, done_something);
			smt->set_res(res);
			break;
		}
		case StateMachineState::Bifurcate: {
			auto smb = (StateMachineBifurcate *)s;
			bbdd *cond = smb->condition;
			rewrite_var(state, cond, done_something);
			smb->set_condition(cond);
			break;
		}
		case StateMachineState::SideEffecting: {
			auto sme = (StateMachineSideEffecting *)s;
			StateMachineSideEffect *n = rewrite_side_effect(state, sme->sideEffect);
			if (n != sme->sideEffect)
				*done_something = true;
			sme->sideEffect = n;
			break;
		}
		}
	}
	return sm;
}

/* End of namespace */
}

StateMachine *
availExpressionAnalysis(SMScopes *scopes,
			const MaiMap &decode,
			StateMachine *sm,
			const AllowableOptimisations &opt,
			bool is_ssa,
			OracleInterface *oracle,
			bool canEarlyOut,
			bool *done_something)
{
	StateMachine *res;
	if (is_ssa) {
		stackedCdf::startAvailExpressionSSA();
		res =_availExpressionAnalysis::ssaAvailAnalysis(scopes, sm, canEarlyOut, done_something);
		stackedCdf::stopAvailExpressionSSA();
	} else {
		stackedCdf::startAvailExpressionBase();
		res = _availExpressionAnalysis::availExpressionAnalysis(scopes, decode, sm, opt, oracle, done_something);
		stackedCdf::stopAvailExpressionBase();
	}
	return res;
}
