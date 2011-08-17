#include <err.h>

#include <map>

#include "sli.h"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"

#include "libvex_parse.h"


static void findUsedBinders(IRExpr *e, std::set<Int> &, const AllowableOptimisations &);

VexPtr<StateMachineSideEffectUnreached, &ir_heap> StateMachineSideEffectUnreached::_this;
Int StateMachineSideEffectLoad::next_key;
VexPtr<StateMachineUnreached, &ir_heap> StateMachineUnreached::_this;
VexPtr<StateMachineCrash, &ir_heap> StateMachineCrash::_this;
VexPtr<StateMachineNoCrash, &ir_heap> StateMachineNoCrash::_this;
AllowableOptimisations AllowableOptimisations::defaultOptimisations(true, false, false, false, false, true);

static bool mentionsBinders(IRExpr *e);

StateMachine *
StateMachine::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
{
	for (auto it = goodPointers.begin(); it != goodPointers.end(); it++)
		*it = simplifyIRExpr(*it, opt);
	for (auto it = goodPointers.begin(); it != goodPointers.end(); ) {
		if (mentionsBinders(*it)) {
			it = goodPointers.erase(it);
			continue;
		}
		for (auto it2 = it + 1; it2 != goodPointers.end(); ) {
			if (definitelyEqual(*it, *it2, opt))
				it2 = goodPointers.erase(it2);
			else
				it2++;
		}
		if (it == goodPointers.end())
			break;
		it++;
	}

	bool b = false;
	StateMachineState *new_root = root->optimise(opt, oracle, &b, freeVariables, goodPointers);
	if (b) {
		*done_something = true;
		StateMachine *sm = new StateMachine(*this);
		sm->root = new_root;
		return sm;
	} else {
		return this;
	}
}

class reduceBadPtrTransformer : public IRExprTransformer {
public:
	knownGoodPointersT &kgp;
	reduceBadPtrTransformer(knownGoodPointersT &_kgp)
		: kgp(_kgp)
	{}
	IRExpr *transformIex(IRExpr::Unop *e)
	{
		if (e->op == Iop_BadPtr) {
			for (auto it = kgp.begin(); it != kgp.end(); it++) {
				if (definitelyEqual(*it, e->arg, AllowableOptimisations::defaultOptimisations))
					return IRExpr_Const(IRConst_U1(0));
			}
		}
		return NULL;
	}
};
static IRExpr *
reduceBadPtrExpressions(IRExpr *orig, knownGoodPointersT &kgp, bool *done_something)
{
	if (kgp.empty())
		return orig;
	reduceBadPtrTransformer t(kgp);
	return t.transformIRExpr(orig, done_something);
}

StateMachineState *
StateMachineBifurcate::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something, FreeVariableMap &fv,
				knownGoodPointersT &kgp)
{
	if (trueTarget->target == StateMachineUnreached::get()) {
		*done_something = true;
		if (falseTarget->target == StateMachineUnreached::get())
			return StateMachineUnreached::get();
		else
			return new StateMachineProxy(origin, falseTarget->optimise(opt, oracle, done_something, fv, kgp));
	}
	if (falseTarget->target == StateMachineUnreached::get()) {
		*done_something = true;
		return new StateMachineProxy(origin, trueTarget->optimise(opt, oracle, done_something, fv, kgp));
	}
	condition = reduceBadPtrExpressions(condition, kgp, done_something);
	condition = optimiseIRExprFP(condition, opt, done_something);
	if (condition->tag == Iex_Const) {
		*done_something = true;
		if (condition->Iex.Const.con->Ico.U1)
			return new StateMachineProxy(origin, trueTarget->optimise(opt, oracle, done_something, fv, kgp));
		else
			return new StateMachineProxy(origin, falseTarget->optimise(opt, oracle, done_something, fv, kgp));
	}
	trueTarget = trueTarget->optimise(opt, oracle, done_something, fv, kgp);
	falseTarget = falseTarget->optimise(opt, oracle, done_something, fv, kgp);

	if (falseTarget->sideEffects.size() == 0 &&
	    trueTarget->sideEffects.size() == 0) {
		if (trueTarget->target == falseTarget->target) {
			*done_something = true;
			return trueTarget->target;
		}

		if (StateMachineBifurcate *falseBifur = dynamic_cast<StateMachineBifurcate *>(falseTarget->target)) {
			if (trueTarget == falseBifur->trueTarget) {
				falseTarget = falseBifur->falseTarget;
				condition = IRExpr_Binop(
					Iop_Or1,
					condition,
					falseBifur->condition);
				*done_something = true;
				return this;
			}
			if (trueTarget == falseBifur->falseTarget) {
				falseTarget = falseBifur->trueTarget;
				condition = IRExpr_Binop(
					Iop_Or1,
					condition,
					IRExpr_Unop(
						Iop_Not1,
						falseBifur->condition));
				*done_something = true;
				return this;
			}
		}
		if (StateMachineBifurcate *trueBifur = dynamic_cast<StateMachineBifurcate *>(trueTarget->target)) {
			if (falseTarget == trueBifur->falseTarget) {
				trueTarget = trueBifur->trueTarget;
				condition = IRExpr_Binop(
					Iop_And1,
					condition,
					trueBifur->condition);
				*done_something = true;
				return this;
			}
			if (falseTarget == trueBifur->trueTarget) {
				trueTarget = trueBifur->falseTarget;
				condition = IRExpr_Binop(
					Iop_And1,
					condition,
					IRExpr_Unop(
						Iop_Not1,
						trueBifur->condition));
				*done_something = true;
				return this;
			}
		}
	}
	return this;
}

void
StateMachineBifurcate::findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt)
{
	assert(s.empty());
	std::set<Int> t;
	trueTarget->findUsedBinders(t, opt);
	falseTarget->findUsedBinders(s, opt);
	for (std::set<Int>::iterator it = t.begin();
	     it != t.end();
	     it++)
		s.insert(*it);
	::findUsedBinders(condition, s, opt);
}

StateMachineSideEffect *
StateMachineSideEffectStore::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
{
	addr = optimiseIRExprFP(addr, opt, done_something);
	data = optimiseIRExprFP(data, opt, done_something);
	if (isBadAddress(addr, opt, oracle) ||
	    definitelyUnevaluatable(data, opt, oracle)) {
		*done_something = true;
		return StateMachineSideEffectUnreached::get();
	}
	return this;
}
void
StateMachineSideEffectStore::updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &opt)
{
	for (std::set<IRExpr *>::iterator it = l.begin();
	     it != l.end();
		) {
		if (definitelyEqual(*it, addr, opt))
			l.erase(it++);
		else
			it++;
	}
}
void
StateMachineSideEffectStore::findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt)
{
	::findUsedBinders(addr, s, opt);
	::findUsedBinders(data, s, opt);
}

void
StateMachineSideEffectLoad::constructed()
{
	bool ign;
	addr = optimiseIRExprFP(addr, AllowableOptimisations::defaultOptimisations, &ign);
}
StateMachineSideEffect *
StateMachineSideEffectLoad::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
{
	addr = optimiseIRExprFP(addr, opt, done_something);
	if (isBadAddress(addr, opt, oracle)) {
		*done_something = true;
		return StateMachineSideEffectUnreached::get();
	}
	constructed();
	return this;
}
void
StateMachineSideEffectLoad::findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt)
{
	s.erase(key);
	::findUsedBinders(addr, s, opt);
}

StateMachineSideEffect *
StateMachineSideEffectCopy::optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something)
{
	value = optimiseIRExprFP(value, opt, done_something);
	if (definitelyUnevaluatable(value, opt, oracle)) {
		*done_something = true;
		return StateMachineSideEffectUnreached::get();
	}
	return this;
}
void
StateMachineSideEffectCopy::findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt)
{
	s.erase(key);
	::findUsedBinders(value, s, opt);
}

class rewriteBinderTransformer : public IRExprTransformer {
public:
	const std::map<Int, IRExpr *> &binders;
	rewriteBinderTransformer(const std::map<Int, IRExpr *> &_binders)
		: binders(_binders)
	{}
	IRExpr *transformIex(IRExpr::Binder *e) {
		if (binders.count(e->binder)) {
			return binders.find(e->binder)->second;
		} else {
			return NULL;
		}
	}
};

static IRExpr *
rewriteBinderExpressions(IRExpr *ex, const std::map<Int, IRExpr *> &binders, bool *done_something)
{
	rewriteBinderTransformer trans(binders);
	return trans.transformIRExpr(ex, done_something);
}

class RewriteBindersTransformer : public IRExprTransformer {
public:
	int key;
	IRExpr *val;
	RewriteBindersTransformer(int _key, IRExpr *_val)
		: key(_key), val(_val)
	{}
	IRExpr *transformIex(IRExpr::Binder *e) {
		if (e->binder == key)
			return val;
		return IRExprTransformer::transformIex(e);
	}
};
static void
applySideEffectToFreeVariables(StateMachineSideEffectCopy *c,
			       FreeVariableMap &fv,
			       bool *done_something)
{
	RewriteBindersTransformer t(c->key, c->value);
	fv.applyTransformation(t, done_something);
}

class RewriteBinderToLoadTransformer : public IRExprTransformer {
public:
	int key;
	ThreadRip rip;
	IRExpr *addr;
	IRExpr *val;
	RewriteBinderToLoadTransformer(int _key, ThreadRip _rip, IRExpr *_addr)
		: key(_key), rip(_rip), addr(_addr), val(NULL)
	{}
	IRExpr *transformIex(IRExpr::Binder *e) {
		if (e->binder == key) {
			if (!val)
				val = IRExpr_Load(false, Iend_LE, Ity_I64, addr, rip);
			return val;
		}
		return IRExprTransformer::transformIex(e);
	}
};
void
applySideEffectToFreeVariables(StateMachineSideEffectLoad *c,
			       FreeVariableMap &fv,
			       bool *done_something)
{
	RewriteBinderToLoadTransformer t(c->key, c->rip, c->addr);
	fv.applyTransformation(t, done_something);
}

struct availEntry {
	IRExpr *addr;
	IRExpr *value;
	bool local;
	availEntry(IRExpr *a, IRExpr *v, bool l)
		: addr(a), value(v), local(l)
	{}
	bool operator<(const availEntry &o) const {
		if (addr < o.addr) return true;
		if (addr > o.addr) return false;
		if (value < o.value) return true;
		if (value > o.value) return false;
		if (local < o.local) return true;
		return false;
	}
};
StateMachineEdge *
StateMachineEdge::optimise(const AllowableOptimisations &opt,
			   OracleInterface *oracle,
			   bool *done_something,
			   FreeVariableMap &freeVariables,
			   knownGoodPointersT &kgp)
{
	if (StateMachineProxy *smp =
	    dynamic_cast<StateMachineProxy *>(target)) {
		sideEffects.insert(sideEffects.end(),
				   smp->target->sideEffects.begin(),
				   smp->target->sideEffects.end());
		target = smp->target->target;
		*done_something = true;
		return optimise(opt, oracle, done_something, freeVariables, kgp);
	}
	if (TIMEOUT)
		return this;
	target = target->optimise(opt, oracle, done_something, freeVariables, kgp);

	std::vector<StateMachineSideEffect *>::iterator it;

	for (it = sideEffects.begin(); !TIMEOUT && it != sideEffects.end(); it++)
		*it = (*it)->optimise(opt, oracle, done_something);

	/* Try to forward stuff from stores to loads wherever
	   possible.  We don't currently do this inter-state, because
	   that's moderately tricky. */
	std::set<availEntry> availExpressions;
	for (it = sideEffects.begin(); !TIMEOUT && it != sideEffects.end(); it++) {
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(*it)) {
			/* If the store isn't thread local, and we're
			   not in no-interferes mode, we can't do any
			   forwarding at all, because some other
			   thread might clober the location we're
			   looking at. */
			bool local = oracle->storeIsThreadLocal(smses);
			if (!opt.assumeNoInterferingStores && !local)
				continue;

			/* Kill anything which might be clobbered by
			   this store. */
			for (std::set<availEntry>::iterator it2 =
				     availExpressions.begin();
			     it2 != availExpressions.end();
				) {
				IRExpr *addr = it2->addr;
				if (local == it2->local &&
				    !definitelyNotEqual(addr, smses->addr, opt))
					availExpressions.erase(it2++);
				else
					it2++;
			}
			/* And add this one to the set */
			availExpressions.insert(availEntry(smses->addr,
							   smses->data,
							   local));
		} else if (StateMachineSideEffectLoad *smsel =
			   dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			/* If the load was definitely satisfied by a
			   known store, eliminate it. */
			bool local = oracle->loadIsThreadLocal(smsel);
			bool killed = false;
			for (std::set<availEntry>::iterator it2 = availExpressions.begin();
			     !TIMEOUT && it2 != availExpressions.end();
			     it2++) {
				if (local == it2->local &&
				    definitelyEqual(it2->addr, smsel->addr, opt)) {
					*it = new StateMachineSideEffectCopy(smsel->key,
									     it2->value);
					*done_something = true;
					killed = true;
					break;
				}
			}

			/* This load can also be used to eliminate
			   some future loads, possibly. */
			if (!killed &&
			    (opt.assumeNoInterferingStores || oracle->loadIsThreadLocal(smsel)))
				availExpressions.insert(availEntry(
								smsel->addr,
								IRExpr_Binder(smsel->key),
								local));
		} else if (dynamic_cast<StateMachineSideEffectUnreached *>(*it)) {
			/* Okay, we know we can't go down this edge.
			 * Turn it into an unreached one. */
			sideEffects.clear();
			target = StateMachineUnreached::get();
/**/			break;
		} else {
			assert(dynamic_cast<StateMachineSideEffectCopy *>(*it));
		}
	}

	/* Propagate any copy operations. */
	std::map<Int, IRExpr *> copies;
	for (std::vector<StateMachineSideEffect *>::iterator it = sideEffects.begin();
	     !TIMEOUT && it != sideEffects.end();
	     it++) {
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(*it)) {
			*it = new StateMachineSideEffectStore(
				rewriteBinderExpressions(smses->addr, copies, done_something),
				rewriteBinderExpressions(smses->data, copies, done_something),
				smses->rip);
		} else if (StateMachineSideEffectLoad *smsel =
			   dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			*it = new StateMachineSideEffectLoad(
				smsel->key,
				rewriteBinderExpressions(smsel->addr, copies, done_something),
				smsel->rip);
		} else if (StateMachineSideEffectCopy *smsec =
			   dynamic_cast<StateMachineSideEffectCopy *>(*it)) {
			smsec = new StateMachineSideEffectCopy(
				smsec->key,
				rewriteBinderExpressions(smsec->value, copies, done_something));
			copies[smsec->key] = smsec->value;
			*it = smsec;
		} else if (dynamic_cast<StateMachineSideEffectUnreached *>(*it)) {
		} else {
			abort();
		}
	}

	/* Now cull completely redundant stores. */
	std::set<IRExpr *> loadedAddresses;
	target->findLoadedAddresses(loadedAddresses, opt);
	std::set<Int> usedBinders;
	target->findUsedBinders(usedBinders, opt);

	it = sideEffects.end();
	while (!TIMEOUT && it != sideEffects.begin()) {
		bool isDead = false;
		it--;
		(*it)->optimise(opt, oracle, done_something);
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(*it)) {
			if (opt.ignoreStore(smses->rip.rip) ||
			    oracle->storeIsThreadLocal(smses))
				isDead = true;
			else
				isDead = false;
			for (std::set<IRExpr *>::iterator it2 = loadedAddresses.begin();
			     isDead && it2 != loadedAddresses.end();
			     it2++) {
				if (!definitelyNotEqual(*it2, smses->addr, opt))
					isDead = false;
			}
		}
		if (StateMachineSideEffectCopy *smsec =
		    dynamic_cast<StateMachineSideEffectCopy *>(*it)) {
			if (!usedBinders.count(smsec->key)) {
				bool ign;
				applySideEffectToFreeVariables(smsec, freeVariables, &ign);
				isDead = true;
			}
		}
		if (StateMachineSideEffectLoad *smsel =
		    dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			if (!usedBinders.count(smsel->key)) {
				bool ign;
				applySideEffectToFreeVariables(smsel, freeVariables, &ign);
				isDead = true;
			}
		}
		if (isDead) {
			*done_something = true;
			it = sideEffects.erase(it);
		} else {
			(*it)->updateLoadedAddresses(loadedAddresses, opt);
			(*it)->findUsedBinders(usedBinders, opt);
		}
	}

	if (TIMEOUT)
		return this;
	return this;
}

static void
findUsedBinders(IRExpr *e, std::set<Int> &out, const AllowableOptimisations &opt)
{
	switch (e->tag) {
	case Iex_Binder:
		out.insert(e->Iex.Binder.binder);
		return;
	case Iex_Get:
		return;
	case Iex_GetI:
		findUsedBinders(e->Iex.GetI.ix, out, opt);
		return;
	case Iex_RdTmp:
		return;
	case Iex_Qop:
		findUsedBinders(e->Iex.Qop.arg4, out, opt);
	case Iex_Triop:
		findUsedBinders(e->Iex.Qop.arg3, out, opt);
	case Iex_Binop:
		findUsedBinders(e->Iex.Qop.arg2, out, opt);
	case Iex_Unop:
		findUsedBinders(e->Iex.Qop.arg1, out, opt);
		return;
	case Iex_Load:
		findUsedBinders(e->Iex.Load.addr, out, opt);
		return;
	case Iex_Const:
		return;
	case Iex_CCall: {
		for (int x = 0; e->Iex.CCall.args[x]; x++)
			findUsedBinders(e->Iex.CCall.args[x], out, opt);
		return;
	}
	case Iex_Mux0X:
		findUsedBinders(e->Iex.Mux0X.cond, out, opt);
		findUsedBinders(e->Iex.Mux0X.expr0, out, opt);
		findUsedBinders(e->Iex.Mux0X.exprX, out, opt);
		return;
	case Iex_Associative:
		for (int it = 0;
		     it < e->Iex.Associative.nr_arguments;
		     it++)
			findUsedBinders(e->Iex.Associative.contents[it], out, opt);
		return;
	case Iex_FreeVariable:
		return;
	case Iex_ClientCall:
		for (int i = 0; e->Iex.ClientCall.args[i]; i++)
			findUsedBinders(e->Iex.ClientCall.args[i], out, opt);
		return;
	case Iex_ClientCallFailed:
		findUsedBinders(e->Iex.ClientCallFailed.target, out, opt);
		return;
	case Iex_HappensBefore:
		return;
	}
	abort();
}

static void
buildStateLabelTable(const StateMachineState *sm, std::map<const StateMachineState *, int> &table,
		     std::vector<const StateMachineState *> &states)
{
	std::vector<const StateMachineState *> toEmit;
	int next_label;

	toEmit.push_back(sm);
	next_label = 1;
	while (!toEmit.empty()) {
		sm = toEmit.back();
		toEmit.pop_back();
		if (!sm || table.count(sm))
			continue;
		states.push_back(sm);
		table[sm] = next_label;
		next_label++;
		if (sm->target0())
			toEmit.push_back(sm->target0()->target);
		if (sm->target1())
			toEmit.push_back(sm->target1()->target);
	}
}

void
FreeVariableMap::print(FILE *f) const
{
	for (map_t::iterator it = content->begin();
	     it != content->end();
	     it++) {
		fprintf(f, "free%d -> ", it.key().val);
		ppIRExpr(it.value(), f);
		fprintf(f, "\n");
	}
}

bool
FreeVariableMap::parse(const char *str, const char **succ, char **err)
{
	content = new map_t();
	while (1) {
		FreeVariableKey k;
		IRExpr *val;
		if (!parseThisString("free", str, &str, err) ||
		    !parseDecimalInt(&k.val, str, &str, err) ||
		    !parseThisString(" -> ", str, &str, err) ||
		    !parseIRExpr(&val, str, &str, err) ||
		    !parseThisChar('\n', str, &str, err))
			break;
		content->set(FreeVariableKey(k), val);
	}
	*succ = str;
	return true;
}

template <typename cont, void printer(const typename cont::value_type, FILE *)> void
printContainer(const cont &v, FILE *f)
{
	fprintf(f, "[");
	for (auto it = v.begin(); it != v.end(); it++) {
		if (it != v.begin())
			fprintf(f, ", ");
		printer(*it, f);
	}
	fprintf(f, "]");
}

void
printStateMachine(const StateMachine *sm, FILE *f)
{
	std::map<const StateMachineState *, int> labels;
	std::vector<const StateMachineState *> states;

	fprintf(f, "Machine for %lx:%d\n", sm->origin, sm->tid);
	buildStateLabelTable(sm->root, labels, states);
	for (std::vector<const StateMachineState *>::iterator it = states.begin();
	     it != states.end();
	     it++) {
		fprintf(f, "l%d: ", labels[*it]);
		(*it)->prettyPrint(f, labels);
		fprintf(f, "\n");
	}
	sm->freeVariables.print(f);
	fprintf(f, "Good pointers: ");
	printContainer<ring_buffer<IRExpr *, 5>, ppIRExpr>(sm->goodPointers, f);
	fprintf(f, "\n");
}

unsigned long
StateMachineEdge::hashval() const
{
	if (!have_hash) {
		unsigned long h = 0xaabb5697;
		for (unsigned x = 0; x < sideEffects.size(); x++)
			h = h * 65537 + sideEffects[x]->hashval();
		_hashval = h;
		have_hash = true;
	}
	return _hashval;
}

bool
sideEffectsBisimilar(StateMachineSideEffect *smse1,
		     StateMachineSideEffect *smse2,
		     const AllowableOptimisations &opt)
{
	if (StateMachineSideEffectStore *smses1 =
	    dynamic_cast<StateMachineSideEffectStore *>(smse1)) {
		StateMachineSideEffectStore *smses2 =
			dynamic_cast<StateMachineSideEffectStore *>(smse2);
		if (!smses2)
			return false;
		return definitelyEqual(smses1->addr, smses2->addr, opt) &&
			definitelyEqual(smses1->data, smses2->data, opt);
	} else if (StateMachineSideEffectLoad *smsel1 =
		   dynamic_cast<StateMachineSideEffectLoad *>(smse1)) {
		StateMachineSideEffectLoad *smsel2 =
			dynamic_cast<StateMachineSideEffectLoad *>(smse2);
		if (!smsel2)
			return false;
		return smsel1->key == smsel2->key &&
			definitelyEqual(smsel1->addr, smsel2->addr, opt);
	} else if (StateMachineSideEffectCopy *smsec1 =
		   dynamic_cast<StateMachineSideEffectCopy *>(smse1)) {
		StateMachineSideEffectCopy *smsec2 =
			dynamic_cast<StateMachineSideEffectCopy *>(smse2);
		if (!smsec2)
			return false;
		return smsec1->key == smsec2->key &&
			definitelyEqual(smsec1->value, smsec2->value, opt);
	} else if (dynamic_cast<StateMachineSideEffectUnreached *>(smse1)) {
		if (dynamic_cast<StateMachineSideEffectUnreached *>(smse2))
			return true;
		else
			return false;
	} else {
		abort();
	}
}

bool
parseStateMachineSideEffect(StateMachineSideEffect **out,
			    const char *str,
			    const char **suffix,
			    char **err)
{
	const char *str2;
	if (parseThisString("<unreached>", str, suffix, err)) {
		*out = StateMachineSideEffectUnreached::get();
		return true;
	}
	IRExpr *addr;
	IRExpr *data;
	ThreadRip rip;
	if (parseThisString("*(", str, &str2, err) &&
	    parseIRExpr(&addr, str2, &str2, err) &&
	    parseThisString(") <- ", str2, &str2, err) &&
	    parseIRExpr(&data, str2, &str2, err) &&
	    parseThisString(" @ ", str2, &str2, err) &&
	    parseThreadRip(&rip, str2, suffix, err)) {
		*out = new StateMachineSideEffectStore(addr, data, rip);
		return true;
	}
	int key;
	if (parseThisChar('B', str, &str2, err) &&
	    parseDecimalInt(&key, str2, &str2, err) &&
	    parseThisString(" <- *(", str2, &str2, err) &&
	    parseIRExpr(&addr, str2, &str2, err) &&
	    parseThisString(")@", str2, &str2, err) &&
	    parseThreadRip(&rip, str2, suffix, err)) {
		*out = new StateMachineSideEffectLoad(key, addr, rip);
		return true;
	}
	if (parseThisChar('B', str, &str2, err) &&
	    parseDecimalInt(&key, str2, &str2, err) &&
	    parseThisString(" = (", str2, &str2, err) &&
	    parseIRExpr(&data, str2, &str2, err) &&
	    parseThisChar(')', str2, suffix, err)) {
		*out = new StateMachineSideEffectCopy(key, data);
		return true;
	}
	return false;
}

/* State machine parser.  We cheat a little bit and stash the state
 * labels in the target field of state machine edges until we have
 * find the state we're actually supposed to point at. */
static bool
parseStateMachineEdge(StateMachineEdge **out,
		      const char *sep,
		      const char *str,
		      const char **suffix,
		      char **err)
{
	int targetLabel;
	std::vector<StateMachineSideEffect *> sideEffects;
	if (parseThisChar('{', str, &str, err)) {
		while (1) {
			StateMachineSideEffect *se;
			if (!parseStateMachineSideEffect(&se, str, &str, err))
				return false;
			sideEffects.push_back(se);
			if (parseThisString(sep, str, &str, err))
				continue;
			if (!parseThisString("} ", str, &str, err))
				return false;
			break;
		}
	}
	if (!parseThisChar('l', str, &str, err) ||
	    !parseDecimalInt(&targetLabel, str, suffix, err))
		return false;
	*out = new StateMachineEdge((StateMachineState *)targetLabel);
	(*out)->sideEffects = sideEffects;
	return true;
}

static bool
parseStateMachineState(StateMachineState **out,
		       const char *str,
		       const char **suffix,
		       char **err)
{
	if (parseThisString("<unreached>", str, suffix, err)) {
		*out = StateMachineUnreached::get();
		return true;
	}
	if (parseThisString("<crash>", str, suffix, err)) {
		*out = StateMachineCrash::get();
		return true;
	}
	if (parseThisString("<survive>", str, suffix, err)) {
		*out = StateMachineNoCrash::get();
		return true;
	}
	unsigned long origin;
	IRExpr *target;
	const char *str2;
	if (parseThisChar('<', str, &str2, err) &&
	    parseHexUlong(&origin, str2, &str2, err) &&
	    parseIRExpr(&target, str2, &str2, err) &&
	    parseThisChar('>', str2, suffix, err)) {
		*out = new StateMachineStub(origin, target);
		return true;
	}
	StateMachineEdge *target1;
	if (parseThisChar('{', str, &str2, err) &&
	    parseHexUlong(&origin, str2, &str2, err) &&
	    parseThisChar(':', str2, &str2, err) &&
	    parseStateMachineEdge(&target1, "\n  ", str2, &str2, err) &&
	    parseThisChar('}', str2, suffix, err)) {
		*out = new StateMachineProxy(origin, target1);
		return true;
	}
	IRExpr *condition;
	StateMachineEdge *target2;
	if (parseHexUlong(&origin, str, &str2, err) &&
	    parseThisString(": if (", str2, &str2, err) &&
	    parseIRExpr(&condition, str2, &str2, err) &&
	    parseThisString(")\n  then {\n\t", str2, &str2, err) &&
	    parseStateMachineEdge(&target1, "\n\t", str2, &str2, err) &&
	    parseThisString("}\n  else {\n\t", str2, &str2, err) &&
	    parseStateMachineEdge(&target2, "\n\t", str2, &str2, err) &&
	    parseThisChar('}', str2, suffix, err)) {
		*out = new StateMachineBifurcate(origin, condition, target1, target2);
		return true;
	}
	return false;
}

static bool
parseOneState(std::map<int, StateMachineState *> &out,
	      const char *str,
	      const char **suffix,
	      char **err)
{
	int label;
	StateMachineState *res;

	if (!parseThisChar('l', str, &str, err) ||
	    !parseDecimalInt(&label, str, &str, err) ||
	    !parseThisString(": ", str, &str, err) ||
	    !parseStateMachineState(&res, str, &str, err) ||
	    !parseThisChar('\n', str, &str, err))
		return false;
	if (out.count(label)) {
		*err = vex_asprintf("label %d defined multiple times", label);
		return false;
	}
	out[label] = res;
	*suffix = str;
	return true;
}

static bool
parseStateMachine(StateMachineState **out, const char *str, const char **suffix, char **err)
{
	std::map<int, StateMachineState *> labelToState;

	while (*str) {
		if (!parseOneState(labelToState, str, &str, err))
			break;
	}
	if (!labelToState.count(1)) {
		*err = (char *)"label 1 must be defined";
		return false;
	}
	for (std::map<int, StateMachineState *>::iterator it = labelToState.begin();
	     it != labelToState.end();
	     it++) {
		if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(it->second)) {
			StateMachineState *t = labelToState[(int)(unsigned long)smp->target->target];
			if (!t) {
				*err = vex_asprintf("Label %d not defined",
						    (int)(unsigned long)smp->target->target);
				return false;
			}
			smp->target->target = t;
		} else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(it->second)) {
			StateMachineState *t = labelToState[(int)(unsigned long)smb->trueTarget->target];
			StateMachineState *f = labelToState[(int)(unsigned long)smb->falseTarget->target];
			if (!t) {
				*err = vex_asprintf("Label %d not defined",
						    (int)(unsigned long)smb->trueTarget->target);
				return false;
			}
			if (!f) {
				*err = vex_asprintf("Label %d not defined",
						    (int)(unsigned long)smb->falseTarget->target);
				return false;
			}

			smb->trueTarget->target = t;
			smb->falseTarget->target = f;
		} else {
			assert(dynamic_cast<StateMachineTerminal *>(it->second));
		}
	}
	*suffix = str;
	*out = labelToState[1];
	return true;
}

bool
StateMachine::parse(StateMachine **out, const char *str, const char **suffix, char **err)
{
	unsigned long origin;
	int tid;
	if (!parseThisString("Machine for ", str, &str, err) ||
	    !parseHexUlong(&origin, str, &str, err) ||
	    !parseThisChar(':', str, &str, err) ||
	    !parseDecimalInt(&tid, str, &str, err) ||
	    !parseThisChar('\n', str, &str, err))
		return false;
	StateMachineState *root;
	if (!parseStateMachine(&root, str, &str, err))
		return false;
	*out = new StateMachine(root, origin, tid);
	if (!(*out)->freeVariables.parse(str, &str, err))
		return false;
	if (!parseThisString("Good pointers: ", str, &str, err) ||
	    !parseContainer(&(*out)->goodPointers, parseIRExpr, str, &str, err) ||
	    !parseThisChar('\n', str, suffix, err))
		return false;
	return true;
}
bool
parseStateMachine(StateMachine **out, const char *str, const char **suffix, char **err)
{
	return StateMachine::parse(out, str, suffix, err);
}

StateMachine *
readStateMachine(int fd)
{
	char *content = readfile(fd);
	const char *end;
	StateMachine *res;
	char *err;
	if (!parseStateMachine(&res, content, &end, &err) || *end)
		errx(1, "error parsing state machine (%s):\n%s", err, content);
	free(content);
	return res;
}

void
StateMachineState::assertAcyclic(std::vector<const StateMachineState *> &stack,
				 std::set<const StateMachineState *> &clean) const
{
	if (clean.count(this))
		return;
	if (std::find(stack.begin(), stack.end(), this) != stack.end())
		goto found_cycle;
	stack.push_back(this);
	if (target0())
		target0()->target->assertAcyclic(stack, clean);
	if (target1())
		target1()->target->assertAcyclic(stack, clean);
	assert(stack.back() == this);
	stack.pop_back();
	//assert(!clean.count(this));
	clean.insert(this);
	return;

found_cycle:
	printf("Unexpected cycle in state machine!\n");
	printf("Found at %p\n", this);
	std::map<const StateMachineState *, int> labels;
	prettyPrint(stdout, labels);
	printf("Path: \n");
	for (std::vector<const StateMachineState *>::const_iterator it = stack.begin();
	     it != stack.end();
	     it++)
		printf("\t%d\n", labels[*it]);
	printf("End\n");
	assert(0);
}

void
StateMachineState::assertAcyclic() const
{
	std::vector<const StateMachineState *> stack;
	std::set<const StateMachineState *> clean;
	assertAcyclic(stack, clean);
}

void
StateMachineState::enumerateMentionedMemoryAccesses(std::set<unsigned long> &instrs)
{
	if (target1())
		target1()->enumerateMentionedMemoryAccesses(instrs);
	if (target0())
		target0()->enumerateMentionedMemoryAccesses(instrs);
}

void
StateMachineEdge::enumerateMentionedMemoryAccesses(std::set<unsigned long> &instrs)
{
	for (std::vector<StateMachineSideEffect *>::iterator it = sideEffects.begin();
	     it != sideEffects.end();
	     it++) {
		StateMachineSideEffect *smse = *it;
		if (StateMachineSideEffectLoad *smsel =
		    dynamic_cast<StateMachineSideEffectLoad *>(smse)) {
			instrs.insert(smsel->rip.rip);
		} else if (StateMachineSideEffectStore *smses =
			   dynamic_cast<StateMachineSideEffectStore *>(smse)) {
			instrs.insert(smses->rip.rip);
		}
	}
	target->enumerateMentionedMemoryAccesses(instrs);
}

void
StateMachineState::sanity_check(std::set<Int> &binders, std::vector<const StateMachineState *> &path) const
{
	for (unsigned x = 0; x < path.size(); x++)
		assert(path[x] != this);
	path.push_back(this);
	if (target0()) target0()->sanity_check(binders, path);
	if (target1()) target1()->sanity_check(binders, path);
	_sanity_check(binders);
	assert(path.back() == this);
	path.pop_back();
}

void
StateMachineEdge::sanity_check(std::set<Int> &binders, std::vector<const StateMachineState *> &path) const
{
	for (std::vector<StateMachineSideEffect *>::const_iterator it = sideEffects.begin();
	     it != sideEffects.end();
	     it++) {
		(*it)->sanity_check(binders);
		if (StateMachineSideEffectLoad *smsel =
		    dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			assert(!binders.count(smsel->key));
			binders.insert(smsel->key);
		} else if (StateMachineSideEffectCopy *smsec =
			   dynamic_cast<StateMachineSideEffectCopy *>(*it)) {
			assert(!binders.count(smsec->key));
			binders.insert(smsec->key);
		}
	}
	target->sanity_check(binders, path);
	for (std::vector<StateMachineSideEffect *>::const_iterator it = sideEffects.begin();
	     it != sideEffects.end();
	     it++) {
		if (StateMachineSideEffectLoad *smsel =
		    dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			binders.erase(smsel->key);
		} else if (StateMachineSideEffectCopy *smsec =
			   dynamic_cast<StateMachineSideEffectCopy *>(*it)) {
			binders.erase(smsec->key);
		}
	}
}

/* Not really a transformer, but this is the easiest way of expressing
   an expression walk. */
class checkBinders : public IRExprTransformer {
public:
	const std::set<Int> &binders;
	IRExpr *transformIex(IRExpr::Binder *e) {
		assert(binders.count(e->binder));
		return IRExprTransformer::transformIex(e);
	}
	checkBinders(const std::set<Int> &_binders)
		: binders(_binders)
	{}
};
void
checkIRExprBindersInScope(const IRExpr *iex, const std::set<Int> &binders)
{
	checkBinders cb(binders);
	bool ign;
	cb.transformIRExpr((IRExpr *)iex, &ign);
}

static void
nrAliasingLoads(StateMachineState *sm,
		StateMachineSideEffectLoad *smsel,
		const Oracle::RegisterAliasingConfiguration &alias,
		const AllowableOptimisations &opt,
		int *out,
		std::set<StateMachineState *> &visited,
		OracleInterface *oracle);
static void
nrAliasingLoads(StateMachineEdge *sme,
		StateMachineSideEffectLoad *smsel,
		const Oracle::RegisterAliasingConfiguration &alias,
		const AllowableOptimisations &opt,
		int *out,
		std::set<StateMachineState *> &visited,
		OracleInterface *oracle)
{
	for (unsigned x = 0; x < sme->sideEffects.size(); x++) {
		StateMachineSideEffectLoad *smsel2 =
			dynamic_cast<StateMachineSideEffectLoad *>(sme->sideEffects[x]);
		if (smsel2 &&
		    alias.ptrsMightAlias(smsel->addr, smsel2->addr, opt.freeVariablesMightAccessStack) &&
		    oracle->memoryAccessesMightAlias(smsel, smsel2) &&
		    definitelyEqual( smsel->addr,
				     smsel2->addr,
				     opt))
			(*out)++;
	}
	nrAliasingLoads(sme->target, smsel, alias, opt, out, visited, oracle);
}
static void
nrAliasingLoads(StateMachineState *sm,
		StateMachineSideEffectLoad *smsel,
		const Oracle::RegisterAliasingConfiguration &alias,
		const AllowableOptimisations &opt,
		int *out,
		std::set<StateMachineState *> &visited,
		OracleInterface *oracle)
{
	if (visited.count(sm))
		return;
	visited.insert(sm);
	if (sm->target0())
		nrAliasingLoads(sm->target0(),
				smsel,
				alias,
				opt,
				out,
				visited,
				oracle);
	if (sm->target1())
		nrAliasingLoads(sm->target1(),
				smsel,
				alias,
				opt,
				out,
				visited,
				oracle);
}
static int
nrAliasingLoads(StateMachine *sm,
		StateMachineSideEffectLoad *smsel,
		const Oracle::RegisterAliasingConfiguration &alias,
		const AllowableOptimisations &opt,
		OracleInterface *oracle)
{
	std::set<StateMachineState *> visited;
	int res = 0;
	nrAliasingLoads(sm->root, smsel, alias, opt, &res, visited, oracle);
	return res;
}
			   
static bool definitelyNoSatisfyingStores(StateMachineState *sm,
					 StateMachineSideEffectLoad *smsel,
					 const Oracle::RegisterAliasingConfiguration &alias,
					 const AllowableOptimisations &opt,
					 bool haveAliasingStore,
					 OracleInterface *oracle);
static bool
definitelyNoSatisfyingStores(StateMachineEdge *sme,
			     StateMachineSideEffectLoad *smsel,
			     const Oracle::RegisterAliasingConfiguration &alias,
			     const AllowableOptimisations &opt,
			     bool haveAliasingStore,
			     OracleInterface *oracle)
{
	for (unsigned x = 0; x < sme->sideEffects.size(); x++) {
		StateMachineSideEffect *smse = sme->sideEffects[x];
		if (smse == smsel) {
			if (haveAliasingStore) {
				return false;
			} else {
				/* The load can't appear twice in one
				   path, and we've not seen a
				   satisfying store yet, so we're
				   fine. */
				return true;
			}
		}
		if (haveAliasingStore)
			continue;
		StateMachineSideEffectStore *smses =
			dynamic_cast<StateMachineSideEffectStore *>(smse);
		if (smses &&
		    alias.ptrsMightAlias(smsel->addr, smses->addr, opt.freeVariablesMightAccessStack) &&
		    oracle->memoryAccessesMightAlias(smsel, smses) &&
		    !definitelyNotEqual( smsel->addr,
					 smses->addr,
					 opt)) {
			/* This store might alias with the load.  If
			   we encounter the load after this, then it
			   might be satisfied. */
			haveAliasingStore = true;
		}
	}
	return definitelyNoSatisfyingStores(sme->target,
					    smsel,
					    alias,
					    opt,
					    haveAliasingStore,
					    oracle);
}
static bool
definitelyNoSatisfyingStores(StateMachineState *sm,
			     StateMachineSideEffectLoad *smsel,
			     const Oracle::RegisterAliasingConfiguration &alias,
			     const AllowableOptimisations &opt,
			     bool haveAliasingStore,
			     OracleInterface *oracle)
{
	if (sm->target0() && !definitelyNoSatisfyingStores(sm->target0(),
							   smsel,
							   alias,
							   opt,
							   haveAliasingStore,
							   oracle))
		return false;
	if (sm->target1() && !definitelyNoSatisfyingStores(sm->target1(),
							   smsel,
							   alias,
							   opt,
							   haveAliasingStore,
							   oracle))
		return false;
	return true;
}
static bool definitelyNoSatisfyingStores(StateMachine *sm,
					 StateMachineSideEffectLoad *smsel,
					 const Oracle::RegisterAliasingConfiguration &alias,
					 const AllowableOptimisations &opt,
					 bool haveAliasingStore,
					 OracleInterface *oracle)
{
	return definitelyNoSatisfyingStores(sm->root, smsel, alias, opt, haveAliasingStore, oracle);
}

/* There are some memory locations which are effectively completely
 * unconstrained by anything which the machine does.  Replace those
 * with freshly allocated free variables.  The idea here is that we
 * can then propagate that through a bit and potentially simplify lots
 * of other bits of the machine by allocating yet more free
 * variables. */
static StateMachineState *introduceFreeVariables(StateMachineState *sm,
						 StateMachine *root_sm,
						 const Oracle::RegisterAliasingConfiguration &alias,
						 const AllowableOptimisations &opt,
						 OracleInterface *oracle,
						 bool *done_something,
						 std::vector<std::pair<FreeVariableKey, IRExpr *> > &fresh);
static StateMachineEdge *
introduceFreeVariables(StateMachineEdge *sme,
		       StateMachine *root_sm,
		       const Oracle::RegisterAliasingConfiguration &alias,
		       const AllowableOptimisations &opt,
		       OracleInterface *oracle,
		       bool *done_something,
		       std::vector<std::pair<FreeVariableKey, IRExpr *> > &fresh)
{
	StateMachineEdge *out = new StateMachineEdge(NULL);
	bool doit = false;
	/* A load results in a free variable if it's local and no
	   stores could potentially alias with it and no other loads
	   could alias with it. */
	for (unsigned idx = 0; idx < sme->sideEffects.size(); idx++) {
		StateMachineSideEffect *smse = sme->sideEffects[idx];
		StateMachineSideEffectLoad *smsel = dynamic_cast<StateMachineSideEffectLoad *>(smse);
		if (!smsel ||
		    !oracle->loadIsThreadLocal(smsel) ||
		    !definitelyNoSatisfyingStores(root_sm, smsel, alias, opt, false, oracle) ||
		    nrAliasingLoads(root_sm, smsel, alias, opt, oracle) != 1) {
			out->sideEffects.push_back(smse);
			continue;
		}
		/* This is a local load from a location which is never
		 * stored.  Remove it. */
		StateMachineSideEffectCopy *smsec = new StateMachineSideEffectCopy(smsel->key, IRExpr_FreeVariable());
		out->sideEffects.push_back(smsec);
		fresh.push_back(std::pair<FreeVariableKey, IRExpr *>
				(smsec->value->Iex.FreeVariable.key,
				 IRExpr_Load(false, Iend_LE, Ity_I64, smsel->addr, smsel->rip)));
		doit = true;
	}
	out->target = introduceFreeVariables(sme->target, root_sm, alias, opt, oracle, &doit, fresh);

	if (doit) {
		*done_something = true;
		return out;
	} else {
		return sme;
	}
}
static StateMachineState *
introduceFreeVariables(StateMachineState *sm,
		       StateMachine *root_sm,
		       const Oracle::RegisterAliasingConfiguration &alias,
		       const AllowableOptimisations &opt,
		       OracleInterface *oracle,
		       bool *done_something,
		       std::vector<std::pair<FreeVariableKey, IRExpr *> > &fresh)
{
	bool doit = false;
	if (dynamic_cast<StateMachineTerminal *>(sm))
		return sm;
	if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
		StateMachineEdge *e = introduceFreeVariables(smp->target,
							     root_sm,
							     alias,
							     opt,
							     oracle,
							     &doit,
							     fresh);
		if (doit) {
			*done_something = true;
			return new StateMachineProxy(smp->origin, e);
		} else {
			return sm;
		}
	}
	StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(sm);
	assert(smb);
	StateMachineEdge *t = introduceFreeVariables(smb->trueTarget,
						     root_sm,
						     alias,
						     opt,
						     oracle,
						     &doit,
						     fresh);
	StateMachineEdge *f = introduceFreeVariables(smb->falseTarget,
						     root_sm,
						     alias,
						     opt,
						     oracle,
						     &doit,
						     fresh);
	if (doit) {
		*done_something = true;
		return new StateMachineBifurcate(smb->origin,
						 smb->condition,
						 t,
						 f);
	} else {
		return sm;
	}
}
StateMachine *
introduceFreeVariables(StateMachine *sm,
		       const Oracle::RegisterAliasingConfiguration &alias,
		       const AllowableOptimisations &opt,
		       OracleInterface *oracle,
		       bool *done_something)
{
	bool b = false;
	std::vector<std::pair<FreeVariableKey, IRExpr *> > fresh;
	StateMachineState *new_root = introduceFreeVariables(sm->root, sm, alias, opt, oracle, &b, fresh);
	if (b) {
		*done_something = true;
		StateMachine *new_sm =  new StateMachine(sm, fresh);
		new_sm->root = new_root;
		return new_sm;
	} else {
		return sm;
	}
}

class countFreeVariablesVisitor : public StateMachineTransformer {
	IRExpr *transformIex(IRExpr::FreeVariable *e) {
		counts[e->key]++;
		return StateMachineTransformer::transformIex(e);
	}
public:
	std::map<FreeVariableKey, int> counts;
};
class simplifyFreeVariablesTransformer : public StateMachineTransformer {
public:
	std::map<FreeVariableKey, int> &counts;
	FreeVariableMap &freeVariables;
	IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
		switch (e->tag) {
		case Iex_Const:
		case Iex_Binder:
		case Iex_Get:
		case Iex_GetI:
		case Iex_RdTmp:
		case Iex_Load:
		case Iex_Mux0X:
		case Iex_CCall:
		case Iex_FreeVariable:
		case Iex_ClientCall:
		case Iex_ClientCallFailed:
		case Iex_HappensBefore:
			break;
		case Iex_Qop:
			if (e->Iex.Qop.arg4->tag == Iex_FreeVariable &&
			    counts[e->Iex.Qop.arg4->Iex.FreeVariable.key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
					e->Iex.Qop.arg4->Iex.FreeVariable.key,
					IRExpr_Qop(
						e->Iex.Qop.op,
						e->Iex.Qop.arg1,
						e->Iex.Qop.arg2,
						e->Iex.Qop.arg3,
						freeVariables.get(e->Iex.Qop.arg4->Iex.FreeVariable.key))));
				return e->Iex.Qop.arg4;
			}
		case Iex_Triop:
			if (e->Iex.Triop.arg3->tag == Iex_FreeVariable &&
			    counts[e->Iex.Triop.arg3->Iex.FreeVariable.key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
					e->Iex.Triop.arg3->Iex.FreeVariable.key,
					IRExpr_Triop(
						e->Iex.Triop.op,
						e->Iex.Triop.arg1,
						e->Iex.Triop.arg2,
						freeVariables.get(e->Iex.Triop.arg3->Iex.FreeVariable.key))));
				return e->Iex.Triop.arg3;
			}
		case Iex_Binop:
			if (e->Iex.Binop.arg2->tag == Iex_FreeVariable &&
			    counts[e->Iex.Binop.arg2->Iex.FreeVariable.key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
					e->Iex.Binop.arg2->Iex.FreeVariable.key,
					IRExpr_Binop(
						e->Iex.Binop.op,
						e->Iex.Binop.arg1,
						freeVariables.get(e->Iex.Binop.arg2->Iex.FreeVariable.key))));
				return e->Iex.Binop.arg2;
			}
		case Iex_Unop:
			if (e->Iex.Unop.arg->tag == Iex_FreeVariable &&
			    counts[e->Iex.Unop.arg->Iex.FreeVariable.key] == 1) {
				*done_something = true;
				fvDelta.push_back(
					std::pair<FreeVariableKey, IRExpr *>(
					e->Iex.Unop.arg->Iex.FreeVariable.key,
					IRExpr_Unop(
						e->Iex.Unop.op,
						freeVariables.get(e->Iex.Unop.arg->Iex.FreeVariable.key))));
				return e->Iex.Unop.arg;
			}
			break;
		case Iex_Associative:
			for (int x = 0; x < e->Iex.Associative.nr_arguments; x++) {
				IRExpr *a = e->Iex.Associative.contents[x];
				if (a->tag == Iex_FreeVariable &&
				    counts[a->Iex.FreeVariable.key] == 1) {
					*done_something = true;
					IRExpr *b = IRExpr_Associative(&e->Iex.Associative);
					assert(freeVariables.get(a->Iex.FreeVariable.key));
					b->Iex.Associative.contents[x] =
						freeVariables.get(a->Iex.FreeVariable.key);
					fvDelta.push_back(
						std::pair<FreeVariableKey, IRExpr *>(
							a->Iex.FreeVariable.key, b));
					return a;
				}
			}
			break;
		}
		return StateMachineTransformer::transformIRExpr(e, done_something);
	}
	simplifyFreeVariablesTransformer(std::map<FreeVariableKey, int> &_counts,
					 FreeVariableMap &fv)
		: counts(_counts), freeVariables(fv)
	{}
};

StateMachine *
optimiseFreeVariables(StateMachine *sm, bool *done_something)
{
	countFreeVariablesVisitor cfvv;
	bool ign;
	cfvv.transform(sm, &ign);
	simplifyFreeVariablesTransformer sfvt(cfvv.counts, sm->freeVariables);
	return sfvt.transform(sm, done_something);
}

StateMachineState::RoughLoadCount
StateMachineEdge::roughLoadCount(StateMachineState::RoughLoadCount acc) const
{
	if (acc == StateMachineState::multipleLoads)
		return StateMachineState::multipleLoads;

	for (std::vector<StateMachineSideEffect *>::const_iterator it = sideEffects.begin();
	     it != sideEffects.end();
	     it++) {
		if (dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			if (acc == StateMachineState::noLoads)
				acc = StateMachineState::singleLoad;
			else
				return StateMachineState::multipleLoads;
		}
	}
	return target->roughLoadCount(acc);
}

void
ppStateMachineSideEffectMemoryAccess(StateMachineSideEffectMemoryAccess *smsema, FILE *f)
{
	fprintf(f, "{%d:0x%lx}", smsema->rip.thread, smsema->rip.rip);
}

void
StateMachine::selectSingleCrashingPath(void)
{
	root = root->selectSingleCrashingPath();
}

void
FreeVariableMap::applyTransformation(IRExprTransformer &x, bool *done_something)
{
	for (map_t::iterator it = content->begin();
	     it != content->end();
	     it++)
		it.set_value(x.transformIRExpr(it.value(), done_something));
}

class mentionsBindersTransformer : public IRExprTransformer {
public:
	IRExpr *transformIex(IRExpr::Binder *e) { res = true; return NULL; }
	bool res;
	mentionsBindersTransformer() : res(false) {}
};
static bool
mentionsBinders(IRExpr *e)
{
	mentionsBindersTransformer t;
	t.transformIRExpr(e);
	return t.res;
}

void
StateMachine::addGoodPointer(IRExpr *e)
{
	if (mentionsBinders(e)) /* Don't want to mark anything as a
				   good pointer if it depends on
				   binders, since they can be changed
				   by other threads */
		return;
	e = simplifyIRExpr(e, AllowableOptimisations::defaultOptimisations);
	if (e->tag == Iex_Const) /* Not much point in retaining
				  * constant expressions. */
		return;
	for (auto it = goodPointers.begin(); it != goodPointers.end(); it++)
		if (definitelyEqual(*it, e, AllowableOptimisations::defaultOptimisations))
			return;
	goodPointers.push(e);
}
