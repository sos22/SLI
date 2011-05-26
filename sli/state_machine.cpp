#include <err.h>

#include <map>

#include "sli.h"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "simplify_irexpr.hpp"

#include "libvex_parse.h"


static void findUsedBinders(IRExpr *e, std::set<Int> &, const AllowableOptimisations &);

VexPtr<StateMachineSideEffectUnreached, &ir_heap> StateMachineSideEffectUnreached::_this;
Int StateMachineSideEffectLoad::next_key;
VexPtr<StateMachineUnreached, &ir_heap> StateMachineUnreached::_this;
VexPtr<StateMachineCrash, &ir_heap> StateMachineCrash::_this;
VexPtr<StateMachineNoCrash, &ir_heap> StateMachineNoCrash::_this;
AllowableOptimisations AllowableOptimisations::defaultOptimisations(true, false, false, false);

StateMachine *
StateMachineBifurcate::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
{
	if (trueTarget->target == StateMachineUnreached::get()) {
		*done_something = true;
		if (falseTarget->target == StateMachineUnreached::get())
			return StateMachineUnreached::get();
		else
			return new StateMachineProxy(origin, falseTarget->optimise(opt, oracle, done_something));
	}
	if (falseTarget->target == StateMachineUnreached::get()) {
		*done_something = true;
		return new StateMachineProxy(origin, trueTarget->optimise(opt, oracle, done_something));
	}
	condition = optimiseIRExprFP(condition, opt, done_something);
	if (condition->tag == Iex_Const) {
		*done_something = true;
		if (condition->Iex.Const.con->Ico.U1)
			return new StateMachineProxy(origin, trueTarget->optimise(opt, oracle, done_something));
		else
			return new StateMachineProxy(origin, falseTarget->optimise(opt, oracle, done_something));
	}
	trueTarget = trueTarget->optimise(opt, oracle, done_something);
	falseTarget = falseTarget->optimise(opt, oracle, done_something);

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
					Iop_And1,
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
					Iop_Or1,
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
StateMachineSideEffectStore::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
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
	smsel_addr = optimiseIRExprFP(smsel_addr, AllowableOptimisations::defaultOptimisations, &ign);
}
StateMachineSideEffect *
StateMachineSideEffectLoad::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
{
	smsel_addr = optimiseIRExprFP(smsel_addr, opt, done_something);
	if (isBadAddress(smsel_addr, opt, oracle)) {
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
	::findUsedBinders(smsel_addr, s, opt);
}

StateMachineSideEffect *
StateMachineSideEffectCopy::optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
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

StateMachineEdge *
StateMachineEdge::optimise(const AllowableOptimisations &opt,
			   Oracle *oracle,
			   bool *done_something)
{
	if (StateMachineProxy *smp =
	    dynamic_cast<StateMachineProxy *>(target)) {
		StateMachineEdge *sme =
			new StateMachineEdge(smp->target->target);
		sme->sideEffects = sideEffects;
		for (std::vector<StateMachineSideEffect *>::iterator it =
			     smp->target->sideEffects.begin();
		     it != smp->target->sideEffects.end();
		     it++)
			sme->sideEffects.push_back(*it);
		*done_something = true;
		return sme->optimise(opt, oracle, done_something);
	}
	target = target->optimise(opt, oracle, done_something);

	std::vector<StateMachineSideEffect *>::iterator it;

	for (it = sideEffects.begin(); it != sideEffects.end(); it++)
		*it = (*it)->optimise(opt, oracle, done_something);

	/* Try to forward stuff from stores to loads wherever
	   possible.  We don't currently do this inter-state, because
	   that's moderately tricky. */
	std::set<std::pair<IRExpr *, IRExpr *> > availExpressions;
	for (it = sideEffects.begin(); it != sideEffects.end(); it++) {
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(*it)) {
			/* If the store isn't thread local, and we're
			   not in execute-atomically mode, we can't do
			   any forwarding at all. */
			if (!opt.assumeExecutesAtomically &&
			    !oracle->storeIsThreadLocal(smses))
				continue;

			/* Kill anything which might be clobbered by
			   this store. */
			for (std::set<std::pair<IRExpr *, IRExpr *> >::iterator it2 =
				     availExpressions.begin();
			     it2 != availExpressions.end();
				) {
				IRExpr *addr = it2->first;
				if (!definitelyNotEqual(addr, smses->addr, opt))
					availExpressions.erase(it2++);
				else
					it2++;
			}
			/* And add this one to the set */
			availExpressions.insert( std::pair<IRExpr *, IRExpr *>(
							 smses->addr,
							 smses->data) );
		} else if (StateMachineSideEffectLoad *smsel =
			   dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			/* If the load was definitely satisfied by a
			   known store, eliminate it. */
			for (std::set<std::pair<IRExpr *, IRExpr *> >::iterator it2 =
				     availExpressions.begin();
			     it2 != availExpressions.end();
			     it2++) {
				if (definitelyEqual(it2->first, smsel->smsel_addr, opt)) {
					*it = new StateMachineSideEffectCopy(smsel->key,
									     it2->second);
					*done_something = true;
					break;
				}
			}			
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

	/* Now cull completely redundant stores. */
	std::set<IRExpr *> loadedAddresses;
	target->findLoadedAddresses(loadedAddresses, opt);
	std::set<Int> usedBinders;
	target->findUsedBinders(usedBinders, opt);

	it = sideEffects.end();
	while (it != sideEffects.begin()) {
		bool isDead = false;
		it--;
		(*it)->optimise(opt, oracle, done_something);
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(*it)) {
			if (opt.ignoreSideEffects ||
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
			if (!usedBinders.count(smsec->key))
				isDead = true;
		}
		if (StateMachineSideEffectLoad *smsel =
		    dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			if (!usedBinders.count(smsel->key))
				isDead = true;
		}
		if (isDead) {
			*done_something = true;
			it = sideEffects.erase(it);
		} else {
			(*it)->updateLoadedAddresses(loadedAddresses, opt);
			(*it)->findUsedBinders(usedBinders, opt);
		}
	}

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
	}
	abort();
}

static void
buildStateLabelTable(const StateMachine *sm, std::map<const StateMachine *, int> &table,
		     std::vector<const StateMachine *> &states)
{
	std::vector<const StateMachine *> toEmit;
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
printStateMachine(const StateMachine *sm, FILE *f)
{
	std::map<const StateMachine *, int> labels;
	std::vector<const StateMachine *> states;

	buildStateLabelTable(sm, labels, states);
	for (std::vector<const StateMachine *>::iterator it = states.begin();
	     it != states.end();
	     it++) {
		fprintf(f, "l%d: ", labels[*it]);
		(*it)->prettyPrint(f, labels);
		fprintf(f, "\n");
	}
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

typedef std::pair<StateMachine *, StateMachine *> st_pair_t;
typedef std::pair<StateMachineEdge *, StateMachineEdge *> st_edge_pair_t;

/* Note that this assumes that bisimilarity reduction, and all the
   other usual optimisations, have already been run! */
static bool stateMachinesBisimilar(StateMachine *a, StateMachine *b,
				   std::set<st_edge_pair_t> &bisimilarEdges,
				   std::set<st_pair_t> &bisimilarStates,
				   const AllowableOptimisations &opt);
static bool
stateMachineEdgesBisimilar(StateMachineEdge *a,
			   StateMachineEdge *b,
			   std::set<st_edge_pair_t> &bisimilarEdges,
			   std::set<st_pair_t> &bisimilarStates,
			   const AllowableOptimisations &opt)
{
	if (bisimilarEdges.count(st_edge_pair_t(a, b)))
		return true;
	bisimilarEdges.insert(st_edge_pair_t(a, b));
	if (a->sideEffects.size() != b->sideEffects.size())
		return false;
	for (unsigned x = 0; x < a->sideEffects.size(); x++) {
		if (!sideEffectsBisimilar(a->sideEffects[x],
					  b->sideEffects[x],
					  opt))
			return false;
	}
	return stateMachinesBisimilar(a->target, b->target, bisimilarEdges,
				      bisimilarStates, opt);
}
static bool
stateMachinesBisimilar(StateMachine *a, StateMachine *b,
		       std::set<st_edge_pair_t> &bisimilarEdges,
		       std::set<st_pair_t> &bisimilarStates,
		       const AllowableOptimisations &opt)
{
	if (bisimilarStates.count(st_pair_t(a, b)))
		return true;
	/* We advance on the assumption that the states *are*
	 * bisimilar, and rely on the fact that bisimilarity has the
	 * right kind of monotonicity for that to actually work. */
	bisimilarStates.insert(st_pair_t(a, b));
	if (dynamic_cast<StateMachineUnreached *>(a))
		return !!dynamic_cast<StateMachineUnreached *>(b);
	if (dynamic_cast<StateMachineCrash *>(a))
		return !!dynamic_cast<StateMachineCrash *>(b);
	if (dynamic_cast<StateMachineNoCrash *>(a))
		return !!dynamic_cast<StateMachineNoCrash *>(b);
	if (StateMachineProxy *smpA = dynamic_cast<StateMachineProxy *>(a)) {
		StateMachineProxy *smpB = dynamic_cast<StateMachineProxy *>(b);
		if (!smpB)
			return false;
		return stateMachineEdgesBisimilar(smpA->target, smpB->target,
						  bisimilarEdges, bisimilarStates,
						  opt);
	}
	if (StateMachineBifurcate *smbA = dynamic_cast<StateMachineBifurcate *>(a)) {
		StateMachineBifurcate *smbB = dynamic_cast<StateMachineBifurcate *>(b);
		if (!smbB)
			return false;
		if (!definitelyEqual(smbA->condition, smbB->condition, opt))
			return false;
		return stateMachineEdgesBisimilar(smbA->trueTarget, smbB->trueTarget,
						  bisimilarEdges, bisimilarStates, opt) &&
		       stateMachineEdgesBisimilar(smbA->falseTarget, smbB->falseTarget,
						  bisimilarEdges, bisimilarStates, opt);
	}
	abort();
}
bool
stateMachinesBisimilar(StateMachine *a, StateMachine *b)
{
	std::set<st_edge_pair_t> bisimilarEdges;
	std::set<st_pair_t> bisimilarStates;

	return stateMachinesBisimilar(a, b, bisimilarEdges, bisimilarStates,
				      AllowableOptimisations::defaultOptimisations);
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
			definitelyEqual(smsel1->smsel_addr, smsel2->smsel_addr, opt);
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

static bool
parseStateMachineSideEffect(StateMachineSideEffect **out,
			    const char *str,
			    const char **suffix)
{
	const char *str2;
	if (parseThisString("<unreached>", str, suffix)) {
		*out = StateMachineSideEffectUnreached::get();
		return true;
	}
	IRExpr *addr;
	IRExpr *data;
	unsigned long rip;
	if (parseThisString("*(", str, &str2) &&
	    parseIRExpr(&addr, str2, &str2) &&
	    parseThisString(") <- ", str2, &str2) &&
	    parseIRExpr(&data, str2, &str2) &&
	    parseThisString(" @ ", str2, &str2) &&
	    parseHexUlong(&rip, str2, suffix)) {
		*out = new StateMachineSideEffectStore(addr, data, rip);
		return true;
	}
	int key;
	if (parseThisChar('B', str, &str2) &&
	    parseDecimalInt(&key, str2, &str2) &&
	    parseThisString(" <- *(", str2, &str2) &&
	    parseIRExpr(&addr, str2, &str2) &&
	    parseThisString(")@", str2, &str2) &&
	    parseHexUlong(&rip, str2, suffix)) {
		*out = new StateMachineSideEffectLoad(key, addr, rip);
		return true;
	}
	if (parseThisChar('B', str, &str2) &&
	    parseDecimalInt(&key, str2, &str2) &&
	    parseThisString(" = (", str2, &str2) &&
	    parseIRExpr(&data, str2, &str2) &&
	    parseThisChar(')', str2, suffix)) {
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
		      const char **suffix)
{
	int targetLabel;
	std::vector<StateMachineSideEffect *> sideEffects;
	if (parseThisChar('{', str, &str)) {
		while (1) {
			StateMachineSideEffect *se;
			if (!parseStateMachineSideEffect(&se, str, &str))
				return false;
			sideEffects.push_back(se);
			if (parseThisString(sep, str, &str))
				continue;
			if (!parseThisString("} ", str, &str))
				return false;
			break;
		}
	}
	if (!parseThisChar('l', str, &str) ||
	    !parseDecimalInt(&targetLabel, str, suffix))
		return false;
	*out = new StateMachineEdge((StateMachine *)targetLabel);
	(*out)->sideEffects = sideEffects;
	return true;
}

static bool
parseStateMachineState(StateMachine **out,
		       const char *str,
		       const char **suffix)
{
	if (parseThisString("<unreached>", str, suffix)) {
		*out = StateMachineUnreached::get();
		return true;
	}
	if (parseThisString("<crash>", str, suffix)) {
		*out = StateMachineCrash::get();
		return true;
	}
	if (parseThisString("<survive>", str, suffix)) {
		*out = StateMachineNoCrash::get();
		return true;
	}
	unsigned long origin;
	IRExpr *target;
	const char *str2;
	if (parseThisChar('<', str, &str2) &&
	    parseHexUlong(&origin, str2, &str2) &&
	    parseIRExpr(&target, str2, &str2) &&
	    parseThisChar('>', str2, suffix)) {
		*out = new StateMachineStub(origin, target);
		return true;
	}
	StateMachineEdge *target1;
	if (parseThisChar('{', str, &str2) &&
	    parseHexUlong(&origin, str2, &str2) &&
	    parseThisChar(':', str2, &str2) &&
	    parseStateMachineEdge(&target1, "\n  ", str2, &str2) &&
	    parseThisChar('}', str2, suffix)) {
		*out = new StateMachineProxy(origin, target1);
		return true;
	}
	IRExpr *condition;
	StateMachineEdge *target2;
	if (parseHexUlong(&origin, str, &str2) &&
	    parseThisString(": if (", str2, &str2) &&
	    parseIRExpr(&condition, str2, &str2) &&
	    parseThisString(")\n  then {\n\t", str2, &str2) &&
	    parseStateMachineEdge(&target1, "\n\t", str2, &str2) &&
	    parseThisString("}\n  else {\n\t", str2, &str2) &&
	    parseStateMachineEdge(&target2, "\n\t", str2, &str2) &&
	    parseThisChar('}', str2, suffix)) {
		*out = new StateMachineBifurcate(origin, condition, target1, target2);
		return true;
	}
	return false;
}

static bool
parseOneState(std::map<int, StateMachine *> &out,
	      const char *str,
	      const char **suffix)
{
	int label;
	StateMachine *res;

	if (!parseThisChar('l', str, &str) ||
	    !parseDecimalInt(&label, str, &str) ||
	    out.count(label) ||
	    !parseThisString(": ", str, &str) ||
	    !parseStateMachineState(&res, str, &str) ||
	    !parseThisChar('\n', str, &str))
		return false;
	out[label] = res;
	*suffix = str;
	return true;
}

bool
parseStateMachine(StateMachine **out, const char *str, const char **suffix)
{
	std::map<int, StateMachine *> labelToState;

	while (*str) {
		if (!parseOneState(labelToState, str, &str))
			return false;
	}
	if (!labelToState.count(1))
		return false;
	for (std::map<int, StateMachine *>::iterator it = labelToState.begin();
	     it != labelToState.end();
	     it++) {
		if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(it->second)) {
			smp->target->target =
				labelToState[(int)(unsigned long)smp->target->target];
			assert(smp->target->target);
		} else if (StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(it->second)) {
			smb->trueTarget->target =
				labelToState[(int)(unsigned long)smb->trueTarget->target];
			smb->falseTarget->target =
				labelToState[(int)(unsigned long)smb->falseTarget->target];
			assert(smb->trueTarget->target);
			assert(smb->falseTarget->target);
		} else {
			assert(dynamic_cast<StateMachineTerminal *>(it->second));
		}
	}
	*suffix = str;
	*out = labelToState[1];
	return true;
}

StateMachine *
readStateMachine(int fd)
{
	char *content = readfile(fd);
	const char *end;
	StateMachine *res;
	if (!parseStateMachine(&res, content, &end) || *end)
		errx(1, "parsing state machine:\n%s", content);
	free(content);
	return res;
}
