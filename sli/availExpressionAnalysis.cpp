/* Available expression analysis on memory locations.  This isn't
   included in the normal optimise() operation because it's
   context-sensitive, and therefore isn't allowed to mutate nodes
   in-place. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "libvex_prof.hpp"

namespace _availExpressionAnalysis {
/* Unconfuse emacs */
#if 0
}
#endif

/* We allow at most 5 assertions to be available at any given point in
 * the state machines, so as to reduce the risk of dependency
 * explosion.  If we go over that then we keep the ones which are
 * earlier in the machine, for two reasons:
 *
 * 1) It's often most useful, as the earlier assumptions are generally
 * ones which have been recently introduced, while later ones have
 * been there a while so have probably already been used as we move
 * backwards through the program.
 * 2) It's much easier to implement.
 */
#define MAX_LIVE_ASSERTIONS 5

class findAllSideEffectsVisitor : public StateMachineTransformer {
	StateMachineSideEffect *transformSideEffect(StateMachineSideEffect *smse, bool *)
	{
		out.insert(smse);
		return smse;
	}
	IRExpr *transformIRExpr(IRExpr *e, bool *)
	{
		return e;
	}
public:
	std::set<StateMachineSideEffect *> &out;
	findAllSideEffectsVisitor(std::set<StateMachineSideEffect *> &o)
		: out(o)
	{}
};
static void
findAllSideEffects(StateMachine *sm, std::set<StateMachineSideEffect *> &out)
{
	findAllSideEffectsVisitor v(out);
	v.transform(sm);
}

class avail_t {
public:
	std::set<StateMachineSideEffect *> sideEffects;
	std::set<IRExpr *> assertFalse;
	std::map<threadAndRegister, IRExpr *, threadAndRegister::fullCompare> registers;

	void clear() { sideEffects.clear(); assertFalse.clear(); registers.clear(); }
	void makeFalse(IRExpr *expr);
	void dereference(IRExpr *ptr);
	/* Go through and remove anything which isn't also present in
	   other.  Returns true if we did anything, and false
	   otherwise. */
	bool intersect(const avail_t &other);

	bool operator !=(const avail_t &other) const;

	void calcRegisterMap();

	void invalidateRegister(threadAndRegister reg, StateMachineSideEffect *preserve);

	int nr_asserts() const {
		int cntr = 0;
		for (auto it = sideEffects.begin(); it != sideEffects.end(); it++)
			if ((*it)->type == StateMachineSideEffect::AssertFalse)
				cntr++;
		return cntr;
	}
	void print(FILE *f);
};

void
avail_t::print(FILE *f)
{
	fprintf(f, "Available side effects:\n");
	for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
		fprintf(f, "\t");
		(*it)->prettyPrint(f);
		fprintf(f, "\n");
	}
	fprintf(f, "Asserted false:\n");
	for (auto it = assertFalse.begin(); it != assertFalse.end(); it++) {
		fprintf(f, "\t");
		ppIRExpr(*it, f);
		fprintf(f, "\n");
	}
}

void
avail_t::makeFalse(IRExpr *expr)
{
	if (expr->tag == Iex_Const)
		return;
	for (auto it = assertFalse.begin();
	     it != assertFalse.end();
	     it++)
		if (definitelyEqual(*it, expr, AllowableOptimisations::defaultOptimisations))
			return;
	assertFalse.insert(expr);
}

void
avail_t::dereference(IRExpr *addr)
{
	if (TIMEOUT)
		return;
	IRExpr *badPtr = IRExpr_Unop(Iop_BadPtr, addr);
	badPtr = simplifyIRExpr(badPtr, AllowableOptimisations::defaultOptimisations);
	makeFalse(badPtr);
}

bool
avail_t::intersect(const avail_t &other)
{
	bool res = false;
	for (std::set<StateMachineSideEffect *>::iterator it = sideEffects.begin();
	     it != sideEffects.end();
		) {
		if (other.sideEffects.count(*it) == 0) {
			res = true;
			sideEffects.erase(it++); 
		} else {
			it++;
		}
	}
	for (auto it = assertFalse.begin();
	     it != assertFalse.end();
		) {
		bool purge = true;
		for (auto it2 = other.assertFalse.begin();
		     purge && it2 != other.assertFalse.end();
		     it2++) {
			if (definitelyEqual(*it, *it2, AllowableOptimisations::defaultOptimisations))
				purge = false;
		}
		if (purge) {
			res = true;
			assertFalse.erase(it++);
		} else {
			it++;
		}
	}
	return res;
}

void
avail_t::invalidateRegister(threadAndRegister reg, StateMachineSideEffect *preserve)
{
	class _ : public StateMachineTransformer {
		bool res;
		threadAndRegister reg;
		StateMachineSideEffect *preserve;
		IRExpr *transformIex(IRExprGet *e) {
			if (threadAndRegister::fullEq(e->reg, reg))
				res = true;
			return NULL;
		}
		StateMachineSideEffectLoad *transformOneSideEffect(StateMachineSideEffectLoad *l,
								   bool *done_something)
		{
			if (l != preserve && threadAndRegister::fullEq(l->target, reg)) {
				res = true;
				return NULL;
			}
			return StateMachineTransformer::transformOneSideEffect(l, done_something);
		}
		StateMachineSideEffectCopy *transformOneSideEffect(StateMachineSideEffectCopy *l,
								   bool *done_something)
		{
			if (l != preserve && threadAndRegister::fullEq(l->target, reg)) {
				res = true;
				return NULL;
			}
			return StateMachineTransformer::transformOneSideEffect(l, done_something);
		}
	public:
		_(threadAndRegister _reg, StateMachineSideEffect *_preserve)
			: reg(_reg), preserve(_preserve)
		{}
		bool operator()(StateMachineSideEffect *se)
		{
			bool ignore;
			res = false;
			transformSideEffect(se, &ignore);
			return res;
		}
		bool operator()(IRExpr *e)
		{
			bool ignore;
			res = false;
			transformIRExpr(e, &ignore);
			return res;
		}
	} isPresent(reg, preserve);

	for (auto it = sideEffects.begin(); it != sideEffects.end(); ) {
		if (isPresent(*it)) {
			sideEffects.erase(it++);
		} else {
			it++;
		}
	}
	for (auto it = assertFalse.begin(); it != assertFalse.end(); ) {
		if (isPresent(*it))
			assertFalse.erase(it++);
		else
			it++;
	}
	for (auto it = registers.begin(); it != registers.end(); ) {
		if (isPresent(it->second))
			registers.erase(it++);
		else
			it++;
	}
}

bool
avail_t::operator!=(const avail_t &other) const
{
	return sideEffects != other.sideEffects || assertFalse != other.assertFalse;
}

void
avail_t::calcRegisterMap()
{
	registers.clear();
	for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
		StateMachineSideEffect *se = *it;
		if (se->type == StateMachineSideEffect::Copy) {
			StateMachineSideEffectCopy *sep = (StateMachineSideEffectCopy *)se;
			registers[sep->target] = sep->value;
		} else if (se->type == StateMachineSideEffect::AssertFalse) {
			StateMachineSideEffectAssertFalse *seaf = (StateMachineSideEffectAssertFalse *)se;
			makeFalse(seaf->value);
		}
	}
}

static void
updateAvailSetForSideEffect(avail_t &outputAvail, StateMachineSideEffect *smse,
			    const AllowableOptimisations &opt,
			    const Oracle::RegisterAliasingConfiguration &alias,
			    OracleInterface *oracle)
{
	if (TIMEOUT)
		return;
	switch (smse->type) {
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectStore *smses =
			dynamic_cast<StateMachineSideEffectStore *>(smse);
		assert(smses);
		/* Eliminate anything which is killed */
		for (std::set<StateMachineSideEffect *>::iterator it = outputAvail.sideEffects.begin();
		     it != outputAvail.sideEffects.end();
			) {
			StateMachineSideEffectStore *smses2 =
				dynamic_cast<StateMachineSideEffectStore *>(*it);
			StateMachineSideEffectLoad *smsel2 =
				dynamic_cast<StateMachineSideEffectLoad *>(*it);
			IRExpr *addr;
			if (smses2)
				addr = smses2->addr;
			else if (smsel2)
				addr = smsel2->addr;
			else
				addr = NULL;

			if ( addr &&
			     alias.ptrsMightAlias(addr, smses->addr, opt.freeVariablesMightAccessStack) &&
			     ((smses2 && oracle->memoryAccessesMightAlias(smses2, smses)) ||
			      (smsel2 && oracle->memoryAccessesMightAlias(smsel2, smses))) &&
			     !definitelyNotEqual( addr,
						  smses->addr,
						  opt) )
				outputAvail.sideEffects.erase(it++);
			else
				it++;
		}
		/* Introduce the store which was generated. */
		if (opt.assumeNoInterferingStores ||
		    oracle->storeIsThreadLocal(smses))
			outputAvail.sideEffects.insert(smses);
		outputAvail.dereference(smses->addr);
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec =
			dynamic_cast<StateMachineSideEffectCopy *>(smse);
		assert(smsec);
		outputAvail.sideEffects.insert(smsec);
		outputAvail.invalidateRegister(smsec->target, smsec);
		break;
	}
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel =
			dynamic_cast<StateMachineSideEffectLoad *>(smse);
		outputAvail.sideEffects.insert(smsel);
		outputAvail.dereference(smsel->addr);
		outputAvail.invalidateRegister(smsel->target, smsel);
		break;
	}
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(smse);
		outputAvail.makeFalse(smseaf->value);
		break;
	}
	case StateMachineSideEffect::Unreached:
		break;
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *p =
			(StateMachineSideEffectPhi *)smse;
		outputAvail.sideEffects.insert(p);
		outputAvail.invalidateRegister(p->reg, smse);
		break;
	}
		
	}
	outputAvail.calcRegisterMap();
}

class applyAvailTransformer : public IRExprTransformer {
public:
	const avail_t &avail;
	const bool use_assumptions;
	IRExpr *transformIex(IRExprGet *e) {
		auto it = avail.registers.find(e->reg);
		if (it != avail.registers.end())
			return it->second;
		return IRExprTransformer::transformIex(e);
	}
	IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
		if (use_assumptions) {
			for (std::set<IRExpr *>::iterator it = avail.assertFalse.begin();
			     it != avail.assertFalse.end();
			     it++) {
				if (definitelyEqual(*it, e,  AllowableOptimisations::defaultOptimisations)) {
					*done_something = true;
					return IRExpr_Const(IRConst_U1(0));
				}
			}
		}
		return IRExprTransformer::transformIRExpr(e, done_something);
	}
	applyAvailTransformer(const avail_t &_avail, bool _use_assumptions)
		: avail(_avail), use_assumptions(_use_assumptions)
	{}
};
static IRExpr *
applyAvailSet(const avail_t &avail, IRExpr *expr, bool use_assumptions, bool *done_something)
{
	applyAvailTransformer aat(avail, use_assumptions);
	return aat.transformIRExpr(expr, done_something);
}

/* Slightly misnamed: this also propagates copy operations.  Also, it
   doesn't so much eliminate loads are replace them with copies of
   already-loaded values. */
static StateMachineState *buildNewStateMachineWithLoadsEliminated(
	StateMachineState *sm,
	std::map<StateMachineState *, avail_t> &availMap,
	std::map<StateMachineState *, StateMachineState *> &memo,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration &aliasing,
	OracleInterface *oracle,
	bool *done_something);
static StateMachineEdge *
buildNewStateMachineWithLoadsEliminated(
	StateMachineEdge *sme,
	const avail_t &initialAvail,
	std::map<StateMachineState *, avail_t> &availMap,
	std::map<StateMachineState *, StateMachineState *> &memo,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration &aliasing,
	OracleInterface *oracle,
	bool *done_something)
{
	if (TIMEOUT)
		return sme;
	StateMachineEdge *res =
		new StateMachineEdge(buildNewStateMachineWithLoadsEliminated(sme->target, availMap, memo, opt, aliasing, oracle,
									     done_something));

	avail_t currentlyAvailable(initialAvail);
	
	for (std::vector<StateMachineSideEffect *>::const_iterator it =
		     sme->sideEffects.begin();
	     !TIMEOUT && it != sme->sideEffects.end();
	     it++) {
		StateMachineSideEffect *newEffect;

		newEffect = NULL;

		switch ((*it)->type) {
		case StateMachineSideEffect::Store: {
			StateMachineSideEffectStore *smses =
				dynamic_cast<StateMachineSideEffectStore *>(*it);
			IRExpr *newAddr, *newData;
			bool doit = false;
			newAddr = applyAvailSet(currentlyAvailable, smses->addr, false, &doit);
			newData = applyAvailSet(currentlyAvailable, smses->data, false, &doit);
			if (doit) {
				newEffect = new StateMachineSideEffectStore(
					newAddr, newData, smses->rip);
				*done_something = true;
			} else {
				newEffect = smses;
			}
			break;
		}
		case StateMachineSideEffect::Load: {
			StateMachineSideEffectLoad *smsel =
				dynamic_cast<StateMachineSideEffectLoad *>(*it);
			IRExpr *newAddr;
			bool doit = false;
			newAddr = applyAvailSet(currentlyAvailable, smsel->addr, false, &doit);
			for (std::set<StateMachineSideEffect *>::iterator it2 = currentlyAvailable.sideEffects.begin();
			     !newEffect && it2 != currentlyAvailable.sideEffects.end();
			     it2++) {
				StateMachineSideEffectStore *smses2 =
					dynamic_cast<StateMachineSideEffectStore *>(*it2);
				StateMachineSideEffectLoad *smsel2 =
					dynamic_cast<StateMachineSideEffectLoad *>(*it2);
				if ( smses2 &&
				     aliasing.ptrsMightAlias(smses2->addr, newAddr, opt.freeVariablesMightAccessStack) &&
				     definitelyEqual(smses2->addr, newAddr, opt) ) {
					newEffect =
						new StateMachineSideEffectCopy(
							smsel->target,
							smses2->data);
				} else if ( smsel2 &&
					    aliasing.ptrsMightAlias(smsel2->addr, newAddr, opt.freeVariablesMightAccessStack) &&
					    definitelyEqual(smsel2->addr, newAddr, opt) ) {
					newEffect =
						new StateMachineSideEffectCopy(
							smsel->target,
							new IRExprGet(smsel2->target, Ity_I64));
				}
			}
			if (!newEffect && doit)
				newEffect = new StateMachineSideEffectLoad(
					smsel->target, newAddr, smsel->rip);
			if (!newEffect)
				newEffect = *it;
			if (newEffect != *it)
				*done_something = true;
			break;
		}
		case StateMachineSideEffect::Copy: {
			StateMachineSideEffectCopy *smsec =
				dynamic_cast<StateMachineSideEffectCopy *>(*it);
			IRExpr *newValue;
			bool doit = false;
			newValue = applyAvailSet(currentlyAvailable, smsec->value, false, &doit);
			if (doit)
				newEffect = new StateMachineSideEffectCopy(
					smsec->target, newValue);
			else
				newEffect = *it;
			break;
		}
		case StateMachineSideEffect::Unreached:
			newEffect = *it;
			break;
		case StateMachineSideEffect::AssertFalse: {
			StateMachineSideEffectAssertFalse *smseaf =
				dynamic_cast<StateMachineSideEffectAssertFalse *>(*it);
			IRExpr *newVal;
			bool doit = false;
			if (currentlyAvailable.nr_asserts() < MAX_LIVE_ASSERTIONS) {
				newVal = applyAvailSet(currentlyAvailable, smseaf->value, true, &doit);
			} else {
				/* We have too many live assertions.
				   That can lead to them holding
				   enormous number of variables live,
				   which isn't much use, so turn this
				   one into a no-op.  It'll get
				   optimised out again later. */
				newVal = IRExpr_Const(IRConst_U1(0));
				doit = true;
			}
			if (doit)
				newEffect = new StateMachineSideEffectAssertFalse(newVal);
			else
				newEffect = *it;
			break;
		}
		case StateMachineSideEffect::Phi:
			newEffect = *it;
			break;
		}
		assert(newEffect);
		updateAvailSetForSideEffect(currentlyAvailable, newEffect, opt, aliasing, oracle);
		res->sideEffects.push_back(newEffect);
	}
	return res;
}
static StateMachineState *
buildNewStateMachineWithLoadsEliminated(
	StateMachineState *sm,
	std::map<StateMachineState *, avail_t> &availMap,
	std::map<StateMachineState *, StateMachineState *> &memo,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration &alias,
	OracleInterface *oracle,
	bool *done_something)
{
	if (dynamic_cast<StateMachineCrash *>(sm) ||
	    dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm) ||
	    dynamic_cast<StateMachineUnreached *>(sm))
		return sm;
	if (memo.count(sm)) {
		/* We rely on whoever it was that set memo[sm] having
		 * also set *done_something if appropriate. */
		return memo[sm];
	}
	avail_t avail(availMap[sm]);
	avail.calcRegisterMap();

	if (StateMachineBifurcate *smb =
	    dynamic_cast<StateMachineBifurcate *>(sm)) {
		StateMachineBifurcate *res;
		bool doit = false;
		res = new StateMachineBifurcate(
			sm->origin,
			applyAvailSet(avail, smb->condition, true, &doit),
			(StateMachineEdge *)NULL, NULL);
		*done_something |= doit;
		memo[sm] = res;
		res->trueTarget = buildNewStateMachineWithLoadsEliminated(
			smb->trueTarget, avail, availMap, memo, opt, alias, oracle,
			done_something);
		res->falseTarget = buildNewStateMachineWithLoadsEliminated(
			smb->falseTarget, avail, availMap, memo, opt, alias, oracle,
			done_something);
		return res;
	} if (StateMachineProxy *smp =
	      dynamic_cast<StateMachineProxy *>(sm)) {
		StateMachineProxy *res;
		res = new StateMachineProxy(sm->origin, (StateMachineEdge *)NULL);
		memo[sm] = res;
		res->target = buildNewStateMachineWithLoadsEliminated(
			smp->target, avail, availMap, memo, opt, alias, oracle,
			done_something);
		return res;
	} else {
		abort();
	}
}

static StateMachine *
buildNewStateMachineWithLoadsEliminated(
	StateMachine *sm,
	std::map<StateMachineState *, avail_t> &availMap,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration &alias,
	OracleInterface *oracle,
	bool *done_something)
{
	std::map<StateMachineState *, StateMachineState *> memo;
	bool d = false;
	StateMachineState *new_root = buildNewStateMachineWithLoadsEliminated(sm->root, availMap, memo, opt, alias, oracle,
									      &d);
	if (d) {
		*done_something = true;
		return new StateMachine(sm, sm->origin, new_root);
	} else {
		return sm;
	}
}

static StateMachine *
availExpressionAnalysis(StateMachine *sm, const AllowableOptimisations &opt,
			const Oracle::RegisterAliasingConfiguration &alias, OracleInterface *oracle,
			bool *done_something)
{
	__set_profiling(availExpressionAnalysis);
	/* Fairly standard available expression analysis.  Each edge
	   in the state machine has two sets of
	   StateMachineSideEffectStores representing the set of things
	   which are available at the start and end of the edge.  We
	   start off with everything available everywhere except at
	   the start node (which has nothing) and then do a Tarski
	   iteration to remove all of the contradictions.  Once we
	   know what's available, it's easy enough to go through and
	   forward all of the remaining stores. */
	/* Minor tweak: the onEntry map is keyed on states rather than
	   edges, since every edge starting at a given state will have
	   the same entry map. */

	/* build the set of potentially-available expressions. */
	avail_t potentiallyAvailable;
	findAllSideEffects(sm, potentiallyAvailable.sideEffects);
	for (std::set<StateMachineSideEffect *>::iterator it = potentiallyAvailable.sideEffects.begin();
	     !TIMEOUT && it != potentiallyAvailable.sideEffects.end();
	     it++) {
		StateMachineSideEffect *smse = *it;
		if (StateMachineSideEffectMemoryAccess *smsema =
		    dynamic_cast<StateMachineSideEffectMemoryAccess *>(smse)) {
			potentiallyAvailable.dereference(smsema->addr);
		} else if (StateMachineSideEffectAssertFalse *smseaf =
			   dynamic_cast<StateMachineSideEffectAssertFalse *>(smse)) {
			potentiallyAvailable.makeFalse(smseaf->value);
		}
	}

	/* If we're not executing atomically, stores to
	   non-thread-local memory locations are never considered to
	   be available. */
	if (!opt.assumeNoInterferingStores) {
		for (std::set<StateMachineSideEffect *>::iterator it = potentiallyAvailable.sideEffects.begin();
		     !TIMEOUT && it != potentiallyAvailable.sideEffects.end();
			) {
			StateMachineSideEffectStore *smses =
				dynamic_cast<StateMachineSideEffectStore *>(*it);
			StateMachineSideEffectLoad *smsel =
				dynamic_cast<StateMachineSideEffectLoad *>(*it);
			if ( (smses && !oracle->storeIsThreadLocal(smses)) ||
			     (smsel && !oracle->loadIsThreadLocal(smsel)) ) {
				potentiallyAvailable.sideEffects.erase(it++);
			} else {
				it++;
			}
		}
	}

	/* build the initial availability map.  We start by assuming
	 * that everything is available everywhere, except that at the
	 * start of the very first state nothing is available, and
	 * then use a Tarski iteration to make everything
	 * consistent. */
	std::set<StateMachineEdge *> allEdges;
	std::set<StateMachineState *> allStates;
	findAllEdges(sm, allEdges);
	findAllStates(sm, allStates);
	std::map<StateMachineState *, avail_t> availOnEntry;
	std::map<StateMachineEdge *, avail_t> availOnExit;
	for (std::set<StateMachineEdge *>::iterator it = allEdges.begin();
	     !TIMEOUT && it != allEdges.end();
	     it++)
		availOnExit[*it] = potentiallyAvailable;
	for (std::set<StateMachineState *>::iterator it = allStates.begin();
	     !TIMEOUT && it != allStates.end();
	     it++)
		availOnEntry[*it] = potentiallyAvailable;
	availOnEntry[sm->root].clear();

	std::set<StateMachineState *> statesNeedingRefresh(allStates);

	/* Tarski iteration.  */
	bool progress;
	do {
		progress = false;

		if (TIMEOUT)
			return sm;

		/* Update the set of things which are available on
		   entry.  This means walking the set of edges and
		   looking at the targets.  If there's something which
		   is available at the start of the target, but not at
		   the end of this edge, remove it from the target. */
		for (std::set<StateMachineEdge *>::iterator it = allEdges.begin();
		     it != allEdges.end();
		     it++) {
			StateMachineEdge *edge = *it;
			StateMachineState *target = edge->target;
			avail_t &avail_at_end_of_edge(availOnExit[edge]);
			avail_t &avail_at_start_of_target(availOnEntry[target]);
			if (avail_at_start_of_target.intersect(avail_at_end_of_edge)) {
				progress = true;
				statesNeedingRefresh.insert(target);
			}
		}

		/* Now go through and update the avail-on-exit set.
		   Use a slightly weird-looking iteration over states
		   instead of over edges because that makes things a
		   bit easier. */
		for (std::set<StateMachineState *>::iterator it = statesNeedingRefresh.begin();
		     it != statesNeedingRefresh.end();
		     it++) {
			if (dynamic_cast<StateMachineCrash *>(*it) ||
			    dynamic_cast<StateMachineNoCrash *>(*it) ||
			    dynamic_cast<StateMachineStub *>(*it) ||
			    dynamic_cast<StateMachineUnreached *>(*it))
				continue;
			StateMachineEdge *edges[2];
			int nr_edges;
			if (StateMachineBifurcate *smb =
			    dynamic_cast<StateMachineBifurcate *>(*it)) {
				edges[0] = smb->trueTarget;
				edges[1] = smb->falseTarget;
				nr_edges = 2;
			} else if (StateMachineProxy *smp =
				   dynamic_cast<StateMachineProxy *>(*it)) {
				edges[0] = smp->target;
				nr_edges = 1;
			} else {
				abort();
			}
			for (int x = 0; x < nr_edges; x++) {
				StateMachineEdge *edge = edges[x];
				assert(availOnEntry.count(*it));
				avail_t outputAvail(availOnEntry[*it]);

				/* Build the output set. */
				for (std::vector<StateMachineSideEffect *>::const_iterator it2 =
					     edge->sideEffects.begin();
				     !TIMEOUT && it2 != edge->sideEffects.end();
				     it2++)
					updateAvailSetForSideEffect(outputAvail, *it2,
								    opt, alias, oracle);
				avail_t &currentAvail(availOnExit[edge]);
				if (!progress && currentAvail != outputAvail)
					progress = true;
				currentAvail = outputAvail;
			}
		}
		statesNeedingRefresh.clear();
	} while (progress);

	/* So after all that we now have a complete map of what's
	   available where.  Given that, we should be able to
	   construct a new state machine with redundant loads replaced
	   with copy side effects. */
	return buildNewStateMachineWithLoadsEliminated(
		sm,
		availOnEntry,
		opt,
		alias,
		oracle,
		done_something);
}

/* End of namespace */
}

StateMachine *
availExpressionAnalysis(StateMachine *sm, const AllowableOptimisations &opt,
			const Oracle::RegisterAliasingConfiguration &alias, OracleInterface *oracle,
			bool *done_something)
{
	return _availExpressionAnalysis::availExpressionAnalysis(sm, opt, alias, oracle, done_something);
}
