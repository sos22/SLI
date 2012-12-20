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

/* Debug options: */
#ifdef NDEBUG
#define dump_avail_table 0 /* Dump the available expression table
			    * after we build it */
#define debug_substitutions 0 /* Debug to do with actually using the
				 table. */
#else
static int dump_avail_table = 0, debug_substitutions = 0;
#endif

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

class avail_t {
	std::set<StateMachineSideEffect *> sideEffects;
public:
	std::set<StateMachineSideEffect *>::iterator beginSideEffects() { return sideEffects.begin(); }
	std::set<StateMachineSideEffect *>::iterator endSideEffects() { return sideEffects.end(); }
	void insertSideEffect(StateMachineSideEffect *smse) {
		sideEffects.insert(smse);
	}
	void eraseSideEffect(std::set<StateMachineSideEffect *>::iterator it) {
		sideEffects.erase(it);
	}

	bbdd *assumption;
	struct registerMapEntry {
		exprbdd *e;
		registerMapEntry()
			: e(NULL)
		{}
		registerMapEntry(exprbdd *_e)
			: e(_e)
		{}
	};
	std::map<threadAndRegister, registerMapEntry> _registers;

	void clear() { sideEffects.clear(); assumption = NULL; _registers.clear(); }
	void makeFalse(bbdd::scope *, bbdd *expr);
	void dereference(SMScopes *scope, exprbdd *ptr, const AllowableOptimisations &opt);
	/* Merge @other into the current availability set.  Returns
	   true if we do anything, and false otherwise. */
	bool mergeIntersection(bbdd::scope *scope, const avail_t &other);
	bool mergeUnion(bbdd::scope *scope, const avail_t &other);

	void calcRegisterMap(bbdd::scope *scope);

	void invalidateRegister(bbdd::scope *scope, threadAndRegister reg, StateMachineSideEffect *preserve);

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
	if (!sideEffects.empty()) {
		fprintf(f, "\tAvailable side effects:\n");
		for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
			fprintf(f, "\t\t");
			(*it)->prettyPrint(f);
			fprintf(f, "\n");
		}
	}
	if (assumption) {
		fprintf(f, "\tAssumption:\n");
		assumption->prettyPrint(f);
	}
	if (!_registers.empty()) {
		fprintf(f, "\tRegister map:\n");
		for (auto it = _registers.begin(); it != _registers.end(); it++) {
			fprintf(f, "\t\t");
			it->first.prettyPrint(f);
			fprintf(f, " -> ");
			it->second.e->prettyPrint(f);
		}
	}
}

void
avail_t::makeFalse(bbdd::scope *scope, bbdd *expr)
{
	expr = bbdd::invert(scope, expr);
	if (assumption)
		assumption =
			bbdd::And(
				scope,
				assumption,
				expr);
	else
		assumption = expr;
}

void
avail_t::dereference(SMScopes *scopes, exprbdd *addr, const AllowableOptimisations &opt)
{
	if (TIMEOUT)
		return;
	exprbdd *badPtr = exprbdd::unop(
		&scopes->exprs,
		&scopes->bools,
		Iop_BadPtr,
		addr);
	bool b;
	badPtr = simplifyBDD(&scopes->exprs, &scopes->bools, badPtr, opt, &b);
	makeFalse(&scopes->bools, exprbdd::to_bbdd(&scopes->bools, badPtr));
}

bool
avail_t::mergeIntersection(bbdd::scope *scope,
			   const avail_t &other)
{
	bool res;
	res = false;
	auto it1 = sideEffects.begin();
	auto it2 = other.sideEffects.begin();
	while (it1 != sideEffects.end() && it2 != other.sideEffects.end()) {
		if (*it1 == *it2) {
			it1++;
			it2++;
		} else if (*it1 < *it2) {
			sideEffects.erase(it1++);
			res = true;
		} else {
			assert(*it2 < *it1);
			it2++;
		}
	}
	while (it1 != sideEffects.end()) {
		res = true;
		sideEffects.erase(it1++);
	}

	/* We're supposed to take the intersection of the two sets
	   i.e. we can only assume things which are true in both input
	   sets, and so the new assumption is the union of the two
	   input assumptions. */
	bbdd *newAssumption;
	if (assumption && other.assumption)
		newAssumption = bbdd::Or(
			scope,
			assumption,
			other.assumption);
	else
		newAssumption = NULL;
	if (newAssumption != assumption) {
		res = true;
		assumption = newAssumption;
	}
	return res;
}

bool
avail_t::mergeUnion(bbdd::scope *scope, const avail_t &other)
{
	bool res;
	res = false;
	for (auto it = other.sideEffects.begin(); it != other.sideEffects.end(); it++)
		res |= sideEffects.insert(*it).second;
	/* We're taking the union of the two avail_ts, so can assume
	   anything which is known to be true in either of them
	   i.e. we take the intersection of the two assumptions. */
	if (assumption && other.assumption)
		assumption = bbdd::And(
			scope,
			assumption,
			other.assumption);
	else if (other.assumption)
		assumption = other.assumption;
	return res;
}

/* Remove any references to register @reg from the available set.
   Most of the time, that includes side effects which either use or
   define @reg.  The exception is the side-effect @preserve, which is
   only purged if it uses @reg (i.e. it'll be left in place if its
   only reference to @reg is to use it). */
struct avail_inv_reg_ctxt {
	threadAndRegister reg;
	const StateMachineSideEffect *preserve;
};
void
avail_t::invalidateRegister(bbdd::scope *scope, threadAndRegister reg, StateMachineSideEffect *preserve)
{
	class {
		typedef avail_inv_reg_ctxt ctxt;
		static visit_result Get(ctxt *ctxt, const IRExprGet *e) {
			if (e->reg == ctxt->reg)
				return visit_abort;
			else
				return visit_continue;
		}
		static visit_result Load(ctxt *ctxt, const StateMachineSideEffectLoad *l)
		{
			if (l != ctxt->preserve && l->target == ctxt->reg)
				return visit_abort;
			else
				return visit_continue;
		}
		static visit_result Copy(ctxt *ctxt, const StateMachineSideEffectCopy *c)
		{
			if (c != ctxt->preserve && c->target == ctxt->reg)
				return visit_abort;
			else
				return visit_continue;
		}
		static visit_result Phi(ctxt *ctxt, const StateMachineSideEffectPhi *phi)
		{
			if (phi == ctxt->preserve)
				return visit_continue;
			if (phi->reg == ctxt->reg)
				return visit_abort;
			for (auto it = phi->generations.begin(); it != phi->generations.end(); it++)
				if (it->reg == ctxt->reg)
					return visit_abort;
			return visit_continue;
		}
	public:
		bool isPresent(const threadAndRegister &reg, const StateMachineSideEffect *preserve,
			       const StateMachineSideEffect *se)
		{
			static state_machine_visitor<ctxt> visitor;
			visitor.irexpr.Get = Get;
			visitor.Load = Load;
			visitor.Copy = Copy;
			visitor.Phi = Phi;
			ctxt ctxt;
			ctxt.reg = reg;
			ctxt.preserve = preserve;
			if (visit_side_effect(&ctxt, &visitor, se) == visit_abort)
				return true;
			else
				return false;
		}
		bbdd *invalidateRegister(bbdd::scope *scope,
					 const threadAndRegister reg,
					 bbdd *expr)
		{
			if (expr->isLeaf)
				return expr;
			bbdd *t = invalidateRegister(scope, reg, expr->internal().trueBranch);
			bbdd *f = invalidateRegister(scope, reg, expr->internal().falseBranch);
			if (t == f)
				return t;
			static irexpr_visitor<ctxt> visitor;
			visitor.Get = Get;
			ctxt ctxt;
			ctxt.reg = reg;
			ctxt.preserve = NULL;
			if (visit_irexpr(&ctxt, &visitor, expr->internal().condition) == visit_abort) {
				/* Behaviour depends on the register
				   which we're trying to kill -> can't
				   do anything */
				return scope->cnst(true);
			} else {
				if (t == expr->internal().trueBranch &&
				    f == expr->internal().falseBranch)
					return expr;
				return scope->makeInternal(expr->internal().condition, t, f);
			}
		}
	} f;

	for (auto it = sideEffects.begin(); it != sideEffects.end(); ) {
		if (f.isPresent(reg, preserve, *it)) {
			sideEffects.erase(it++);
		} else {
			it++;
		}
	}
	if (assumption)
		assumption = f.invalidateRegister(scope, reg, assumption);
}

void
avail_t::calcRegisterMap(bbdd::scope *scope)
{
	_registers.clear();
	for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
		StateMachineSideEffect *se = *it;
		if (se->type == StateMachineSideEffect::Copy) {
			StateMachineSideEffectCopy *sep = (StateMachineSideEffectCopy *)se;
			/* It's really bad news if we have two
			   available expressions which both define the
			   same register. */
			assert(!_registers.count(sep->target));
			_registers[sep->target] = avail_t::registerMapEntry(sep->value);
		} else if (se->type == StateMachineSideEffect::AssertFalse) {
			StateMachineSideEffectAssertFalse *seaf = (StateMachineSideEffectAssertFalse *)se;
			makeFalse(scope, seaf->value);
		} else if (se->type == StateMachineSideEffect::Phi) {
			StateMachineSideEffectPhi *smsep = (StateMachineSideEffectPhi *)se;
			assert(!smsep->generations.empty());
			if (smsep->generations.size() == 1)
				_registers[smsep->reg] = registerMapEntry(smsep->generations[0].val);
		}
	}
}

static void
updateAvailSetForSideEffect(SMScopes *scopes,
			    const MaiMap &decode,
			    avail_t &outputAvail,
			    StateMachineSideEffect *smse,
			    const AllowableOptimisations &opt,
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
		for (auto it = outputAvail.beginSideEffects();
		     it != outputAvail.endSideEffects();
			) {
			StateMachineSideEffectStore *smses2 =
				dynamic_cast<StateMachineSideEffectStore *>(*it);
			StateMachineSideEffectLoad *smsel2 =
				dynamic_cast<StateMachineSideEffectLoad *>(*it);
			exprbdd *addr;
			if (smses2)
				addr = smses2->addr;
			else if (smsel2)
				addr = smsel2->addr;
			else
				addr = NULL;

			if ( addr &&
			     ((smses2 && oracle->memoryAccessesMightAlias(decode, opt, smses2, smses)) ||
			      (smsel2 && oracle->memoryAccessesMightAlias(decode, opt, smsel2, smses))) &&
			     !definitelyNotEqual( addr,
						  smses->addr,
						  opt) )
				outputAvail.eraseSideEffect(it++);
			else
				it++;
		}
		/* Introduce the store which was generated. */
		if (!oracle->hasConflictingRemoteStores(decode, opt, smses))
			outputAvail.insertSideEffect(smses);
		outputAvail.dereference(scopes, smses->addr, opt);
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec =
			dynamic_cast<StateMachineSideEffectCopy *>(smse);
		assert(smsec);
		outputAvail.insertSideEffect(smsec);
		break;
	}
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel =
			dynamic_cast<StateMachineSideEffectLoad *>(smse);
		if (!oracle->hasConflictingRemoteStores(decode, opt, smsel))
			outputAvail.insertSideEffect(smsel);
		outputAvail.dereference(scopes, smsel->addr, opt);
		break;
	}
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(smse);
		outputAvail.makeFalse(&scopes->bools, smseaf->value);
		break;
	}
	case StateMachineSideEffect::Unreached:
		break;
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *p =
			(StateMachineSideEffectPhi *)smse;
		outputAvail.insertSideEffect(p);
		break;
	}
	case StateMachineSideEffect::StartAtomic:
	case StateMachineSideEffect::EndAtomic:
		/* XXX we could be a bit more cunning here and keep
		   loads to shared locations available until the end
		   of the atomic section, but that's a bit tricky and
		   doesn't actually make much difference in any of the
		   places where we use atomic blocks. */
		break;
	case StateMachineSideEffect::StartFunction:
	case StateMachineSideEffect::EndFunction:
	case StateMachineSideEffect::ImportRegister:
	case StateMachineSideEffect::StackLayout:
		break;
	}

	threadAndRegister r(threadAndRegister::invalid());
	if (smse->definesRegister(r))
		outputAvail.invalidateRegister(&scopes->bools, r, smse);
}

class applyAvailTransformer : public IRExprTransformer {
	const avail_t &avail;
	IRExpr *transformIex(IRExprGet *e) {
		auto it = avail._registers.find(e->reg);
		if (it != avail._registers.end()) {
			if (it->second.e->type() >= e->type())
				return coerceTypes(e->type(), exprbdd::to_irexpr(it->second.e));
		}
		return IRExprTransformer::transformIex(e);
	}
public:
	applyAvailTransformer(const avail_t &_avail)
		: avail(_avail)
	{}
};
static bbdd *
applyAvailSet(bbdd::scope *scope, const avail_t &avail, bbdd *expr, bool *done_something)
{
	applyAvailTransformer aat(avail);
	bbdd *e = aat.transform_bbdd(scope, expr, done_something);
	if (!avail.assumption)
		return e;
	bbdd *e2 = bbdd::assume(
		scope,
		e,
		avail.assumption);
	if (e2 != e)
		*done_something = true;
	return e2;
}
static smrbdd *
applyAvailSet(SMScopes *scopes, const avail_t &avail, smrbdd *expr, bool *done_something)
{
	applyAvailTransformer aat(avail);
	smrbdd *e = aat.transform_smrbdd(&scopes->bools, &scopes->smrs, expr, done_something);
	if (!avail.assumption)
		return e;
	smrbdd *e2 = smrbdd::assume(
		&scopes->smrs,
		e,
		avail.assumption);
	if (e2 != e)
		*done_something = true;
	return e2;
}
static exprbdd *
applyAvailSet(SMScopes *scopes, const avail_t &avail, exprbdd *expr, bool *done_something)
{
	applyAvailTransformer aat(avail);
	exprbdd *e = aat.transform_exprbdd(&scopes->bools, &scopes->exprs, expr, done_something);
	if (!avail.assumption)
		return e;
	exprbdd *e2 = exprbdd::assume(
		&scopes->exprs,
		e,
		avail.assumption);
	if (e2 != e)
		*done_something = true;
	return e2;
}

/* Slightly misnamed: this also propagates copy operations.  Also, it
   doesn't so much eliminate loads are replace them with copies of
   already-loaded values. */
static StateMachineSideEffect *
buildNewStateMachineWithLoadsEliminated(SMScopes *scopes,
					const MaiMap &decode,
					StateMachineSideEffect *smse,
					avail_t &currentlyAvailable,
					OracleInterface *oracle,
					bool *done_something,
					const AllowableOptimisations &opt)
{
	StateMachineSideEffect *newEffect;

	if (debug_substitutions) {
		printf("Side effect ");
		smse->prettyPrint(stdout);
		printf("\n");
	}

	newEffect = NULL;
	switch (smse->type) {
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectStore *smses =
			dynamic_cast<StateMachineSideEffectStore *>(smse);
		exprbdd *newAddr;
		exprbdd *newData;
		bool doit = false;
		newAddr = applyAvailSet(scopes, currentlyAvailable, smses->addr, &doit);
		newData = applyAvailSet(scopes, currentlyAvailable, smses->data, &doit);
		if (doit) {
			newEffect = new StateMachineSideEffectStore(
				smses, newAddr, newData);
			*done_something = true;
		} else {
			newEffect = smses;
		}
		break;
	}
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel =
			dynamic_cast<StateMachineSideEffectLoad *>(smse);
		exprbdd *newAddr;
		bool doit = false;
		newAddr = applyAvailSet(scopes, currentlyAvailable, smsel->addr, &doit);
		for (auto it2 = currentlyAvailable.beginSideEffects();
		     !newEffect && it2 != currentlyAvailable.endSideEffects();
		     it2++) {
			StateMachineSideEffectStore *smses2 =
				dynamic_cast<StateMachineSideEffectStore *>(*it2);
			StateMachineSideEffectLoad *smsel2 =
				dynamic_cast<StateMachineSideEffectLoad *>(*it2);
			if ( smses2 &&
			     smsel->type <= smses2->data->type() &&
			     smsel->tag == smses2->tag &&
			     definitelyEqual(smses2->addr, newAddr, opt) ) {
				newEffect =
					new StateMachineSideEffectCopy(
						smsel->target,
						exprbdd::coerceTypes(
							&scopes->exprs,
							&scopes->bools,
							smsel->type,
							smses2->data));
			} else if ( smsel2 &&
				    smsel->type <= smsel2->type &&
				    smsel->tag == smsel2->tag &&
				    definitelyEqual(smsel2->addr, newAddr, opt) ) {
				newEffect =
					new StateMachineSideEffectCopy(
						smsel->target,
						exprbdd::var(&scopes->exprs, &scopes->bools, new IRExprGet(smsel2->target, smsel->type)));
			}
		}
		if (!newEffect && doit)
			newEffect = new StateMachineSideEffectLoad(smsel, newAddr);
		if (!newEffect)
			newEffect = smse;
		if (newEffect != smse)
			*done_something = true;
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec =
			dynamic_cast<StateMachineSideEffectCopy *>(smse);
		exprbdd *newValue;
		bool doit = false;
		newValue = applyAvailSet(scopes, currentlyAvailable, smsec->value, &doit);
		if (doit) {
			*done_something = true;
			newEffect = new StateMachineSideEffectCopy(
				smsec->target, newValue);
		} else
			newEffect = smse;
		break;
	}
	case StateMachineSideEffect::Unreached:
	case StateMachineSideEffect::StartAtomic:
	case StateMachineSideEffect::EndAtomic:
	case StateMachineSideEffect::StackLayout:
	case StateMachineSideEffect::ImportRegister:
		newEffect = smse;
		break;
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(smse);
		bbdd *newVal;
		bool doit = false;
		if (currentlyAvailable.nr_asserts() < MAX_LIVE_ASSERTIONS) {
			newVal = applyAvailSet(&scopes->bools, currentlyAvailable, smseaf->value, &doit);
		} else {
			/* We have too many live assertions.
			   That can lead to them holding
			   enormous number of variables live,
			   which isn't much use, so turn this
			   one into a no-op.  It'll get
			   optimised out again later. */
			newVal = NULL;
			doit = true;
		}
		if (doit) {
			if (newVal)
				newEffect = new StateMachineSideEffectAssertFalse(newVal, smseaf->reflectsActualProgram);
			else
				newEffect = NULL;
			*done_something = true;
		} else
			newEffect = smse;
		break;
	}
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *phi =
			(StateMachineSideEffectPhi *)smse;
		StateMachineSideEffectPhi *newPhi = NULL;
		for (unsigned x = 0; x < phi->generations.size(); x++) {
			bool t = false;
			exprbdd *e = applyAvailSet(scopes,
						   currentlyAvailable,
						   phi->generations[x].val,
						   &t);
			if (t) {
				if (!newPhi)
					newPhi = new StateMachineSideEffectPhi(*phi);
				newPhi->generations[x].val = e;
			}
		}
		if (newPhi) {
			newEffect = newPhi;
			*done_something = true;
		} else {
			newEffect = phi;
		}
		break;
	}
	case StateMachineSideEffect::StartFunction: {
		StateMachineSideEffectStartFunction *sf =
			(StateMachineSideEffectStartFunction *)smse;
		bool doit = false;
		exprbdd *newRsp;
		newRsp = applyAvailSet(scopes, currentlyAvailable, sf->rsp, &doit);
		if (doit) {
			newEffect = new StateMachineSideEffectStartFunction(newRsp, sf->frame);
			*done_something = true;
		} else {
			newEffect = smse;
		}
		break;
	}
	case StateMachineSideEffect::EndFunction: {
		StateMachineSideEffectEndFunction *sf =
			(StateMachineSideEffectEndFunction *)smse;
		bool doit = false;
		exprbdd *newRsp;
		newRsp = applyAvailSet(scopes, currentlyAvailable, sf->rsp, &doit);
		if (doit) {
			newEffect = new StateMachineSideEffectEndFunction(newRsp, sf->frame);
			*done_something = true;
		} else {
			newEffect = smse;
		}
		break;
	}
	}
	if (debug_substitutions) {
		printf("New side effect ");
		newEffect->prettyPrint(stdout);
		printf("\n");
	}
	if (!*done_something) assert(newEffect == smse);
	if (newEffect)
		updateAvailSetForSideEffect(scopes, decode, currentlyAvailable, newEffect, opt, oracle);
	currentlyAvailable.calcRegisterMap(&scopes->bools);
	if (debug_substitutions) {
		printf("New available set:\n");
		currentlyAvailable.print(stdout);
	}

	return newEffect;
}

static StateMachineState *
buildNewStateMachineWithLoadsEliminated(
	SMScopes *scopes,
	const MaiMap &decode,
	StateMachineState *sm,
	std::map<StateMachineState *, avail_t> &availMap,
	std::map<StateMachineState *, StateMachineState *> &memo,
	const AllowableOptimisations &opt,
	OracleInterface *oracle,
	bool *done_something,
	std::map<const StateMachineState *, int> &edgeLabels)
{
	if (memo.count(sm)) {
		/* We rely on whoever it was that set memo[sm] having
		 * also set *done_something if appropriate. */
		return memo[sm];
	}
	avail_t avail(availMap[sm]);

	StateMachineState *res;
	/* Shut compiler up */
	res = (StateMachineState *)0xf001ul;
	switch (sm->type) {
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)sm;
		avail.calcRegisterMap(&scopes->bools);
		res = new StateMachineBifurcate(
			smb,
			applyAvailSet(&scopes->bools, avail, smb->condition, done_something));
		break;
	}
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *smp = (StateMachineSideEffecting *)sm;
		StateMachineSideEffect *newEffect;
		avail.calcRegisterMap(&scopes->bools);
		if (smp->sideEffect)
			newEffect = buildNewStateMachineWithLoadsEliminated(scopes,
									    decode,
									    smp->sideEffect,
									    avail,
									    oracle,
									    done_something,
									    opt);
		else
			newEffect = NULL;
		res = new StateMachineSideEffecting(smp, newEffect);
		break;
	}
	case StateMachineState::Terminal: {
		StateMachineTerminal *smt = (StateMachineTerminal *)sm;
		avail.calcRegisterMap(&scopes->bools);
		res = new StateMachineTerminal(
			smt,
			applyAvailSet(scopes, avail, smt->res, done_something));
		break;
	}
	}

	memo[sm] = res;
	std::vector<StateMachineState **> targets;
	res->targets(targets);
	for (auto it = targets.begin(); it != targets.end(); it++) {
		**it = buildNewStateMachineWithLoadsEliminated(
			scopes, decode, **it, availMap, memo, opt, oracle,
			done_something, edgeLabels);
	}
	return res;
}

static StateMachine *
buildNewStateMachineWithLoadsEliminated(
	SMScopes *scopes,
	const MaiMap &decode,
	StateMachine *sm,
	std::map<StateMachineState *, avail_t> &availMap,
	const AllowableOptimisations &opt,
	OracleInterface *oracle,
	bool *done_something,
	std::map<const StateMachineState *, int> &edgeLabels)
{
	std::map<StateMachineState *, StateMachineState *> memo;
	bool d = false;
	StateMachineState *new_root = buildNewStateMachineWithLoadsEliminated(scopes,
									      decode,
									      sm->root,
									      availMap,
									      memo,
									      opt,
									      oracle,
									      &d,
									      edgeLabels);
	if (d) {
		*done_something = true;
		return new StateMachine(sm, new_root);
	} else {
		return sm;
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
	std::map<const StateMachineState *, int> edgeLabels;
	if (dump_avail_table || debug_substitutions) {
		printf("Avail analysis on state machine:\n");
		printStateMachine(sm, stdout, edgeLabels);
	}

	__set_profiling(availExpressionAnalysis);

	std::set<StateMachineState *> allStates;
	enumStates(sm, &allStates);

	std::map<StateMachineState *, avail_t> availOnEntry;

	static class _ {
	public:
		int nr_avail_calls;
		int nr_phase1_iters;
		int nr_phase2_iters;
		int nr_useful_phase2;
		_()
			: nr_avail_calls(0),
			  nr_phase1_iters(0),
			  nr_phase2_iters(0),
			  nr_useful_phase2(0)
		{}
		~_() {
			printf("Avail analysis: invoked %d times, %d phase 1 iters (%f per), %d phase 2 (%f per), %d phase2 useful (%f%%)\n",
			       nr_avail_calls,
			       nr_phase1_iters,
			       (double)nr_phase1_iters / nr_avail_calls,
			       nr_phase2_iters,
			       (double)nr_phase2_iters / nr_avail_calls,
			       nr_useful_phase2,
			       nr_useful_phase2 * 100.0 / nr_avail_calls);
		}
	} stats;

	stats.nr_avail_calls++;

	/* We use a two-phase building process here.  In the first
	 * phase, we build an availability map using unions at
	 * path-join, which is an overapproximation.  We then refine
	 * it using intersections at path-join, which is an
	 * underapproximation.  This ends up being equivalant to
	 * starting with an initial state in which everything is
	 * available everywhere and then going straight to the
	 * intersection phase, except that it means you don't need to
	 * build the full O(n^2) everything-everywhere availability
	 * table. */
	std::queue<StateMachineState *> statesNeedingRefresh;
	for (auto it = allStates.begin(); it != allStates.end(); it++)
		statesNeedingRefresh.push(*it);
	while (!statesNeedingRefresh.empty() && !TIMEOUT) {
		StateMachineState *state = statesNeedingRefresh.front();
		statesNeedingRefresh.pop();

		avail_t outputAvail(availOnEntry[state]);
		if ( state->type == StateMachineState::SideEffecting ) {
			StateMachineSideEffect *se = ((StateMachineSideEffecting *)state)->sideEffect;
			if (se)
				updateAvailSetForSideEffect(scopes, decode, outputAvail,
							    se, opt, oracle);
		}

		std::vector<StateMachineState *> edges;
		state->targets(edges);
		for (auto it2 = edges.begin(); it2 != edges.end(); it2++) {
			if (availOnEntry[*it2].mergeUnion(&scopes->bools, outputAvail))
				statesNeedingRefresh.push(*it2);
		}
		stats.nr_phase1_iters++;
	}

	if (TIMEOUT)
		return sm;

	if (dump_avail_table) {
		printf("Availability map after phase one:\n");
		for (auto it = availOnEntry.begin();
		     it != availOnEntry.end();
		     it++) {
			printf("Edge %d:\n", edgeLabels[it->first]);
			it->second.print(stdout);
		}
	}

	bool phase2_useful = false;

	/* Now do it using intersections. */
	for (auto it = allStates.begin(); it != allStates.end(); it++)
		statesNeedingRefresh.push(*it);
	while (!statesNeedingRefresh.empty() && !TIMEOUT) {
		StateMachineState *state = statesNeedingRefresh.front();
		statesNeedingRefresh.pop();

		avail_t outputAvail(availOnEntry[state]);
		if ( state->type == StateMachineState::SideEffecting ) {
			StateMachineSideEffect *se = ((StateMachineSideEffecting *)state)->sideEffect;
			if (se)
				updateAvailSetForSideEffect(scopes, decode, outputAvail,
							    se, opt, oracle);
		}

		std::vector<StateMachineState *> edges;
		state->targets(edges);
		for (auto it2 = edges.begin(); it2 != edges.end(); it2++) {
			if (availOnEntry[*it2].mergeIntersection(&scopes->bools, outputAvail)) {
				phase2_useful = true;
				statesNeedingRefresh.push(*it2);
			}
		}
		stats.nr_phase2_iters++;
	}

	if (phase2_useful)
		stats.nr_useful_phase2++;

	if (dump_avail_table) {
		if (phase2_useful) {
			printf("Final entry availability map:\n");
			for (auto it = availOnEntry.begin();
			     it != availOnEntry.end();
			     it++) {
				printf("Edge %d:\n", edgeLabels[it->first]);
				it->second.print(stdout);
			}
		} else {
			printf("Phase 2 had no effect.\n");
		}

	}

	if (TIMEOUT)
		return sm;

	/* So after all that we now have a complete map of what's
	   available where.  Given that, we should be able to
	   construct a new state machine with redundant loads replaced
	   with copy side effects. */
	return buildNewStateMachineWithLoadsEliminated(
		scopes,
		decode,
		sm,
		availOnEntry,
		opt,
		oracle,
		done_something,
		edgeLabels);
}

typedef std::map<threadAndRegister, exprbdd *> regDefT;

template <typename k, typename v> class sane_map : public std::map<k, v> {
public:
	std::pair<typename std::map<k,v>::iterator, bool> insert(const k &a, const v &b)
	{
		return std::map<k,v>::insert(std::pair<k, v>(a, b));
	}
};

struct ssa_avail_state {
	SMScopes *scopes;
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
			assert(it->second->isLeaf);
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
			if ( it2->second->isLeaf )
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
				it2->second = state.scopes->ordering.trueBranch(it2->second, *bestVar);
			substTableT falseTable(t);
			for (auto it2 = falseTable.begin(); it2 != falseTable.end(); it2++)
				it2->second = state.scopes->ordering.falseBranch(it2->second, *bestVar);
			it->second = bbdd::ifelse(
				&state.scopes->bools,
				bbdd::var(&state.scopes->bools, bestCond),
				ssaApplyAvailExprBool(state, trueTable, e, memo),
				ssaApplyAvailExprBool(state, falseTable, e, memo));
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
			if ( it2->second->isLeaf )
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
				it2->second = state.scopes->ordering.trueBranch(it2->second, *bestVar);
			substTableT falseTable(t);
			for (auto it2 = falseTable.begin(); it2 != falseTable.end(); it2++)
				it2->second = state.scopes->ordering.falseBranch(it2->second, *bestVar);
			it->second = exprbdd::ifelse(
				&state.scopes->exprs,
				bbdd::var(&state.scopes->bools, bestCond),
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
		if (inp->isLeaf) {
			it->second = inp;
		} else {
			auto newCond(ssaApplyAvailExprBool(state, inp->internal().condition));
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
	return it->second;
}

static smrbdd *
ssaApplyAvail(ssa_avail_state &state, smrbdd *inp)
{
	auto it_did_insert = state.smrMemo.insert(inp, NULL);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (inp->isLeaf) {
			it->second = inp;
		} else {
			auto newCond(ssaApplyAvailExprBool(state, inp->internal().condition));
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
	return it->second;
}

static exprbdd *
ssaApplyAvail(ssa_avail_state &state, exprbdd *inp)
{
	auto it_did_insert = state.exprMemo.insert(inp, NULL);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (inp->isLeaf) {
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
	return it->second;
}

template <typename t> static void
rewrite_var(ssa_avail_state &state, t *&arg, bool *done_something)
{
	t *n = ssaApplyAvail(state, arg);
	if (n != arg)
		*done_something = n;
	arg = n;
}

static void
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectLoad *inp,
		bool *done_something)
{
	rewrite_var(state, inp->addr, done_something);
}
static void
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectStore *inp,
		bool *done_something)
{
	rewrite_var(state, inp->addr, done_something);
	rewrite_var(state, inp->data, done_something);
}
static void
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectCopy *inp,
		bool *done_something)
{
	rewrite_var(state, inp->value, done_something);
}
static void
ssaApplyAvailSE(ssa_avail_state &, StateMachineSideEffectUnreached *, bool *)
{}
static void
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectAssertFalse *inp,
		bool *done_something)
{
	rewrite_var(state, inp->value, done_something);
}
static void
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectPhi *inp,
		bool *done_something)
{
	for (auto it = inp->generations.begin(); it != inp->generations.end(); it++)
		rewrite_var(state, it->val, done_something);
}
static void
ssaApplyAvailSE(ssa_avail_state &, StateMachineSideEffectStartAtomic *, bool *)
{}
static void
ssaApplyAvailSE(ssa_avail_state &, StateMachineSideEffectEndAtomic *, bool *)
{}
static void
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectStartFunction *inp,
		bool *done_something)
{
	rewrite_var(state, inp->rsp, done_something);
}
static void
ssaApplyAvailSE(ssa_avail_state &state, StateMachineSideEffectEndFunction *inp,
		bool *done_something)
{
	rewrite_var(state, inp->rsp, done_something);
}
static void
ssaApplyAvailSE(ssa_avail_state &, StateMachineSideEffectImportRegister *, bool *)
{}
static void
ssaApplyAvailSE(ssa_avail_state &, StateMachineSideEffectStackLayout *, bool *)
{}

static void
rewrite_side_effect(ssa_avail_state &state, StateMachineSideEffect *inp,
		    bool *done_something)
{
	if (!inp)
		return;
	switch (inp->type) {
#define do_type(name)							\
		case StateMachineSideEffect:: name :			\
			ssaApplyAvailSE(				\
				state,					\
				(StateMachineSideEffect ## name *)inp,	\
				done_something);			\
			return;
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
	static irexpr_visitor<ssa_avail_state> visitor;
	visitor.Get = foo.Get;
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
ssaAvailAnalysis(SMScopes *scopes, StateMachine *sm, bool *done_something)
{
	ssa_avail_state state;
	state.scopes = scopes;
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
		StateMachineState *s = *it;
		switch (s->type) {
		case StateMachineState::Terminal: {
			auto smt = (StateMachineTerminal *)s;
			rewrite_var(state, smt->res, done_something);
			break;
		}
		case StateMachineState::Bifurcate: {
			auto smb = (StateMachineBifurcate *)s;
			rewrite_var(state, smb->condition, done_something);
			break;
		}
		case StateMachineState::SideEffecting: {
			auto sme = (StateMachineSideEffecting *)s;
			rewrite_side_effect(state, sme->sideEffect, done_something);
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
			bool *done_something)
{
	if (is_ssa)
		return _availExpressionAnalysis::ssaAvailAnalysis(scopes, sm, done_something);
	else
		return _availExpressionAnalysis::availExpressionAnalysis(scopes, decode, sm, opt, oracle, done_something);
}
