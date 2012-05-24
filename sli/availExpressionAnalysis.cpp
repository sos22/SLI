/* Available expression analysis on memory locations.  This isn't
   included in the normal optimise() operation because it's
   context-sensitive, and therefore isn't allowed to mutate nodes
   in-place. */
#include "sli.h"
#include "offline_analysis.hpp"
#include "libvex_prof.hpp"
#include "allowable_optimisations.hpp"

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
	std::set<StateMachineSideEffect *> sideEffects;
public:
	std::set<StateMachineSideEffect *>::iterator beginSideEffects() { return sideEffects.begin(); }
	std::set<StateMachineSideEffect *>::iterator endSideEffects() { return sideEffects.end(); }
	void insertSideEffect(StateMachineSideEffect *smse) {
		smse->sanityCheck();
		sideEffects.insert(smse);
	}
	void eraseSideEffect(std::set<StateMachineSideEffect *>::iterator it) {
		sideEffects.erase(it);
	}

	std::set<IRExpr *> assertFalse;
	struct registerMapEntry {
		IRExpr *e;
		threadAndRegister phiFrom;
		registerMapEntry()
			: e(NULL), phiFrom(threadAndRegister::invalid())
		{}
		registerMapEntry(IRExpr *_e)
			: e(_e), phiFrom(threadAndRegister::invalid())
		{}
		registerMapEntry(const threadAndRegister &tr)
			: e(NULL), phiFrom(tr)
		{}
	};
	std::map<threadAndRegister, registerMapEntry, threadAndRegister::fullCompare> _registers;

	void clear() { sideEffects.clear(); assertFalse.clear(); _registers.clear(); }
	void makeFalse(IRExpr *expr, const AllowableOptimisations &opt);
	void dereference(IRExpr *ptr, const AllowableOptimisations &opt);
	/* Merge @other into the current availability set.  Returns
	   true if we do anything, and false otherwise. */
	bool merge(const avail_t &other, const AllowableOptimisations &opt,
		   bool is_ssa);

	void calcRegisterMap(const AllowableOptimisations &opt);

	void invalidateRegister(threadAndRegister reg, StateMachineSideEffect *preserve);

	void findAllPotentiallyAvailable(StateMachine *sm, const AllowableOptimisations &opt, Oracle *oracle);

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
	if (!assertFalse.empty()) {
		fprintf(f, "\tAsserted false:\n");
		for (auto it = assertFalse.begin(); it != assertFalse.end(); it++) {
			fprintf(f, "\t\t");
			ppIRExpr(*it, f);
			fprintf(f, "\n");
		}
	}
	if (!_registers.empty()) {
		fprintf(f, "\tRegister map:\n");
		for (auto it = _registers.begin(); it != _registers.end(); it++) {
			fprintf(f, "\t\t");
			it->first.prettyPrint(f);
			fprintf(f, " -> ");
			if (it->second.e)
				ppIRExpr(it->second.e, f);
			else
				fprintf(f, "%s", it->second.phiFrom.name());
			fprintf(f, "\n");
		}
	}
}

void
avail_t::makeFalse(IRExpr *expr, const AllowableOptimisations &opt)
{
	if (expr->tag == Iex_Const)
		return;
	assert(expr->type() == Ity_I1);
	for (auto it = assertFalse.begin();
	     it != assertFalse.end();
	     it++)
		if (definitelyEqual(*it, expr, opt))
			return;
	assertFalse.insert(expr);
}

void
avail_t::dereference(IRExpr *addr, const AllowableOptimisations &opt)
{
	if (TIMEOUT)
		return;
	IRExpr *badPtr = IRExpr_Unop(Iop_BadPtr, addr);
	badPtr = simplifyIRExpr(badPtr, opt);
	makeFalse(badPtr, opt);
}

template <typename a> bool
intersectSets(std::set<a> &x, const std::set<a> &y)
{
	bool res = false;
	auto it1 = x.begin();
	auto it2 = y.begin();

	while (it1 != x.end() && it2 != y.end()) {
		if (*it1 == *it2) {
			it1++;
			it2++;
		} else if (*it1 < *it2) {
			x.erase(it1++);
			res = true;
		} else {
			assert(*it2 < *it1);
			it2++;
		}
	}
	while (it1 != x.end()) {
		res = true;
		x.erase(it1++);
	}
	return res;
}

bool
avail_t::merge(const avail_t &other,
	       const AllowableOptimisations &opt,
	       bool is_ssa)
{
	bool res;

	/* The merge rules are a little bit tricky.  The obvious
	   answer is an intersection, but that's a bit more
	   conservative than we need, at least for registers.  The
	   observation is that if a parent doesn't define a register
	   at all then it must be that if we came from that parent
	   then we will never use that register, because otherwise
	   we'd have a use-without-initialisation bug.  Therefore, if
	   one parent defines a register and the other doesn't, we can
	   just take the value from whichever parent *does* define it.

	   i.e. the output is the *union* of inputs for
	   register-defining side effects, unless we have conflicting
	   definitions for the same register.

	   In SSA form, we can't ever have conflicting definitions for
	   a single register, because that would violate the SSA
	   property, so this cunningness is safe in SSA form but not
	   otherwise. */
	/* We only do this for copies and phis, since those are the
	   only ones for which it's safe. */
	struct {
		bool operator()(StateMachineSideEffect::sideEffectType t) {
			return t == StateMachineSideEffect::Copy ||
				t == StateMachineSideEffect::Phi;
		}
	} ssa_cunningness_safe;
	res = false;
	if (is_ssa) {
		for (auto it = other.sideEffects.begin(); it != other.sideEffects.end(); it++) {
			StateMachineSideEffect *smse = *it;
			if (ssa_cunningness_safe(smse->type))
				res |= sideEffects.insert(*it).second;
		}
	}

	std::set<StateMachineSideEffect *> newEffectsToIntroduce;
	auto it1 = sideEffects.begin();
	auto it2 = other.sideEffects.begin();
	while (it1 != sideEffects.end() && it2 != other.sideEffects.end()) {
		if (*it1 == *it2) {
			it1++;
			it2++;
		} else if (*it1 < *it2) {
			if ( is_ssa && ssa_cunningness_safe((*it1)->type) ) {
				it1++;
			} else {
				sideEffects.erase(it1++);
			}
			res = true;
		} else {
			assert(*it2 < *it1);
			if ( is_ssa && ssa_cunningness_safe( (*it2)->type) )
				newEffectsToIntroduce.insert(*it2);
			it2++;
		}
	}
	while (it1 != sideEffects.end()) {
		res = true;
		if ( is_ssa && ssa_cunningness_safe((*it1)->type) )
			it1++;
		else
			sideEffects.erase(it1++);
	}
	sideEffects.insert(newEffectsToIntroduce.begin(), newEffectsToIntroduce.end());

	for (auto it = assertFalse.begin();
	     it != assertFalse.end();
		) {
		bool purge = true;
		if (other.assertFalse.count(*it))
			purge = false;
		for (auto it2 = other.assertFalse.begin();
		     purge && it2 != other.assertFalse.end();
		     it2++) {
			if (definitelyEqual(*it, *it2, opt))
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

/* Remove any references to register @reg from the available set.
   Most of the time, that includes side effects which either use or
   define @reg.  The exception is the side-effect @preserve, which is
   only purged if it uses @reg (i.e. it'll be left in place if its
   only reference to @reg is to use it). */
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
		StateMachineSideEffectPhi *transformOneSideEffect(StateMachineSideEffectPhi *l,
								  bool *done_something)
		{
			if (l != preserve && threadAndRegister::fullEq(l->reg, reg)) {
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
}

void
avail_t::calcRegisterMap(const AllowableOptimisations &opt)
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
			sep->value->sanity_check();
			_registers[sep->target] = avail_t::registerMapEntry(sep->value);
		} else if (se->type == StateMachineSideEffect::AssertFalse) {
			StateMachineSideEffectAssertFalse *seaf = (StateMachineSideEffectAssertFalse *)se;
			makeFalse(seaf->value, opt);
		} else if (se->type == StateMachineSideEffect::Phi) {
			StateMachineSideEffectPhi *smsep = (StateMachineSideEffectPhi *)se;
			if (smsep->generations.size() == 0) {
				_registers[smsep->reg] = avail_t::registerMapEntry(smsep->reg.setGen(-1));
			} else if (smsep->generations.size() == 1) {
				_registers[smsep->reg] = avail_t::registerMapEntry(smsep->reg.setGen(smsep->generations[0].first));
			}
		}
	}
}

static void
updateAvailSetForSideEffect(avail_t &outputAvail, StateMachineSideEffect *smse,
			    const AllowableOptimisations &opt,
			    const Oracle::RegisterAliasingConfiguration *alias,
			    Oracle *oracle)
{
	if (TIMEOUT)
		return;
	smse->sanityCheck();
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
			IRExpr *addr;
			if (smses2)
				addr = smses2->addr;
			else if (smsel2)
				addr = smsel2->addr;
			else
				addr = NULL;

			if ( addr &&
			     (!alias || alias->ptrsMightAlias(addr, smses->addr)) &&
			     ((smses2 && oracle->memoryAccessesMightAlias(opt, smses2, smses)) ||
			      (smsel2 && oracle->memoryAccessesMightAlias(opt, smsel2, smses))) &&
			     !definitelyNotEqual( addr,
						  smses->addr,
						  opt) )
				outputAvail.eraseSideEffect(it++);
			else
				it++;
		}
		/* Introduce the store which was generated. */
		if (opt.assumeNoInterferingStores() || !oracle->hasConflictingRemoteStores(smses))
			outputAvail.insertSideEffect(smses);
		outputAvail.dereference(smses->addr, opt);
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
		outputAvail.insertSideEffect(smsel);
		outputAvail.dereference(smsel->addr, opt);
		break;
	}
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(smse);
		outputAvail.makeFalse(smseaf->value, opt);
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
		
	}

	threadAndRegister r(threadAndRegister::invalid());
	if (smse->definesRegister(r))
		outputAvail.invalidateRegister(r, smse);
}

class applyAvailTransformer : public IRExprTransformer {
public:
	const avail_t &avail;
	const bool use_assumptions;
	const AllowableOptimisations &opt;
	IRExpr *transformIex(IRExprGet *e) {
		auto it = avail._registers.find(e->reg);
		if (it != avail._registers.end()) {
			if (it->second.e) {
				if (it->second.e->type() >= e->type())
					return coerceTypes(e->type(), it->second.e);
			} else {
				return IRExpr_Get(it->second.phiFrom, e->type());
			}
		}
		return IRExprTransformer::transformIex(e);
	}
	IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
		if (use_assumptions && e->type() == Ity_I1) {
			for (std::set<IRExpr *>::iterator it = avail.assertFalse.begin();
			     it != avail.assertFalse.end();
			     it++) {
				if (definitelyEqual(*it, e,  opt)) {
					*done_something = true;
					return IRExpr_Const(IRConst_U1(0));
				}
			}
		}
		return IRExprTransformer::transformIRExpr(e, done_something);
	}
	applyAvailTransformer(const avail_t &_avail, bool _use_assumptions,
			      const AllowableOptimisations &_opt)
		: avail(_avail), use_assumptions(_use_assumptions), opt(_opt)
	{}
};
static IRExpr *
applyAvailSet(const avail_t &avail, IRExpr *expr, bool use_assumptions, bool *done_something,
	      const AllowableOptimisations &opt)
{
	applyAvailTransformer aat(avail, use_assumptions, opt);
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
	const Oracle::RegisterAliasingConfiguration *aliasing,
	Oracle *oracle,
	bool *done_something,
	std::map<const StateMachineState *, int> &edgeLabels
	);
static StateMachineSideEffect *
buildNewStateMachineWithLoadsEliminated(StateMachineSideEffect *smse,
					avail_t &currentlyAvailable,
					Oracle *oracle,
					bool *done_something,
					const Oracle::RegisterAliasingConfiguration *aliasing,
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
		IRExpr *newAddr, *newData;
		bool doit = false;
		newAddr = applyAvailSet(currentlyAvailable, smses->addr, false, &doit, opt);
		newData = applyAvailSet(currentlyAvailable, smses->data, false, &doit, opt);
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
			dynamic_cast<StateMachineSideEffectLoad *>(smse);
		IRExpr *newAddr;
		bool doit = false;
		newAddr = applyAvailSet(currentlyAvailable, smsel->addr, false, &doit, opt);
		for (auto it2 = currentlyAvailable.beginSideEffects();
		     !newEffect && it2 != currentlyAvailable.endSideEffects();
		     it2++) {
			StateMachineSideEffectStore *smses2 =
				dynamic_cast<StateMachineSideEffectStore *>(*it2);
			StateMachineSideEffectLoad *smsel2 =
				dynamic_cast<StateMachineSideEffectLoad *>(*it2);
			if ( smses2 &&
			     (!aliasing || aliasing->ptrsMightAlias(smses2->addr, newAddr)) &&
			     definitelyEqual(smses2->addr, newAddr, opt) ) {
				newEffect =
					new StateMachineSideEffectCopy(
						smsel->target,
						smses2->data);
			} else if ( smsel2 &&
				    (!aliasing || aliasing->ptrsMightAlias(smsel2->addr, newAddr)) &&
				    definitelyEqual(smsel2->addr, newAddr, opt) ) {
				newEffect =
					new StateMachineSideEffectCopy(
						smsel->target,
						new IRExprGet(smsel2->target, Ity_I64));
			}
		}
		if (!newEffect && doit)
			newEffect = new StateMachineSideEffectLoad(
				smsel->target, newAddr, smsel->rip, smsel->type);
		if (!newEffect)
			newEffect = smse;
		if (newEffect != smse)
			*done_something = true;
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec =
			dynamic_cast<StateMachineSideEffectCopy *>(smse);
		IRExpr *newValue;
		bool doit = false;
		newValue = applyAvailSet(currentlyAvailable, smsec->value, false, &doit, opt);
		if (doit) {
			*done_something = true;
			newEffect = new StateMachineSideEffectCopy(
				smsec->target, newValue);
		} else
			newEffect = smse;
		break;
	}
	case StateMachineSideEffect::Unreached:
		newEffect = smse;
		break;
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(smse);
		IRExpr *newVal;
		bool doit = false;
		if (currentlyAvailable.nr_asserts() < MAX_LIVE_ASSERTIONS) {
			newVal = applyAvailSet(currentlyAvailable, smseaf->value, true, &doit, opt);
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
		if (doit) {
			newEffect = new StateMachineSideEffectAssertFalse(newVal);
			*done_something = true;
		} else
			newEffect = smse;
		break;
	}
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *phi =
			(StateMachineSideEffectPhi *)smse;
		StateMachineSideEffectPhi *newPhi = NULL;
		bool needSort = false;
		for (auto it = currentlyAvailable._registers.begin();
		     it != currentlyAvailable._registers.end();
		     it++) {
			if (threadAndRegister::partialEq(phi->reg, it->first)) {
				for (unsigned x = 0; x < phi->generations.size(); x++) {
					if (phi->generations[x].first == it->first.gen()) {
						if (it->second.e) {
							if (phi->generations[x].second &&
							    physicallyEqual(phi->generations[x].second,
									    it->second.e))
								break;
							if (!newPhi)
								newPhi = new StateMachineSideEffectPhi(*phi);
							newPhi->generations[x].second = it->second.e;
						} else {
							if (!newPhi)
								newPhi = new StateMachineSideEffectPhi(*phi);
							assert(threadAndRegister::partialEq(phi->reg,
											    it->second.phiFrom));
							newPhi->generations[x].first = it->second.phiFrom.gen();
							newPhi->generations[x].second = NULL;
							needSort = true;
						}
					}
				}
			}
		}
		for (unsigned x = 0; x < phi->generations.size(); x++) {
			IRExpr *e;
			e = (newPhi ? newPhi : phi)->generations[x].second;
			if (e) {
				bool t = false;
				IRExpr *e2 = applyAvailSet(currentlyAvailable,
							   e,
							   false,
							   &t,
							   opt);
				if (t) {
					assert(e != e2);
					if (!newPhi)
						newPhi = new StateMachineSideEffectPhi(*phi);
					newPhi->generations[x].second = e2;
					*done_something = true;
				}
			}
		}
		if (needSort) {
			assert(newPhi);
			std::sort(newPhi->generations.begin(), newPhi->generations.end());
			for (unsigned x = 0; x + 1 < newPhi->generations.size(); ) {
				if (newPhi->generations[x].first ==
				    newPhi->generations[x+1].first) {
					IRExpr *v = newPhi->generations[x].second;
					if (!v) {
						v = newPhi->generations[x+1].second;
					} else {
						assert(!newPhi->generations[x+1].second ||
						       v == newPhi->generations[x+1].second);
					}
					newPhi->generations[x].second = v;
					newPhi->generations.erase(newPhi->generations.begin() + x + 1);
				} else {
					x++;
				}
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
	}
	if (debug_substitutions) {
		printf("New side effect ");
		newEffect->prettyPrint(stdout);
		printf("\n");
	}
	assert(newEffect);
	if (!*done_something) assert(newEffect == smse);
	updateAvailSetForSideEffect(currentlyAvailable, newEffect, opt, aliasing, oracle);
	currentlyAvailable.calcRegisterMap(opt);
	if (debug_substitutions) {
		printf("New available set:\n");
		currentlyAvailable.print(stdout);
	}

	return newEffect;
}

static StateMachineState *
buildNewStateMachineWithLoadsEliminated(
	StateMachineState *sm,
	std::map<StateMachineState *, avail_t> &availMap,
	std::map<StateMachineState *, StateMachineState *> &memo,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration *alias,
	Oracle *oracle,
	bool *done_something,
	std::map<const StateMachineState *, int> &edgeLabels)
{
	if (sm->isTerminal())
		return sm;
	if (memo.count(sm)) {
		/* We rely on whoever it was that set memo[sm] having
		 * also set *done_something if appropriate. */
		return memo[sm];
	}
	avail_t avail(availMap[sm]);

	StateMachineState *res;
	switch (sm->type) {
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)sm;
		avail.calcRegisterMap(opt);
		res = new StateMachineBifurcate(
			sm->origin,
			applyAvailSet(avail, smb->condition, true, done_something, opt),
			smb->trueTarget, smb->falseTarget);
		break;
	}
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *smp = (StateMachineSideEffecting *)sm;
		StateMachineSideEffect *newEffect;
		avail.calcRegisterMap(opt);
		if (smp->sideEffect)
			newEffect = buildNewStateMachineWithLoadsEliminated(smp->sideEffect,
									    avail,
									    oracle,
									    done_something,
									    alias,
									    opt);
		else
			newEffect = NULL;
		res = new StateMachineSideEffecting(sm->origin, newEffect, smp->target);
		break;
	}
	case StateMachineState::NdChoice: {
		StateMachineNdChoice *smnd = (StateMachineNdChoice *)sm;
		res = new StateMachineNdChoice(smnd->origin,
					       smnd->successors);
		break;
	}
	case StateMachineState::Unreached:
	case StateMachineState::Crash:
	case StateMachineState::NoCrash:
	case StateMachineState::Stub:
		abort();
	}

	memo[sm] = res;
	std::vector<StateMachineState **> targets;
	res->targets(targets);
	for (auto it = targets.begin(); it != targets.end(); it++) {
		**it = buildNewStateMachineWithLoadsEliminated(
			**it, availMap, memo, opt, alias, oracle,
			done_something, edgeLabels);
	}
	return res;
}

static StateMachine *
buildNewStateMachineWithLoadsEliminated(
	StateMachine *sm,
	std::map<StateMachineState *, avail_t> &availMap,
	const AllowableOptimisations &opt,
	const Oracle::RegisterAliasingConfiguration *alias,
	Oracle *oracle,
	bool *done_something,
	std::map<const StateMachineState *, int> &edgeLabels)
{
	std::map<StateMachineState *, StateMachineState *> memo;
	bool d = false;
	StateMachineState *new_root = buildNewStateMachineWithLoadsEliminated(sm->root, availMap, memo, opt, alias, oracle,
									      &d, edgeLabels);
	if (d) {
		*done_something = true;
		return new StateMachine(new_root, sm->origin);
	} else {
		return sm;
	}
}

void
avail_t::findAllPotentiallyAvailable(StateMachine *sm,
				     const AllowableOptimisations &opt,
				     Oracle *oracle)
{
	findAllSideEffects(sm, sideEffects);
	for (auto it = sideEffects.begin();
	     !TIMEOUT && it != sideEffects.end();
	     it++) {
		StateMachineSideEffect *smse = *it;
		if (StateMachineSideEffectMemoryAccess *smsema =
		    dynamic_cast<StateMachineSideEffectMemoryAccess *>(smse)) {
			dereference(smsema->addr, opt);
		} else if (StateMachineSideEffectAssertFalse *smseaf =
			   dynamic_cast<StateMachineSideEffectAssertFalse *>(smse)) {
			makeFalse(smseaf->value, opt);
		}
	}

	/* If we're not executing atomically, stores to
	   non-thread-local memory locations are never considered to
	   be available. */
	if (!opt.assumeNoInterferingStores()) {
		for (auto it = sideEffects.begin();
		     !TIMEOUT && it != sideEffects.end();
			) {
			StateMachineSideEffectMemoryAccess *smsema =
				dynamic_cast<StateMachineSideEffectMemoryAccess *>(*it);
			if ( smsema && oracle->hasConflictingRemoteStores(smsema) ) {
				sideEffects.erase(it++);
			} else {
				it++;
			}
		}
	}
}

static StateMachine *
availExpressionAnalysis(StateMachine *sm,
			const AllowableOptimisations &opt,
			const Oracle::RegisterAliasingConfiguration *alias,
			bool is_ssa,
			Oracle *oracle,
			bool *done_something)
{
	std::map<const StateMachineState *, int> edgeLabels;
	if (dump_avail_table || debug_substitutions) {
		printf("Avail analysis on state machine:\n");
		printStateMachine(sm, stdout, edgeLabels);
	}

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
	potentiallyAvailable.findAllPotentiallyAvailable(sm, opt, oracle);

	/* build the initial availability map.  We start by assuming
	 * that everything is available everywhere, except that at the
	 * start of the very first state nothing is available, and
	 * then use a Tarski iteration to make everything
	 * consistent. */
	std::set<StateMachineState *> allStates;
	findAllStates(sm, allStates);
	std::map<StateMachineState *, avail_t> availOnEntry;
	for (auto it = allStates.begin();
	     !TIMEOUT && it != allStates.end();
	     it++)
		availOnEntry[*it] = potentiallyAvailable;
	availOnEntry[sm->root].clear();

	std::queue<StateMachineState *> statesNeedingRefresh;

	/* Tarski iteration.  */
	for (auto it = allStates.begin(); it != allStates.end(); it++)
		statesNeedingRefresh.push(*it);
	while (!statesNeedingRefresh.empty() && !TIMEOUT) {
		StateMachineState *state = statesNeedingRefresh.front();
		statesNeedingRefresh.pop();

		avail_t outputAvail(availOnEntry[state]);
		if ( state->type == StateMachineState::SideEffecting ) {
			StateMachineSideEffect *se = ((StateMachineSideEffecting *)state)->sideEffect;
			if (se)
				updateAvailSetForSideEffect(outputAvail, se, opt,
							    alias, oracle);
		}

		std::vector<StateMachineState *> edges;
		state->targets(edges);
		for (auto it2 = edges.begin(); it2 != edges.end(); it2++) {
			if (availOnEntry[*it2].merge(outputAvail, opt, is_ssa))
				statesNeedingRefresh.push(*it2);
		}
	}

	if (dump_avail_table) {
		printf("Final entry availability map:\n");
		for (auto it = availOnEntry.begin();
		     it != availOnEntry.end();
		     it++) {
			printf("Edge %d:\n", edgeLabels[it->first]);
			it->second.print(stdout);
		}
	}

	if (TIMEOUT)
		return sm;

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
		done_something,
		edgeLabels);
}

/* End of namespace */
}

StateMachine *
availExpressionAnalysis(StateMachine *sm,
			const AllowableOptimisations &opt,
			const Oracle::RegisterAliasingConfiguration *alias,
			bool is_ssa,
			Oracle *oracle,
			bool *done_something)
{
	sm->sanityCheck();
	if (is_ssa)
		sm->assertSSA();
	StateMachine *res = _availExpressionAnalysis::availExpressionAnalysis(sm, opt, alias, is_ssa, oracle, done_something);
	res->sanityCheck();
	if (is_ssa)
		res->assertSSA();
	return res;
}
