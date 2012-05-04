#ifndef STATEMACHINE_HPP__
#define STATEMACHINE_HPP__

#include <map>
#include <set>
#include <queue>

#include "simplify_irexpr.hpp"
#include "oracle_rip.hpp"
#include "typesdb.hpp"

class StateMachine;
class StateMachineSideEffect;

#ifdef NDEBUG
static inline
#endif
void sanityCheckIRExpr(IRExpr *e, const std::set<threadAndRegister, threadAndRegister::fullCompare> *live)
#ifdef NDEBUG
{}
#else
;
#endif

/* Flags:

   assumePrivateStack -- Assume that the stack is ``private'', in the
                         sense that no constant expressions can ever
                         alias with rsp.

   assumeExecutesAtomically -- Assume that the state machine executes
                               atomically.  This is useful for the
                               read-side machine, but not for the
                               write-side ones.

   ignoreSideEffects -- Effectively assume that the program terminates
  	                as soon as the machine completes, so that
  	                stores which aren't loaded by this machine are
  	                necessarily redundant.

   assumeNoInterferingStores -- Assume that there will be no stores
                                from other threads which interfere
                                with the machine we're currently

   freeVariablesNeverAccessStack -- If true, assume that free
 				    variables can never point at the
 				    current stack frame.  This is
 				    appropriate for state machines
 				    generated at function heads, for
 				    instance.

   Other fields:

   interestingStores -- Bit of a hack: sometimes, only some side
	                effects are interesting, so allow them to be
	                listed here.  If haveInterestingStoresSet is
	                false then we don't look at interestingStores
	                at all, and instead rely on ignoreSideEffects.

   nonLocalLoads -- If this is non-NULL then rather than using the
                    oracle to check whether loads might possibly load,
                    we just look in here.

   as -- if non-NULL, used to resolve BadPtr expressions with a
         constant address.

*/
class AllowableOptimisations {
#define _optimisation_flags(f)						\
	f(assumePrivateStack, bool)					\
	f(assumeExecutesAtomically, bool)				\
	f(ignoreSideEffects, bool)					\
	f(assumeNoInterferingStores, bool)				\
	f(freeVariablesNeverAccessStack,bool)
#define optimisation_flags(f)						\
	_optimisation_flags(f)						\
	f(interestingStores, const std::set<DynAnalysisRip> *)		\
	f(nonLocalLoads, std::set<DynAnalysisRip> *)

	/* The value of @d doesn't matter, it's just there so that we
	   can select this constructor. */
	AllowableOptimisations(double d)
		:
#define default_flag(name, type)		\
		_ ## name(false),
		_optimisation_flags(default_flag)
#undef default_flag
		_interestingStores(NULL),
		_nonLocalLoads(NULL),
		_as(NULL)
	{}

#define mk_field(name, type) type _ ## name;
	optimisation_flags(mk_field)
#undef mk_field

	/* If non-NULL, use this to resolve BadPtr expressions where
	   the address is a constant. */
	VexPtr<AddressSpace> _as;

public:
	static AllowableOptimisations defaultOptimisations;
	AllowableOptimisations(
#define mk_arg(name, type) type __ ## name,
		optimisation_flags(mk_arg)
#undef mk_arg
		AddressSpace *__as)
		:
#define mk_init(name, type) _ ## name(__ ## name),
		optimisation_flags(mk_init)
#undef mk_init
		_as(__as)
	{
	}
	AllowableOptimisations(const AllowableOptimisations &o)
		:
#define mk_init(name, type) _ ## name(o._ ## name),
		optimisation_flags(mk_init)
#undef mk_init
		_as(o._as)
	{}

#define mk_set_value(name, type)				\
	AllowableOptimisations set ## name (type value) const	\
	{							\
		AllowableOptimisations res(*this);		\
		res._ ## name = value;				\
		return res;					\
	}
	optimisation_flags(mk_set_value);
#undef mk_set_value

#define mk_get_value(name, type)				\
	type name() const					\
	{							\
		return _ ## name ;				\
	}
	optimisation_flags(mk_get_value)
#undef mk_get_value
#define mk_set_flags(name, type)				\
	AllowableOptimisations enable ## name () const		\
	{							\
		return set ## name(true);			\
	}							\
	AllowableOptimisations disable ## name () const		\
	{							\
		return set ## name(false);			\
	}
	_optimisation_flags(mk_set_flags)
#undef mk_set_flags

	AllowableOptimisations setAddressSpace(AddressSpace *as) const
	{
		AllowableOptimisations res(*this);
		res._as = as;
		return res;
	}

	AddressSpace *getAddressSpace()
	{
		return _as;
	}

	unsigned asUnsigned() const {
		unsigned x = 1; /* turning off all of the optional
				   optimisations doesn't turn off the
				   ones which are always available, so
				   have an implicit bit for them.
				   i.e. 0 means no optimisations at
				   all, and 1 means only the most
				   basic ones which are always
				   safe. */

		unsigned acc = 2;

#define do_flag(name, type)			\
		if ( _ ## name )			\
			x |= acc;		\
		acc *= 2;
		_optimisation_flags(do_flag)
#undef do_flag
		if (_as != NULL)
			x |= acc;
		return x;
	}

	bool ignoreStore(const VexRip &rip) const {
		if (_ignoreSideEffects)
			return true;
		if (_interestingStores &&
		    !_interestingStores->count(DynAnalysisRip(rip)))
			return true;
		return false;
	}

	/* If @addr is definitely accessible, set *@res to true and
	   return true.  If it's definitely not accessible, set *@res
	   to false and return true.  If we can't be sure, return
	   false. */
	bool addressAccessible(unsigned long addr, bool *res) const {
		if (!_as)
			return false;
		*res = _as->isReadable(addr, 1);
		return true;
	}

#undef _optimisation_flags
#undef optimisation_flags
};

class IRExprTransformer;

/* Caution: needs someone external to visit it! */
class FreeVariableMap {
	typedef gc_heap_map<FreeVariableKey, IRExpr, &ir_heap>::type map_t;
public:
	map_t *content;
	FreeVariableMap()
		: content(new map_t())
	{}
	FreeVariableMap(const FreeVariableMap &p)
		: content(new map_t(*p.content))
	{}
	FreeVariableMap(const FreeVariableMap &p, std::vector<std::pair<FreeVariableKey, IRExpr *> > &delta)
		: content(new map_t(*p.content))
	{
		for (unsigned x = 0; x < delta.size(); x++) {
			assert(delta[x].second);
			content->set(delta[x].first, delta[x].second);
		}
	}
	void merge(FreeVariableMap &other) {
		for (map_t::iterator it = other.content->begin();
		     it != other.content->end();
		     it++) {
			assert(!content->get(it.key()));
			content->set(it.key(), it.value());
		}
	}
	IRExpr *get(FreeVariableKey k) { IRExpr *res = content->get(k); assert(res); return res; }
	void visit(HeapVisitor &hv) { hv(content); }
	void applyTransformation(IRExprTransformer &t, bool *done_something);
	void print(FILE *f) const;
	bool parse(const char *str, const char **succ);
	bool empty() const { return content->empty(); }
	void optimise(const AllowableOptimisations &opt, bool *done_something);
};

class StateMachineState;

class StateMachine : public GarbageCollected<StateMachine, &ir_heap> {
	StateMachine(StateMachineState *_root, const VexRip &_origin, unsigned _tid)
		: root(_root), origin(_origin), tid(_tid)
	{
	}
public:
	StateMachineState *root;
	VexRip origin;
	FreeVariableMap freeVariables;
	unsigned tid;

	static bool parse(StateMachine **out, const char *str, const char **suffix);

	StateMachine(StateMachineState *_root, const VexRip &_origin, const FreeVariableMap &fv, unsigned _tid)
		: root(_root), origin(_origin), freeVariables(fv), tid(_tid)
	{
	}
	StateMachine(StateMachine *parent, const VexRip &_origin, StateMachineState *new_root)
		: root(new_root), origin(_origin), freeVariables(parent->freeVariables),
		  tid(parent->tid)
	{}
	StateMachine(StateMachine *parent)
		: root(parent->root), origin(parent->origin), freeVariables(parent->freeVariables),
		  tid(parent->tid)
	{}
	StateMachine(StateMachine *parent, std::vector<std::pair<FreeVariableKey, IRExpr *> > &delta)
		: root(parent->root),
		  origin(parent->origin),
		  freeVariables(parent->freeVariables, delta),
		  tid(parent->tid)
	{}
	StateMachine *optimise(const AllowableOptimisations &opt,
			       Oracle *oracle,
			       bool *done_something);
	void visit(HeapVisitor &hv) { hv(root); freeVariables.visit(hv); }
#ifdef NDEBUG
	void sanityCheck() const {}
	void assertAcyclic() const {}
	void assertSSA() const {}
#else
	void sanityCheck() const;
	void assertAcyclic() const;
	void assertSSA() const;
#endif

	NAMED_CLASS
};

class StateMachineState : public GarbageCollected<StateMachineState, &ir_heap> {
public:
#define all_state_types(f)						\
	f(Unreached) f(Crash) f(NoCrash) f(Stub) f(Bifurcate) f(SideEffecting)
#define mk_state_type(name) name ,
	enum stateType {
		all_state_types(mk_state_type)
	};
#undef mk_state_type
	static bool stateTypeIsTerminal(enum stateType t) {
		return t == Unreached || t == Crash || t == NoCrash || t == Stub;
	}
protected:
	StateMachineState(const VexRip &_origin,
			  enum stateType _type)
		: type(_type), origin(_origin)
	{}
	virtual bool _canCrash(std::set<const StateMachineState *> &memo) const = 0;
public:
	stateType type;
	VexRip origin; /* RIP we were looking at when we constructed
			* the thing.  Not very meaningful, but
			* occasionally provides useful hints for
			* debugging.*/

	bool isTerminal() const {
		return stateTypeIsTerminal(type);
	}

	/* Another peephole optimiser.  Again, must be
	   context-independent and result in no changes to the
	   semantic value of the machine, and can mutate in-place. */
	virtual StateMachineState *optimise(const AllowableOptimisations &, Oracle *, bool *, FreeVariableMap &,
					    std::set<StateMachineState *> &done) = 0;
	void findLoadedAddresses(std::set<IRExpr *> &out, const AllowableOptimisations &opt);
	bool canCrash(std::set<const StateMachineState *> &memo) const {
		if (memo.insert(this).second)
			return _canCrash(memo);
		else
			return false;
	}
	virtual void targets(std::vector<StateMachineState *> &) = 0;
	virtual void targets(std::vector<const StateMachineState *> &) const = 0;
	void targets(std::set<StateMachineState *> &out) {
		std::vector<StateMachineState *> r;
		targets(r);
		for (auto it = r.begin(); it != r.end(); it++)
			out.insert(*it);
	}
	void targets(std::set<const StateMachineState *> &out) const {
		std::vector<const StateMachineState *> r;
		targets(r);
		for (auto it = r.begin(); it != r.end(); it++)
			out.insert(*it);
	}
	void targets(std::queue<StateMachineState *> &out);
	enum RoughLoadCount { noLoads, singleLoad, multipleLoads };
	RoughLoadCount roughLoadCount(RoughLoadCount acc = noLoads) const;
	void enumerateMentionedMemoryAccesses(std::set<VexRip> &out);
	virtual void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const = 0;

	virtual StateMachineSideEffect *getSideEffect() = 0;
	virtual const StateMachineSideEffect *getSideEffect() const {
		return const_cast<StateMachineState *>(this)->getSideEffect();
	}

	virtual void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const = 0;

#ifndef NDEBUG
	void assertAcyclic(std::vector<const StateMachineState *> &stack,
			   std::set<const StateMachineState *> &clean) const;
#endif

	NAMED_CLASS
};

class StateMachineSideEffect : public GarbageCollected<StateMachineSideEffect, &ir_heap>, public PrettyPrintable {
	StateMachineSideEffect(); /* DNE */
public:
	enum sideEffectType {
		Load, Store, Copy, Unreached, AssertFalse, Phi
	} type;
protected:
	StateMachineSideEffect(enum sideEffectType _type)
		: type(_type)
	{}
public:
	virtual StateMachineSideEffect *optimise(const AllowableOptimisations &, Oracle *, bool *) = 0;
	virtual void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) = 0;
	virtual void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live = NULL) const = 0;
	virtual bool definesRegister(threadAndRegister &res) const = 0;
	NAMED_CLASS
};

class StateMachineTerminal : public StateMachineState {
protected:
	virtual void prettyPrint(FILE *f) const = 0;
	StateMachineTerminal(const VexRip &rip, StateMachineState::stateType type) : StateMachineState(rip, type) {}
	virtual bool canCrash() const = 0;
	bool _canCrash(std::set<const StateMachineState *> &) const { return canCrash(); }
public:
	StateMachineState *optimise(const AllowableOptimisations &, Oracle *, bool *, FreeVariableMap &,
				    std::set<StateMachineState *> &) { return this; }
	virtual void visit(HeapVisitor &hv) {}
	void targets(std::vector<StateMachineState *> &) { }
	void targets(std::vector<const StateMachineState *> &) const { }
	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &) const { prettyPrint(f); }
	StateMachineSideEffect *getSideEffect() { return NULL; }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *) const { return; }
};

class StateMachineUnreached : public StateMachineTerminal {
	StateMachineUnreached() : StateMachineTerminal(VexRip(), StateMachineState::Unreached) {}
	static VexPtr<StateMachineUnreached, &ir_heap> _this;
	void prettyPrint(FILE *f) const { fprintf(f, "<unreached>"); }
	bool canCrash() const { return false; }
public:
	static StateMachineUnreached *get() {
		if (!_this) _this = new StateMachineUnreached();
		return _this;
	}
};

class StateMachineCrash : public StateMachineTerminal {
	StateMachineCrash() : StateMachineTerminal(VexRip(), StateMachineState::Crash) {}
	static VexPtr<StateMachineCrash, &ir_heap> _this;
	bool canCrash() const { return true; }
public:
	static StateMachineCrash *get() {
		if (!_this) _this = new StateMachineCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<crash>"); }
};

class StateMachineNoCrash : public StateMachineTerminal {
	StateMachineNoCrash() : StateMachineTerminal(VexRip(), StateMachineState::NoCrash) {}
	static VexPtr<StateMachineNoCrash, &ir_heap> _this;
	bool canCrash() const { return false; }
public:
	static StateMachineNoCrash *get() {
		if (!_this) _this = new StateMachineNoCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<survive>"); }
};

class StateMachineSideEffecting : public StateMachineState {
	bool _canCrash(std::set<const StateMachineState *> &memo) const { return target->canCrash(memo); }
public:
	StateMachineState *target;
	StateMachineSideEffect *sideEffect;

	StateMachineSideEffecting(const VexRip &origin, StateMachineSideEffect *smse, StateMachineState *t)
		: StateMachineState(origin, StateMachineState::SideEffecting),
		  target(t),
		  sideEffect(smse)
	{
	}
	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const
	{
		fprintf(f, "{%s:", origin.name());
		if (sideEffect)
			sideEffect->prettyPrint(f);
		fprintf(f, " then l%d}", labels[target]);
	}
	void visit(HeapVisitor &hv)
	{
		hv(target);
		hv(sideEffect);
	}
	void prependSideEffect(StateMachineSideEffect *sideEffect);

	StateMachineState *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something, FreeVariableMap &fv,
				    std::set<StateMachineState *> &done);
	void targets(std::vector<StateMachineState *> &out) { out.push_back(target); }
	void targets(std::vector<const StateMachineState *> &out) const { out.push_back(target); }
	StateMachineSideEffect *getSideEffect() { return sideEffect; }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const
	{
		if (sideEffect)
			sideEffect->sanityCheck(live);
	}
};

class StateMachineBifurcate : public StateMachineState {
	bool _canCrash(std::set<const StateMachineState *> &memo) const {
		return trueTarget->canCrash(memo) || falseTarget->canCrash(memo);
	}
public:
	StateMachineBifurcate(const VexRip &origin,
			      IRExpr *_condition,
			      StateMachineState *t,
			      StateMachineState *f)
		: StateMachineState(origin, StateMachineState::Bifurcate),
		  condition(_condition),
		  trueTarget(t),
		  falseTarget(f)
	{
	}

	IRExpr *condition; /* Should be typed Ity_I1.  If zero, we go
			      to the false target.  Otherwise, we go
			      to the true one. */
	StateMachineState *trueTarget;
	StateMachineState *falseTarget;

	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const {
		fprintf(f, "%s: if (", origin.name());
		ppIRExpr(condition, f);
		fprintf(f, ") then l%d else l%d",
			labels[trueTarget], labels[falseTarget]);
	}
	void visit(HeapVisitor &hv)
	{
		hv(trueTarget);
		hv(falseTarget);
		hv(condition);
	}
	StateMachineState *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something, FreeVariableMap &,
				    std::set<StateMachineState *> &);
	void targets(std::vector<StateMachineState *> &out) {
		out.push_back(falseTarget);
		out.push_back(trueTarget);
	}
	void targets(std::vector<const StateMachineState *> &out) const {
		out.push_back(falseTarget);
		out.push_back(trueTarget);
	}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const
	{
		sanityCheckIRExpr(condition, live);
		assert(condition->type() == Ity_I1);
	}
	StateMachineSideEffect *getSideEffect() { return NULL; }
};

/* A node in the state machine representing a bit of code which we
   haven't explored yet. */
class StateMachineStub : public StateMachineTerminal {
	bool canCrash() const { return false; }
public:
	VexRip target;

	StateMachineStub(const VexRip &origin, const VexRip &t) : StateMachineTerminal(origin, StateMachineState::Stub), target(t) {}

	void prettyPrint(FILE *f) const
	{
		fprintf(f, "<%s: jmp %s>", origin.name(), target.name());
	}
	void visit(HeapVisitor &hv) { }
};


class StateMachineSideEffectUnreached : public StateMachineSideEffect {
	static VexPtr<StateMachineSideEffectUnreached, &ir_heap> _this;
	StateMachineSideEffectUnreached() : StateMachineSideEffect(StateMachineSideEffect::Unreached) {}
public:
	static StateMachineSideEffectUnreached *get() {
		if (!_this) _this = new StateMachineSideEffectUnreached();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<unreached>"); }
	StateMachineSideEffect *optimise(const AllowableOptimisations &, Oracle *, bool *) { return this; }
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {}
	void visit(HeapVisitor &hv) {}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *) const {}
	bool definesRegister(threadAndRegister &reg) const {
		return false;
	}
};

class StateMachineSideEffectMemoryAccess : public StateMachineSideEffect {
public:
	IRExpr *addr;
	MemoryAccessIdentifier rip;
	StateMachineSideEffectMemoryAccess(IRExpr *_addr, const MemoryAccessIdentifier &_rip,
					   StateMachineSideEffect::sideEffectType _type)
		: StateMachineSideEffect(_type), addr(_addr), rip(_rip)
	{
		if (addr)
			sanityCheck(NULL);
	}
	virtual void visit(HeapVisitor &hv) {
		hv(addr);
	}
	virtual void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		sanityCheckIRExpr(addr, live);
		assert(addr->type() == Ity_I64);
	}
};
class StateMachineSideEffectStore : public StateMachineSideEffectMemoryAccess {
public:
	StateMachineSideEffectStore(IRExpr *_addr, IRExpr *_data, const MemoryAccessIdentifier &_rip)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, StateMachineSideEffect::Store),
		  data(_data)
	{
	}
	IRExpr *data;
	void prettyPrint(FILE *f) const {
		fprintf(f, "*(");
		ppIRExpr(addr, f);
		fprintf(f, ") <- ");
		ppIRExpr(data, f);
		fprintf(f, " @ %s", rip.name());
	}
	void visit(HeapVisitor &hv) {
		StateMachineSideEffectMemoryAccess::visit(hv);
		hv(data);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &opt);
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		StateMachineSideEffectMemoryAccess::sanityCheck(live);
		sanityCheckIRExpr(data, live);
	}
	bool definesRegister(threadAndRegister &reg) const {
		return false;
	}
};

template <typename ret>
class nullaryFunction {
public:
	virtual ret operator()() = 0;
};
typedef nullaryFunction<threadAndRegister> threadAndRegisterAllocator;
class StateMachineSideEffectLoad : public StateMachineSideEffectMemoryAccess {
	void constructed();
public:
	StateMachineSideEffectLoad(threadAndRegisterAllocator &alloc, IRExpr *_addr, const MemoryAccessIdentifier &_rip, IRType _type)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, StateMachineSideEffect::Load),
		  target(alloc()), type(_type)
	{
		constructed();
	}
	StateMachineSideEffectLoad(threadAndRegister reg, IRExpr *_addr, const MemoryAccessIdentifier &_rip, IRType _type)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, StateMachineSideEffect::Load),
		  target(reg), type(_type)
	{
		constructed();
	}
	threadAndRegister target;
	IRType type;
	void prettyPrint(FILE *f) const {
		fprintf(f, "LOAD ");
		target.prettyPrint(f);
		fprintf(f, ":");
		ppIRType(type, f);
		fprintf(f, " <- *(");
		ppIRExpr(addr, f);
		fprintf(f, ")@%s", rip.name());
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {
		l.insert(addr);
	}
	bool definesRegister(threadAndRegister &reg) const {
		reg = target;
		return true;
	}
};
class StateMachineSideEffectCopy : public StateMachineSideEffect {
public:
	StateMachineSideEffectCopy(threadAndRegister k, IRExpr *_value)
		: StateMachineSideEffect(StateMachineSideEffect::Copy),
		  target(k), value(_value)
	{
	}
	threadAndRegister target;
	IRExpr *value;
	void prettyPrint(FILE *f) const {
		fprintf(f, "COPY ");
		target.prettyPrint(f);
		fprintf(f, " = ");
		ppIRExpr(value, f);
	}
	void visit(HeapVisitor &hv) {
		hv(value);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) { }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		sanityCheckIRExpr(value, live);
	}
	bool definesRegister(threadAndRegister &reg) const {
		reg = target;
		return true;
	}
};
class StateMachineSideEffectAssertFalse : public StateMachineSideEffect {
public:
	StateMachineSideEffectAssertFalse(IRExpr *_value)
		: StateMachineSideEffect(StateMachineSideEffect::AssertFalse),
		  value(_value)
	{
	}
	IRExpr *value;
	void prettyPrint(FILE *f) const {
		fprintf(f, "Assert !(");
		ppIRExpr(value, f);
		fprintf(f, ")");
	}
	void visit(HeapVisitor &hv) {
		hv(value);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) { }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		sanityCheckIRExpr(value, live);
		assert(value->type() == Ity_I1);
	}
	bool definesRegister(threadAndRegister &reg) const {
		return false;
	}
};
class StateMachineSideEffectPhi : public StateMachineSideEffect {
public:
	threadAndRegister reg;
	std::vector<std::pair<unsigned, IRExpr *> > generations;
	StateMachineSideEffectPhi(const threadAndRegister &_reg,
				  const std::set<unsigned> &_generations)
		: StateMachineSideEffect(StateMachineSideEffect::Phi),
		  reg(_reg)
	{
		generations.reserve(_generations.size());
		for (auto it = _generations.begin(); it != _generations.end(); it++) {
			std::pair<unsigned, IRExpr *> item;
			item.first = *it;
			item.second = NULL;
			generations.push_back(item);
		}
	}
	StateMachineSideEffectPhi(const threadAndRegister &_reg,
				  const std::vector<unsigned> &_generations)
		: StateMachineSideEffect(StateMachineSideEffect::Phi),
		  reg(_reg)
	{
		generations.reserve(_generations.size());
		for (auto it = _generations.begin(); it != _generations.end(); it++) {
			std::pair<unsigned, IRExpr *> item;
			item.first = *it;
			item.second = NULL;
			generations.push_back(item);
		}
	}
	StateMachineSideEffectPhi(const threadAndRegister &_reg,
				  const std::vector<std::pair<unsigned, IRExpr *> > &_generations)
		: StateMachineSideEffect(StateMachineSideEffect::Phi),
		  reg(_reg), generations(_generations)
	{
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "Phi");
		reg.prettyPrint(f);
		fprintf(f, "(");
		for (auto it = generations.begin(); it != generations.end(); it++) {
			if (it != generations.begin())
				fprintf(f, ", ");
			fprintf(f, "%d", it->first);
			if (it->second) {
				fprintf(f, "=");
				ppIRExpr(it->second, f);
			}
		}
		fprintf(f, ")");
	}
	void visit(HeapVisitor &hv) {}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		assert(generations.size() != 0);
	}
	bool definesRegister(threadAndRegister &reg) const {
		reg = this->reg;
		return true;
	}
};

void printStateMachine(const StateMachine *sm, FILE *f);
void printStateMachine(const StateMachine *sm, FILE *f, std::map<const StateMachineState *, int> &labels);
bool sideEffectsBisimilar(StateMachineSideEffect *smse1,
			  StateMachineSideEffect *smse2,
			  const AllowableOptimisations &opt);
bool parseStateMachine(StateMachine **out, const char *str, const char **suffix);
StateMachine *readStateMachine(int fd);

bool parseStateMachineSideEffect(StateMachineSideEffect **out,
				 const char *str,
				 const char **suffix);

template <typename t> t
pop(std::set<t> &x)
{
	auto it = x.begin();
	if (it == x.end()) abort();
	t res = *it;
	x.erase(it);
	return res;
}

template <typename stateType> void
enumStates(StateMachine *sm, std::set<stateType *> *states)
{
	std::set<StateMachineState *> toVisit;
	std::set<StateMachineState *> visited;

	toVisit.insert(sm->root);
	while (!toVisit.empty()) {
		StateMachineState *s = pop(toVisit);
		if (!visited.insert(s).second)
			continue;
		if (states) {
			stateType *ss = dynamic_cast<stateType *>(s);
			if (ss)
				states->insert(ss);
		}
		s->targets(toVisit);
	}
}

template <typename stateType> void
enumStates(const StateMachine *sm, std::set<const stateType *> *states)
{
	std::set<const StateMachineState *> toVisit;
	std::set<const StateMachineState *> visited;

	toVisit.insert(sm->root);
	while (!toVisit.empty()) {
		const StateMachineState *s = pop(toVisit);
		if (!visited.insert(s).second)
			continue;
		if (states) {
			const stateType *ss = dynamic_cast<const stateType *>(s);
			if (ss)
				states->insert(ss);
		}
		s->targets(toVisit);
	}
}

template <typename stateType> void
enumStates(const StateMachine *sm, std::vector<const stateType *> *states)
{
	std::set<const StateMachineState *> toVisit;
	std::set<const StateMachineState *> visited;

	toVisit.insert(sm->root);
	while (!toVisit.empty()) {
		const StateMachineState *s = pop(toVisit);
		if (!visited.insert(s).second)
			continue;
		if (states) {
			const stateType *ss = dynamic_cast<const stateType *>(s);
			if (ss)
				states->push_back(ss);
		}
		s->targets(toVisit);
	}
}

#endif /* !STATEMACHINE_HPP__ */
