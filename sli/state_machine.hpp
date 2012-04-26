#ifndef STATEMACHINE_HPP__
#define STATEMACHINE_HPP__

#include <map>
#include <set>
#include <queue>

#include "simplify_irexpr.hpp"
#include "oracle_rip.hpp"
#include "typesdb.hpp"

class StateMachine;
class StateMachineEdge;
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

   freeVariablesMightAccessStack -- If false, assume that free
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
	f(freeVariablesMightAccessStack,bool)
#define optimisation_flags(f)						\
	_optimisation_flags(f)						\
	f(interestingStores, const std::set<DynAnalysisRip> *)		\
	f(nonLocalLoads, std::set<DynAnalysisRip> *)
public:
	static AllowableOptimisations defaultOptimisations;
	AllowableOptimisations(
#define mk_arg(name, type) type _ ## name,
		optimisation_flags(mk_arg)
#undef mk_arg
		AddressSpace *_as)
		:
#define mk_init(name, type) name(_ ## name),
		optimisation_flags(mk_init)
#undef mk_init
		as(_as)
	{
	}
	AllowableOptimisations(const AllowableOptimisations &o)
		:
#define mk_init(name, type) name(o.name),
		optimisation_flags(mk_init)
#undef mk_init
		as(o.as)
	{}

#define mk_field(name, type) type name;
	optimisation_flags(mk_field)
#undef mk_field

	/* If non-NULL, use this to resolve BadPtr expressions where
	   the address is a constant. */
	VexPtr<AddressSpace> as;

#define mk_set_value(name, type)				\
	AllowableOptimisations set ## name (type value) const	\
	{							\
		AllowableOptimisations res(*this);		\
		res.name = value;				\
		return res;					\
	}
	optimisation_flags(mk_set_value);
#undef mk_set_value

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
		res.as = as;
		return res;
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
		if ( name )			\
			x |= acc;		\
		acc *= 2;
		_optimisation_flags(do_flag)
#undef do_flag
		if (as != NULL)
			x |= acc;
		return x;
	}

	bool ignoreStore(const VexRip &rip) const {
		if (ignoreSideEffects)
			return true;
		if (interestingStores &&
		    !interestingStores->count(DynAnalysisRip(rip)))
			return true;
		return false;
	}

	/* If @addr is definitely accessible, set *@res to true and
	   return true.  If it's definitely not accessible, set *@res
	   to false and return true.  If we can't be sure, return
	   false. */
	bool addressAccessible(unsigned long addr, bool *res) const {
		if (!as)
			return false;
		*res = as->isReadable(addr, 1);
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
#else
	void sanityCheck() const;
	void assertAcyclic() const;
#endif

	NAMED_CLASS
};

class StateMachineState : public GarbageCollected<StateMachineState, &ir_heap> {
protected:
	StateMachineState(const VexRip &_origin) : origin(_origin) {}
public:
	VexRip origin; /* RIP we were looking at when we constructed
			* the thing.  Not very meaningful, but
			* occasionally provides useful hints for
			* debugging.*/

	/* Another peephole optimiser.  Again, must be
	   context-independent and result in no changes to the
	   semantic value of the machine, and can mutate in-place. */
	virtual StateMachineState *optimise(const AllowableOptimisations &, Oracle *, bool *, FreeVariableMap &,
					    std::set<StateMachineState *> &done) = 0;
	void findLoadedAddresses(std::set<IRExpr *> &out, const AllowableOptimisations &opt);
	virtual void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &) = 0;
	virtual bool canCrash(std::vector<StateMachineEdge *> &) = 0;
	virtual void targets(std::vector<StateMachineEdge *> &) = 0;
	virtual void targets(std::vector<const StateMachineEdge *> &) const = 0;
	void targets(std::set<StateMachineEdge *> &out) {
		std::vector<StateMachineEdge *> r;
		targets(r);
		for (auto it = r.begin(); it != r.end(); it++)
			out.insert(*it);
	}
	void targets(std::set<const StateMachineEdge *> &out) const {
		std::vector<const StateMachineEdge *> r;
		targets(r);
		for (auto it = r.begin(); it != r.end(); it++)
			out.insert(*it);
	}
	void targets(std::set<StateMachineState *> &out);
	void targets(std::set<const StateMachineState *> &out) const;
	void targets(std::vector<StateMachineState *> &out);
	void targets(std::vector<const StateMachineState *> &out) const;
	void targets(std::queue<StateMachineEdge *> &out);
	enum RoughLoadCount { noLoads, singleLoad, multipleLoads };
	RoughLoadCount roughLoadCount(RoughLoadCount acc = noLoads) const;
	void enumerateMentionedMemoryAccesses(std::set<VexRip> &out);
	virtual void prettyPrint(FILE *f, std::map<const StateMachineEdge *, int> &labels) const = 0;

#ifdef NDEBUG
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live, std::vector<const StateMachineEdge *> &done) const {}
#else
	virtual void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live, std::vector<const StateMachineEdge *> &done) const = 0;
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
	virtual void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &) = 0;
	virtual void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> *live = NULL) const = 0;
	NAMED_CLASS
};

class StateMachineEdge : public GarbageCollected<StateMachineEdge, &ir_heap> {
	void assertAcyclic(std::vector<const StateMachineEdge *> &,
			   std::set<const StateMachineEdge *> &) const;
public:
	void assertAcyclic() const;
	StateMachineEdge(StateMachineState *t) : target(t) {}
	StateMachineEdge(const std::vector<StateMachineSideEffect *> &_sideEffects,
			 StateMachineState *t)
		: target(t), sideEffects(_sideEffects)
	{}
	StateMachineState *target;
	std::vector<StateMachineSideEffect *> sideEffects;

	void prependSideEffect(StateMachineSideEffect *k) {
		std::vector<StateMachineSideEffect *> n;
		n.reserve(sideEffects.size() + 1);
		n.push_back(k);
		for (std::vector<StateMachineSideEffect *>::iterator it = sideEffects.begin();
		     it != sideEffects.end();
		     it++)
			n.push_back(*it);
		sideEffects = n;
	}

	void prettyPrint(FILE *f, std::map<const StateMachineEdge *, int> &labels) const {
		for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
			fprintf(f, "\t");
			(*it)->prettyPrint(f);
			fprintf(f, "\n");
		}
		target->prettyPrint(f, labels);
		fprintf(f, "\n");
	}
	void visit(HeapVisitor &hv) {
		hv(target);
		for (std::vector<StateMachineSideEffect *>::iterator it = sideEffects.begin();
		     it != sideEffects.end();
		     it++)
			hv(*it);
	}
	StateMachineEdge *optimise(const AllowableOptimisations &, Oracle *, bool *done_something, FreeVariableMap &,
				   std::set<StateMachineState *> &);
	void findLoadedAddresses(std::set<IRExpr *> &s, const AllowableOptimisations &opt) {
		if (TIMEOUT)
			return;
		target->findLoadedAddresses(s, opt);
		for (std::vector<StateMachineSideEffect *>::reverse_iterator it = sideEffects.rbegin();
		     it != sideEffects.rend();
		     it++)
			(*it)->updateLoadedAddresses(s, opt);
	}
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &s, const AllowableOptimisations &opt) {
		if (TIMEOUT)
			return;
		target->findUsedRegisters(s, opt);
		for (std::vector<StateMachineSideEffect *>::reverse_iterator it = sideEffects.rbegin();
		     it != sideEffects.rend();
		     it++)
			(*it)->findUsedRegisters(s, opt);
	}
	void enumerateMentionedMemoryAccesses(std::set<VexRip> &instrs);
	bool canCrash(std::vector<StateMachineEdge *> &memo) {
		for (auto it = memo.begin(); it != memo.end(); it++)
			if (*it == this)
				return false;
		memo.push_back(this);
		unsigned sz = memo.size();
		bool res = target->canCrash(memo);
		assert(sz == memo.size());
		assert(memo[sz - 1] == this);
		memo.pop_back();
		return res;
	}
	StateMachineState::RoughLoadCount roughLoadCount(StateMachineState::RoughLoadCount acc) const;
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live,
			 std::vector<const StateMachineEdge *> &done) const {
#ifndef NDEBUG
		for (auto it = done.begin(); it != done.end(); it++)
			if (*it == this)
				return;
		std::set<threadAndRegister, threadAndRegister::fullCompare> *live2;
		std::set<threadAndRegister, threadAndRegister::fullCompare> _live2;
		if (live) {
			live2 = &_live2;
			_live2 = *live;
		} else {
			live2 = NULL;
		}
		for (auto it = sideEffects.begin(); it != sideEffects.end(); it++) {
			if ((*it)->type == StateMachineSideEffect::Unreached) {
				/* Don't want to check past these,
				   because they often lead to bad
				   areas of the machine. */
				return;
			}
			(*it)->sanityCheck(live2);
		}
		if (TIMEOUT)
			return;
		unsigned sz = done.size();
		done.push_back(this);
		target->sanityCheck(live2, done);
		assert(done.back() == this);
		done.pop_back();
		assert(done.size() == sz);
#endif
	}

	NAMED_CLASS
};

class StateMachineTerminal : public StateMachineState {
protected:
	virtual void prettyPrint(FILE *f) const = 0;
	StateMachineTerminal(const VexRip &rip) : StateMachineState(rip) {}
public:
	StateMachineState *optimise(const AllowableOptimisations &, Oracle *, bool *, FreeVariableMap &,
				    std::set<StateMachineState *> &) { return this; }
	virtual void visit(HeapVisitor &hv) {}
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &) {}
	void targets(std::vector<StateMachineEdge *> &) { }
	void targets(std::vector<const StateMachineEdge *> &) const { }
	void prettyPrint(FILE *f, std::map<const StateMachineEdge *, int> &) const { prettyPrint(f); }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live,
			 std::vector<const StateMachineEdge *> &) const { return; }
};

class StateMachineUnreached : public StateMachineTerminal {
	StateMachineUnreached() : StateMachineTerminal(VexRip()) {}
	static VexPtr<StateMachineUnreached, &ir_heap> _this;
	void prettyPrint(FILE *f) const { fprintf(f, "<unreached>"); }
public:
	static StateMachineUnreached *get() {
		if (!_this) _this = new StateMachineUnreached();
		return _this;
	}
	bool canCrash(std::vector<StateMachineEdge *> &) { return false; }
};

class StateMachineCrash : public StateMachineTerminal {
	StateMachineCrash() : StateMachineTerminal(VexRip()) {}
	static VexPtr<StateMachineCrash, &ir_heap> _this;
public:
	static StateMachineCrash *get() {
		if (!_this) _this = new StateMachineCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<crash>"); }
	bool canCrash(std::vector<StateMachineEdge *> &) { return true; }
};

class StateMachineNoCrash : public StateMachineTerminal {
	StateMachineNoCrash() : StateMachineTerminal(VexRip()) {}
	static VexPtr<StateMachineNoCrash, &ir_heap> _this;
public:
	static StateMachineNoCrash *get() {
		if (!_this) _this = new StateMachineNoCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<survive>"); }
	bool canCrash(std::vector<StateMachineEdge *> &) { return false; }
};

/* A state machine node which always advances to another one.  These
   can be safely eliminated, but they're sometimes kind of handy when
   you're building the machine. */
class StateMachineProxy : public StateMachineState {
public:
	StateMachineEdge *target;

	StateMachineProxy(const VexRip &origin, StateMachineState *t)
		: StateMachineState(origin),
		  target(new StateMachineEdge(t))		  
	{
	}
	StateMachineProxy(const VexRip &origin, StateMachineEdge *t)
		: StateMachineState(origin),
		  target(t)
	{
	}
	void prettyPrint(FILE *f, std::map<const StateMachineEdge *, int> &labels) const
	{
		fprintf(f, "{%s:l%d}", origin.name(), labels[target]);
	}
	void visit(HeapVisitor &hv)
	{
		hv(target);
	}
	StateMachineState *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something, FreeVariableMap &fv,
				    std::set<StateMachineState *> &done);
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &s, const AllowableOptimisations &opt) {
		target->findUsedRegisters(s, opt);
	}
	bool canCrash(std::vector<StateMachineEdge *> &memo) { return target->canCrash(memo); }
	void targets(std::vector<StateMachineEdge *> &out) { out.push_back(target); }
	void targets(std::vector<const StateMachineEdge *> &out) const { out.push_back(target); }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live,
			 std::vector<const StateMachineEdge *> &done) const
	{
		target->sanityCheck(live, done);
	}
};

class StateMachineBifurcate : public StateMachineState {
public:
	StateMachineBifurcate(const VexRip &origin,
			      IRExpr *_condition,
			      StateMachineEdge *t,
			      StateMachineEdge *f)
		: StateMachineState(origin),
		  condition(_condition),
		  trueTarget(t),
		  falseTarget(f)
	{
	}	
	StateMachineBifurcate(const VexRip &origin,
			      IRExpr *_condition,
			      StateMachineState *t,
			      StateMachineState *f)
		: StateMachineState(origin),
		  condition(_condition),
		  trueTarget(new StateMachineEdge(t)),
		  falseTarget(new StateMachineEdge(f))
	{
	}

	IRExpr *condition; /* Should be typed Ity_I1.  If zero, we go
			      to the false target.  Otherwise, we go
			      to the true one. */
	StateMachineEdge *trueTarget;
	StateMachineEdge *falseTarget;

	void prettyPrint(FILE *f, std::map<const StateMachineEdge *, int> &labels) const {
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
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &s, const AllowableOptimisations &opt);
	bool canCrash(std::vector<StateMachineEdge *> &memo) {
		return trueTarget->canCrash(memo) || falseTarget->canCrash(memo);
	}
	void targets(std::vector<StateMachineEdge *> &out) {
		out.push_back(falseTarget);
		out.push_back(trueTarget);
	}
	void targets(std::vector<const StateMachineEdge *> &out) const {
		out.push_back(falseTarget);
		out.push_back(trueTarget);
	}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live,
			 std::vector<const StateMachineEdge *> &done) const
	{
		sanityCheckIRExpr(condition, live);
		assert(condition->type() == Ity_I1);
		trueTarget->sanityCheck(live, done);
		falseTarget->sanityCheck(live, done);
	}
};

/* A node in the state machine representing a bit of code which we
   haven't explored yet. */
class StateMachineStub : public StateMachineTerminal {
public:
	VexRip target;

	StateMachineStub(const VexRip &origin, const VexRip &t) : StateMachineTerminal(origin), target(t) {}

	void prettyPrint(FILE *f) const
	{
		fprintf(f, "<%s: jmp %s>", origin.name(), target.name());
	}
	void visit(HeapVisitor &hv) { }
	bool canCrash(std::vector<StateMachineEdge *> &) { return false; }
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
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &) {}
	void visit(HeapVisitor &hv) {}
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> *) const {}
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
	virtual void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
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
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &);
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		StateMachineSideEffectMemoryAccess::sanityCheck(live);
		sanityCheckIRExpr(data, live);
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
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &);
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		StateMachineSideEffectMemoryAccess::sanityCheck(live);
		if (live)
			live->insert(target);
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
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &);
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		sanityCheckIRExpr(value, live);
		if (live)
			live->insert(target);
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
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &);
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		sanityCheckIRExpr(value, live);
		assert(value->type() == Ity_I1);
	}
};
class StateMachineSideEffectPhi : public StateMachineSideEffect {
public:
	StateMachineSideEffectPhi(const threadAndRegister &_reg,
				  const std::set<unsigned> &_generations)
		: StateMachineSideEffect(StateMachineSideEffect::Phi),
		  reg(_reg)
	{
		generations.reserve(_generations.size());
		for (auto it = _generations.begin(); it != _generations.end(); it++)
			generations.push_back(*it);
	}
	StateMachineSideEffectPhi(const threadAndRegister &_reg,
				  const std::vector<unsigned> &_generations)
		: StateMachineSideEffect(StateMachineSideEffect::Phi),
		  reg(_reg), generations(_generations)
	{
	}
	threadAndRegister reg;
	std::vector<unsigned> generations;
	void prettyPrint(FILE *f) const {
		fprintf(f, "Phi");
		reg.prettyPrint(f);
		fprintf(f, "(");
		for (auto it = generations.begin(); it != generations.end(); it++) {
			if (it != generations.begin())
				fprintf(f, ", ");
			fprintf(f, "%d", *it);
		}
		fprintf(f, ")");
	}
	void visit(HeapVisitor &hv) {}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {}
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &a, const AllowableOptimisations &) { a.erase(reg); }
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		if (live)
			live->insert(reg);
	}
};

void printStateMachine(const StateMachine *sm, FILE *f);
void printStateMachine(const StateMachine *sm, FILE *f, std::map<const StateMachineEdge *, int> &labels);
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
enumStatesAndEdges(StateMachine *sm,
		   std::set<stateType *> *states,
		   std::set<StateMachineEdge *> *edges)
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
		if (edges) {
			std::vector<StateMachineEdge *> targets;
			s->targets(targets);
			for (auto it = targets.begin(); it != targets.end(); it++) {
				if (edges->insert(*it).second)
					toVisit.insert((*it)->target);
			}
		} else {
			s->targets(toVisit);
		}
	}
}

#endif /* !STATEMACHINE_HPP__ */
