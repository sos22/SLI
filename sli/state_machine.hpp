#ifndef STATEMACHINE_HPP__
#define STATEMACHINE_HPP__

#include <map>
#include <set>

#include "simplify_irexpr.hpp"
#include "oracle_rip.hpp"

class StateMachine;
class StateMachineEdge;
class StateMachineSideEffect;

#ifdef NDEBUG
static inline
#endif
void sanityCheckIRExpr(IRExpr *e, const std::set<threadAndRegister, threadAndRegister::fullCompare> &live)
#ifdef NDEBUG
{}
#else
;
#endif

class AllowableOptimisations {
public:
	static AllowableOptimisations defaultOptimisations;
	AllowableOptimisations(bool x, bool s, bool a, bool i, bool as, bool fvmas,
			       AddressSpace *_as)
		: xPlusMinusX(x), assumePrivateStack(s), assumeExecutesAtomically(a),
		  ignoreSideEffects(i), assumeNoInterferingStores(as),
		  freeVariablesMightAccessStack(fvmas), as(_as), haveInterestingStoresSet(false)
	{
	}
	AllowableOptimisations(const AllowableOptimisations &o)
		: xPlusMinusX(o.xPlusMinusX),
		  assumePrivateStack(o.assumePrivateStack),
		  assumeExecutesAtomically(o.assumeExecutesAtomically),
		  ignoreSideEffects(o.ignoreSideEffects),
		  assumeNoInterferingStores(o.assumeNoInterferingStores),
		  freeVariablesMightAccessStack(o.freeVariablesMightAccessStack),
		  as(o.as),
		  haveInterestingStoresSet(o.haveInterestingStoresSet),
		  interestingStores(o.interestingStores)
	{}

	/* Transform x + (-x) to 0.  This is always safe, in the sense
	   that x + (-x) is always zero, but actually checking it can
	   sometimes lead to an infinite recursion if you're not a bit
	   careful.  This should pretty much only be turned off from
	   inside the optimiser. */
	/* (The same toggle also controls the rule x & ~x -> 0) */
	bool xPlusMinusX;

	/* Assume that the stack is ``private'', in the sense that no
	   constant expressions can ever alias with rsp. */
	bool assumePrivateStack;

	/* Assume that the state machine executes atomically.  This is
	   useful for the read-side machine, but not for the
	   write-side ones. */
	bool assumeExecutesAtomically;

	/* Effectively assume that the program terminates as soon as
	   the machine completes, so that stores which aren't loaded
	   by this machine are necessarily redundant. */
	bool ignoreSideEffects;

	/* Assume that there will be no stores from other threads
	   which interfere with the machine we're currently
	   examining. */
	bool assumeNoInterferingStores;

	/* If false, assume that free variables can never point at the
	   current stack frame.  This is appropriate for state
	   machines generated at function heads, for instance. */
	bool freeVariablesMightAccessStack;

	/* If non-NULL, use this to resolve BadPtr expressions where
	   the address is a constant. */
	VexPtr<AddressSpace> as;

	/* Bit of a hack: sometimes, only some side effects are
	   interesting, so allow them to be listed here.  If
	   haveInterestingStoresSet is false then we don't look at
	   interestingStores at all, and instead rely on
	   ignoreSideEffects. */
	bool haveInterestingStoresSet;
	std::set<VexRip> interestingStores;

	/* If this is non-NULL then rather than using the oracle to
	   check whether loads might possibly load, we just look in
	   here. */
	std::set<VexRip> *nonLocalLoads;

	AllowableOptimisations disablexPlusMinusX() const
	{
		return AllowableOptimisations(false, assumePrivateStack, assumeExecutesAtomically, ignoreSideEffects,
					      assumeNoInterferingStores, freeVariablesMightAccessStack, as);
	}
	AllowableOptimisations enableassumePrivateStack() const
	{
		return AllowableOptimisations(xPlusMinusX, true, assumeExecutesAtomically, ignoreSideEffects,
					      assumeNoInterferingStores, freeVariablesMightAccessStack, as);
	}
	AllowableOptimisations enableassumeExecutesAtomically() const
	{
		return AllowableOptimisations(xPlusMinusX, assumePrivateStack, true, ignoreSideEffects,
					      true /* If we're running atomically then there are definitely
						      no interfering stores */,
					      freeVariablesMightAccessStack, as);
	}
	AllowableOptimisations enableignoreSideEffects() const
	{
		return AllowableOptimisations(xPlusMinusX, assumePrivateStack, assumeExecutesAtomically, true,
					      assumeNoInterferingStores, freeVariablesMightAccessStack, as);
	}
	AllowableOptimisations enableassumeNoInterferingStores() const
	{
		return AllowableOptimisations(xPlusMinusX, assumePrivateStack, assumeExecutesAtomically, ignoreSideEffects,
					      true, freeVariablesMightAccessStack, as);
	}
	AllowableOptimisations disablefreeVariablesMightAccessStack() const
	{
		return AllowableOptimisations(xPlusMinusX, assumePrivateStack, assumeExecutesAtomically, ignoreSideEffects,
					      assumeNoInterferingStores, false, as);
	}
	AllowableOptimisations setAddressSpace(AddressSpace *as) const
	{
		return AllowableOptimisations(xPlusMinusX, assumePrivateStack, assumeExecutesAtomically, ignoreSideEffects,
					      assumeNoInterferingStores, freeVariablesMightAccessStack, as);
	}
	unsigned asUnsigned() const {
		unsigned x = 64; /* turning off all of the optional
				    optimisations doesn't turn off the
				    ones which are always available, so
				    have an implicit bit for them.
				    i.e. 0 means no optimisations at
				    all, and 64 means only the most
				    basic ones which are always
				    safe. */

		if (xPlusMinusX)
			x |= 1;
		if (assumePrivateStack)
			x |= 2;
		if (assumeExecutesAtomically)
			x |= 3;
		if (ignoreSideEffects)
			x |= 4;
		if (assumeNoInterferingStores)
			x |= 8;
		if (freeVariablesMightAccessStack)
			x |= 16;
		if (as != NULL)
			x |= 32;
		return x;
	}

	bool ignoreStore(const VexRip &rip) const {
		if (ignoreSideEffects)
			return true;
		if (!haveInterestingStoresSet)
			return false;
		if (interestingStores.count(rip))
			return false;
		else
			return true;
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
	StateMachine(StateMachineState *_root, unsigned long _origin, unsigned _tid)
		: root(_root), origin(_origin), tid(_tid)
	{
	}
public:
	StateMachineState *root;
	unsigned long origin;
	FreeVariableMap freeVariables;
	unsigned tid;

	static bool parse(StateMachine **out, const char *str, const char **suffix);

	StateMachine(StateMachineState *_root, unsigned long _origin, const FreeVariableMap &fv, unsigned _tid)
		: root(_root), origin(_origin), freeVariables(fv), tid(_tid)
	{
	}
	StateMachine(StateMachine *parent, unsigned long _origin, StateMachineState *new_root)
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
	void selectSingleCrashingPath();
	void visit(HeapVisitor &hv) { hv(root); freeVariables.visit(hv); }
	StateMachine *clone() const;
#ifdef NDEBUG
	void sanityCheck() const {}
#else
	void sanityCheck() const;
#endif
	NAMED_CLASS
};

class StateMachineState : public GarbageCollected<StateMachineState, &ir_heap> {
	mutable unsigned long __hashval;
	mutable bool have_hash;
	void assertAcyclic(std::vector<const StateMachineState *> &,
			   std::set<const StateMachineState *> &) const;
protected:
	StateMachineState(unsigned long _origin) : have_hash(false), origin(_origin) {}
	virtual unsigned long _hashval() const = 0;
public:
	unsigned long origin; /* RIP we were looking at when we
			       * constructed the thing.  Not very
			       * meaningful, but occasionally provides
			       * useful hints for debugging.*/

	/* Another peephole optimiser.  Again, must be
	   context-independent and result in no changes to the
	   semantic value of the machine, and can mutate in-place. */
	virtual StateMachineState *optimise(const AllowableOptimisations &, Oracle *, bool *, FreeVariableMap &,
					    std::set<StateMachineState *> &done) = 0;
	virtual void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) = 0;
	virtual void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &) = 0;
	virtual StateMachineState *selectSingleCrashingPath(std::set<StateMachineEdge *> &memo) __attribute__((warn_unused_result)) = 0;
	virtual bool canCrash(std::vector<StateMachineEdge *> &) = 0;
	virtual int complexity(std::vector<StateMachineEdge *> &) = 0;
	virtual StateMachineEdge *target0() = 0;
	virtual const StateMachineEdge *target0() const = 0;
	virtual StateMachineEdge *target1() = 0;
	virtual const StateMachineEdge *target1() const = 0;
	enum RoughLoadCount { noLoads, singleLoad, multipleLoads };
	virtual RoughLoadCount roughLoadCount(RoughLoadCount acc = noLoads) const = 0;
	void assertAcyclic() const;
	unsigned long hashval() const { if (!have_hash) __hashval = _hashval(); return __hashval; }
	void enumerateMentionedMemoryAccesses(std::set<VexRip> &out);
	virtual void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const = 0;

#ifdef NDEBUG
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> &live, std::vector<const StateMachineEdge *> &done) const {}
#else
	virtual void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> &live, std::vector<const StateMachineEdge *> &done) const = 0;
#endif

	virtual StateMachineState *clone(std::map<const StateMachineState *, StateMachineState *> &stateMap,
					 std::map<const StateMachineEdge *, StateMachineEdge *> &edgeMap) const = 0;

	NAMED_CLASS
};

class StateMachineSideEffect : public GarbageCollected<StateMachineSideEffect, &ir_heap>, public PrettyPrintable {
	mutable unsigned long __hashval;
	mutable bool have_hash;
	StateMachineSideEffect(); /* DNE */
public:
	enum sideEffectType {
		Load, Store, Copy, Unreached, AssertFalse, Phi
	} type;
protected:
	virtual unsigned long _hashval() const = 0;
	StateMachineSideEffect(enum sideEffectType _type)
		: type(_type)
	{}
public:
	virtual StateMachineSideEffect *optimise(const AllowableOptimisations &, Oracle *, bool *) = 0;
	virtual void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) = 0;
	virtual void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &) = 0;
	virtual int complexity() = 0;
	unsigned long hashval() const { if (!have_hash) __hashval = _hashval(); return __hashval; }
	virtual void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> &live) const = 0;
	NAMED_CLASS
};

class StateMachineEdge : public GarbageCollected<StateMachineEdge, &ir_heap> {
	mutable bool have_hash;
	mutable unsigned long _hashval;
public:
	unsigned long hashval() const;
	StateMachineEdge(StateMachineState *t) : have_hash(false), target(t) {}
	StateMachineEdge(const std::vector<StateMachineSideEffect *> &_sideEffects,
			 StateMachineState *t)
		: have_hash(false), target(t), sideEffects(_sideEffects)
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

	void prettyPrint(FILE *f, const char *seperator, std::map<const StateMachineState *, int> &labels) const {
		if (sideEffects.size() != 0) {
			fprintf(f, "{");
			bool b = true;
			for (std::vector<StateMachineSideEffect *>::const_iterator it = sideEffects.begin();
			     it != sideEffects.end();
			     it++) {
				if (!b)
					fprintf(f, "%s", seperator);
				b = false;
				(*it)->prettyPrint(f);
			}
			fprintf(f, "} ");
		}
		fprintf(f, "l%d", labels[target]);
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
	StateMachineEdge *selectSingleCrashingPath(std::set<StateMachineEdge *> &memo) __attribute__((warn_unused_result)) {
		if (!memo.count(this)) {
			memo.insert(this);
			target = target->selectSingleCrashingPath(memo);
		}
		return this;
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
	int complexity(std::vector<StateMachineEdge *> &path) {
		for (auto it = path.begin(); it != path.end(); it++)
			if (*it == this)
				return 1000; /* Assign a high-ish
					      * fixed cost to every
					      * cycle. */
		path.push_back(this);
		unsigned sz = path.size();
		int r = target->complexity(path);
		assert(sz == path.size());
		assert(path[sz - 1] == this);
		path.pop_back();

		for (unsigned i = 0; i < sideEffects.size(); i++)
			r += sideEffects[i]->complexity();
		return r;
	}
	StateMachineState::RoughLoadCount roughLoadCount(StateMachineState::RoughLoadCount acc) const;
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> live,
			 std::vector<const StateMachineEdge *> &done) const {
#ifndef NDEBUG
		for (auto it = done.begin(); it != done.end(); it++)
			if (*it == this)
				return;
		for (auto it = sideEffects.begin(); it != sideEffects.end(); it++)
			(*it)->sanityCheck(live);
		unsigned sz = done.size();
		done.push_back(this);
		target->sanityCheck(live, done);
		assert(done.back() == this);
		done.pop_back();
		assert(done.size() == sz);
#endif
	}

	StateMachineEdge *clone(std::map<const StateMachineState *, StateMachineState *> &stateMap,
				std::map<const StateMachineEdge *, StateMachineEdge *> &edgeMap) const
	{
		if (edgeMap.count(this))
			return edgeMap[this];
		auto res = new StateMachineEdge(sideEffects, target->clone(stateMap, edgeMap));
		edgeMap[this] = res;
		return res;
	}

	NAMED_CLASS
};

class StateMachineTerminal : public StateMachineState {
protected:
	virtual void prettyPrint(FILE *f) const = 0;
	StateMachineTerminal(unsigned long rip) : StateMachineState(rip) {}
public:
	StateMachineState *optimise(const AllowableOptimisations &, Oracle *, bool *, FreeVariableMap &,
				    std::set<StateMachineState *> &) { return this; }
	virtual void visit(HeapVisitor &hv) {}
	void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &) {}
	StateMachineState *selectSingleCrashingPath(std::set<StateMachineEdge *> &memo) { return this; }
	int complexity(std::vector<StateMachineEdge *> &) { return 1; }
	StateMachineEdge *target0() { return NULL; }
	const StateMachineEdge *target0() const { return NULL; }
	StateMachineEdge *target1() { return NULL; }
	const StateMachineEdge *target1() const { return NULL; }
	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &) const { prettyPrint(f); }
	StateMachineState::RoughLoadCount roughLoadCount(StateMachineState::RoughLoadCount acc) const { return acc; }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> &live,
			 std::vector<const StateMachineEdge *> &) const { return; }
};

class StateMachineUnreached : public StateMachineTerminal {
	StateMachineUnreached() : StateMachineTerminal(0) {}
	static VexPtr<StateMachineUnreached, &ir_heap> _this;
	unsigned long _hashval() const { return 0x72; }
	void prettyPrint(FILE *f) const { fprintf(f, "<unreached>"); }
public:
	static StateMachineUnreached *get() {
		if (!_this) _this = new StateMachineUnreached();
		return _this;
	}
	bool canCrash(std::vector<StateMachineEdge *> &) { return false; }
	StateMachineState *clone(std::map<const StateMachineState *, StateMachineState *> &stateMap,
				 std::map<const StateMachineEdge *, StateMachineEdge *> &edgeMap) const {
		return get();
	}
};

class StateMachineCrash : public StateMachineTerminal {
	StateMachineCrash() : StateMachineTerminal(0) {}
	static VexPtr<StateMachineCrash, &ir_heap> _this;
	unsigned long _hashval() const { return 0x73; }
public:
	static StateMachineCrash *get() {
		if (!_this) _this = new StateMachineCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<crash>"); }
	bool canCrash(std::vector<StateMachineEdge *> &) { return true; }
	StateMachineState *clone(std::map<const StateMachineState *, StateMachineState *> &stateMap,
				 std::map<const StateMachineEdge *, StateMachineEdge *> &edgeMap) const {
		return get();
	}
};

class StateMachineNoCrash : public StateMachineTerminal {
	StateMachineNoCrash() : StateMachineTerminal(0) {}
	static VexPtr<StateMachineNoCrash, &ir_heap> _this;
	unsigned long _hashval() const { return 0x74; }
public:
	static StateMachineNoCrash *get() {
		if (!_this) _this = new StateMachineNoCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<survive>"); }
	bool canCrash(std::vector<StateMachineEdge *> &) { return false; }
	StateMachineState *clone(std::map<const StateMachineState *, StateMachineState *> &stateMap,
				 std::map<const StateMachineEdge *, StateMachineEdge *> &edgeMap) const {
		return get();
	}
};

/* A state machine node which always advances to another one.  These
   can be safely eliminated, but they're sometimes kind of handy when
   you're building the machine. */
class StateMachineProxy : public StateMachineState {
	unsigned long _hashval() const { return target->hashval(); }
public:
	StateMachineEdge *target;

	StateMachineProxy(unsigned long origin, StateMachineState *t)
		: StateMachineState(origin),
		  target(new StateMachineEdge(t))		  
	{
	}
	StateMachineProxy(unsigned long origin, StateMachineEdge *t)
		: StateMachineState(origin),
		  target(t)
	{
	}
	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const
	{
		fprintf(f, "{%lx:", origin);
		if (target)
			target->prettyPrint(f, "\n  ", labels);
		else
			fprintf(f, "<NULL>");
		fprintf(f, "}");
	}
	void visit(HeapVisitor &hv)
	{
		hv(target);
	}
	StateMachineState *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something, FreeVariableMap &fv,
				    std::set<StateMachineState *> &done);
	void findLoadedAddresses(std::set<IRExpr *> &s, const AllowableOptimisations &opt) {
		target->findLoadedAddresses(s, opt);
	}
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &s, const AllowableOptimisations &opt) {
		target->findUsedRegisters(s, opt);
	}
	StateMachineState *selectSingleCrashingPath(std::set<StateMachineEdge *> &memo) {
		target = target->selectSingleCrashingPath(memo);
		return this;
	}
	bool canCrash(std::vector<StateMachineEdge *> &memo) { return target->canCrash(memo); }
	int complexity(std::vector<StateMachineEdge *> &path) { return target->complexity(path); }
	StateMachineEdge *target0() { return target; }
	const StateMachineEdge *target0() const { return target; }
	StateMachineEdge *target1() { return NULL; }
	const StateMachineEdge *target1() const { return NULL; }
	StateMachineState::RoughLoadCount roughLoadCount(StateMachineState::RoughLoadCount acc) const { return target->roughLoadCount(acc); }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> &live,
			 std::vector<const StateMachineEdge *> &done) const
	{
		target->sanityCheck(live, done);
	}
	StateMachineState *clone(std::map<const StateMachineState *, StateMachineState *> &stateMap,
				 std::map<const StateMachineEdge *, StateMachineEdge *> &edgeMap) const {
		if (stateMap.count(this))
			return stateMap[this];
		auto res = new StateMachineProxy(origin, target->clone(stateMap, edgeMap));
		stateMap[this] = res;
		return res;
	}
};

class StateMachineBifurcate : public StateMachineState {
	unsigned long _hashval() const {
		return trueTarget->hashval() * 7 + 
			falseTarget->hashval() * 11 +
			condition->hashval() * 3;
	}
public:
	StateMachineBifurcate(unsigned long origin,
			      IRExpr *_condition,
			      StateMachineEdge *t,
			      StateMachineEdge *f)
		: StateMachineState(origin),
		  condition(_condition),
		  trueTarget(t),
		  falseTarget(f)
	{
	}	
	StateMachineBifurcate(unsigned long origin,
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

	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const {
		fprintf(f, "%lx: if (", origin);
		ppIRExpr(condition, f);
		fprintf(f, ")\n  then {\n\t");
		if (trueTarget)
			trueTarget->prettyPrint(f, "\n\t", labels);
		else
			fprintf(f, "<NULL>\n\t");
		fprintf(f, "}\n  else {\n\t");
		if (falseTarget)
			falseTarget->prettyPrint(f, "\n\t", labels);
		else
			fprintf(f, "<NULL>\n\t");
		fprintf(f, "}");
	}
	void visit(HeapVisitor &hv)
	{
		hv(trueTarget);
		hv(falseTarget);
		hv(condition);
	}
	StateMachineState *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something, FreeVariableMap &,
				    std::set<StateMachineState *> &);
	void findLoadedAddresses(std::set<IRExpr *> &s, const AllowableOptimisations &opt)
	{
		std::set<IRExpr *> t;
		trueTarget->findLoadedAddresses(t, opt);
		falseTarget->findLoadedAddresses(s, opt);
		/* Result is the union of the two branches */
		for (std::set<IRExpr *>::iterator it = t.begin();
		     it != t.end();
		     it++)
			s.insert(*it);
	}
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &s, const AllowableOptimisations &opt);
	StateMachineState *selectSingleCrashingPath(std::set<StateMachineEdge *> &memo) {
		trueTarget = trueTarget->selectSingleCrashingPath(memo);
		falseTarget = falseTarget->selectSingleCrashingPath(memo);
		std::vector<StateMachineEdge *> edgeMemo;
		bool tCrash = trueTarget->canCrash(edgeMemo);
		bool fCrash = falseTarget->canCrash(edgeMemo);
		if (!tCrash && !fCrash) {
			/* Bit of a hack: if we're definitely going to
			   survive, just substitute this state with a
			   survive state. */
			return StateMachineNoCrash::get();
		}
		if (tCrash && fCrash) {
			std::vector<StateMachineEdge *> path;
			if (trueTarget->complexity(path) > falseTarget->complexity(path))
				return new StateMachineProxy(origin, falseTarget);
			else
				return new StateMachineProxy(origin, trueTarget);
		}
		return this;
	}
	bool canCrash(std::vector<StateMachineEdge *> &memo) {
		return trueTarget->canCrash(memo) || falseTarget->canCrash(memo);
	}
	int complexity(std::vector<StateMachineEdge *> &path) {
		return trueTarget->complexity(path) + falseTarget->complexity(path) + exprComplexity(condition) + 50;
	}
	StateMachineEdge *target0() { return falseTarget; }
	const StateMachineEdge *target0() const { return falseTarget; }
	StateMachineEdge *target1() { return trueTarget; }
	const StateMachineEdge *target1() const { return trueTarget; }
	StateMachineState::RoughLoadCount roughLoadCount(StateMachineState::RoughLoadCount acc) const {
		return trueTarget->roughLoadCount(
			falseTarget->roughLoadCount(acc));
	}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> &live,
			 std::vector<const StateMachineEdge *> &done) const
	{
		sanityCheckIRExpr(condition, live);
		trueTarget->sanityCheck(live, done);
		falseTarget->sanityCheck(live, done);
	}

	StateMachineState *clone(std::map<const StateMachineState *, StateMachineState *> &stateMap,
				 std::map<const StateMachineEdge *, StateMachineEdge *> &edgeMap) const {
		if (stateMap.count(this))
			return stateMap[this];
		auto res = new StateMachineBifurcate(origin, condition,
						     trueTarget->clone(stateMap, edgeMap),
						     falseTarget->clone(stateMap, edgeMap));
		stateMap[this] = res;
		return res;
	}
};

/* A node in the state machine representing a bit of code which we
   haven't explored yet. */
class StateMachineStub : public StateMachineTerminal {
	unsigned long _hashval() const { return target->hashval(); }
public:
	IRExpr *target;

	StateMachineStub(unsigned long origin, IRExpr *t) : StateMachineTerminal(origin), target(t) {}

	void prettyPrint(FILE *f) const
	{
		fprintf(f, "<%lx: jmp ", origin);
		ppIRExpr(target, f);
		fprintf(f, ">");
	}
	void visit(HeapVisitor &hv) { hv(target); }
	bool canCrash(std::vector<StateMachineEdge *> &) { return false; }

	StateMachineState *clone(std::map<const StateMachineState *, StateMachineState *> &stateMap,
				 std::map<const StateMachineEdge *, StateMachineEdge *> &edgeMap) const {
		if (stateMap.count(this))
			return stateMap[this];
		auto res = new StateMachineStub(origin, target);
		stateMap[this] = res;
		return res;
	}
};


class StateMachineSideEffectUnreached : public StateMachineSideEffect {
	static VexPtr<StateMachineSideEffectUnreached, &ir_heap> _this;
	StateMachineSideEffectUnreached() : StateMachineSideEffect(StateMachineSideEffect::Unreached) {}
	unsigned long _hashval() const { return 0x91; }
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
	int complexity() { return 0; }
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> &) const {}
};
class StateMachineSideEffectMemoryAccess : public StateMachineSideEffect {
public:
	IRExpr *addr;
	ThreadVexRip rip;
	StateMachineSideEffectMemoryAccess(IRExpr *_addr, const ThreadVexRip &_rip,
					   StateMachineSideEffect::sideEffectType _type)
		: StateMachineSideEffect(_type), addr(_addr), rip(_rip)
	{}
	virtual void visit(HeapVisitor &hv) {
		hv(addr);
	}
	virtual void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> &live) const {
		sanityCheckIRExpr(addr, live);
	}
};
class StateMachineSideEffectStore : public StateMachineSideEffectMemoryAccess {
	unsigned long _hashval() const { return addr->hashval() * 223 + data->hashval() * 971; }
public:
	StateMachineSideEffectStore(IRExpr *_addr, IRExpr *_data, const ThreadVexRip &_rip)
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
	int complexity() { return exprComplexity(addr) * 2 + exprComplexity(data) + 20; }
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> &live) const {
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
	unsigned long _hashval() const { return addr->hashval() * 757 + target.hash() * 118409; }
public:
	StateMachineSideEffectLoad(threadAndRegisterAllocator &alloc, IRExpr *_addr, const ThreadVexRip &_rip)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, StateMachineSideEffect::Load),
		  target(alloc())
	{
		constructed();
	}
	StateMachineSideEffectLoad(threadAndRegister reg, IRExpr *_addr, const ThreadVexRip &_rip)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, StateMachineSideEffect::Load),
		  target(reg)
	{
		constructed();
	}
	threadAndRegister target;
	void prettyPrint(FILE *f) const {
		fprintf(f, "LOAD ");
		target.prettyPrint(f);
		fprintf(f, " <- *(");
		ppIRExpr(addr, f);
		fprintf(f, ")@%s", rip.name());
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {
		l.insert(addr);
	}
	void findUsedRegisters(std::set<threadAndRegister, threadAndRegister::fullCompare> &, const AllowableOptimisations &);
	int complexity() { return exprComplexity(addr) + 20; }
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> &live) const {
		StateMachineSideEffectMemoryAccess::sanityCheck(live);
		live.insert(target);
	}
};
class StateMachineSideEffectCopy : public StateMachineSideEffect {
	unsigned long _hashval() const { return value->hashval(); }
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
	int complexity() { return exprComplexity(value); }
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> &live) const {
		sanityCheckIRExpr(value, live);
		live.insert(target);
	}
};
class StateMachineSideEffectAssertFalse : public StateMachineSideEffect {
	unsigned long _hashval() const { return value->hashval(); }
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
	int complexity() { return exprComplexity(value); }
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> &live) const {
		sanityCheckIRExpr(value, live);
	}
};
class StateMachineSideEffectPhi : public StateMachineSideEffect {
	unsigned long _hashval() const { return reg.hash(); }
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
	int complexity() { return 100; }
	void sanityCheck(std::set<threadAndRegister, threadAndRegister::fullCompare> &live) const {
		live.insert(reg);
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

#endif /* !STATEMACHINE_HPP__ */
