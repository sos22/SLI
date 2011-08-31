#ifndef STATEMACHINE_HPP__
#define STATEMACHINE_HPP__

#include <map>
#include <set>

#include "simplify_irexpr.hpp"

class StateMachine;
class StateMachineEdge;
class StateMachineSideEffect;
class OracleInterface;
class threadAndRegister;

class AllowableOptimisations {
public:
	static AllowableOptimisations defaultOptimisations;
	AllowableOptimisations(bool x, bool s, bool a, bool i, bool as, bool fvmas)
		: xPlusMinusX(x), assumePrivateStack(s), assumeExecutesAtomically(a),
		  ignoreSideEffects(i), assumeNoInterferingStores(as),
		  freeVariablesMightAccessStack(fvmas), haveInterestingStoresSet(false)
	{
	}

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

	/* Bit of a hack: sometimes, only some side effects are
	   interesting, so allow them to be listed here.  If
	   haveInterestingStoresSet is false then we don't look at
	   interestingStores at all, and instead rely on
	   ignoreSideEffects. */
	bool haveInterestingStoresSet;
	std::set<unsigned long> interestingStores;

	AllowableOptimisations disablexPlusMinusX() const
	{
		return AllowableOptimisations(false, assumePrivateStack, assumeExecutesAtomically, ignoreSideEffects,
					      assumeNoInterferingStores, freeVariablesMightAccessStack);
	}
	AllowableOptimisations enableassumePrivateStack() const
	{
		return AllowableOptimisations(xPlusMinusX, true, assumeExecutesAtomically, ignoreSideEffects,
					      assumeNoInterferingStores, freeVariablesMightAccessStack);
	}
	AllowableOptimisations enableassumeExecutesAtomically() const
	{
		return AllowableOptimisations(xPlusMinusX, assumePrivateStack, true, ignoreSideEffects,
					      true /* If we're running atomically then there are definitely
						      no interfering stores */,
					      freeVariablesMightAccessStack
			);
	}
	AllowableOptimisations enableignoreSideEffects() const
	{
		return AllowableOptimisations(xPlusMinusX, assumePrivateStack, assumeExecutesAtomically, true,
					      assumeNoInterferingStores, freeVariablesMightAccessStack);
	}
	AllowableOptimisations enableassumeNoInterferingStores() const
	{
		return AllowableOptimisations(xPlusMinusX, assumePrivateStack, assumeExecutesAtomically, ignoreSideEffects,
					      true, freeVariablesMightAccessStack);
	}
	AllowableOptimisations disablefreeVariablesMightAccessStack() const
	{
		return AllowableOptimisations(xPlusMinusX, assumePrivateStack, assumeExecutesAtomically, ignoreSideEffects,
					      assumeNoInterferingStores, false);
	}
	unsigned asUnsigned() const {
		unsigned x = 32; /* turning off all of the optional
				    optimisations doesn't turn off the
				    ones which are always available, so
				    have an implicit bit for them.
				    i.e. 0 means no optimisations at
				    all, and 8 means only the most
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
		return x;
	}

	bool ignoreStore(unsigned long rip) const {
		if (ignoreSideEffects)
			return true;
		if (!haveInterestingStoresSet)
			return false;
		if (interestingStores.count(rip))
			return false;
		else
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
	bool parse(const char *str, const char **succ, char **err);
	bool empty() const { return content->empty(); }
	void optimise(const AllowableOptimisations &opt, bool *done_something);
};

void checkIRExprBindersInScope(const IRExpr *iex, const std::set<Int> &binders);

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

	static bool parse(StateMachine **out, const char *str, const char **suffix, char **err);

	StateMachine(StateMachineState *_root, unsigned long _origin, FreeVariableMap &fv, unsigned _tid)
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
			       OracleInterface *oracle,
			       bool *done_something);
	void selectSingleCrashingPath();
	void visit(HeapVisitor &hv) { hv(root); freeVariables.visit(hv); }
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
	virtual void _sanity_check(const std::set<Int> &binders) const = 0;
public:
	unsigned long origin; /* RIP we were looking at when we
			       * constructed the thing.  Not very
			       * meaningful, but occasionally provides
			       * useful hints for debugging.*/

	/* Another peephole optimiser.  Again, must be
	   context-independent and result in no changes to the
	   semantic value of the machine, and can mutate in-place. */
	virtual StateMachineState *optimise(const AllowableOptimisations &, OracleInterface *, bool *, FreeVariableMap &,
					    std::set<StateMachineState *> &done) = 0;
	virtual void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) = 0;
	virtual void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) = 0;
	virtual void findUsedRegisters(std::set<threadAndRegister> &, const AllowableOptimisations &) = 0;
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
	void enumerateMentionedMemoryAccesses(std::set<unsigned long> &out);
	virtual void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const = 0;
	void sanity_check(std::set<Int> &binders, std::vector<const StateMachineState *> &path) const;
	void sanity_check() const {
		std::set<Int> binders;
		std::vector<const StateMachineState *> path;
		sanity_check(binders, path);
	}
	NAMED_CLASS
};

class StateMachineSideEffect : public GarbageCollected<StateMachineSideEffect, &ir_heap>, public PrettyPrintable {
	mutable unsigned long __hashval;
	mutable bool have_hash;
	StateMachineSideEffect(); /* DNE */
public:
	enum sideEffectType {
		Load, Store, Copy, Unreached, Put, AssertFalse
	} type;
protected:
	virtual unsigned long _hashval() const = 0;
	StateMachineSideEffect(enum sideEffectType _type)
		: type(_type)
	{}
public:
	virtual StateMachineSideEffect *optimise(const AllowableOptimisations &, OracleInterface *, bool *) = 0;
	virtual void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) = 0;
	virtual void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) = 0;
	virtual void findUsedRegisters(std::set<threadAndRegister> &, const AllowableOptimisations &) = 0;
	virtual int complexity() = 0;
	virtual void sanity_check(const std::set<Int> &) const = 0;
	unsigned long hashval() const { if (!have_hash) __hashval = _hashval(); return __hashval; }
	NAMED_CLASS
};

class StateMachineEdge : public GarbageCollected<StateMachineEdge, &ir_heap> {
	mutable bool have_hash;
	mutable unsigned long _hashval;
public:
	unsigned long hashval() const;
	StateMachineEdge(StateMachineState *t) : have_hash(false), target(t) {}
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
	StateMachineEdge *optimise(const AllowableOptimisations &, OracleInterface *, bool *done_something, FreeVariableMap &,
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
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt) {
		if (TIMEOUT)
			return;
		target->findUsedBinders(s, opt);
		for (std::vector<StateMachineSideEffect *>::reverse_iterator it = sideEffects.rbegin();
		     it != sideEffects.rend();
		     it++)
			(*it)->findUsedBinders(s, opt);
	}
	void findUsedRegisters(std::set<threadAndRegister> &s, const AllowableOptimisations &opt) {
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
	void enumerateMentionedMemoryAccesses(std::set<unsigned long> &instrs);
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
	void sanity_check(std::set<Int> &binders, std::vector<const StateMachineState *> &path) const;
	StateMachineState::RoughLoadCount roughLoadCount(StateMachineState::RoughLoadCount acc) const;
	NAMED_CLASS
};

class StateMachineTerminal : public StateMachineState {
protected:
	virtual void prettyPrint(FILE *f) const = 0;
	StateMachineTerminal(unsigned long rip) : StateMachineState(rip) {}
public:
	StateMachineState *optimise(const AllowableOptimisations &, OracleInterface *, bool *, FreeVariableMap &,
				    std::set<StateMachineState *> &) { return this; }
	virtual void visit(HeapVisitor &hv) {}
	void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) {}
	void findUsedRegisters(std::set<threadAndRegister> &, const AllowableOptimisations &) {}
	StateMachineState *selectSingleCrashingPath(std::set<StateMachineEdge *> &memo) { return this; }
	int complexity(std::vector<StateMachineEdge *> &) { return 1; }
	StateMachineEdge *target0() { return NULL; }
	const StateMachineEdge *target0() const { return NULL; }
	StateMachineEdge *target1() { return NULL; }
	const StateMachineEdge *target1() const { return NULL; }
	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &) const { prettyPrint(f); }
	StateMachineState::RoughLoadCount roughLoadCount(StateMachineState::RoughLoadCount acc) const { return acc; }
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
	void _sanity_check(const std::set<Int> &) const {}
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
	void _sanity_check(const std::set<Int> &) const {}
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
	void _sanity_check(const std::set<Int> &) const {}
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
		target->prettyPrint(f, "\n  ", labels);
		fprintf(f, "}");
	}
	void visit(HeapVisitor &hv)
	{
		hv(target);
	}
	StateMachineState *optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something, FreeVariableMap &fv,
				    std::set<StateMachineState *> &done);
	void findLoadedAddresses(std::set<IRExpr *> &s, const AllowableOptimisations &opt) {
		target->findLoadedAddresses(s, opt);
	}
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt) {
		target->findUsedBinders(s, opt);
	}
	void findUsedRegisters(std::set<threadAndRegister> &s, const AllowableOptimisations &opt) {
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
	void _sanity_check(const std::set<Int> &) const {}
	StateMachineState::RoughLoadCount roughLoadCount(StateMachineState::RoughLoadCount acc) const { return target->roughLoadCount(acc); }
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
		trueTarget->prettyPrint(f, "\n\t", labels);
		fprintf(f, "}\n  else {\n\t");
		falseTarget->prettyPrint(f, "\n\t", labels);
		fprintf(f, "}");
	}
	void visit(HeapVisitor &hv)
	{
		hv(trueTarget);
		hv(falseTarget);
		hv(condition);
	}
	StateMachineState *optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something, FreeVariableMap &,
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
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt);
	void findUsedRegisters(std::set<threadAndRegister> &s, const AllowableOptimisations &opt);
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
	void _sanity_check(const std::set<Int> &binders) const {checkIRExprBindersInScope(condition, binders);}
	StateMachineState::RoughLoadCount roughLoadCount(StateMachineState::RoughLoadCount acc) const {
		return trueTarget->roughLoadCount(
			falseTarget->roughLoadCount(acc));
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
	void _sanity_check(const std::set<Int> &binders) const {checkIRExprBindersInScope(target, binders);}
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
	StateMachineSideEffect *optimise(const AllowableOptimisations &, OracleInterface *, bool *) { return this; }
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {}
	void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) {}
	void findUsedRegisters(std::set<threadAndRegister> &, const AllowableOptimisations &) {}
	void visit(HeapVisitor &hv) {}
	int complexity() { return 0; }
	void sanity_check(const std::set<Int> &binders) const {}
};
class StateMachineSideEffectMemoryAccess : public StateMachineSideEffect {
public:
	IRExpr *addr;
	ThreadRip rip;
	StateMachineSideEffectMemoryAccess(IRExpr *_addr, ThreadRip _rip, StateMachineSideEffect::sideEffectType _type)
		: StateMachineSideEffect(_type), addr(_addr), rip(_rip)
	{}
	virtual void visit(HeapVisitor &hv) {
		hv(addr);
	}
};
class StateMachineSideEffectStore : public StateMachineSideEffectMemoryAccess {
	unsigned long _hashval() const { return addr->hashval() * 223 + data->hashval() * 971; }
public:
	StateMachineSideEffectStore(IRExpr *_addr, IRExpr *_data, ThreadRip _rip)
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
		fprintf(f, " @ %d:%lx", rip.thread, rip.rip);
	}
	void visit(HeapVisitor &hv) {
		StateMachineSideEffectMemoryAccess::visit(hv);
		hv(data);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &opt);
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt);
	void findUsedRegisters(std::set<threadAndRegister> &, const AllowableOptimisations &);
	int complexity() { return exprComplexity(addr) * 2 + exprComplexity(data) + 20; }
	void sanity_check(const std::set<Int> &binders) const {
		checkIRExprBindersInScope(addr, binders);
		checkIRExprBindersInScope(data, binders);
	}
};

class StateMachineSideEffectLoad : public StateMachineSideEffectMemoryAccess {
	void constructed();
	static Int next_key;
	unsigned long _hashval() const { return addr->hashval() * 757 + key; }
public:
	StateMachineSideEffectLoad(IRExpr *_addr, ThreadRip _rip)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, StateMachineSideEffect::Load)
	{
		key = next_key++;
		constructed();
	}
	StateMachineSideEffectLoad(Int k, IRExpr *_addr, ThreadRip _rip)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, StateMachineSideEffect::Load), key(k)
	{
		constructed();
	}
	Int key;
	void prettyPrint(FILE *f) const {
		fprintf(f, "B%d <- *(", key);
		ppIRExpr(addr, f);
		fprintf(f, ")@%d:%lx", rip.thread, rip.rip);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {
		l.insert(addr);
	}
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt);
	void findUsedRegisters(std::set<threadAndRegister> &, const AllowableOptimisations &);
	int complexity() { return exprComplexity(addr) + 20; }
	void sanity_check(const std::set<Int> &binders) const {
		checkIRExprBindersInScope(addr, binders);
	}
};
class StateMachineSideEffectCopy : public StateMachineSideEffect {
	unsigned long _hashval() const { return value->hashval(); }
public:
	StateMachineSideEffectCopy(Int k, IRExpr *_value)
		: StateMachineSideEffect(StateMachineSideEffect::Copy),
		  key(k), value(_value)
	{
	}
	Int key;
	IRExpr *value;
	void prettyPrint(FILE *f) const {
		fprintf(f, "B%d = (", key);
		ppIRExpr(value, f);
		fprintf(f, ")");
	}
	void visit(HeapVisitor &hv) {
		hv(value);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) { }
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt);
	void findUsedRegisters(std::set<threadAndRegister> &, const AllowableOptimisations &);
	int complexity() { return exprComplexity(value); }
	void sanity_check(const std::set<Int> &binders) const {
		checkIRExprBindersInScope(value, binders);
	}
};
class StateMachineSideEffectPut : public StateMachineSideEffect {
	unsigned long _hashval() const { return value->hashval() + offset * 5000000743ul; }
public:
	StateMachineSideEffectPut(unsigned _offset, IRExpr *_value, ThreadRip _rip)
		: StateMachineSideEffect(StateMachineSideEffect::Put),
		  offset(_offset), value(_value), rip(_rip)
	{
	}
	unsigned offset;
	IRExpr *value;
	ThreadRip rip;
	void prettyPrint(FILE *f) const {
		fprintf(f, "Put%d <- ", offset);
		ppIRExpr(value, f);
		fprintf(f, " @ %d:%lx", rip.thread, rip.rip);
	}
	void visit(HeapVisitor &hv) {
		hv(value);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) { }
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt);
	void findUsedRegisters(std::set<threadAndRegister> &, const AllowableOptimisations &);
	int complexity() { return exprComplexity(value); }
	void sanity_check(const std::set<Int> &binders) const {
		checkIRExprBindersInScope(value, binders);
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
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) { }
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt);
	void findUsedRegisters(std::set<threadAndRegister> &, const AllowableOptimisations &);
	int complexity() { return exprComplexity(value); }
	void sanity_check(const std::set<Int> &binders) const {
		checkIRExprBindersInScope(value, binders);
	}
};

class threadAndRegister : public std::pair<unsigned, unsigned> {
public:
	threadAndRegister(IRExpr::Get &e)
		: std::pair<unsigned, unsigned>(e.tid, e.offset)
	{}
	threadAndRegister(IRExpr::RdTmp &e)
		: std::pair<unsigned, unsigned>(e.tid, -e.tmp - 1)
	{}
	threadAndRegister(StateMachineSideEffectPut &s)
		: std::pair<unsigned, unsigned>(s.rip.thread, s.offset)
	{}
};


void printStateMachine(const StateMachine *sm, FILE *f);
bool sideEffectsBisimilar(StateMachineSideEffect *smse1,
			  StateMachineSideEffect *smse2,
			  const AllowableOptimisations &opt);
bool parseStateMachine(StateMachine **out, const char *str, const char **suffix, char **err);
StateMachine *readStateMachine(int fd);

void applySideEffectToFreeVariables(FreeVariableMap &fv,
				    StateMachineSideEffect *e,
				    bool *done_something = NULL);

bool parseStateMachineSideEffect(StateMachineSideEffect **out,
				 const char *str,
				 const char **suffix,
				 char **err);

#endif /* !STATEMACHINE_HPP__ */
