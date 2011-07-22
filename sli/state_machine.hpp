#ifndef STATEMACHINE_HPP__
#define STATEMACHINE_HPP__

#include <map>
#include <set>

#include "simplify_irexpr.hpp"

class StateMachine;
class StateMachineEdge;
class StateMachineSideEffect;
class OracleInterface;

class AllowableOptimisations {
public:
	static AllowableOptimisations defaultOptimisations;
	AllowableOptimisations(bool x, bool s, bool a, bool i, bool as, bool fvmas)
		: xPlusMinusX(x), assumePrivateStack(s), assumeExecutesAtomically(a),
		  ignoreSideEffects(i), assumeNoInterferingStores(as),
		  freeVariablesMightAccessStack(fvmas)
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
	map_t *content;
public:
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
	IRExpr *get(FreeVariableKey k) { IRExpr *res = content->get(k); assert(res); return res; }
	void visit(HeapVisitor &hv) { hv(content); }
	void applyTransformation(IRExprTransformer &t);
	void print(FILE *f) const;
};

void checkIRExprBindersInScope(const IRExpr *iex, const std::set<Int> &binders);

class StateMachineState;

class StateMachine : public GarbageCollected<StateMachine, &ir_heap> {
public:
	StateMachineState *root;
	unsigned long origin;
	FreeVariableMap freeVariables;

	StateMachine(StateMachineState *_root, unsigned long _origin, bool ign)
		: root(_root), origin(_origin)
	{
	}
	StateMachine(StateMachine *parent, StateMachineState *new_root)
		: root(root), origin(parent->origin), freeVariables(parent->freeVariables)
	{}
	StateMachine(StateMachine *parent, std::vector<std::pair<FreeVariableKey, IRExpr *> > &delta)
		: root(parent->root),
		  origin(parent->origin),
		  freeVariables(parent->freeVariables, delta)
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
	virtual StateMachineState *optimise(const AllowableOptimisations &, OracleInterface *, bool *, FreeVariableMap &) = 0;
	virtual void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) = 0;
	virtual void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) = 0;
	virtual StateMachineState *selectSingleCrashingPath() __attribute__((warn_unused_result)) = 0;
	virtual bool canCrash() = 0;
	virtual int complexity() = 0;
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
protected:
	virtual unsigned long _hashval() const = 0;
public:
	virtual StateMachineSideEffect *optimise(const AllowableOptimisations &, OracleInterface *, bool *) = 0;
	virtual void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) = 0;
	virtual void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) = 0;
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
	StateMachineEdge *optimise(const AllowableOptimisations &, OracleInterface *, bool *done_something, FreeVariableMap &);
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
	StateMachineEdge *selectSingleCrashingPath() __attribute__((warn_unused_result)) {
		target = target->selectSingleCrashingPath();
		return this;
	}
	void enumerateMentionedMemoryAccesses(std::set<unsigned long> &instrs);
	bool canCrash() { return target->canCrash(); }
	int complexity() {
		int r = target->complexity();
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
	StateMachineState *optimise(const AllowableOptimisations &, OracleInterface *, bool *, FreeVariableMap &) { return this; }
	virtual void visit(HeapVisitor &hv) {}
	void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) {}
	StateMachineState *selectSingleCrashingPath() { return this; }
	int complexity() { return 1; }
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
	bool canCrash() { return false; }
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
	bool canCrash() { return true; }
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
	bool canCrash() { return false; }
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
	StateMachineState *optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something, FreeVariableMap &fv)
	{
		if (target->target == StateMachineUnreached::get()) {
			*done_something = true;
			return target->target;
		}
		if (target->sideEffects.size() == 0) {
			*done_something = true;
			return target->target->optimise(opt, oracle, done_something, fv);
		}
		target = target->optimise(opt, oracle, done_something, fv);
		return this;
	}
	void findLoadedAddresses(std::set<IRExpr *> &s, const AllowableOptimisations &opt) {
		target->findLoadedAddresses(s, opt);
	}
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt) {
		target->findUsedBinders(s, opt);
	}
	StateMachineState *selectSingleCrashingPath() {
		target = target->selectSingleCrashingPath();
		return this;
	}
	bool canCrash() { return target->canCrash(); }
	int complexity() { return target->complexity(); }
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
	StateMachineState *optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something, FreeVariableMap &);
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
	StateMachineState *selectSingleCrashingPath() {
		trueTarget = trueTarget->selectSingleCrashingPath();
		falseTarget = falseTarget->selectSingleCrashingPath();
		if (trueTarget->canCrash() && falseTarget->canCrash()) {
			if (trueTarget->complexity() > falseTarget->complexity())
				return new StateMachineProxy(origin, falseTarget);
			else
				return new StateMachineProxy(origin, trueTarget);
		}
		return this;
	}
	bool canCrash() { return trueTarget->canCrash() || falseTarget->canCrash(); }
	int complexity() { return trueTarget->complexity() + falseTarget->complexity() + exprComplexity(condition) + 50; }
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
	bool canCrash() { return false; }
	void _sanity_check(const std::set<Int> &binders) const {checkIRExprBindersInScope(target, binders);}
};


class StateMachineSideEffectUnreached : public StateMachineSideEffect {
	static VexPtr<StateMachineSideEffectUnreached, &ir_heap> _this;
	StateMachineSideEffectUnreached() {}
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
	void visit(HeapVisitor &hv) {}
	int complexity() { return 0; }
	void sanity_check(const std::set<Int> &binders) const {}
};
class StateMachineSideEffectMemoryAccess : public StateMachineSideEffect {
public:
	IRExpr *addr;
	unsigned long rip;
	StateMachineSideEffectMemoryAccess(IRExpr *_addr, unsigned long _rip)
		: addr(_addr), rip(_rip)
	{}
	virtual void visit(HeapVisitor &hv) {
		hv(addr);
	}
};
class StateMachineSideEffectStore : public StateMachineSideEffectMemoryAccess {
	unsigned long _hashval() const { return addr->hashval() * 223 + data->hashval() * 971; }
public:
	StateMachineSideEffectStore(IRExpr *_addr, IRExpr *_data, unsigned long _rip)
		: StateMachineSideEffectMemoryAccess(_addr, _rip),
		  data(_data)
	{
	}
	IRExpr *data;
	void prettyPrint(FILE *f) const {
		fprintf(f, "*(");
		ppIRExpr(addr, f);
		fprintf(f, ") <- ");
		ppIRExpr(data, f);
		fprintf(f, " @ %lx", rip);
	}
	void visit(HeapVisitor &hv) {
		StateMachineSideEffectMemoryAccess::visit(hv);
		hv(data);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &opt);
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt);
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
	StateMachineSideEffectLoad(IRExpr *_addr, unsigned long _rip)
		: StateMachineSideEffectMemoryAccess(_addr, _rip)
	{
		key = next_key++;
		constructed();
	}
	StateMachineSideEffectLoad(Int k, IRExpr *_addr, unsigned long _rip)
		: StateMachineSideEffectMemoryAccess(_addr, _rip), key(k)
	{
		constructed();
	}
	Int key;
	void prettyPrint(FILE *f) const {
		fprintf(f, "B%d <- *(", key);
		ppIRExpr(addr, f);
		fprintf(f, ")@%lx", rip);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, OracleInterface *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {
		l.insert(addr);
	}
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt);
	int complexity() { return exprComplexity(addr) + 20; }
	void sanity_check(const std::set<Int> &binders) const {
		checkIRExprBindersInScope(addr, binders);
	}
};
class StateMachineSideEffectCopy : public StateMachineSideEffect {
	unsigned long _hashval() const { return value->hashval(); }
public:
	StateMachineSideEffectCopy(Int k, IRExpr *_value)
		: key(k), value(_value)
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
	int complexity() { return exprComplexity(value); }
	void sanity_check(const std::set<Int> &binders) const {
		checkIRExprBindersInScope(value, binders);
	}
};


void printStateMachine(const StateMachine *sm, FILE *f);
bool sideEffectsBisimilar(StateMachineSideEffect *smse1,
			  StateMachineSideEffect *smse2,
			  const AllowableOptimisations &opt);
bool parseStateMachine(StateMachine **out, const char *str, const char **suffix, char **err);
StateMachine *readStateMachine(int fd);

#endif /* !STATEMACHINE_HPP__ */
