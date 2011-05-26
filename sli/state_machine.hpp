#ifndef STATEMACHINE_HPP__
#define STATEMACHINE_HPP__

#include <map>
#include <set>

class StateMachine;
class StateMachineEdge;
class StateMachineSideEffect;
class Oracle;

int exprComplexity(const IRExpr *e);

class AllowableOptimisations {
public:
	static AllowableOptimisations defaultOptimisations;
	AllowableOptimisations(bool x, bool s, bool a, bool i)
		: xPlusMinusX(x), assumePrivateStack(s), assumeExecutesAtomically(a),
		  ignoreSideEffects(i)
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

	AllowableOptimisations disablexPlusMinusX() const
	{
		return AllowableOptimisations(false, assumePrivateStack, assumeExecutesAtomically, ignoreSideEffects);
	}
	AllowableOptimisations enableassumePrivateStack() const
	{
		return AllowableOptimisations(xPlusMinusX, true, assumeExecutesAtomically, ignoreSideEffects);
	}
	AllowableOptimisations enableassumeExecutesAtomically() const
	{
		return AllowableOptimisations(xPlusMinusX, assumePrivateStack, true, ignoreSideEffects);
	}
	AllowableOptimisations enableignoreSideEffects() const
	{
		return AllowableOptimisations(xPlusMinusX, assumePrivateStack, assumeExecutesAtomically, true);
	}
	unsigned asUnsigned() const {
		unsigned x = 8; /* turning off all of the optional
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
		return x;
	}
};

class StateMachine : public GarbageCollected<StateMachine, &ir_heap> {
	mutable unsigned long __hashval;
	mutable bool have_hash;
protected:
	StateMachine(unsigned long _origin) : have_hash(false), origin(_origin) {}
	virtual unsigned long _hashval() const = 0;
public:
	unsigned long origin; /* RIP we were looking at when we
			       * constructed the thing.  Not very
			       * meaningful, but occasionally provides
			       * useful hints for debugging.*/

	/* Another peephole optimiser.  Again, must be
	   context-independent and result in no changes to the
	   semantic value of the machine, and can mutate in-place. */
	virtual StateMachine *optimise(const AllowableOptimisations &, Oracle *, bool *) = 0;
	virtual void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) = 0;
	virtual void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) = 0;
	virtual StateMachine *selectSingleCrashingPath() __attribute__((warn_unused_result)) = 0;
	virtual bool canCrash() = 0;
	virtual int complexity() = 0;
	virtual StateMachineEdge *target0() = 0;
	virtual const StateMachineEdge *target0() const = 0;
	virtual StateMachineEdge *target1() = 0;
	virtual const StateMachineEdge *target1() const = 0;
	unsigned long hashval() const { if (!have_hash) __hashval = _hashval(); return __hashval; }
	virtual void prettyPrint(FILE *f, std::map<const StateMachine *, int> &labels) const = 0;
	NAMED_CLASS
};

class StateMachineSideEffect : public GarbageCollected<StateMachineSideEffect, &ir_heap>, public PrettyPrintable {
	mutable unsigned long __hashval;
	mutable bool have_hash;
protected:
	virtual unsigned long _hashval() const = 0;
public:
	virtual StateMachineSideEffect *optimise(const AllowableOptimisations &, Oracle *, bool *) = 0;
	virtual void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) = 0;
	virtual void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) = 0;
	virtual int complexity() = 0;
	unsigned long hashval() const { if (!have_hash) __hashval = _hashval(); return __hashval; }
	NAMED_CLASS
};

class StateMachineEdge : public GarbageCollected<StateMachineEdge, &ir_heap> {
	mutable bool have_hash;
	mutable unsigned long _hashval;
public:
	unsigned long hashval() const;
	StateMachineEdge(StateMachine *t) : have_hash(false), target(t) {}
	StateMachine *target;
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

	void prettyPrint(FILE *f, const char *seperator, std::map<const StateMachine *, int> &labels) const {
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
	StateMachineEdge *optimise(const AllowableOptimisations &, Oracle *, bool *done_something);
	void findLoadedAddresses(std::set<IRExpr *> &s, const AllowableOptimisations &opt) {
		target->findLoadedAddresses(s, opt);
		for (std::vector<StateMachineSideEffect *>::reverse_iterator it = sideEffects.rbegin();
		     it != sideEffects.rend();
		     it++)
			(*it)->updateLoadedAddresses(s, opt);
	}
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt) {
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
	bool canCrash() { return target->canCrash(); }
	int complexity() {
		int r = target->complexity();
		for (unsigned i = 0; i < sideEffects.size(); i++)
			r += sideEffects[i]->complexity();
		return r;
	}
	NAMED_CLASS
};

class StateMachineTerminal : public StateMachine {
protected:
	virtual void prettyPrint(FILE *f) const = 0;
	StateMachineTerminal(unsigned long rip) : StateMachine(rip) {}
public:
	StateMachine *optimise(const AllowableOptimisations &, Oracle *, bool *) { return this; }
	virtual void visit(HeapVisitor &hv) {}
	void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) {}
	StateMachine *selectSingleCrashingPath() { return this; }
	int complexity() { return 1; }
	StateMachineEdge *target0() { return NULL; }
	const StateMachineEdge *target0() const { return NULL; }
	StateMachineEdge *target1() { return NULL; }
	const StateMachineEdge *target1() const { return NULL; }
	void prettyPrint(FILE *f, std::map<const StateMachine *, int> &) const { prettyPrint(f); }
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
};

/* A state machine node which always advances to another one.  These
   can be safely eliminated, but they're sometimes kind of handy when
   you're building the machine. */
class StateMachineProxy : public StateMachine {
	unsigned long _hashval() const { return target->hashval(); }
public:
	StateMachineEdge *target;

	StateMachineProxy(unsigned long origin, StateMachine *t)
		: StateMachine(origin),
		  target(new StateMachineEdge(t))		  
	{
	}
	StateMachineProxy(unsigned long origin, StateMachineEdge *t)
		: StateMachine(origin),
		  target(t)
	{
	}
	void prettyPrint(FILE *f, std::map<const StateMachine *, int> &labels) const
	{
		fprintf(f, "{%lx:", origin);
		target->prettyPrint(f, "\n  ", labels);
		fprintf(f, "}");
	}
	void visit(HeapVisitor &hv)
	{
		hv(target);
	}
	StateMachine *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
	{
		if (target->target == StateMachineUnreached::get()) {
			*done_something = true;
			return target->target;
		}
		if (target->sideEffects.size() == 0) {
			*done_something = true;
			return target->target->optimise(opt, oracle, done_something);
		}
		target = target->optimise(opt, oracle, done_something);
		return this;
	}
	void findLoadedAddresses(std::set<IRExpr *> &s, const AllowableOptimisations &opt) {
		target->findLoadedAddresses(s, opt);
	}
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt) {
		target->findUsedBinders(s, opt);
	}
	StateMachine *selectSingleCrashingPath() {
		target = target->selectSingleCrashingPath();
		return this;
	}
	bool canCrash() { return target->canCrash(); }
	int complexity() { return target->complexity(); }
	StateMachineEdge *target0() { return target; }
	const StateMachineEdge *target0() const { return target; }
	StateMachineEdge *target1() { return NULL; }
	const StateMachineEdge *target1() const { return NULL; }
};

class StateMachineBifurcate : public StateMachine {
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
		: StateMachine(origin),
		  condition(_condition),
		  trueTarget(t),
		  falseTarget(f)
	{
	}	
	StateMachineBifurcate(unsigned long origin,
			      IRExpr *_condition,
			      StateMachine *t,
			      StateMachine *f)
		: StateMachine(origin),
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

	void prettyPrint(FILE *f, std::map<const StateMachine *, int> &labels) const {
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
	StateMachine *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something);
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
	StateMachine *selectSingleCrashingPath() {
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
	StateMachineSideEffect *optimise(const AllowableOptimisations &, Oracle *, bool *) { return this; }
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {}
	void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) {}
	void visit(HeapVisitor &hv) {}
	int complexity() { return 0; }
};
class StateMachineSideEffectStore : public StateMachineSideEffect {
	unsigned long _hashval() const { return addr->hashval() * 223 + data->hashval() * 971; }
public:
	StateMachineSideEffectStore(IRExpr *_addr, IRExpr *_data, unsigned long _rip)
		: addr(_addr), data(_data), rip(_rip)
	{
	}
	IRExpr *addr;
	IRExpr *data;
	unsigned long rip;
	void prettyPrint(FILE *f) const {
		fprintf(f, "*(");
		ppIRExpr(addr, f);
		fprintf(f, ") <- ");
		ppIRExpr(data, f);
		fprintf(f, " @ %lx", rip);
	}
	void visit(HeapVisitor &hv) {
		hv(addr);
		hv(data);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &opt);
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt);
	int complexity() { return exprComplexity(addr) * 2 + exprComplexity(data) + 20; }
};

class StateMachineSideEffectLoad : public StateMachineSideEffect {
	void constructed();
	static Int next_key;
	unsigned long _hashval() const { return smsel_addr->hashval() * 757 + key; }
public:
	StateMachineSideEffectLoad(IRExpr *_addr, unsigned long _rip)
		: smsel_addr(_addr), rip(_rip)
	{
		key = next_key++;
		constructed();
	}
	StateMachineSideEffectLoad(Int k, IRExpr *_addr, unsigned long _rip)
		: key(k), smsel_addr(_addr), rip(_rip)
	{
		constructed();
	}
	Int key;
	IRExpr *smsel_addr;
	unsigned long rip;
	void prettyPrint(FILE *f) const {
		fprintf(f, "B%d <- *(", key);
		ppIRExpr(smsel_addr, f);
		fprintf(f, ")@%lx", rip);
	}
	void visit(HeapVisitor &hv) {
		hv(smsel_addr);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {
		l.insert(smsel_addr);
	}
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt);
	int complexity() { return exprComplexity(smsel_addr) + 20; }
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
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) { }
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt);
	int complexity() { return exprComplexity(value); }
};


bool definitelyEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt);
bool definitelyNotEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt);
IRExpr *optimiseIRExpr(IRExpr *e, const AllowableOptimisations &opt);
IRExpr *optimiseIRExpr(IRExpr *src, const AllowableOptimisations &opt, bool *done_something);
bool sortIRExprs(IRExpr *a, IRExpr *b);
void addArgumentToAssoc(IRExpr *e, IRExpr *arg);
bool physicallyEqual(const IRExpr *a, const IRExpr *b);
IRExpr *internIRExpr(IRExpr *x);
IRExpr *simplifyIRExprAsBoolean(IRExpr *inp);
void printStateMachine(const StateMachine *sm, FILE *f);
bool stateMachinesBisimilar(StateMachine *a, StateMachine *b);
bool sideEffectsBisimilar(StateMachineSideEffect *smse1,
			  StateMachineSideEffect *smse2,
			  const AllowableOptimisations &opt);
bool parseStateMachine(StateMachine **out, const char *str, const char **suffix);

#endif /* !STATEMACHINE_HPP__ */
