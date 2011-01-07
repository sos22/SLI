/* Re-implementation of direct which tries to work off of just a core
   dump, rather than needing the full trace. */
#include <err.h>
#include <time.h>

#include <algorithm>
#include <queue>
#include <map>
#include <set>

#include "sli.h"
#include "nd_chooser.h"
#include "range_tree.h"

#include "libvex_guest_offsets.h"

#include "../VEX/priv/guest_generic_bb_to_IR.h"
#include "../VEX/priv/guest_amd64_defs.h"

class Oracle;

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
};
AllowableOptimisations AllowableOptimisations::defaultOptimisations(true, false, false, false);

static bool definitelyEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt);
static bool definitelyNotEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt);

static bool physicallyEqual(const IRExpr *a, const IRExpr *b);

class PrettyPrintable {
public:
	virtual void prettyPrint(FILE *f) const = 0;
};

/* Perform simple peephole optimisation on the IRExpr.  The resulting
   expression is guaranteed to be equivalent to the old one in any
   context.  We may mutate the expression in-place, which is okay
   because there are no semantic changes. */
static IRExpr *optimiseIRExpr(IRExpr *e, const AllowableOptimisations &, bool *done_something);
static IRExpr *optimiseIRExpr(IRExpr *e, const AllowableOptimisations &);
static void assertUnoptimisable(IRExpr *e, const AllowableOptimisations &);

static void findUsedBinders(IRExpr *e, std::set<Int> &, const AllowableOptimisations &);

class StateMachine : public GarbageCollected<StateMachine, &ir_heap>, public PrettyPrintable {
public:
	/* Another peephole optimiser.  Again, must be
	   context-independent and result in no changes to the
	   semantic value of the machine, and can mutate in-place. */
	virtual StateMachine *optimise(const AllowableOptimisations &, Oracle *, bool *) = 0;
	virtual void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) = 0;
	virtual void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) = 0;
	NAMED_CLASS
};

class StateMachineSideEffect : public GarbageCollected<StateMachineSideEffect, &ir_heap>, public PrettyPrintable {
public:
	virtual StateMachineSideEffect *optimise(const AllowableOptimisations &, Oracle *, bool *) = 0;
	virtual void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) = 0;
	virtual void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) = 0;
	NAMED_CLASS
};

static bool isBadAddress(IRExpr *, const AllowableOptimisations &, Oracle *);
static bool definitelyUnevaluatable(IRExpr *, const AllowableOptimisations &, Oracle *);

class StateMachineSideEffectUnreached : public StateMachineSideEffect {
	static VexPtr<StateMachineSideEffectUnreached, &ir_heap> _this;
	StateMachineSideEffectUnreached() {}
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
};
VexPtr<StateMachineSideEffectUnreached, &ir_heap> StateMachineSideEffectUnreached::_this;

class StateMachineSideEffectStore : public StateMachineSideEffect {
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
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something) {
		addr = optimiseIRExpr(addr, opt, done_something);
		data = optimiseIRExpr(data, opt, done_something);
		if (isBadAddress(addr, opt, oracle) ||
		    definitelyUnevaluatable(data, opt, oracle)) {
			*done_something = true;
			return StateMachineSideEffectUnreached::get();
		}
		return this;
	}
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &opt) {
		for (std::set<IRExpr *>::iterator it = l.begin();
		     it != l.end();
			) {
			if (definitelyEqual(*it, addr, opt))
				l.erase(it++);
			else
				it++;
		}
	}
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt) {
		::findUsedBinders(addr, s, opt);
		::findUsedBinders(data, s, opt);
	}
};

class StateMachineSideEffectLoad : public StateMachineSideEffect {
	static Int next_key;
	void constructed()
	{
		IRExpr *old = smsel_addr;
		bool ign;
		smsel_addr = optimiseIRExpr(smsel_addr, AllowableOptimisations::defaultOptimisations, &ign);
		if (smsel_addr->tag == Iex_Const &&
		    (long)smsel_addr->Iex.Const.con->Ico.U64 < 4096)
			dbg_break("constructing funny (StateMachineSideEffectLoad *)%p\n",
				  this);
		(void)old;
	}
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
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something) {
		smsel_addr = optimiseIRExpr(smsel_addr, opt, done_something);
		if (isBadAddress(smsel_addr, opt, oracle)) {
			*done_something = true;
			return StateMachineSideEffectUnreached::get();
		}
		constructed();
		return this;
	}
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {
		l.insert(smsel_addr);
	}
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt) {
		s.erase(key);
		::findUsedBinders(smsel_addr, s, opt);
	}
};
Int StateMachineSideEffectLoad::next_key;

class StateMachineSideEffectCopy : public StateMachineSideEffect {
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
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something) {
		value = optimiseIRExpr(value, opt, done_something);
		if (definitelyUnevaluatable(value, opt, oracle)) {
			*done_something = true;
			return StateMachineSideEffectUnreached::get();
		}
		return this;
	}
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) { }
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt) {
		s.erase(key);
		::findUsedBinders(value, s, opt);
	}
};

class StateMachineEdge : public GarbageCollected<StateMachineEdge, &ir_heap>, public PrettyPrintable {
public:
	StateMachineEdge(StateMachine *t) : target(t) {}
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

	void prettyPrint(FILE *f) const {
		fprintf(f, "%p", this);
		if (sideEffects.size() != 0) {
			fprintf(f, "{");
			bool b = true;
			for (std::vector<StateMachineSideEffect *>::const_iterator it = sideEffects.begin();
			     it != sideEffects.end();
			     it++) {
				if (!b)
					fprintf(f, "; ");
				b = false;
				(*it)->prettyPrint(f);
			}
			fprintf(f, "} ");
		}
		fprintf(f, "%p", target);
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
	NAMED_CLASS
};

class StateMachineUnreached : public StateMachine {
	StateMachineUnreached() {}
	static VexPtr<StateMachineUnreached, &ir_heap> _this;
public:
	static StateMachineUnreached *get() {
		if (!_this) _this = new StateMachineUnreached();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<unreached>"); }
	StateMachine *optimise(const AllowableOptimisations &, Oracle *, bool *) { return this; }
	void visit(HeapVisitor &hv) {}
	void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) {}
};
VexPtr<StateMachineUnreached, &ir_heap> StateMachineUnreached::_this;

class StateMachineCrash : public StateMachine {
	StateMachineCrash() {}
	static VexPtr<StateMachineCrash, &ir_heap> _this;
public:
	static StateMachineCrash *get() {
		if (!_this) _this = new StateMachineCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<crash>"); }
	StateMachine *optimise(const AllowableOptimisations &, Oracle *, bool *) { return this; }
	void visit(HeapVisitor &hv) {}
	void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) {}
};
VexPtr<StateMachineCrash, &ir_heap> StateMachineCrash::_this;

class StateMachineNoCrash : public StateMachine {
	StateMachineNoCrash() {}
	static VexPtr<StateMachineNoCrash, &ir_heap> _this;
public:
	static StateMachineNoCrash *get() {
		if (!_this) _this = new StateMachineNoCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<survive>"); }
	StateMachine *optimise(const AllowableOptimisations &, Oracle *, bool *) { return this; }
	void visit(HeapVisitor &hv) {}
	void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) {}
};
VexPtr<StateMachineNoCrash, &ir_heap> StateMachineNoCrash::_this;

/* A state machine node which always advances to another one.  These
   can be safely eliminated, but they're sometimes kind of handy when
   you're building the machine. */
class StateMachineProxy : public StateMachine {
public:
	StateMachineEdge *target;

	StateMachineProxy(StateMachine *t)
		: target(new StateMachineEdge(t))
	{
	}
	StateMachineProxy(StateMachineEdge *t)
		: target(t)
	{
	}
	void prettyPrint(FILE *f) const
	{
		target->prettyPrint(f);
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
};

class StateMachineBifurcate : public StateMachine {
public:
	StateMachineBifurcate(IRExpr *_condition,
			      StateMachineEdge *t,
			      StateMachineEdge *f)
		: condition(_condition),
		  trueTarget(t),
		  falseTarget(f)
	{
	}	
	StateMachineBifurcate(IRExpr *_condition,
			      StateMachine *t,
			      StateMachine *f)
		: condition(_condition),
		  trueTarget(new StateMachineEdge(t)),
		  falseTarget(new StateMachineEdge(f))
	{
	}

	IRExpr *condition; /* Should be typed Ity_I1.  If zero, we go
			      to the false target.  Otherwise, we go
			      to the true one. */
	StateMachineEdge *trueTarget;
	StateMachineEdge *falseTarget;

	void prettyPrint(FILE *f) const {
		fprintf(f, "if (");
		ppIRExpr(condition, f);
		fprintf(f, ") then {");
		trueTarget->prettyPrint(f);
		fprintf(f, "} else {");
		falseTarget->prettyPrint(f);
		fprintf(f, "}");
	}
	void visit(HeapVisitor &hv)
	{
		hv(trueTarget);
		hv(falseTarget);
		hv(condition);
	}
	StateMachine *optimise(const AllowableOptimisations &opt, Oracle *oracle, bool *done_something)
	{
		if (trueTarget->target == StateMachineUnreached::get()) {
			*done_something = true;
			if (falseTarget->target == StateMachineUnreached::get())
				return StateMachineUnreached::get();
			else
				return new StateMachineProxy(falseTarget->optimise(opt, oracle, done_something));
		}
		if (falseTarget->target == StateMachineUnreached::get()) {
			*done_something = true;
			return new StateMachineProxy(trueTarget->optimise(opt, oracle, done_something));
		}
		condition = optimiseIRExpr(condition, opt, done_something);
		if (condition->tag == Iex_Const) {
			*done_something = true;
			if (condition->Iex.Const.con->Ico.U1)
				return new StateMachineProxy(trueTarget->optimise(opt, oracle, done_something));
			else
				return new StateMachineProxy(falseTarget->optimise(opt, oracle, done_something));
		}
		trueTarget = trueTarget->optimise(opt, oracle, done_something);
		falseTarget = falseTarget->optimise(opt, oracle, done_something);
		if (trueTarget->target == falseTarget->target &&
		    trueTarget->sideEffects.size() == 0 &&
		    falseTarget->sideEffects.size() == 0) {
			*done_something = true;
			return trueTarget->target;
		}
		return this;
	}
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
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt)
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
};

/* A node in the state machine representing a bit of code which we
   haven't explored yet. */
class StateMachineStub : public StateMachine {
public:
	IRExpr *target;

	StateMachineStub(IRExpr *t) : target(t) {}

	void prettyPrint(FILE *f) const
	{
		fprintf(f, "<jmp ");
		ppIRExpr(target, f);
		fprintf(f, ">");
	}
	void visit(HeapVisitor &hv) { hv(target); }
	StateMachine *optimise(const AllowableOptimisations &, Oracle *, bool *) { return this; }
	void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) { }
};

class InstructionSet {
public:
	std::set<unsigned long> rips;
};
static bool
operator<(const InstructionSet &a, const InstructionSet &b)
{
	return a.rips < b.rips;
}

/* All of the information from sources other than the main crash dump.
 * Information from the oracle will be true of some executions but not
 * necessarily all of them, so should only really be used where static
 * analysis is insufficient. */
class Oracle : public GarbageCollected<Oracle> {
	struct tag_entry {
		std::set<unsigned long> loads;
		std::set<unsigned long> stores;
	};
	std::vector<tag_entry> tag_table;
	void loadTagTable(const char *path);
public:
	MachineState *ms;
	Thread *crashedThread;

	void findPreviousInstructions(std::vector<unsigned long> &output);
	void findConflictingStores(StateMachineSideEffectLoad *smsel,
				   std::set<unsigned long> &out);
	void clusterRips(const std::set<unsigned long> &inputRips,
			 std::set<InstructionSet> &outputClusters);
	bool storeIsThreadLocal(StateMachineSideEffectStore *s);
	bool memoryAccessesMightAlias(StateMachineSideEffectLoad *, StateMachineSideEffectStore *);
	bool functionCanReturn(unsigned long rip);

	Oracle(MachineState *_ms, Thread *_thr, const char *tags)
		: ms(_ms), crashedThread(_thr)
	{
		loadTagTable(tags);
	}
	void visit(HeapVisitor &hv) {
		hv(ms);
		hv(crashedThread);
	}
	NAMED_CLASS
};

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

/* A VEX RIP combines an ordinary machine code RIP with an offset into
   a VEX IRSB.  An idx of 0 corresponds to just before the start of
   the block, and stmts_used corresponds to just after the end. */
class VexRip : public Named {
protected:
	char *mkName() const { return my_asprintf("%lx:%x", rip, idx); }
public:
	VexRip(unsigned long _rip, unsigned _idx) : rip(_rip), idx(_idx) {}
	unsigned long rip;
	unsigned idx;	
	void changedIdx() { clearName(); }
	unsigned long hash(void) const {
		return rip ^ (idx * 13);
	}
	bool operator<(const VexRip &a) const {
		return rip < a.rip || (rip == a.rip && idx < a.idx);
	}
	bool operator==(const VexRip &a) const {
		return rip == a.rip && idx == a.idx;
	}
};

class CrashReason : public GarbageCollected<CrashReason, &ir_heap>,
		    public PrettyPrintable {
public:
	/* A crash reason represents a summary of information which is
	   believed to be relevant in explaining a crash.  It consists
	   of state machine and a rip, such that the state machine
	   will evaluate to 0 if we're likely to crash and 1 if we're
	   not. */	   
	VexRip rip;
	StateMachine *sm;

	CrashReason(const VexRip &_rip, StateMachine *_sm)
		: rip(_rip), sm(_sm)
	{}

	void visit(HeapVisitor &hv) { hv(sm); }
	void prettyPrint(FILE *f) const
	{
		fprintf(f, "%s: ", rip.name());
		sm->prettyPrint(f);
	}

	NAMED_CLASS
};

/* A bunch of heuristics for figuring out why we crashed.  Returns
 * NULL on failure.  Pretty stupid. */
static CrashReason *
getProximalCause(MachineState *ms, Thread *thr)
{
	unsigned long rip = thr->regs.rip();
	IRSB *irsb;
	int x;
	int nr_marks;

	if (rip == 0) {
		/* Probably caused by calling a bad function pointer.
		 * Look at the call site. */
		rip = ms->addressSpace->fetch<unsigned long>(thr->regs.rsp(), NULL) - 2;
		irsb = ms->addressSpace->getIRSBForAddress(thr->tid._tid(), rip);
		if (!irsb) {
			/* I guess that wasn't it.  Give up. */
			return NULL;
		}
		/* That should be a call instruction, in which case
		   we'll have a single mark, a jumpkind of Call, and a
		   next pointer of some expression. */
		if (irsb->jumpkind != Ijk_Call)
			return NULL;
		nr_marks = 0;
		for (x = 0; x < irsb->stmts_used; x++) {
			if (irsb->stmts[x]->tag == Ist_IMark)
				nr_marks++;
		}
		if (nr_marks != 1)
			return NULL;

		/* We now guess that we crashed because the function
		   pointer called turned out to be NULL. */
		return new CrashReason(VexRip(rip, irsb->stmts_used),
				       new StateMachineBifurcate(
					       IRExpr_Binop(
						       Iop_CmpEQ64,
						       irsb->next,
						       IRExpr_Const(IRConst_U64(0))),
					       StateMachineCrash::get(),
					       StateMachineNoCrash::get()));
	}

	/* Next guess: it's caused by dereferencing a bad pointer.
	   Grab the crashing instruction and try emulating it.  If it
	   results in a crash, we can be pretty confident that we've
	   found the problem. */
	irsb = ms->addressSpace->getIRSBForAddress(thr->tid._tid(), rip);
	thr->temporaries.setSize(irsb->tyenv->types_used);
	for (int x = 1 /* Skip the initial IMark */;
	     x < irsb->stmts_used;
	     x++) {
		IRStmt *stmt = irsb->stmts[x];
		ThreadEvent *evt = interpretStatement(stmt,
						      thr,
						      NULL,
						      ms,
						      irsb);
		if (evt == NULL)
			continue;
		if (evt == DUMMY_EVENT || evt == FINISHED_BLOCK) {
			/* Okay, so re-interpreting this instruction
			   didn't give us any clues as to why we're
			   crashing.  Give up. */
			break;
		}

		SignalEvent *se = dynamic_cast<SignalEvent *>(evt);
		if (se && se->signr == 11) {
			/* Program tripped over a segfault -> almost
			   certainly the cause of the crash.  It'll be
			   from either a load or a store, and we
			   special case the two cases here. */
			IRExpr *addr = NULL;
			if (stmt->tag == Ist_Dirty &&
			    (!strcmp(stmt->Ist.Dirty.details->cee->name,
				     "helper_load_8") ||
			     !strcmp(stmt->Ist.Dirty.details->cee->name,
				     "helper_load_16") ||
			     !strcmp(stmt->Ist.Dirty.details->cee->name,
				     "helper_load_32") ||			     
			     !strcmp(stmt->Ist.Dirty.details->cee->name,
				     "helper_load_64"))) {
				/* It's a load; the address loaded is
				   in the first argument. */
				addr = stmt->Ist.Dirty.details->args[0];
			} else if (stmt->tag == Ist_Store) {
				addr = stmt->Ist.Store.addr;
			} else {
				/* Neither a load nor a store.  That
				   shouldn't be generating a segfault,
				   then. */
				abort();
			}
			assert(addr != NULL);
			return new CrashReason(VexRip(rip, x),
					       new StateMachineBifurcate(
						       IRExpr_Binop(
							       Iop_CmpEQ64,
							       addr,
							       IRExpr_Const(IRConst_U64(se->virtaddr))),
						       StateMachineCrash::get(),
						       StateMachineNoCrash::get()));
		}
		printf("Generated event %s\n", evt->name());
	}

	printf("Hit end of block without any events -> no idea why we crashed.\n");
	return NULL;
}

class StateMachineTransformer {
private:
	/* Transformations are memoised.  This is important, because
	   it means that we preserve the state machine structure
	   rather than unrolling it. */
	std::map<const StateMachine *, StateMachine *> memoTable;
	StateMachine *doit(StateMachine *inp);
	StateMachineEdge *doit(StateMachineEdge *inp);

protected:
	virtual StateMachine *transformedCrash()
	{
		return StateMachineCrash::get();
	}
	virtual StateMachine *transformedNoCrash()
	{
		return StateMachineNoCrash::get();
	}
	virtual StateMachine *transformedUnreached()
	{
		return StateMachineUnreached::get();
	}
	virtual IRExpr *transformIRExpr(IRExpr *e);

	virtual IRExpr *transformIexGet(IRExpr *e) { return e; }
	virtual IRExpr *transformIexGetI(IRExpr *e)
	{
		IRExpr *e2 = transformIRExpr(e->Iex.GetI.ix);
		if (e2 == e)
			return e;
		else
			return IRExpr_GetI(e->Iex.GetI.descr,
					   e2,
					   e->Iex.GetI.bias,
					   e->Iex.GetI.tid);
	}
	virtual IRExpr *transformIexRdTmp(IRExpr *e) { return e; }
	virtual IRExpr *transformIexQop(IRExpr *e)
	{
		IRExpr *a1 = transformIRExpr(e->Iex.Qop.arg1);
		IRExpr *a2 = transformIRExpr(e->Iex.Qop.arg2);
		IRExpr *a3 = transformIRExpr(e->Iex.Qop.arg3);
		IRExpr *a4 = transformIRExpr(e->Iex.Qop.arg4);
		if (a1 == e->Iex.Qop.arg1 &&
		    a2 == e->Iex.Qop.arg2 &&
		    a3 == e->Iex.Qop.arg3 &&
		    a4 == e->Iex.Qop.arg4)
			return e;
		else
			return IRExpr_Qop(e->Iex.Qop.op,
					  a1,
					  a2,
					  a3,
					  a4);
	}
	virtual IRExpr *transformIexTriop(IRExpr *e)
	{
		IRExpr *a1 = transformIRExpr(e->Iex.Qop.arg1);
		IRExpr *a2 = transformIRExpr(e->Iex.Qop.arg2);
		IRExpr *a3 = transformIRExpr(e->Iex.Qop.arg3);
		if (a1 == e->Iex.Qop.arg1 &&
		    a2 == e->Iex.Qop.arg2 &&
		    a3 == e->Iex.Qop.arg3)
			return e;
		else
			return IRExpr_Triop(e->Iex.Qop.op,
					    a1,
					    a2,
					    a3);
	}
	virtual IRExpr *transformIexBinop(IRExpr *e)
	{
		IRExpr *a1 = transformIRExpr(e->Iex.Qop.arg1);
		IRExpr *a2 = transformIRExpr(e->Iex.Qop.arg2);
		if (a1 == e->Iex.Qop.arg1 &&
		    a2 == e->Iex.Qop.arg2)
			return e;
		else
			return IRExpr_Binop(e->Iex.Qop.op,
					    a1,
					    a2);
	}
	virtual IRExpr *transformIexUnop(IRExpr *e)
	{
		IRExpr *a1 = transformIRExpr(e->Iex.Qop.arg1);
		if (a1 == e->Iex.Qop.arg1)
			return e;
		else
			return IRExpr_Unop(e->Iex.Qop.op,
					    a1);
	}
	virtual IRExpr *transformIexLoad(IRExpr *e)
	{
		IRExpr *addr = transformIRExpr(e->Iex.Load.addr);
		if (addr == e->Iex.Load.addr)
			return e;
		else
			return IRExpr_Load(e->Iex.Load.isLL,
					   e->Iex.Load.end,
					   e->Iex.Load.ty,
					   addr);
	}
	virtual IRExpr *transformIexConst(IRExpr *e)
	{
		return e;
	}
	virtual IRExpr *transformIexMux0X(IRExpr *e)
	{
		IRExpr *c = transformIRExpr(e->Iex.Mux0X.cond);
		IRExpr *z = transformIRExpr(e->Iex.Mux0X.expr0);
		IRExpr *x = transformIRExpr(e->Iex.Mux0X.exprX);
		if (c == e->Iex.Mux0X.cond &&
		    z == e->Iex.Mux0X.expr0 &&
		    x == e->Iex.Mux0X.exprX)
			return e;
		else
			return IRExpr_Mux0X(c, z, x);
	}
	virtual IRExpr *transformIexCCall(IRExpr *);
	virtual IRExpr *transformIexAssociative(IRExpr *);
public:
	StateMachine *transform(StateMachine *start);
};

StateMachine *
StateMachineTransformer::doit(StateMachine *inp)
{
	if (memoTable.count(inp))
		return memoTable[inp];
	StateMachine *out;
	if (inp == StateMachineCrash::get()) {
		out = transformedCrash();
	} else if (inp == StateMachineNoCrash::get()) {
		out = transformedNoCrash();
	} else if (inp == StateMachineUnreached::get()) {
		out = transformedUnreached();
	} else if (StateMachineBifurcate *smb =
		   dynamic_cast<StateMachineBifurcate *>(inp)) {
		StateMachineEdge *t = doit(smb->trueTarget);
		StateMachineEdge *f = doit(smb->falseTarget);
		IRExpr *cond = transformIRExpr(smb->condition);
		if (t == smb->trueTarget && f == smb->falseTarget && cond == smb->condition)
			out = inp;
		else
			out = new StateMachineBifurcate(cond, t, f);
	} else if (StateMachineProxy *smp =
		   dynamic_cast<StateMachineProxy *>(inp)) {
		StateMachineEdge *t = doit(smp->target);
		if (t == smp->target)
			out = inp;
		else
			out = new StateMachineProxy(t);
	} else if (StateMachineStub *sms =
		   dynamic_cast<StateMachineStub *>(inp)) {
		IRExpr *target = transformIRExpr(sms->target);
		if (target == sms->target)
			out = inp;
		else
			out = new StateMachineStub(target);
	} else {
		abort();
	}
	memoTable[inp] = out;
	return out;
}

StateMachineEdge *
StateMachineTransformer::doit(StateMachineEdge *inp)
{
	StateMachine *t = doit(inp->target);
	StateMachineEdge *res = new StateMachineEdge(t);
	bool changedSideEffect = false;
	for (std::vector<StateMachineSideEffect *>::iterator it = inp->sideEffects.begin();
	     it != inp->sideEffects.end();
	     it++) {
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(*it)) {
			IRExpr *a, *d;
			a = transformIRExpr(smses->addr);
			d = transformIRExpr(smses->data);
			if (a != smses->addr || d != smses->data)
				changedSideEffect = true;
			res->sideEffects.push_back(
				new StateMachineSideEffectStore(
					a,
					d,
					smses->rip));
		} else if (StateMachineSideEffectLoad *smsel =
			   dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			IRExpr *a = transformIRExpr(smsel->smsel_addr);
			if (a != smsel->smsel_addr)
				changedSideEffect = true;
			res->sideEffects.push_back(
				new StateMachineSideEffectLoad(
					smsel->key,
					a,
					smsel->rip));
		} else if (StateMachineSideEffectCopy *smsec =
			   dynamic_cast<StateMachineSideEffectCopy *>(*it)) {
			IRExpr *v = transformIRExpr(smsec->value);
			if (v != smsec->value)
				changedSideEffect = true;
			res->sideEffects.push_back(
				new StateMachineSideEffectCopy(
					smsec->key,
					v));
		} else if (dynamic_cast<StateMachineSideEffectUnreached *>(*it)) {
			res->sideEffects.push_back(*it);
		} else {
			abort();
		}
	}
	if (!changedSideEffect && t == inp->target)
		return inp;
	else
		return res;
}

StateMachine *
StateMachineTransformer::transform(StateMachine *inp)
{
	return doit(inp);
}

IRExpr *
StateMachineTransformer::transformIRExpr(IRExpr *e)
{
	switch (e->tag) {
	case Iex_Binder:
		return e;
	case Iex_Get:
		return transformIexGet(e);
	case Iex_GetI:
		return transformIexGetI(e);
	case Iex_RdTmp:
		return transformIexRdTmp(e);
	case Iex_Qop:
		return transformIexQop(e);
	case Iex_Triop:
		return transformIexTriop(e);
	case Iex_Binop:
		return transformIexBinop(e);
	case Iex_Unop:
		return transformIexUnop(e);
	case Iex_Load:
		return transformIexLoad(e);
	case Iex_Const:
		return transformIexConst(e);
	case Iex_CCall:
		return transformIexCCall(e);
	case Iex_Mux0X:
		return transformIexMux0X(e);
	case Iex_Associative:
		return transformIexAssociative(e);
	}
	abort();
}

IRExpr *
StateMachineTransformer::transformIexCCall(IRExpr *e)
{
	IRExpr **newArgs;
	int nr_args;
	int x;
	bool changedSomething;

	for (nr_args = 0; e->Iex.CCall.args[nr_args]; nr_args++)
		;
	newArgs = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_args + 1);
	changedSomething = false;
	for (x = 0; x < nr_args; x++) {
		newArgs[x] = transformIRExpr(e->Iex.CCall.args[x]);
		if (newArgs[x] != e->Iex.CCall.args[x])
			changedSomething = true;
	}
	newArgs[nr_args] = NULL;
	if (!changedSomething)
		return e;
	else
		return IRExpr_CCall(e->Iex.CCall.cee,
				    e->Iex.CCall.retty,
				    newArgs);
}

IRExpr *
StateMachineTransformer::transformIexAssociative(IRExpr *e)
{
	IRExpr *r = IRExpr_Associative(e);
	bool changedSomething = false;
	for (int x = 0; x < r->Iex.Associative.nr_arguments; x++) {
		r->Iex.Associative.contents[x] =
			transformIRExpr(r->Iex.Associative.contents[x]);
		if (e->Iex.Associative.contents[x] !=
		    r->Iex.Associative.contents[x])
			changedSomething = true;
	}
	if (!changedSomething)
		return e;
	else
		return r;
}

class RewriteRegister : public StateMachineTransformer {
	unsigned idx;
	IRExpr *to;
protected:
	IRExpr *transformIexGet(IRExpr *what);
public:
	RewriteRegister(unsigned _idx, IRExpr *_to)
		: idx(_idx), to(_to)
	{
	}
};

IRExpr *
RewriteRegister::transformIexGet(IRExpr *what)
{
	if (what->Iex.Get.offset == (int)idx)
		return to;
	else
		return what;
}

static StateMachine *
rewriteRegister(StateMachine *sm,
		unsigned reg_idx,
		IRExpr *newval)
{
	RewriteRegister rr(reg_idx, newval);
	return rr.transform(sm);
}

class RewriteTemporary : public StateMachineTransformer {
	IRTemp tmp;
	IRExpr *to;
protected:
	IRExpr *transformIexRdTmp(IRExpr *what)
	{
		if (what->Iex.RdTmp.tmp == tmp)
			return to;
		else
			return what;
	}
public:
	RewriteTemporary(IRTemp _tmp, IRExpr *_to)
		: tmp(_tmp), to(_to)
	{
	}
};

static StateMachine *
rewriteTemporary(StateMachine *sm,
		 IRTemp tmp,
		 IRExpr *newval)
{
	RewriteTemporary rt(tmp, newval);
	return rt.transform(sm);
}

static StateMachine *
backtrackStateMachineOneStatement(StateMachine *sm, IRStmt *stmt, unsigned long rip)
{
	switch (stmt->tag) {
	case Ist_NoOp:
	case Ist_IMark:
	case Ist_AbiHint:
		break;
	case Ist_Put:
		sm = rewriteRegister(sm,
				     stmt->Ist.Put.offset,
				     stmt->Ist.Put.data);
		break;
	case Ist_PutI:
		/* We can't handle these correctly. */
		abort();
		return NULL;
	case Ist_WrTmp:
		sm = rewriteTemporary(sm,
				      stmt->Ist.WrTmp.tmp,
				      stmt->Ist.WrTmp.data);
		break;
	case Ist_Store: {
		StateMachineProxy *smp = new StateMachineProxy(sm);
		smp->target->prependSideEffect(
			new StateMachineSideEffectStore(
				stmt->Ist.Store.addr,
				stmt->Ist.Store.data,
				rip));
		sm = smp;
		break;
	}

	case Ist_Dirty:
		if (!strcmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_8") ||
		    !strcmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_64") ||
		    !strcmp(stmt->Ist.Dirty.details->cee->name,
			    "helper_load_32")) {
			StateMachineSideEffectLoad *smsel =
				new StateMachineSideEffectLoad(
					stmt->Ist.Dirty.details->args[0],
					rip);
			sm = rewriteTemporary(
				sm,
				stmt->Ist.Dirty.details->tmp,
				IRExpr_Binder(smsel->key));
			StateMachineProxy *smp = new StateMachineProxy(sm);
			smp->target->prependSideEffect(smsel);
			sm = smp;
		}  else {
			abort();
		}
		break;

	case Ist_CAS:
		/* Can't backtrack across these */
		abort();
		sm = NULL;
		break;

	case Ist_MBE:
		break;
	case Ist_Exit:
		sm = new StateMachineBifurcate(
			stmt->Ist.Exit.guard,
			new StateMachineStub(
				IRExpr_Const(stmt->Ist.Exit.dst)),
			sm);
		break;
	default:
		abort();
	}
	return sm;
}

static CrashReason *
backtrackOneStatement(CrashReason *cr, IRStmt *stmt)
{
	StateMachine *sm = cr->sm;

	VexRip newRip(cr->rip);
	assert(newRip.idx > 0);
	newRip.idx--;
	newRip.changedIdx();
	sm = backtrackStateMachineOneStatement(sm, stmt, cr->rip.rip);
	return new CrashReason(newRip, sm);
}

static CrashReason *
backtrackToStartOfInstruction(unsigned tid, CrashReason *cr, AddressSpace *as)
{
	IRSB *irsb = as->getIRSBForAddress(tid, cr->rip.rip);
	assert((int)cr->rip.idx <= irsb->stmts_used);
	while (cr->rip.idx != 0)
		cr = backtrackOneStatement(cr, irsb->stmts[cr->rip.idx-1]);
	return cr;
}

static void
printStateMachine(const StateMachine *sm, FILE *f)
{
	std::set<const StateMachine *> emitted;
	std::vector<const StateMachine *> toEmit;

	toEmit.push_back(sm);
	while (!toEmit.empty()) {
		sm = toEmit.back();
		toEmit.pop_back();
		if (emitted.count(sm))
			continue;
		emitted.insert(sm);
		fprintf(f, "%p: ", sm);
		sm->prettyPrint(f);
		fprintf(f, "\n");
		if (const StateMachineBifurcate *smb =
		    dynamic_cast<const StateMachineBifurcate *>(sm)) {
			toEmit.push_back(smb->trueTarget->target);
			toEmit.push_back(smb->falseTarget->target);
		} else if (const StateMachineProxy *smp =
			   dynamic_cast<const StateMachineProxy *>(sm)) {
			toEmit.push_back(smp->target->target);
		}
	}
}

template <typename t>
class CFGNode : public GarbageCollected<CFGNode<t>, &ir_heap>, public PrettyPrintable {
public:
	t fallThroughRip;
	t branchRip;
	CFGNode<t> *fallThrough;
	CFGNode<t> *branch;

	t my_rip;

	bool accepting;

	CFGNode(t rip) : my_rip(rip), accepting(false) {}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%#lx: %#lx(%p), %#lx(%p)",
			wrappedRipToRip(my_rip),
			wrappedRipToRip(fallThroughRip),
			fallThrough,
			wrappedRipToRip(branchRip),
			branch);
	}
	void visit(HeapVisitor &hv) {
		hv(fallThrough);
		hv(branch);
	}
	NAMED_CLASS
};

/* All the various bits and pieces which we've discovered so far, in one
 * convenient place. */
class InferredInformation : public GarbageCollected<InferredInformation> {
public:
	Oracle *oracle;
	VexPtr<gc_heap_map<VexRip, CrashReason, &ir_heap>::type, &ir_heap> crashReasons;

	InferredInformation(Oracle *_oracle) :
		oracle(_oracle),
		crashReasons(new gc_heap_map<VexRip, CrashReason, &ir_heap>::type())
	{}
	void addCrashReason(CrashReason *cr) { crashReasons->set(cr->rip, cr); }
	CFGNode<unsigned long> *CFGFromRip(unsigned long rip, const std::set<unsigned long> &terminalFunctions);
	CrashReason *CFGtoCrashReason(unsigned tid, CFGNode<unsigned long> *cfg);

	void visit(HeapVisitor &hv) {
		hv(oracle);
	}
	void relocate(InferredInformation *to, size_t s) {
		crashReasons.relocate(&to->crashReasons);
	}
	NAMED_CLASS
};

static void
enumerateReachableStates(CFGNode<unsigned long> *from, std::set<CFGNode<unsigned long> *> &out)
{
	if (!from || out.count(from))
		return;
	out.insert(from);
	enumerateReachableStates(from->fallThrough, out);
	enumerateReachableStates(from->branch, out);
}

/* Build a control flow graph which covers all of the RIPs in @rips.
 * @output is filled in with pointers to all of the possible start
 * nodes.
 */
/* This only really makes sense if @rips are similar enough that the
 * CFGs are likely to overlap. */
static void
buildCFGForRipSet(AddressSpace *as,
		  const std::set<unsigned long> &rips,
		  const std::set<unsigned long> &terminalFunctions,
		  std::set<CFGNode<unsigned long> *> &output,
		  Oracle *oracle)
{
	std::map<unsigned long, CFGNode<unsigned long> *> builtSoFar;
	std::vector<unsigned long> needed;
	unsigned long rip;

	/* Mild hack to make some corned cases easier. */
	builtSoFar[0] = NULL;

	/* Step one: discover all of the instructions which we're
	 * going to need. */
	for (std::set<unsigned long>::const_iterator it = rips.begin();
	     it != rips.end();
	     it++)
		needed.push_back(*it);
	while (!needed.empty()) {
		rip = needed.back();
		needed.pop_back();
		if (builtSoFar.count(rip))
			continue;
		IRSB *irsb = as->getIRSBForAddress(-1, rip);
		CFGNode<unsigned long> *work = new CFGNode<unsigned long>(rip);
		int x;
		for (x = 1; x < irsb->stmts_used; x++) {
			if (irsb->stmts[x]->tag == Ist_IMark) {
				work->fallThroughRip = irsb->stmts[x]->Ist.IMark.addr;
				needed.push_back(work->fallThroughRip);
				break;
			}
			if (irsb->stmts[x]->tag == Ist_Exit) {
				assert(work->branch == 0);
				work->branchRip = irsb->stmts[x]->Ist.Exit.dst->Ico.U64;
				needed.push_back(work->branchRip);
			}
		}
		if (x == irsb->stmts_used) {
			if (irsb->jumpkind == Ijk_Call) {
				work->fallThroughRip = extract_call_follower(irsb);
				if (irsb->next->tag == Iex_Const) {
					if (terminalFunctions.count(irsb->next->Iex.Const.con->Ico.U64))
						work->fallThroughRip = irsb->next->Iex.Const.con->Ico.U64;
					else if (!oracle->functionCanReturn(irsb->next->Iex.Const.con->Ico.U64))
						work->fallThroughRip = 0;
				}
				if (work->fallThroughRip)
					needed.push_back(work->fallThroughRip);
			} else if (irsb->jumpkind == Ijk_Ret) {
				work->accepting = true;
			} else {
				/* Don't currently try to trace across indirect branches. */
				if (irsb->next->tag == Iex_Const) {
					work->fallThroughRip = irsb->next->Iex.Const.con->Ico.U64;
					needed.push_back(work->fallThroughRip);
				}
			}
		}
		builtSoFar[rip] = work;
	}

	/* Now we have a CFG node for every needed instruction.  Go
	   through and resolve exit branches. */
	for (std::map<unsigned long, CFGNode<unsigned long> *>::iterator it = builtSoFar.begin();
	     it != builtSoFar.end();
	     it++) {
		if (it->second) {
			it->second->fallThrough = builtSoFar[it->second->fallThroughRip];
			it->second->branch = builtSoFar[it->second->branchRip];
		}
	}

	/* Extract the start states.  These will be some subset of the
	   input root nodes. */
	std::set<CFGNode<unsigned long> *> outputSoFar;
	for (std::set<unsigned long>::const_iterator it = rips.begin();
	     it != rips.end();
	     it++) {
		CFGNode<unsigned long> *startnode = builtSoFar[*it];
		if (outputSoFar.count(startnode))
			continue;
		output.insert(startnode);

		enumerateReachableStates(startnode, outputSoFar);
	}
}

/* Special case of buildCFGForRipSet() when you only have one entry
 * RIP */
CFGNode<unsigned long> *
InferredInformation::CFGFromRip(unsigned long start, const std::set<unsigned long> &terminalFunctions)
{
	std::set<unsigned long> rips;
	std::set<CFGNode<unsigned long> *> out;
	rips.insert(start);
	buildCFGForRipSet(oracle->ms->addressSpace, rips, terminalFunctions, out, oracle);
	if (out.size() == 0)
		return NULL;
	assert(out.size() == 1);
	return *out.begin();
}

CrashReason *
InferredInformation::CFGtoCrashReason(unsigned tid, CFGNode<unsigned long> *cfg)
{
	VexRip finalRip(cfg->my_rip, 0);
	if (crashReasons->hasKey(finalRip)) {
		assert(crashReasons->get(finalRip));
		return crashReasons->get(finalRip);
	}
	CrashReason *res;
	if (!cfg->branch && !cfg->fallThrough) {
		res = new CrashReason(finalRip, StateMachineNoCrash::get());
	} else {
		IRSB *irsb = oracle->ms->addressSpace->getIRSBForAddress(tid, finalRip.rip);
		int x;
		for (x = 1; x < irsb->stmts_used; x++)
			if (irsb->stmts[x]->tag == Ist_IMark)
				break;
		if (cfg->fallThrough) {
			CrashReason *ft;
			ft = CFGtoCrashReason(tid, cfg->fallThrough);
			if (x == irsb->stmts_used &&
			    irsb->jumpkind == Ijk_Call &&
			    cfg->fallThroughRip == extract_call_follower(irsb)) {
				/* This call is suppressed -> ignore
				   it, rather than doing the
				   backtracking thing. */
				ft = new CrashReason(finalRip, ft->sm);
			} else {
				ft = new CrashReason(VexRip(finalRip.rip, x), ft->sm);
				while (ft->rip.idx != 0) {
					IRStmt *stmt = irsb->stmts[ft->rip.idx-1];
					if (stmt->tag == Ist_Exit) {
						VexRip newRip(ft->rip);
						newRip.idx--;
						newRip.changedIdx();
						if (cfg->branch) {
							ft = new CrashReason(
								newRip,
								new StateMachineBifurcate(
									stmt->Ist.Exit.guard,
									CFGtoCrashReason(tid, cfg->branch)->sm,
									ft->sm));
						} else {
							ft = new CrashReason(
								newRip,
								ft->sm);
						}
					} else {
						ft = backtrackOneStatement(ft, stmt);
					}
				}
			}
			res = ft;
		} else {
			assert(cfg->branch);
			CrashReason *b = CFGtoCrashReason(tid, cfg->branch);
			for (x--; x >= 0; x--)
				if (irsb->stmts[x]->tag == Ist_Exit)
					break;
			assert(x > 0);
			b = new CrashReason(VexRip(finalRip.rip, x), b->sm);
			while (b->rip.idx != 0) {
				IRStmt *stmt = irsb->stmts[b->rip.idx-1];
				b = backtrackOneStatement(b, stmt);
			}
			res = b;
		}
	}
	assert(finalRip == res->rip);
	assert(res);
	crashReasons->set(finalRip, res);
	return res;
}

template <typename t> void
printCFG(const CFGNode<t> *cfg)
{
	std::vector<const CFGNode<t> *> pending;
	std::set<const CFGNode<t> *> done;

	pending.push_back(cfg);
	while (!pending.empty()) {
		cfg = pending.back();
		pending.pop_back();
		if (done.count(cfg))
			continue;
		printf("%p: ", cfg);
		cfg->prettyPrint(stdout);
		printf("\n");
		if (cfg->fallThrough)
			pending.push_back(cfg->fallThrough);
		if (cfg->branch)
			pending.push_back(cfg->branch);
		done.insert(cfg);
	}
}

void
Oracle::findPreviousInstructions(std::vector<unsigned long> &out)
{
	getDominators(crashedThread, ms, out);
}

bool
Oracle::functionCanReturn(unsigned long rip)
{
#warning Horrible, horrible hack
	if (rip == 0x768440 /* ut_dbg_assertion_failed */ ||
	    rip == 0x7683e0 /* ut_dbg_stop_thread */)
		return false;
	else
		return true;
}

unsigned long
hash_ulong_pair(const std::pair<unsigned long, unsigned long> &p)
{
	return p.first + p.second * 59;
}

typedef gc_map<std::pair<unsigned long, unsigned long>,
	       bool,
	       hash_ulong_pair,
	       __default_eq_function<std::pair<unsigned long, unsigned long> >,
	       __default_visit_function<bool>,
	       &ir_heap> gc_pair_ulong_set_t;

static void
mergeUlongSets(gc_pair_ulong_set_t *dest, const gc_pair_ulong_set_t *src)
{
	for (gc_pair_ulong_set_t::iterator it = src->begin();
	     it != src->end();
	     it++)
		dest->set(it.key(), it.value());
}

template<typename t> void
operator |=(std::set<t> &x, const std::set<t> &y)
{
	for (typename std::set<t>::iterator it = y.begin();
	     it != y.end();
	     it++)
		x.insert(*it);
}

/* Try to find the RIPs of some stores which might conceivably have
   interfered with the observed load.  Stack accesses are not tracked
   by this mechanism. */
/* We do this using a profiling-based scheme.  There's some initial
   training phase during which we log, for every memory location, the
   set of loads and stores which access it, and we then just return
   the union of the store sets for all the locations whose load set
   includes the observed address. */
void
Oracle::findConflictingStores(StateMachineSideEffectLoad *smsel,
			      std::set<unsigned long> &out)
{
	out.clear();
	for (std::vector<tag_entry>::iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++) {
		if (it->loads.count(smsel->rip))
			out |= it->stores;
	}
}

/* Try to guess whether this store might ever be consumed by another
   thread.  We approximate this by saying that anything not included
   in our database of dynamic information is thread-local. */
bool
Oracle::storeIsThreadLocal(StateMachineSideEffectStore *s)
{
	static std::set<unsigned long> threadLocal;
	static std::set<unsigned long> notThreadLocal;
	if (threadLocal.count(s->rip))
		return true;
	if (notThreadLocal.count(s->rip))
		return false;
	for (std::vector<tag_entry>::iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++)
		if (it->stores.count(s->rip)) {
			notThreadLocal.insert(s->rip);
			return false;
		}
	threadLocal.insert(s->rip);
	return true;
}

bool
Oracle::memoryAccessesMightAlias(StateMachineSideEffectLoad *smsel,
				 StateMachineSideEffectStore *smses)
{
	for (std::vector<tag_entry>::iterator it = tag_table.begin();
	     it != tag_table.end();
	     it++)
		if (it->loads.count(smsel->rip) &&
		    it->stores.count(smses->rip))
			return true;
	return false;
}

template <typename t> void
enumerateCFG(CFGNode<t> *root, std::map<t, CFGNode<t> *> &rips)
{
	if (!root)
		return;
	if (rips.count(root->my_rip))
		return;
	rips[root->my_rip] = root;
	enumerateCFG(root->branch, rips);
	enumerateCFG(root->fallThrough, rips);
}

static bool
instructionIsInteresting(const InstructionSet &i, unsigned long r)
{
	return i.rips.count(r) != 0;
}

/* Remove all of the nodes which appear to be uninteresting.  A node
   is uninteresting if it is not in the initial interesting set and
   there are no paths from it to an interesting node. */
template <typename t> void
trimCFG(CFGNode<t> *root, const InstructionSet &interestingAddresses)
{
	std::map<t, CFGNode<t> *> uninteresting;
	std::map<t, CFGNode<t> *> interesting;
	/* Start on the assumption that everything is uninteresting. */
	enumerateCFG<t>(root, uninteresting);
	/* addresses which are explicitly flagged as interesting are
	   not uninteresting. */
	for (typename std::map<t, CFGNode<t> *>::iterator it = uninteresting.begin();
	     it != uninteresting.end();
		) {
		if (it->second->accepting ||
		    instructionIsInteresting(interestingAddresses, it->first)) {
			interesting[it->first] = it->second;
			uninteresting.erase(it++);
		} else {
			it++;
		}
	}

	/* Tarski iteration */
	bool progress;
	do {
		progress = false;
		for (typename std::map<t, CFGNode<t> *>::iterator it = uninteresting.begin();
		     it != uninteresting.end();
			) {
			CFGNode<t> *n = it->second;
			bool shouldBeUninteresting = true;
			if (n->branch &&
			    !uninteresting.count(n->branch->my_rip))
				shouldBeUninteresting = false;
			if (n->fallThrough &&
			    !uninteresting.count(n->fallThrough->my_rip))
				shouldBeUninteresting = false;
			if (shouldBeUninteresting) {
				it++;
			} else {
				progress = true;
				interesting[it->first] = it->second;
				uninteresting.erase(it++);
			}
		}
	} while (progress);

	/* The uninteresting set should now be correct.  Eliminate any
	   edges which go to an uninteresting target. */
	for (typename std::map<t, CFGNode<t> *>::iterator it = interesting.begin();
	     it != interesting.end();
	     it++) {
		CFGNode<t> *n = it->second;
		assert(n);
		if (n->branch && uninteresting.count(n->branch->my_rip))
			n->branch = NULL;
		if (n->fallThrough && uninteresting.count(n->fallThrough->my_rip))
			n->fallThrough = NULL;
	}

	/* All done. */
}

/* Break cycles using a simple depth-first iteration.  @cfg is the
   current node in the iteration and @onPath is the set of nodes on
   the path from the root to the current node.  We will always try to
   break the cycle on a back edge, defined to be one where the value
   in @numbering decreases.  *@lastBackEdge should be the last back
   pointer which we followed on this path, and it is where we will
   break the cycle.  Returns false if we broke a cycle, in which case
   the whole thing needs to be re-run, or true otherwise. */
template <typename t> bool
breakCycles(CFGNode<t> *cfg, std::map<CFGNode<t> *, unsigned> &numbering,
	    CFGNode<t> **lastBackEdge, std::set<CFGNode<t> *> &onPath,
	    std::set<CFGNode<t> *> &clean)
{
	if (clean.count(cfg))
		return true;

	if (onPath.count(cfg)) {
		/* We have a cycle.  Break it. */
		assert(lastBackEdge);
		*lastBackEdge = NULL;
		return false;
	}

	onPath.insert(cfg);
	if (cfg->branch) {
		CFGNode<t> **p = lastBackEdge;
		if (numbering[cfg->branch] < numbering[cfg])
			p = &cfg->branch;
		if (!breakCycles(cfg->branch, numbering, p, onPath, clean))
			return false;
	}
	if (cfg->fallThrough) {
		CFGNode<t> **p = lastBackEdge;
		if (numbering[cfg->fallThrough] < numbering[cfg])
			p = &cfg->fallThrough;
		if (!breakCycles(cfg->fallThrough, numbering, p, onPath, clean))
			return false;
	}

	onPath.erase(cfg);

        clean.insert(cfg);
	return true;
}

/* We use a breadth first search to number the nodes and then use a
   variant of Tarjan's algorithm to detect cycles.  When we detect a
   cycle, we use the numbering scheme to identify a back edge and
   eliminate it. */
template <typename t> void
breakCycles(CFGNode<t> *cfg)
{
	std::map<CFGNode<t> *, unsigned> numbering;
	std::queue<CFGNode<t> *> queue;
	CFGNode<t> *tmp;

	/* Assign numbering */
	unsigned idx;
	idx = 0;
	queue.push(cfg);
	while (!queue.empty()) {
		tmp = queue.front();
		queue.pop();
		if (numbering.count(tmp))
			continue;
		numbering[tmp] = idx;
		idx++;
		if (tmp->branch)
			queue.push(tmp->branch);
		if (tmp->fallThrough)
			queue.push(tmp->fallThrough);
	}

	std::set<CFGNode<t> *> visited;
	std::set<CFGNode<t> *> clean;
	while (!breakCycles<t>(cfg, numbering, NULL, visited, clean)) {
		visited.clear();
		clean.clear();
	}
}

/* Returns true if the operation definitely commutes, or false if
 * we're not sure. */
static bool
operationCommutes(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) ||
		(op >= Iop_CmpEQ8 && op <= Iop_CmpEQ64) ||
		(op == Iop_And1) ||
		(op == Iop_Or1);
}

/* Returns true if the operation definitely associates in the sense
 * that (a op b) op c == a op (b op c), or false if we're not sure. */
static bool
operationAssociates(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) || (op == Iop_And1) ||
		(op >= Iop_And8 && op <= Iop_And64) || (op >= Iop_Xor8 && op <= Iop_Xor64);
}

static bool
physicallyEqual(const IRConst *a, const IRConst *b)
{
	if (a->tag != b->tag)
		return false;
	switch (a->tag) {
#define do_case(t)					\
		case Ico_ ## t:				\
			return a->Ico. t == b->Ico. t
		do_case(U1);
		do_case(U8);
		do_case(U16);
		do_case(U32);
		do_case(U64);
		do_case(F64);
		do_case(F64i);
		do_case(V128);
	}
	abort();
}

static bool
physicallyEqual(const IRRegArray *a, const IRRegArray *b)
{
	return a->base == b->base && a->elemTy == b->elemTy && a->nElems == b->nElems;
}

static bool
physicallyEqual(const IRCallee *a, const IRCallee *b)
{
	return a->addr == b->addr;
}

static bool
physicallyEqual(const IRExpr *a, const IRExpr *b)
{
	if (a == b)
		return true;
	if (a->tag != b->tag)
		return false;
	switch (a->tag) {
	case Iex_Binder:
		return a->Iex.Binder.binder == b->Iex.Binder.binder;
	case Iex_Get:
		return a->Iex.Get.offset == b->Iex.Get.offset &&
			a->Iex.Get.ty == b->Iex.Get.ty;
	case Iex_GetI:
		return a->Iex.GetI.bias == b->Iex.GetI.bias &&
			physicallyEqual(a->Iex.GetI.descr,
					b->Iex.GetI.descr) &&
			physicallyEqual(a->Iex.GetI.ix,
					b->Iex.GetI.ix);
	case Iex_RdTmp:
		return a->Iex.RdTmp.tmp == b->Iex.RdTmp.tmp;

	case Iex_Qop:
		if (!physicallyEqual(a->Iex.Qop.arg4,
				     b->Iex.Qop.arg4))
			return false;
	case Iex_Triop:
		if (!physicallyEqual(a->Iex.Qop.arg3,
				     b->Iex.Qop.arg3))
			return false;
	case Iex_Binop:
		if (!physicallyEqual(a->Iex.Qop.arg2,
				     b->Iex.Qop.arg2))
			return false;
	case Iex_Unop:
		if (!physicallyEqual(a->Iex.Qop.arg1,
				     b->Iex.Qop.arg1))
			return false;
		return a->Iex.Qop.op == b->Iex.Qop.op;
	case Iex_Load:
		return a->Iex.Load.isLL == b->Iex.Load.isLL &&
			a->Iex.Load.end == b->Iex.Load.end &&
			a->Iex.Load.ty == b->Iex.Load.ty &&
			physicallyEqual(a->Iex.Load.addr, b->Iex.Load.addr);
	case Iex_Const:
		return physicallyEqual(a->Iex.Const.con, b->Iex.Const.con);
	case Iex_CCall: {
		if (a->Iex.CCall.retty != b->Iex.CCall.retty ||
		    !physicallyEqual(a->Iex.CCall.cee, b->Iex.CCall.cee))
			return false;
		int x;
		for (x = 0; a->Iex.CCall.args[x]; x++) {
			if (!b->Iex.CCall.args[x])
				return false;
			if (!physicallyEqual(a->Iex.CCall.args[x],
					     b->Iex.CCall.args[x]))
				return false;
		}
		if (b->Iex.CCall.args[x])
			return false;
		return true;
	}
	case Iex_Mux0X:
		return physicallyEqual(a->Iex.Mux0X.cond,
				       b->Iex.Mux0X.cond) &&
			physicallyEqual(a->Iex.Mux0X.expr0,
					b->Iex.Mux0X.expr0) &&
			physicallyEqual(a->Iex.Mux0X.exprX,
					b->Iex.Mux0X.exprX);
	case Iex_Associative:
		if (a->Iex.Associative.op != b->Iex.Associative.op ||
		    a->Iex.Associative.nr_arguments != b->Iex.Associative.nr_arguments)
			return false;
		for (int x = 0; x < a->Iex.Associative.nr_arguments; x++)
			if (!physicallyEqual(a->Iex.Associative.contents[x],
					     b->Iex.Associative.contents[x]))
				return false;
		return true;
	}
	abort();
}

static IRExpr *
optimise_condition_calculation(
	IRExpr *cond,
	IRExpr *cc_op,
	IRExpr *dep1,
	IRExpr *dep2,
	IRExpr *ndep,
	const AllowableOptimisations &opt)
{
	/* We only handle a few very special cases here. */
	if (cond->tag != Iex_Const || cc_op->tag != Iex_Const)
		return NULL;
	if (cond->Iex.Const.con->Ico.U64 != AMD64CondZ)
		return NULL;
	switch (cc_op->Iex.Const.con->Ico.U64) {
	case AMD64G_CC_OP_SUBL:
		return IRExpr_Binop(
			Iop_CmpEQ32,
			dep1,
			dep2);
	case AMD64G_CC_OP_SUBQ:
		return IRExpr_Binop(
			Iop_CmpEQ64,
			dep1,
			dep2);
	case AMD64G_CC_OP_LOGICL:
		return IRExpr_Binop(
			Iop_CmpEQ64,
			dep1,
			IRExpr_Const(IRConst_U64(0)));
	default:
		return NULL;
	}
}

/* Wherever we have a choice as to the ordering of an expression's
   sub-expressions, we sort them into ascending order of complexity,
   where complexity is defined by this function.  The main requirement
   is that if both x and -x occur in the argument list, x will occur
   before -x. */
/* If two expressions have the same complexity, we use a lexicographic
   ordering to distinguish them. */
static int
exprComplexity(const IRExpr *e)
{
	switch (e->tag) {
	case Iex_Binder:
		return 10;
	case Iex_Get:
		return 20;
	case Iex_GetI:
		return 20 + exprComplexity(e->Iex.GetI.ix);
	case Iex_RdTmp:
		return 30;
	case Iex_Qop:
		return 10 +
			exprComplexity(e->Iex.Qop.arg1) +
			exprComplexity(e->Iex.Qop.arg2) +
			exprComplexity(e->Iex.Qop.arg3) +
			exprComplexity(e->Iex.Qop.arg4);
	case Iex_Triop:
		return 10 +
			exprComplexity(e->Iex.Qop.arg1) +
			exprComplexity(e->Iex.Qop.arg2) +
			exprComplexity(e->Iex.Qop.arg3);
	case Iex_Binop:
		return 10 +
			exprComplexity(e->Iex.Qop.arg1) +
			exprComplexity(e->Iex.Qop.arg2);
	case Iex_Unop:
		return 10 + exprComplexity(e->Iex.Qop.arg1);
	case Iex_Load:
		return 10 + exprComplexity(e->Iex.Load.addr);
	case Iex_Const:
		return 0;
	case Iex_Mux0X:
		return 10 + exprComplexity(e->Iex.Mux0X.cond) +
			exprComplexity(e->Iex.Mux0X.expr0) +
			exprComplexity(e->Iex.Mux0X.exprX);
	case Iex_CCall: {
		int acc = 50;
		for (int x = 0; e->Iex.CCall.args[x]; x++)
			acc += exprComplexity(e->Iex.CCall.args[x]);
		return acc;
	}
	case Iex_Associative: {
		int acc = 10;
		for (int x = 0; x < e->Iex.Associative.nr_arguments; x++)
			acc += exprComplexity(e->Iex.Associative.contents[x]);
		return acc;
	}
	}
	abort();
}

static bool
IexTagLessThan(IRExprTag a, IRExprTag b)
{
	if (a == b)
		return false;
	if (a == Iex_Const)
		return true;
	if (b == Iex_Const)
		return false;
	if (a == Iex_Get)
		return true;
	if (b == Iex_Get)
		return false;
	if (a == Iex_GetI)
		return true;
	if (b == Iex_GetI)
		return false;
	if (a == Iex_RdTmp)
		return true;
	if (b == Iex_RdTmp)
		return false;
	if (b == Iex_Qop || b == Iex_Triop || b == Iex_Binop || b == Iex_Unop || b == Iex_Associative)
		return false;
	if (a == Iex_Qop || a == Iex_Triop || a == Iex_Binop || a == Iex_Unop || a == Iex_Associative)
		return true;
	if (a == Iex_Mux0X)
		return true;
	if (b == Iex_Mux0X)
		return false;
	if (a == Iex_Load)
		return true;
	if (b == Iex_Load)
		return false;
	if (a == Iex_CCall)
		return true;
	if (b == Iex_CCall)
		return false;
	abort();
}

static bool
sortIRConsts(IRConst *a, IRConst *b)
{
	if (a->tag < b->tag)
		return true;
	if (a->tag > b->tag)
		return false;
	switch (a->tag) {
#define do_type(t)					\
		case Ico_ ## t :			\
			return a->Ico. t < b->Ico. t
		do_type(U1);
		do_type(U8);
		do_type(U16);
		do_type(U32);
		do_type(U64);
		do_type(F64);
		do_type(F64i);
		do_type(V128);
#undef do_type
	}
	abort();
}

static bool
sortIRExprs(IRExpr *a, IRExpr *b)
{
	int ac = exprComplexity(a);
	int bc = exprComplexity(b);
	if (ac < bc)
		return true;
	if (ac > bc)
		return false;
	if (IexTagLessThan(a->tag, b->tag)) {
		return true;
	} else if (a->tag != b->tag) {
		return false;
	}

	switch (a->tag) {
	case Iex_Binder:
		return a->Iex.Binder.binder < b->Iex.Binder.binder;
	case Iex_Get:
		return a->Iex.Get.offset < b->Iex.Get.offset;
	case Iex_GetI:
		return sortIRExprs(a->Iex.GetI.ix, b->Iex.GetI.ix);
	case Iex_RdTmp:
		return a->Iex.RdTmp.tmp < b->Iex.RdTmp.tmp;
	case Iex_Qop:
		if (a->Iex.Qop.op < b->Iex.Qop.op)
			return true;
		if (a->Iex.Qop.op > b->Iex.Qop.op)
			return false;
		if (physicallyEqual(a->Iex.Qop.arg1, b->Iex.Qop.arg1)) {
			if (physicallyEqual(a->Iex.Qop.arg2,
					    b->Iex.Qop.arg2)) {
				if (physicallyEqual(a->Iex.Qop.arg3,
						    b->Iex.Qop.arg3))
					return sortIRExprs(a->Iex.Qop.arg4,
							   b->Iex.Qop.arg4);
				else
					return sortIRExprs(a->Iex.Qop.arg3,
							   b->Iex.Qop.arg3);
			} else
				return sortIRExprs(a->Iex.Qop.arg2,
						   b->Iex.Qop.arg2);
		} else {
			return sortIRExprs(a->Iex.Qop.arg1,
					   b->Iex.Qop.arg1);
		}
	case Iex_Triop:
		if (a->Iex.Qop.op < b->Iex.Qop.op)
			return true;
		if (a->Iex.Qop.op > b->Iex.Qop.op)
			return false;
		if (physicallyEqual(a->Iex.Qop.arg1, b->Iex.Qop.arg1)) {
			if (physicallyEqual(a->Iex.Qop.arg2,
					    b->Iex.Qop.arg2)) {
				return sortIRExprs(a->Iex.Qop.arg3,
						   b->Iex.Qop.arg3);
			} else
				return sortIRExprs(a->Iex.Qop.arg2,
						   b->Iex.Qop.arg2);
		} else {
			return sortIRExprs(a->Iex.Qop.arg1,
					   b->Iex.Qop.arg1);
		}
	case Iex_Binop:
		if (a->Iex.Qop.op < b->Iex.Qop.op)
			return true;
		if (a->Iex.Qop.op > b->Iex.Qop.op)
			return false;
		if (physicallyEqual(a->Iex.Qop.arg1, b->Iex.Qop.arg1)) {
			return sortIRExprs(a->Iex.Qop.arg2,
					   b->Iex.Qop.arg2);
		} else {
			return sortIRExprs(a->Iex.Qop.arg1,
					   b->Iex.Qop.arg1);
		}
	case Iex_Unop:
		if (a->Iex.Qop.op < b->Iex.Qop.op)
			return true;
		if (a->Iex.Qop.op > b->Iex.Qop.op)
			return false;
		return sortIRExprs(a->Iex.Qop.arg1,
				   b->Iex.Qop.arg1);
	case Iex_Load:
		return sortIRExprs(a->Iex.Load.addr, b->Iex.Load.addr);
	case Iex_Const:
		return sortIRConsts(a->Iex.Const.con, b->Iex.Const.con);
	case Iex_CCall: {
		int r = strcmp(a->Iex.CCall.cee->name,
			       b->Iex.CCall.cee->name);
		if (r < 0)
			return true;
		else if (r > 0)
			return false;
		for (int x = 0; 1; x++) {
			if (!a->Iex.CCall.args[x] &&
			    !b->Iex.CCall.args[x])
				return false;
			if (!a->Iex.CCall.args[x])
				return false;
			if (!b->Iex.CCall.args[x])
				return false;
			if (!physicallyEqual(a->Iex.CCall.args[x],
					     b->Iex.CCall.args[x]))
				return sortIRExprs(a->Iex.CCall.args[x],
						   b->Iex.CCall.args[x]);
		}
	}
	case Iex_Mux0X:
		if (!physicallyEqual(a->Iex.Mux0X.cond,
				     b->Iex.Mux0X.cond))
			return sortIRExprs(a->Iex.Mux0X.cond,
					   b->Iex.Mux0X.cond);
		if (!physicallyEqual(a->Iex.Mux0X.expr0,
				     b->Iex.Mux0X.expr0))
			return sortIRExprs(a->Iex.Mux0X.expr0,
					   b->Iex.Mux0X.expr0);
		return sortIRExprs(a->Iex.Mux0X.exprX,
				   b->Iex.Mux0X.exprX);
	case Iex_Associative: {
		if (a->Iex.Associative.op < b->Iex.Associative.op)
			return true;
		if (a->Iex.Associative.op > b->Iex.Associative.op)
			return false;
		int x;
		x = 0;
		while (1) {
			if (x == a->Iex.Associative.nr_arguments &&
			    x == b->Iex.Associative.nr_arguments)
				return false;
			if (x == a->Iex.Associative.nr_arguments)
				return true;
			if (x == b->Iex.Associative.nr_arguments)
				return false;
			if (!physicallyEqual( a->Iex.Associative.contents[x],
					      b->Iex.Associative.contents[x] ))
				return sortIRExprs( a->Iex.Associative.contents[x],
						    b->Iex.Associative.contents[x] );
			x++;
		}
	}
	}

	abort();
}

static void
addArgumentToAssoc(IRExpr *e, IRExpr *arg)
{
	if (e->Iex.Associative.nr_arguments == e->Iex.Associative.nr_arguments_allocated) {
		e->Iex.Associative.nr_arguments_allocated += 8;
		e->Iex.Associative.contents = (IRExpr **)
			LibVEX_realloc(&ir_heap,
				       e->Iex.Associative.contents,
				       sizeof(IRExpr *) * e->Iex.Associative.nr_arguments_allocated);
	}
	e->Iex.Associative.contents[e->Iex.Associative.nr_arguments] = arg;
	e->Iex.Associative.nr_arguments++;
}

static void
purgeAssocArgument(IRExpr *e, int idx)
{
	assert(e->tag == Iex_Associative);
	assert(idx < e->Iex.Associative.nr_arguments);
	memmove(e->Iex.Associative.contents + idx,
		e->Iex.Associative.contents + idx + 1,
		sizeof(IRExpr *) * (e->Iex.Associative.nr_arguments - idx - 1));
	e->Iex.Associative.nr_arguments--;
}

static IRExpr *
optimiseIRExprUnderAssumption(IRExpr *src, const AllowableOptimisations &opt,
			      bool *done_something, IRExpr *assumption)
{
	switch (src->tag) {
	case Iex_Qop: {
		bool p1, p2, p3, p4;
		p1 = p2 = p3 = p4 = false;
		IRExpr *arg1, *arg2, *arg3, *arg4;
#define do_arg(x)							\
		arg ## x = optimiseIRExprUnderAssumption(		\
			src->Iex.Qop.arg ## x, opt, &p ## x,		\
			assumption)
		do_arg(1);
		do_arg(2);
		do_arg(3);
		do_arg(4);
#undef do_arg
		if (p1 || p2 || p3 || p4) {
			*done_something = true;
			src = IRExpr_Qop(src->Iex.Qop.op,
					 arg1, arg2, arg3, arg4);
		}
		break;
	}

	case Iex_Triop: {
		bool p1, p2, p3;
		p1 = p2 = p3 = false;
		IRExpr *arg1, *arg2, *arg3;
#define do_arg(x)							\
		arg ## x = optimiseIRExprUnderAssumption(		\
			src->Iex.Triop.arg ## x, opt, &p ## x,		\
			assumption)
		do_arg(1);
		do_arg(2);
		do_arg(3);
#undef do_arg
		if (p1 || p2 || p3) {
			*done_something = true;
			src = IRExpr_Triop(src->Iex.Triop.op,
					   arg1, arg2, arg3);
		}
		break;
	}

	case Iex_Binop: {
		bool p1, p2;
		p1 = p2 = false;
		IRExpr *arg1, *arg2;
#define do_arg(x)							\
		arg ## x = optimiseIRExprUnderAssumption(		\
			src->Iex.Binop.arg ## x, opt, &p ## x,		\
			assumption)
		do_arg(1);
		do_arg(2);
#undef do_arg
		if (p1 || p2) {
			*done_something = true;
			src = IRExpr_Binop(src->Iex.Binop.op,
					   arg1, arg2);
		}
		break;
	}

	case Iex_Unop: {
		bool p;
		p = false;
		IRExpr *arg = optimiseIRExprUnderAssumption(
			src->Iex.Unop.arg, opt, &p, assumption);
		if (p) {
			*done_something = true;
			src = IRExpr_Unop(src->Iex.Unop.op, arg);
		}
		break;
	}

	case Iex_Load: {
		bool p;
		p = false;
		IRExpr *addr = optimiseIRExprUnderAssumption(
			src->Iex.Load.addr, opt, &p, assumption);
		if (p) {
			*done_something = true;
			src = IRExpr_Load(
				src->Iex.Load.isLL,
				src->Iex.Load.end,
				src->Iex.Load.ty,
				addr);
		}
		break;
	}

	case Iex_CCall: {
		int x;
		bool progress = false;
		IRExpr *arg = NULL;
		for (x = 0; src->Iex.CCall.args[x]; x++) {
			arg = optimiseIRExprUnderAssumption(
				src->Iex.CCall.args[x],
				opt,
				&progress,
				assumption);
			if (progress)
				break;
		}
		if (progress) {
			*done_something = true;
			src = deepCopyIRExpr(src);
			assert(src->Iex.CCall.args[x]);
			assert(arg);
			src->Iex.CCall.args[x] = arg;
			while (src->Iex.CCall.args[x]) {
				src->Iex.CCall.args[x] =
					optimiseIRExprUnderAssumption(
						src->Iex.CCall.args[x],
						opt,
						&progress,
						assumption);
				x++;
			}
		}
		break;
	}

	case Iex_Mux0X: {
		bool pcond, pexpr0, pexprX;
		pcond = pexpr0 = pexprX = false;
		IRExpr *cond, *expr0, *exprX;
#define do_arg(arg)							\
		arg = optimiseIRExprUnderAssumption(		\
			src->Iex.Mux0X.arg, opt, &p ## arg,	\
			assumption)
		do_arg(cond);
		do_arg(expr0);
		do_arg(exprX);
#undef do_arg
		if (pcond || pexpr0 || pexprX) {
			*done_something = true;
			src = IRExpr_Mux0X(cond, expr0, exprX);
		}
		break;
	}

	case Iex_Associative: {
		int x;
		bool progress = false;
		IRExpr *arg = NULL;
		for (x = 0; x < src->Iex.Associative.nr_arguments; x++) {
			arg = optimiseIRExprUnderAssumption(
				src->Iex.Associative.contents[x],
				opt,
				&progress,
				assumption);
			if (progress)
				break;
		}
		if (progress) {
			*done_something = true;
			src = deepCopyIRExpr(src);
			src->Iex.Associative.contents[x] = arg;
			while (x < src->Iex.Associative.nr_arguments) {
				src->Iex.Associative.contents[x] =
					optimiseIRExprUnderAssumption(
						src->Iex.Associative.contents[x],
						opt,
						&progress,
						assumption);
				x++;
			}
		}
		break;
	}

	default:
		break;
	}
	if (definitelyEqual(src, assumption, opt)) {
		*done_something = true;
		return IRExpr_Const(IRConst_U1(1));
	} else {
		return src;
	}
}

static IRExpr *
optimiseIRExpr(IRExpr *src, const AllowableOptimisations &opt, bool *done_something)
{
	/* First, recursively optimise our arguments. */
	switch (src->tag) {
	case Iex_Qop:
		src->Iex.Qop.arg4 = optimiseIRExpr(src->Iex.Qop.arg4, opt, done_something);
	case Iex_Triop:
		src->Iex.Triop.arg3 = optimiseIRExpr(src->Iex.Triop.arg3, opt, done_something);
	case Iex_Binop:
		src->Iex.Binop.arg2 = optimiseIRExpr(src->Iex.Binop.arg2, opt, done_something);
	case Iex_Unop:
		src->Iex.Unop.arg = optimiseIRExpr(src->Iex.Unop.arg, opt, done_something);
		break;
	case Iex_Load:
		src->Iex.Load.addr = optimiseIRExpr(src->Iex.Load.addr, opt, done_something);
		if (src->Iex.Load.addr->tag == Iex_Const &&
		    (long)src->Iex.Load.addr->Iex.Const.con->Ico.U64 < 4096)
			dbg_break("optimising load to load of strange constant address (IRExpr *)%p\n",
				  src);
		break;
	case Iex_CCall: {
		for (int x = 0; src->Iex.CCall.args[x]; x++) {
			src->Iex.CCall.args[x] =
				optimiseIRExpr(src->Iex.CCall.args[x], opt, done_something);
		}
		/* Special cases for amd64g_calculate_condition. */
		if (!strcmp(src->Iex.CCall.cee->name,
			    "amd64g_calculate_condition")) {
			IRExpr *e;
			e = optimise_condition_calculation(
				src->Iex.CCall.args[0],
				src->Iex.CCall.args[1],
				src->Iex.CCall.args[2],
				src->Iex.CCall.args[3],
				src->Iex.CCall.args[4],
				opt);
			if (e) {
				*done_something = true;
				src = e;
			}
		}
		break;
	}
	case Iex_Mux0X:
		src->Iex.Mux0X.cond = optimiseIRExpr(src->Iex.Mux0X.cond, opt, done_something);
		src->Iex.Mux0X.expr0 = optimiseIRExpr(src->Iex.Mux0X.expr0, opt, done_something);
		src->Iex.Mux0X.exprX = optimiseIRExpr(src->Iex.Mux0X.exprX, opt, done_something);
		break;
	case Iex_Associative:
		for (int x = 0; x < src->Iex.Associative.nr_arguments; x++)
			src->Iex.Associative.contents[x] =
				optimiseIRExpr(src->Iex.Associative.contents[x], opt, done_something);
		break;
	default:
		break;
	}

	if (src->tag == Iex_Associative) {
		/* Drag up nested associatives. */
		bool haveNestedAssocs = false;
		for (int x = 0; !haveNestedAssocs && x < src->Iex.Associative.nr_arguments; x++)
			if (src->Iex.Associative.contents[x]->tag == Iex_Associative &&
			    src->Iex.Associative.contents[x]->Iex.Associative.op ==
				src->Iex.Associative.op)
				haveNestedAssocs = true;
		if (haveNestedAssocs) {
			IRExpr *e = IRExpr_Associative(src->Iex.Associative.op, NULL);
			for (int x = 0; x < src->Iex.Associative.nr_arguments; x++) {
				IRExpr *arg = src->Iex.Associative.contents[x];
				if (arg->tag == Iex_Associative &&
				    arg->Iex.Associative.op == arg->Iex.Associative.op) {
					for (int y = 0; y < arg->Iex.Associative.nr_arguments; y++)
						addArgumentToAssoc(e, arg->Iex.Associative.contents[y]);
				} else {
					addArgumentToAssoc(e, arg);
				}
			}
			src = e;
			*done_something = true;
		}

		/* Sort IRExprs so that ``related'' expressions are likely to
		 * be close together. */
		if (operationCommutes(src->Iex.Associative.op))
			std::sort(src->Iex.Associative.contents,
				  src->Iex.Associative.contents + src->Iex.Associative.nr_arguments,
				  sortIRExprs);
		/* Fold together constants.  For commutative
		   operations they'll all be at the beginning, but
		   don't assume that associativity implies
		   commutativity. */
		for (int x = 0; x + 1 < src->Iex.Associative.nr_arguments; x++) {
			IRExpr *a, *b;
			a = src->Iex.Associative.contents[x];
			b = src->Iex.Associative.contents[x+1];
			if (a->tag == Iex_Const && b->tag == Iex_Const) {
				IRExpr *res;
				IRConst *l, *r;
				l = a->Iex.Const.con;
				r = b->Iex.Const.con;
				switch (src->Iex.Associative.op) {
				case Iop_Add8:
					res = IRExpr_Const(
						IRConst_U8((l->Ico.U8 + r->Ico.U8) & 0xff));
					break;
				case Iop_Add16:
					res = IRExpr_Const(
						IRConst_U16((l->Ico.U16 + r->Ico.U16) & 0xffff));
					break;
				case Iop_Add32:
					res = IRExpr_Const(
						IRConst_U32((l->Ico.U32 + r->Ico.U32) & 0xffffffff));
					break;
				case Iop_Add64:
					res = IRExpr_Const(IRConst_U64(l->Ico.U64 + r->Ico.U64));
					break;
				case Iop_And1:
					res = IRExpr_Const(IRConst_U1(l->Ico.U1 & r->Ico.U1));
					break;
				case Iop_And32:
					res = IRExpr_Const(IRConst_U32(l->Ico.U32 & r->Ico.U32));
					break;
				case Iop_And64:
					res = IRExpr_Const(IRConst_U64(l->Ico.U64 & r->Ico.U64));
					break;
				case Iop_Xor32:
					res = IRExpr_Const(IRConst_U32(l->Ico.U32 ^ r->Ico.U32));
					break;
				default:
					printf("Warning: can't constant-fold in ");
					ppIRExpr(src, stdout);
					printf("\n");
					res = NULL;
					break;
				}
				if (res) {
					memmove(src->Iex.Associative.contents + x + 1,
						src->Iex.Associative.contents + x + 2,
						sizeof(IRExpr *) * (src->Iex.Associative.nr_arguments - x - 2));
					src->Iex.Associative.nr_arguments--;
					src->Iex.Associative.contents[x] = res;
					x--;
					*done_something = true;
				}
			}
		}
		/* Some special cases for And1: 1 & x -> x, 0 & x -> 0 */
		if (src->Iex.Associative.op == Iop_And1) {
			/* If there are any constants, they'll be at the start. */
			while (src->Iex.Associative.nr_arguments > 1 &&
			       src->Iex.Associative.contents[0]->tag == Iex_Const) {
				IRConst *c = src->Iex.Associative.contents[0]->Iex.Const.con;
				*done_something = true;
				if (c->Ico.U1) {
					purgeAssocArgument(src, 0);
				} else {
					return src->Iex.Associative.contents[0];
				}
			}
		}
		/* Likewise for Or1 */
		if (src->Iex.Associative.op == Iop_Or1) {
			while (src->Iex.Associative.nr_arguments > 1 &&
			       src->Iex.Associative.contents[0]->tag == Iex_Const) {
				IRConst *c = src->Iex.Associative.contents[0]->Iex.Const.con;
				*done_something = true;
				if (!c->Ico.U1) {
					purgeAssocArgument(src, 0);
				} else {
					return src->Iex.Associative.contents[0];
				}
			}
		}

		/* x & x -> x, for any and-like operator */
		if (src->Iex.Associative.op >= Iop_And8 && src->Iex.Associative.op <= Iop_And64) {
			for (int it1 = 0;
			     it1 < src->Iex.Associative.nr_arguments;
			     it1++) {
				for (int it2 = it1 + 1;
				     it2 < src->Iex.Associative.nr_arguments;
					) {
					if (definitelyEqual(src->Iex.Associative.contents[it1],
							    src->Iex.Associative.contents[it2],
							    opt)) {
						*done_something = true;
						purgeAssocArgument(src, it2);
					} else {
						it2++;
					}
				}
			}
		}

		/* When evaluating the y in x & y, you can safely
		   assume that x holds.  Take advantage of this. */
		if (src->Iex.Associative.op == Iop_And1) {
			for (int it1 = 0;
			     it1 < src->Iex.Associative.nr_arguments;
			     it1++) {
				for (int it2 = it1 + 1;
				     it2 < src->Iex.Associative.nr_arguments;
				     it2++)
					src->Iex.Associative.contents[it2] =
						optimiseIRExprUnderAssumption(
						src->Iex.Associative.contents[it2],
						opt,
						done_something,
						src->Iex.Associative.contents[it1]);
			}
		}

		/* x + -x -> 0, for any plus-like operator, so remove
		 * both x and -x from the list. */
		/* Also do x & ~x -> 0, x ^ x -> 0, while we're here. */
		if (opt.xPlusMinusX) {
			bool plus_like;
			bool and_like;
			bool xor_like;
			plus_like = src->Iex.Associative.op >= Iop_Add8 && src->Iex.Associative.op <= Iop_Add64;
			and_like = (src->Iex.Associative.op >= Iop_And8 && src->Iex.Associative.op <= Iop_And64) ||
				src->Iex.Associative.op == Iop_And1;
			xor_like = src->Iex.Associative.op >= Iop_Xor8 && src->Iex.Associative.op <= Iop_Xor64;
			if (plus_like || and_like || xor_like) {
				for (int it1 = 0;
				     it1 < src->Iex.Associative.nr_arguments;
					) {
					IRExpr *l = src->Iex.Associative.contents[it1];
					int it2;
					for (it2 = 0;
					     it2 < src->Iex.Associative.nr_arguments;
					     it2++) {
						if (it2 == it1)
							continue;
						IRExpr *r = src->Iex.Associative.contents[it2];
						bool purge;
						if (plus_like) {
							if (r->tag == Iex_Unop) {
								purge = r->Iex.Unop.op >= Iop_Neg8 &&
									r->Iex.Unop.op <= Iop_Neg64;
							} else {
								purge = false;
							}
							if (purge)
								purge = definitelyEqual(l, r->Iex.Unop.arg,
											opt.disablexPlusMinusX());
						} else if (and_like) {
							if (r->tag == Iex_Unop)
								purge = (r->Iex.Unop.op >= Iop_Not8 &&
									 r->Iex.Unop.op <= Iop_Not64) ||
									r->Iex.Unop.op == Iop_Not1;
							else
								purge = false;
							if (purge)
								purge = definitelyEqual(l, r->Iex.Unop.arg,
											opt.disablexPlusMinusX());
						} else {
							assert(xor_like);
							purge = definitelyEqual(l, r,
										opt.disablexPlusMinusX());
						}

						if (purge) {
							/* Careful: do the largest index first so that the
							   other index remains valid. */
							*done_something = true;
							if (it1 < it2) {
								purgeAssocArgument(src, it2);
								src->Iex.Associative.contents[it1] =
									IRExpr_Const(IRConst_U64(0));
							} else {
								purgeAssocArgument(src, it1);
								src->Iex.Associative.contents[it2] =
									IRExpr_Const(IRConst_U64(0));
							}
							break;
						}
					}
					if (it2 == src->Iex.Associative.nr_arguments)
						it1++;
				}
			}
			if (src->Iex.Associative.nr_arguments == 0) {
				*done_something = true;
				switch (src->Iex.Associative.op) {
				case Iop_Add8:
				case Iop_Xor8:
					return IRExpr_Const(IRConst_U8(0));
				case Iop_Add16:
				case Iop_Xor16:
					return IRExpr_Const(IRConst_U16(0));
				case Iop_Add32:
				case Iop_Xor32:
					return IRExpr_Const(IRConst_U32(0));
				case Iop_Add64:
				case Iop_Xor64:
					return IRExpr_Const(IRConst_U64(0));

				case Iop_And1:
					return IRExpr_Const(IRConst_U1(1));
				case Iop_And8:
					return IRExpr_Const(IRConst_U8(0xff));
				case Iop_And16:
					return IRExpr_Const(IRConst_U16(0xffff));
				case Iop_And32:
					return IRExpr_Const(IRConst_U32(0xffffffff));
				case Iop_And64:
					return IRExpr_Const(IRConst_U64(0xfffffffffffffffful));

				default:
					abort();
				}
			}
		}

		/* If the size is reduced to one, eliminate the assoc list */
		if (src->Iex.Associative.nr_arguments == 1) {
			*done_something = true;
			return src->Iex.Associative.contents[0];
		}
	}

	/* Now use some special rules to simplify a few classes of binops and unops. */
	if (src->tag == Iex_Unop) {
		if (src->Iex.Unop.op == Iop_64to1 &&
		    src->Iex.Unop.arg->tag == Iex_Binop &&
		    (src->Iex.Unop.arg->Iex.Binop.op == Iop_CmpEQ64 ||
		     src->Iex.Unop.arg->Iex.Binop.op == Iop_CmpEQ32)) {
			/* This can happen sometimes because of the
			   way we simplify condition codes.  Very easy
			   fix: strip off the outer 64to1. */
			*done_something = true;
			return src->Iex.Unop.arg;
		}

		if (src->Iex.Unop.op >= Iop_8Uto16 &&
		    src->Iex.Unop.op <= Iop_32Uto64) {
			/* Get rid of signed upcasts; they tend to
			   show up where you don't want them, and they
			   don't actually do anything useful. */
			*done_something = true;
			return src->Iex.Unop.arg;
		}

		if (src->Iex.Unop.op == Iop_Not1 &&
		    src->Iex.Unop.arg->tag == Iex_Unop &&
		    src->Iex.Unop.arg->Iex.Unop.op == src->Iex.Unop.op) {
			*done_something = true;
			return src->Iex.Unop.arg->Iex.Unop.arg;
		}
		if (src->Iex.Unop.op == Iop_Not1 &&
		    src->Iex.Unop.arg->tag == Iex_Associative &&
		    (src->Iex.Unop.arg->Iex.Associative.op == Iop_And1 ||
		     src->Iex.Unop.arg->Iex.Associative.op == Iop_Or1)) {
			/* Convert ~(x & y) to ~x | ~y */
			IRExpr *a = IRExpr_Associative(src->Iex.Unop.arg);
			for (int i = 0;
			     i < a->Iex.Associative.nr_arguments;
			     i++) {
				a->Iex.Associative.contents[i] =
					optimiseIRExpr(
						IRExpr_Unop(
							Iop_Not1,
							a->Iex.Associative.contents[i]),
						opt,
						done_something);
			}
			if (a->Iex.Associative.op == Iop_And1)
				a->Iex.Associative.op = Iop_Or1;
			else
				a->Iex.Associative.op = Iop_And1;
			*done_something = true;
			return a;
		}
		if (src->Iex.Unop.arg->tag == Iex_Const) {
			IRConst *c = src->Iex.Unop.arg->Iex.Const.con;
			switch (src->Iex.Unop.op) {
			case Iop_Neg8:
				*done_something = true;
				return IRExpr_Const(IRConst_U8(-c->Ico.U8));
			case Iop_Neg16:
				*done_something = true;
				return IRExpr_Const(IRConst_U16(-c->Ico.U16));
			case Iop_Neg32:
				*done_something = true;
				return IRExpr_Const(IRConst_U32(-c->Ico.U32));
			case Iop_Neg64:
				*done_something = true;
				return IRExpr_Const(IRConst_U64(-c->Ico.U64));
			case Iop_Not1:
				*done_something = true;
				return IRExpr_Const(IRConst_U1(c->Ico.U1 ^ 1));
			case Iop_32Uto64:
				*done_something = true;
				return IRExpr_Const(IRConst_U64(c->Ico.U32));
			default:
				break;
			}
		}
	} else if (src->tag == Iex_Binop) {
		IRExpr *l = src->Iex.Binop.arg1;
		IRExpr *r = src->Iex.Binop.arg2;
		if (operationAssociates(src->Iex.Binop.op)) {
			/* Convert to an associative operation. */
			*done_something = true;
			return optimiseIRExpr(
				IRExpr_Associative(
					src->Iex.Binop.op,
					l,
					r,
					NULL),
				opt,
				done_something);
		}
		if (src->Iex.Binop.op >= Iop_Sub8 &&
		    src->Iex.Binop.op <= Iop_Sub64) {
			/* Replace a - b with a + (-b), so as to
			   eliminate binary -. */
			*done_something = true;
			src->Iex.Binop.op = (IROp)(src->Iex.Binop.op - Iop_Sub8 + Iop_Add8);
			src->Iex.Binop.arg2 =
				optimiseIRExpr(
					IRExpr_Unop( (IROp)((src->Iex.Binop.op - Iop_Add8) + Iop_Neg8),
						     r ),
					opt,
					done_something);
		}
		/* If a op b commutes, sort the arguments. */
		if (operationCommutes(src->Iex.Binop.op) &&
		    sortIRExprs(r, l)) {
			src->Iex.Binop.arg1 = r;
			src->Iex.Binop.arg2 = l;
			l = src->Iex.Binop.arg1;
			r = src->Iex.Binop.arg2;
			*done_something = true;
		}

		/* x << 0 -> x */
		if (src->Iex.Binop.op >= Iop_Shl8 && src->Iex.Binop.op <= Iop_Shl64 &&
		    src->Iex.Binop.arg2->tag == Iex_Const &&
		    src->Iex.Binop.arg2->Iex.Const.con->Ico.U8 == 0) {
			*done_something = true;
			return src->Iex.Binop.arg1;
		}

		/* We simplify == expressions with sums on the left
		   and right by trying to move all of the constants to
		   the left and all of the non-constants to the
		   right. */
		if (src->Iex.Binop.op == Iop_CmpEQ64) {
			if (r->tag == Iex_Associative &&
			    r->Iex.Associative.op == Iop_Add64 &&
			    r->Iex.Associative.contents[0]->tag == Iex_Const) {
				assert(r->Iex.Associative.nr_arguments > 1);
				/* a == C + b -> -C + a == b */
				IRExpr *cnst = r->Iex.Associative.contents[0];
				IRExpr *newRight = IRExpr_Associative(r);
				purgeAssocArgument(newRight, 0);
				IRExpr *newLeft = IRExpr_Associative(
					Iop_Add64,
					IRExpr_Unop(
						Iop_Neg64,
						cnst),
					l,
					NULL);
				l = src->Iex.Binop.arg1 = optimiseIRExpr(newLeft, opt, done_something);
				r = src->Iex.Binop.arg2 = optimiseIRExpr(newRight, opt, done_something);
				*done_something = true;
			}
			if (l->tag == Iex_Associative &&
			    l->Iex.Associative.op == Iop_Add64) {
				/* C + a == b -> C == b - a */
				assert(l->Iex.Associative.nr_arguments > 1);
				IRExpr *newR = IRExpr_Associative(Iop_Add64, r, NULL);
				for (int it = 1;
				     it < l->Iex.Associative.nr_arguments;
				     it++)
					addArgumentToAssoc(newR,
							   IRExpr_Unop(
								   Iop_Neg64,
								   l->Iex.Associative.contents[it]));
				IRExpr *cnst = l->Iex.Associative.contents[0];
				if (cnst->tag != Iex_Const) {
					cnst = IRExpr_Const(IRConst_U64(0));
					addArgumentToAssoc(newR,
							   IRExpr_Unop(
								   Iop_Neg64,
								   cnst));
				}
				l = src->Iex.Binop.arg1 = cnst;
				r = src->Iex.Binop.arg2 = optimiseIRExpr(newR, opt, done_something);
				*done_something = true;
			}
			/* If, in a == b, a and b are physically
			 * identical, the result is a constant 1. */
			if (physicallyEqual(l, r)) {
				*done_something = true;
				return IRExpr_Const(IRConst_U1(1));
			}

			/* Otherwise, a == b -> 0 == b - a, provided that a is not a constant. */
			if (l->tag != Iex_Const) {
				src->Iex.Binop.arg1 = IRExpr_Const(IRConst_U64(0));
				src->Iex.Binop.arg2 =
					IRExpr_Binop(
						Iop_Add64,
						r,
						IRExpr_Unop(
							Iop_Neg64,
							l));
				*done_something = true;
				return optimiseIRExpr(src, opt, done_something);
			}
		}

		/* And another one: -x == c -> x == -c if c is a constant. */
		if (src->Iex.Binop.op == Iop_CmpEQ64 &&
		    src->Iex.Binop.arg1->tag == Iex_Unop &&
		    src->Iex.Binop.arg1->Iex.Unop.op == Iop_Neg64 &&
		    src->Iex.Binop.arg2->tag == Iex_Const) {
			src->Iex.Binop.arg1 = src->Iex.Binop.arg1->Iex.Unop.arg;
			src->Iex.Binop.arg2 = IRExpr_Const(
				IRConst_U64(-src->Iex.Binop.arg2->Iex.Const.con->Ico.U64));
			*done_something = true;
			return optimiseIRExpr(src, opt, done_something);
		}

		/* If enabled, assume that the stack is ``private'',
		   in the sense that it doesn't alias with any global
		   variables, and is therefore never equal to any
		   constants which are present in the machine code. */
		if (opt.assumePrivateStack &&
		    src->Iex.Binop.op == Iop_CmpEQ64 &&
		    src->Iex.Binop.arg2->tag == Iex_Get &&
		    src->Iex.Binop.arg2->Iex.Get.offset == OFFSET_amd64_RSP &&
		    src->Iex.Binop.arg1->tag == Iex_Const) {
			*done_something = true;
			return IRExpr_Const(IRConst_U1(0));
		}

		/* If both arguments are constant, try to constant
		 * fold everything away. */
		if (src->Iex.Binop.arg1->tag == Iex_Const &&
		    src->Iex.Binop.arg2->tag == Iex_Const) {
			switch (src->Iex.Binop.op) {
			case Iop_CmpEQ32:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U1(
						src->Iex.Binop.arg1->Iex.Const.con->Ico.U32 ==
						src->Iex.Binop.arg2->Iex.Const.con->Ico.U32));
			case Iop_CmpEQ64:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U1(
						src->Iex.Binop.arg1->Iex.Const.con->Ico.U64 ==
						src->Iex.Binop.arg2->Iex.Const.con->Ico.U64));
			default:
				break;
			}
		}


	}
				      
	return src;
}

static IRExpr *
optimiseIRExpr(IRExpr *e, const AllowableOptimisations &opt)
{
	bool progress;
	do {
		progress = false;
		e = optimiseIRExpr(e, opt, &progress);
	} while (progress);
	return e;
}

static void
assertUnoptimisable(IRExpr *e, const AllowableOptimisations &opt)
{
	bool progress = false;
	optimiseIRExpr(e, opt, &progress);
	assert(!progress);
}

static bool
definitelyEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt)
{
	IRExpr *r = optimiseIRExpr(IRExpr_Binop(Iop_CmpEQ64, a, b), opt);
	return r->tag == Iex_Const && r->Iex.Const.con->Ico.U1;
}
static bool
definitelyNotEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt)
{
	IRExpr *r = optimiseIRExpr(IRExpr_Binop(Iop_CmpEQ64, a, b), opt);
	return r->tag == Iex_Const && !r->Iex.Const.con->Ico.U1;
}

class StateMachineWalker {
	void doit(StateMachine *s, std::set<StateMachine *> &visited);
	void doit(StateMachineEdge *s, std::set<StateMachine *> &visited);
public:
	virtual void visitEdge(StateMachineEdge *e) {}
	virtual void visitState(StateMachine *s) {}
	virtual void visitSideEffect(StateMachineSideEffect *smse) {}
	void doit(StateMachine *s);
};

void
StateMachineWalker::doit(StateMachine *sm, std::set<StateMachine *> &visited)
{
	if (visited.count(sm))
		return;
	visited.insert(sm);

	visitState(sm);
	if (dynamic_cast<StateMachineCrash *>(sm) ||
	    dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm) ||
	    dynamic_cast<StateMachineUnreached *>(sm))
		return;
	if (StateMachineBifurcate *smb =
	    dynamic_cast<StateMachineBifurcate *>(sm)) {
		doit(smb->trueTarget, visited);
		doit(smb->falseTarget, visited);
	} else if (StateMachineProxy *smp =
		   dynamic_cast<StateMachineProxy *>(sm)) {
		doit(smp->target, visited);
	} else {
		abort();
	}
}
void
StateMachineWalker::doit(StateMachineEdge *se, std::set<StateMachine *> &visited)
{
	visitEdge(se);
	for (std::vector<StateMachineSideEffect *>::iterator it = se->sideEffects.begin();
	     it != se->sideEffects.end();
	     it++)
		visitSideEffect(*it);
	doit(se->target, visited);
}
void
StateMachineWalker::doit(StateMachine *s)
{
	std::set<StateMachine *> visited;
	doit(s, visited);
}

class findAllStoresVisitor : public StateMachineWalker {
public:
	std::set<StateMachineSideEffectStore *> &out;
	findAllStoresVisitor(std::set<StateMachineSideEffectStore *> &o)
		: out(o)
	{}
	void visitSideEffect(StateMachineSideEffect *smse)
	{
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(smse))
			out.insert(smses);
	}
};
static void
findAllStores(StateMachine *sm, std::set<StateMachineSideEffectStore *> &out)
{
	findAllStoresVisitor v(out);
	v.doit(sm);
}

class findAllLoadsVisitor : public StateMachineWalker {
public:
	std::set<StateMachineSideEffectLoad *> &out;
	findAllLoadsVisitor(std::set<StateMachineSideEffectLoad *> &o)
		: out(o)
	{}
	void visitSideEffect(StateMachineSideEffect *smse)
	{
		if (StateMachineSideEffectLoad *smsel =
		    dynamic_cast<StateMachineSideEffectLoad *>(smse))
			out.insert(smsel);
	}
};
static void
findAllLoads(StateMachine *sm, std::set<StateMachineSideEffectLoad *> &out)
{
	findAllLoadsVisitor v(out);
	v.doit(sm);
}

class findAllEdgesVisitor : public StateMachineWalker {
public:
	std::set<StateMachineEdge *> &out;
	findAllEdgesVisitor(std::set<StateMachineEdge *> &o)
		: out(o)
	{}
	void visitEdge(StateMachineEdge *sme)
	{
		out.insert(sme);
	}
};
static void
findAllEdges(StateMachine *sm, std::set<StateMachineEdge *> &out)
{
	findAllEdgesVisitor v(out);
	v.doit(sm);
}

class findAllStatesVisitor : public StateMachineWalker {
public:
	std::set<StateMachine *> &out;
	findAllStatesVisitor(std::set<StateMachine *> &o)
		: out(o)
	{}
	void visitState(StateMachine *sm)
	{
		out.insert(sm);
	}
};
static void
findAllStates(StateMachine *sm, std::set<StateMachine *> &out)
{
	findAllStatesVisitor v(out);
	v.doit(sm);
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


static StateMachine *buildNewStateMachineWithLoadsEliminated(
	StateMachine *sm,
	std::map<StateMachine *,
	               std::set<StateMachineSideEffectStore *> > &availMap,
	std::map<StateMachine *, StateMachine *> &memo,
	const AllowableOptimisations &opt,
	Oracle *oracle);

static StateMachineEdge *
buildNewStateMachineWithLoadsEliminated(
	StateMachineEdge *sme,
	std::set<StateMachineSideEffectStore *> &initialAvail,
	std::map<StateMachine *,
	               std::set<StateMachineSideEffectStore *> > &availMap,
	std::map<StateMachine *, StateMachine *> &memo,
	const AllowableOptimisations &opt,
	Oracle *oracle)
{
	StateMachineEdge *res =
		new StateMachineEdge(buildNewStateMachineWithLoadsEliminated(sme->target, availMap, memo, opt, oracle));

	std::set<StateMachineSideEffectStore *> currentlyAvailable(initialAvail);

	for (std::vector<StateMachineSideEffect *>::const_iterator it =
		     sme->sideEffects.begin();
	     it != sme->sideEffects.end();
	     it++) {
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(*it)) {
			for (std::set<StateMachineSideEffectStore *>::iterator it2 =
				     currentlyAvailable.begin();
			     it2 != currentlyAvailable.end();
				) {
				if ( !definitelyNotEqual((*it2)->addr, smses->addr, opt) ) {
					currentlyAvailable.erase(it2++);
				} else {
					it2++;
				}
			}
			if (opt.assumeExecutesAtomically || oracle->storeIsThreadLocal(smses))
				currentlyAvailable.insert(smses);
			res->sideEffects.push_back(*it);
		} else if (StateMachineSideEffectLoad *smsel =
			   dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			bool done = false;
			for (std::set<StateMachineSideEffectStore *>::iterator it2 =
				     currentlyAvailable.begin();
			     !done && it2 != currentlyAvailable.end();
			     it2++) {
				if ( definitelyEqual((*it2)->addr, smsel->smsel_addr, opt) ) {
					res->sideEffects.push_back(
						new StateMachineSideEffectCopy(
							smsel->key,
							(*it2)->data));
					done = true;
				}
			}
			if (!done)
				res->sideEffects.push_back(*it);
		} else {
			assert(dynamic_cast<StateMachineSideEffectCopy *>(*it) ||
			       dynamic_cast<StateMachineSideEffectUnreached *>(*it));
			res->sideEffects.push_back(*it);
		}
	}
	return res;
}

static StateMachine *
buildNewStateMachineWithLoadsEliminated(
	StateMachine *sm,
	std::map<StateMachine *,
	               std::set<StateMachineSideEffectStore *> > &availMap,
	std::map<StateMachine *, StateMachine *> &memo,
	const AllowableOptimisations &opt,
	Oracle *oracle)
{
	if (dynamic_cast<StateMachineCrash *>(sm) ||
	    dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm) ||
	    dynamic_cast<StateMachineUnreached *>(sm))
		return sm;
	if (memo.count(sm))
		return memo[sm];
	if (StateMachineBifurcate *smb =
	    dynamic_cast<StateMachineBifurcate *>(sm)) {
		StateMachineBifurcate *res;
		res = new StateMachineBifurcate(smb->condition, (StateMachineEdge *)NULL, NULL);
		memo[sm] = res;
		res->trueTarget = buildNewStateMachineWithLoadsEliminated(
			smb->trueTarget, availMap[sm], availMap, memo, opt, oracle);
		res->falseTarget = buildNewStateMachineWithLoadsEliminated(
			smb->falseTarget, availMap[sm], availMap, memo, opt, oracle);
		return res;
	} if (StateMachineProxy *smp =
	      dynamic_cast<StateMachineProxy *>(sm)) {
		StateMachineProxy *res;
		res = new StateMachineProxy((StateMachineEdge *)NULL);
		memo[sm] = res;
		res->target = buildNewStateMachineWithLoadsEliminated(
			smp->target, availMap[sm], availMap, memo, opt, oracle);
		return res;
	} else {
		abort();
	}
}

static StateMachine *
buildNewStateMachineWithLoadsEliminated(
	StateMachine *sm,
	std::map<StateMachine *,
	         std::set<StateMachineSideEffectStore *> > &availMap,
	const AllowableOptimisations &opt,
	Oracle *oracle)
{
	std::map<StateMachine *, StateMachine *> memo;
	return buildNewStateMachineWithLoadsEliminated(sm, availMap, memo, opt, oracle);
}

/* Available expression analysis on memory locations.  This isn't
   included in the normal optimise() operation because it's
   context-sensitive, and therefore isn't allowed to mutate nodes
   in-place. */
static StateMachine *
availExpressionAnalysis(StateMachine *sm, const AllowableOptimisations &opt, Oracle *oracle)
{
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
	typedef std::set<StateMachineSideEffectStore *> avail_t;

	/* build the set of potentially-available expressions. */
	avail_t potentiallyAvailable;
	findAllStores(sm, potentiallyAvailable);

	/* If we're not executing atomically, stores to
	   non-thread-local memory locations are never considered to
	   be available. */
	if (!opt.assumeExecutesAtomically) {
		for (avail_t::iterator it = potentiallyAvailable.begin();
		     it != potentiallyAvailable.end();
			) {
			if (oracle->storeIsThreadLocal(*it)) {
				it++;
			} else {
				potentiallyAvailable.erase(it++);
			}
		}
	}

	/* build the initial availability map. */
	std::set<StateMachineEdge *> allEdges;
	std::set<StateMachine *> allStates;
	findAllEdges(sm, allEdges);
	findAllStates(sm, allStates);
	std::map<StateMachine *, avail_t> availOnEntry;
	std::map<StateMachineEdge *, avail_t> availOnExit;
	for (std::set<StateMachineEdge *>::iterator it = allEdges.begin();
	     it != allEdges.end();
	     it++)
		availOnExit[*it] = potentiallyAvailable;
	for (std::set<StateMachine *>::iterator it = allStates.begin();
	     it != allStates.end();
	     it++)
		availOnEntry[*it] = potentiallyAvailable;
	availOnEntry[sm].clear();

	std::set<StateMachine *> statesNeedingRefresh(allStates);

	/* Tarski iteration.  */
	bool progress;
	do {
		progress = false;

		/* Update the set of things which are available on
		   entry.  This means walking the set of edges and
		   looking at the targets.  If there's something which
		   is available at the start of the target, but not at
		   the end of this edge, remove it from the target. */
		for (std::set<StateMachineEdge *>::iterator it = allEdges.begin();
		     it != allEdges.end();
		     it++) {
			StateMachineEdge *edge = *it;
			StateMachine *target = edge->target;
			avail_t &avail_at_end_of_edge(availOnExit[edge]);
			avail_t &avail_at_start_of_target(availOnEntry[target]);
			for (avail_t::iterator it2 = avail_at_start_of_target.begin();
			     it2 != avail_at_start_of_target.end();
				) {
				if (avail_at_end_of_edge.count(*it2) == 0) {
					statesNeedingRefresh.insert(target);
					avail_at_start_of_target.erase(it2++); 
					progress = true;
				} else {
					it2++;
				}
			}
		}

		/* Now go through and update the avail-on-exit set.
		   Use a slightly weird-looking iteration over states
		   instead of over edges because that makes things a
		   bit easier. */
		for (std::set<StateMachine *>::iterator it = statesNeedingRefresh.begin();
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
				     it2 != edge->sideEffects.end();
				     it2++) {
					StateMachineSideEffectStore *smses =
						dynamic_cast<StateMachineSideEffectStore *>(*it2);
					if (!smses)
						continue;
					/* Eliminate anything which is killed */
					for (avail_t::iterator it3 = outputAvail.begin();
					     it3 != outputAvail.end();
						) {
						if (!definitelyNotEqual( (*it3)->addr,
									 smses->addr,
									 opt) )
							outputAvail.erase(it3++);
						else
							it3++;
					}
					/* Introduce the store which was generated. */
					if (opt.assumeExecutesAtomically ||
					    oracle->storeIsThreadLocal(smses))
						outputAvail.insert(smses);
				}
				/* Now check whether we actually did anything. */
				avail_t &currentAvail(availOnExit[edge]);
				for (avail_t::iterator it2 = currentAvail.begin();
				     it2 != currentAvail.end();
				     it2++) {
					if (!outputAvail.count(*it2))
						progress = true;
				}
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
		oracle);
}

typedef std::pair<StateMachine *, StateMachine *> st_pair_t;
typedef std::pair<StateMachineEdge *, StateMachineEdge *> st_edge_pair_t;

static bool
hasDisallowedSideEffects(StateMachineEdge *sme,
			 const AllowableOptimisations &opt)
{
	if (opt.ignoreSideEffects)
		return false;
	for (std::vector<StateMachineSideEffect *>::iterator sideEffect =
		     sme->sideEffects.begin();
	     sideEffect != sme->sideEffects.end();
	     sideEffect++) {
		if (dynamic_cast<StateMachineSideEffectStore *>(*sideEffect))
			return true;
	}
	return false;
}

static bool
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
edgesLocallyBisimilar(StateMachineEdge *sme1,
		      StateMachineEdge *sme2,
		      const std::set<st_pair_t> &states,
		      const std::set<st_edge_pair_t> &edges,
		      const AllowableOptimisations &opt)
{
	if (sme1->sideEffects.size() !=
	    sme2->sideEffects.size())
		return false;
	for (unsigned x = 0; x < sme1->sideEffects.size(); x++) {
		if (!sideEffectsBisimilar(sme1->sideEffects[x],
					  sme2->sideEffects[x],
					  opt))
			return false;
	}
	if (states.count(st_pair_t(sme1->target, sme2->target)))
		return true;
	else
		return false;
}

static bool
statesLocallyBisimilar(StateMachine *sm1,
		       StateMachine *sm2,
		       const std::set<st_edge_pair_t> &edges,
		       const std::set<st_pair_t> &others,
		       const AllowableOptimisations &opt)
{
	/* Sort our arguments by type.  Ordering is:

	   Crash
	   NoCrash
	   Stub
	   Unreached
	   Proxy
	   Bifurcation
	*/
	bool swapArgs = false;
	if (!dynamic_cast<StateMachineCrash *>(sm1)) {
		if (dynamic_cast<StateMachineCrash *>(sm2)) {
			swapArgs = true;
		} else if (!dynamic_cast<StateMachineNoCrash *>(sm1)) {
			if (dynamic_cast<StateMachineNoCrash *>(sm2)) {
				swapArgs = true;
			} else if (!dynamic_cast<StateMachineStub *>(sm1)) {
				if (dynamic_cast<StateMachineStub *>(sm2)) {
					swapArgs = true;
				} else if (!dynamic_cast<StateMachineUnreached *>(sm1)) {
					if (dynamic_cast<StateMachineUnreached *>(sm2)) {
						swapArgs = true;
					} else if (!dynamic_cast<StateMachineProxy *>(sm1)) {
						assert(dynamic_cast<StateMachineBifurcate *>(sm1));
						if (dynamic_cast<StateMachineProxy *>(sm2)) {
							swapArgs = true;
						}
					}
				}
			}
		}
	}
	if (swapArgs)
		return statesLocallyBisimilar(sm2, sm1, edges, others, opt);

	if (dynamic_cast<StateMachineCrash *>(sm1)) {
		if (dynamic_cast<StateMachineCrash *>(sm2)) {
			return true;
		} else if (dynamic_cast<StateMachineNoCrash *>(sm2)) {
			return false;
		} else if (dynamic_cast<StateMachineUnreached *>(sm2)) {
			return false;
		} else if (StateMachineProxy *smp =
			   dynamic_cast<StateMachineProxy *>(sm2)) {
			/* We're locally bisimilar to a proxy if the
			   proxy's target is bisimilar to us and the
			   proxy has no disallowed side effects. */
			if (!hasDisallowedSideEffects(smp->target, opt) &&
			    others.count(st_pair_t(sm1, smp->target->target)))
				return true;
			else
				return false;
		} else if (StateMachineBifurcate *smb =
			   dynamic_cast<StateMachineBifurcate *>(sm2)) {
			/* Likewise, we're similar to a proxy if it
			   has no disallowed side-effects and both
			   targets are crash nodes. */
			if (!hasDisallowedSideEffects(smb->trueTarget, opt) &&
			    others.count(st_pair_t(sm1, smb->trueTarget->target)) &&
			    !hasDisallowedSideEffects(smb->falseTarget, opt) &&
			    others.count(st_pair_t(sm1, smb->falseTarget->target)))
				return true;
			else
				return false;
		} else {
			assert(dynamic_cast<StateMachineStub *>(sm2));
			return false;
		}
	}

	if (dynamic_cast<StateMachineNoCrash *>(sm1)) {
		if (dynamic_cast<StateMachineNoCrash *>(sm2)) {
			return true;
		} else if (dynamic_cast<StateMachineUnreached *>(sm2)) {
			return false;
		} else if (StateMachineProxy *smp =
			   dynamic_cast<StateMachineProxy *>(sm2)) {
			if (!hasDisallowedSideEffects(smp->target, opt) &&
			    others.count(st_pair_t(sm1, smp->target->target)))
				return true;
			else
				return false;
		} else if (StateMachineBifurcate *smb =
			   dynamic_cast<StateMachineBifurcate *>(sm2)) {
			if (!hasDisallowedSideEffects(smb->trueTarget, opt) &&
			    others.count(st_pair_t(sm1, smb->trueTarget->target)) &&
			    !hasDisallowedSideEffects(smb->falseTarget, opt) &&
			    others.count(st_pair_t(sm1, smb->falseTarget->target)))
				return true;
			else
				return false;
		} else {
			assert(dynamic_cast<StateMachineStub *>(sm2));
			return false;
		}
	}

	if (dynamic_cast<StateMachineUnreached *>(sm1)) {
		/* We ignore side effects for unreached states: since
		   we never go down here, any side effects are
		   completely irrelevant. */
		if (dynamic_cast<StateMachineUnreached *>(sm2)) {
			return true;
		} else if (StateMachineProxy *smp =
			   dynamic_cast<StateMachineProxy *>(sm2)) {
			if (others.count(st_pair_t(sm1, smp->target->target)))
				return true;
			else
				return false;
		} else if (StateMachineBifurcate *smb =
			   dynamic_cast<StateMachineBifurcate *>(sm2)) {
			if (others.count(st_pair_t(sm1, smb->trueTarget->target)) &&
			    others.count(st_pair_t(sm1, smb->falseTarget->target)))
				return true;
			else
				return false;
		} else {
			assert(dynamic_cast<StateMachineStub *>(sm2));
			return false;
		}
	}
	if (StateMachineStub *sms1 =
	    dynamic_cast<StateMachineStub *>(sm1)) {
		if (StateMachineStub *sms2 = dynamic_cast<StateMachineStub *>(sm2))
			return definitelyEqual(sms1->target, sms2->target, opt);
		else
			return false;
	}

	if (StateMachineProxy *smp1 =
	    dynamic_cast<StateMachineProxy *>(sm1)) {
		if (StateMachineProxy *smp2 =
		    dynamic_cast<StateMachineProxy *>(sm2)) {
			return edges.count(st_edge_pair_t(smp1->target, smp2->target)) ||
				edgesLocallyBisimilar(smp1->target,
						      smp2->target,
						      others,
						      edges,
						      opt);
		} else if (StateMachineBifurcate *smb2 =
			   dynamic_cast<StateMachineBifurcate *>(sm2)) {
			return (edges.count(st_edge_pair_t(smp1->target,
							   smb2->trueTarget)) ||
				edgesLocallyBisimilar(smp1->target,
						      smb2->trueTarget,
						      others,
						      edges,
						      opt)) &&
				(edges.count(st_edge_pair_t(smp1->target,
							    smb2->falseTarget)) ||
				 edgesLocallyBisimilar(smp1->target,
						       smb2->falseTarget,
						       others,
						       edges,
						       opt));
		} else {
			abort();
		}
	}

	StateMachineBifurcate *smb1 =
		dynamic_cast<StateMachineBifurcate *>(sm1);
	StateMachineBifurcate *smb2 =
		dynamic_cast<StateMachineBifurcate *>(sm2);
	assert(smb1);
	assert(smb2);
	return
		(edges.count(st_edge_pair_t(smb1->trueTarget, smb2->trueTarget)) ||
		 edgesLocallyBisimilar(smb1->trueTarget, smb2->trueTarget, others, edges, opt)) &&
		(edges.count(st_edge_pair_t(smb1->falseTarget, smb2->falseTarget)) ||
		 edgesLocallyBisimilar(smb1->falseTarget, smb2->falseTarget, others, edges, opt)) &&
		definitelyEqual(smb1->condition, smb2->condition, opt);
}

static StateMachine *
rewriteStateMachine(StateMachine *sm,
		    std::map<StateMachine *, StateMachine *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules,
		    std::set<StateMachine *> &memo,
		    std::set<StateMachineEdge *> &edgeMemo);

static StateMachineEdge *
rewriteStateMachineEdge(StateMachineEdge *sme,
			std::map<StateMachine *, StateMachine *> &rules,
			std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules,
			std::set<StateMachine *> &memo,
			std::set<StateMachineEdge *> &edgeMemo)
{
	if (edgeRules.count(sme)) {
		edgeMemo.insert(edgeRules[sme]);
		return rewriteStateMachineEdge(edgeRules[sme], rules, edgeRules, memo, edgeMemo);
	}
	edgeMemo.insert(sme);
	sme->target = rewriteStateMachine(sme->target,
					  rules,
					  edgeRules,
					  memo,
					  edgeMemo);
	return sme;
}

static StateMachine *
rewriteStateMachine(StateMachine *sm,
		    std::map<StateMachine *, StateMachine *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules,
		    std::set<StateMachine *> &memo,
		    std::set<StateMachineEdge *> &edgeMemo)
{
	if (rules.count(sm) && rules[sm] != sm) {
		memo.insert(rules[sm]);
		return rewriteStateMachine(rules[sm], rules, edgeRules, memo, edgeMemo);
	}
	memo.insert(sm);
	if (dynamic_cast<StateMachineCrash *>(sm) ||
	    dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm) ||
	    dynamic_cast<StateMachineUnreached *>(sm)) {
		return sm;
	} else if (StateMachineBifurcate *smb =
		   dynamic_cast<StateMachineBifurcate *>(sm)) {
		smb->trueTarget = rewriteStateMachineEdge(
			smb->trueTarget,
			rules,
			edgeRules,
			memo,
			edgeMemo);
		smb->falseTarget = rewriteStateMachineEdge(
			smb->falseTarget,
			rules,
			edgeRules,
			memo,
			edgeMemo);
		return sm;
	} else if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
		smp->target = rewriteStateMachineEdge(
			smp->target,
			rules,
			edgeRules,
			memo,
			edgeMemo);
		return sm;
	} else {
		abort();
	}
}

static StateMachine *
rewriteStateMachine(StateMachine *sm, std::map<StateMachine *, StateMachine *> &rules,
		    std::map<StateMachineEdge *, StateMachineEdge *> &edgeRules)
{
	std::set<StateMachine *> memo;
	std::set<StateMachineEdge *> edgeMemo;
	return rewriteStateMachine(sm, rules, edgeRules, memo, edgeMemo);
}

/* Try to identify states which are bisimilar, and then go and merge
 * them.  This is in-place, so should really be part of ::optimise();
 * nevermind. */
static StateMachine *
bisimilarityReduction(StateMachine *sm, const AllowableOptimisations &opt)
{
	/* We start by assuming that all states are bisimilar to each
	   other, and then use Tarski iteration to eliminate the
	   contradictions.  That allows us to build up maximal sets of
	   states such that the states in the sets are bisimilar to
	   each other.  Once we've got that, we pick one of the states
	   as being representative of the set, and then use it in
	   place of the other states. */

	std::set<StateMachine *> allStates;
	findAllStates(sm, allStates);
	std::set<StateMachineEdge *> allEdges;
	findAllEdges(sm, allEdges);

	std::set<st_pair_t> bisimilarStates;
	std::set<st_edge_pair_t> bisimilarEdges;

	/* Initially, everything is bisimilar to everything else. */
	for (std::set<StateMachine *>::iterator it = allStates.begin();
	     it != allStates.end();
	     it++)
		for (std::set<StateMachine *>::iterator it2 = allStates.begin();
		     it2 != allStates.end();
		     it2++)
			bisimilarStates.insert(st_pair_t(*it, *it2));
	for (std::set<StateMachineEdge *>::iterator it = allEdges.begin();
	     it != allEdges.end();
	     it++)
		for (std::set<StateMachineEdge *>::iterator it2 = allEdges.begin();
		     it2 != allEdges.end();
		     it2++)
			bisimilarEdges.insert(st_edge_pair_t(*it, *it2));

	bool progress;
	do {
		progress = false;

		/* Iterate over every suspected bisimilarity pair and
		   check for ``local bisimilarity''.  Once we're
		   consistent with the local bisimilarity
		   relationship, we will also be consistent with
		   global bismilarity. */
		for (std::set<st_pair_t>::iterator it = bisimilarStates.begin();
		     it != bisimilarStates.end();
			) {
			if (statesLocallyBisimilar(it->first, it->second, bisimilarEdges, bisimilarStates, opt)) {
				it++;
			} else {
				bisimilarStates.erase(it++);
				progress = true;
			}
		}
		for (std::set<st_edge_pair_t>::iterator it = bisimilarEdges.begin();
		     it != bisimilarEdges.end();
			) {
			if (edgesLocallyBisimilar(it->first, it->second, bisimilarStates, bisimilarEdges, opt)) {
				it++;
			} else {
				bisimilarEdges.erase(it++);
				progress = true;
			}
		}
	} while (progress);

	std::map<StateMachine *, StateMachine *> canonMap;
	/* While we're here, iterate over every bifurcation node, and
	   if the branches are bisimilar to each other then replace it
	   with a proxy. */

	for (std::set<StateMachine *>::iterator it = allStates.begin();
	     it != allStates.end();
	     it++) {
		StateMachineBifurcate *smb = dynamic_cast<StateMachineBifurcate *>(*it);
		if (smb && bisimilarEdges.count(st_edge_pair_t(smb->trueTarget, smb->falseTarget)))
			canonMap[*it] = new StateMachineProxy(smb->trueTarget);
	}

	/* Now build a mapping from states to canonical states, using
	   the bisimilarity information, such that two states map to
	   the same canonical state iff they are bisimilar. */
	/* The canonMap effectively forms an inverted forest.  Each
	   tree in the forest represents some set of bisimilar nodes,
	   and each node's entry points at its parent in the tree, if
	   it has one.  The canonical representation of each set is
	   the root of its corresponding tree.  We advance by merging
	   sets, by inserting one as a child of the root of the other,
	   in response to bisimilar state entries. */

	for (std::set<st_pair_t>::iterator it = bisimilarStates.begin();
	     it != bisimilarStates.end();
	     it++) {
		StateMachine *s1 = it->first;
		StateMachine *s2 = it->second;

		/* Map the two nodes to their canonicalisations, if
		 * they have them. */
		while (canonMap.count(s1))
			s1 = canonMap[s1];
		while (canonMap.count(s2))
			s2 = canonMap[s2];
		/* This is more subtle than it looks.  It might appear
		   that we should be able to pick pretty much
		   arbitrarily which way round we perform the mapping
		   (s2 -> s1 or s1 -> s2).  Not so: the mapping we
		   build has to respect a depth-first ordering of the
		   graph, or you risk introducing loops.  This way
		   around does respect that ordering, whereas the
		   other way around wouldn't. */
		/* XXX I'm not entirely convinced I believe that
		 * explanation. */
		if (s1 != s2)
			canonMap[s2] = s1;
	}

	/* Do the same thing for edges */
	std::map<StateMachineEdge *, StateMachineEdge *> canonEdgeMap;
	for (std::set<st_edge_pair_t>::iterator it = bisimilarEdges.begin();
	     it != bisimilarEdges.end();
	     it++) {
		StateMachineEdge *s1 = it->first;
		StateMachineEdge *s2 = it->second;
		while (canonEdgeMap.count(s1))
			s1 = canonEdgeMap[s1];
		while (canonEdgeMap.count(s2))
			s2 = canonEdgeMap[s2];
		if (s1 != s2)
			canonEdgeMap[s2] = s1;
	}

	/* Perform the rewrite.  We do this in-place, because it's not
	   context-dependent. */
	return rewriteStateMachine(sm, canonMap, canonEdgeMap);
}

template <typename t>
class union_find {
public:
	struct entry {
		entry(const t &_parent, unsigned _d)
			: parent(_parent), depth(_d)
		{}
		entry() { abort(); /* shouldn't happen */ }
		t parent;
		unsigned depth;
	};
	std::map<t, entry> content;

	/* Check whether we know anything at all about x */
	bool present(t x) { return content.count(x) != 0; }

	/* Insert x into the structure as a singleton, if it's not
	   already present. */
	void insert(t x) { if (!present(x)) content.insert(std::pair<t, entry>(x, entry(x, 0))); }

	/* Insert x and y into the structure, if they're not present,
	   and then merge their containing sets. */
	void insert(t x, t y) {
		t xr = representative(x);
		t yr = representative(y);
		if (xr != yr) {
			entry &xe(content[xr]);
			entry &ye(content[yr]);
			if (xe.depth < ye.depth)
				xe.parent = yr;
			else
				ye.parent = xr;
		}
		assert(representative(x) == representative(y));
	}

	/* Find the representative for the set to which a given item
	   belongs.  Create the item as a singleton if it isn't
	   already present. */
	t representative(t x) {
		if (!present(x)) {
			insert(x);
			return x;
		}
		while (1) {
			assert(content.count(x) != 0);
			entry *e = &content[x];
			if (e->parent == x)
				return x;
			assert(content.count(e->parent) != 0);
			entry *pe = &content[e->parent];
			if (pe->parent)
				e->parent = pe->parent;
			x = e->parent;
		}
	}
};

static void
findInstrSuccessorsAndCallees(AddressSpace *as,
			      unsigned long rip,
			      std::vector<unsigned long> &directExits,
			      gc_pair_ulong_set_t *callees)
{
	IRSB *irsb;
	try {
		irsb = as->getIRSBForAddress(-1, rip);
	} catch (BadMemoryException &e) {
		return;
	}
	int i;

	for (i = 1; i < irsb->stmts_used; i++) {
		if (irsb->stmts[i]->tag == Ist_IMark) {
			/* That's the end of this instruction */
			directExits.push_back(irsb->stmts[i]->Ist.IMark.addr);
			return;
		}
		if (irsb->stmts[i]->tag == Ist_Exit)
			directExits.push_back(irsb->stmts[i]->Ist.Exit.dst->Ico.U64);
	}

	/* If we get here then there are no other marks in the IRSB,
	   so we need to look at the fall through addresses. */
	if (irsb->jumpkind == Ijk_Call) {
		directExits.push_back(extract_call_follower(irsb));
		/* Emit the target as well, if possible. */
		if (irsb->next->tag == Iex_Const)
			callees->set(std::pair<unsigned long, unsigned long>(rip, irsb->next->Iex.Const.con->Ico.U64),
				     true);
		return;
	}

	if (irsb->jumpkind != Ijk_NoDecode &&
	    irsb->next->tag == Iex_Const) {
		directExits.push_back(irsb->next->Iex.Const.con->Ico.U64);
	} else {
		/* Should really do something more clever here,
		   possibly based on dynamic analysis. */
	}
}

static void
findSuccessors(AddressSpace *as, unsigned long rip, std::vector<unsigned long> &out)
{
	gc_pair_ulong_set_t *callees = new gc_pair_ulong_set_t();
	findInstrSuccessorsAndCallees(as, rip, out, callees);
	for (gc_pair_ulong_set_t::iterator it = callees->begin();
	     it != callees->end();
	     it++)
		out.push_back(it.key().second);
}

/* Try to group the RIPs into clusters which are likely to execute
 * together.  We'll eventually build state machines for each cluster,
 * rather than for individual RIPs. */
/* The mechanism used is a bit stupid: pick a RIP pretty much at
 * random out of the input set and create a new output set for it.  We
 * then explore the machine code from that address, and if we find any
 * other input RIPs we add them to the current output set.  If we find
 * a RIP which has already been assigned an output set then we merge
 * the relevant output sets. */
void
Oracle::clusterRips(const std::set<unsigned long> &inputRips,
		    std::set<InstructionSet> &outputClusters)
{
	union_find<unsigned long> output;
	std::set<unsigned long> explored;

	for (std::set<unsigned long>::const_iterator it = inputRips.begin();
	     it != inputRips.end();
	     it++) {
		unsigned long r = *it;
		assert(r);
		if (output.present(r))
			continue;

		output.insert(r);
		std::vector<unsigned long> discoveredInstructions;
		discoveredInstructions.push_back(r);
		while (!discoveredInstructions.empty()) {
			unsigned long r2 = discoveredInstructions.back();
			discoveredInstructions.pop_back();
			if (!explored.count(r2))
				findSuccessors(ms->addressSpace, r2, discoveredInstructions);
			output.insert(r, r2);
			explored.insert(r2);
		}
	}

	/* Now explode the union-find structure into a set of sets. */
	std::set<unsigned long> unprocessedInput(inputRips);
	while (!unprocessedInput.empty()) {
		unsigned long r = *unprocessedInput.begin();

		InstructionSet thisSet;
		unsigned long representative = output.representative(r);
		for (std::set<unsigned long>::iterator it = unprocessedInput.begin();
		     it != unprocessedInput.end();
			) {
			if (output.representative(*it) == representative) {
				thisSet.rips.insert(*it);
				unprocessedInput.erase(it++);
			} else {
				it++;
			}
		}
		outputClusters.insert(thisSet);
	}
}

static unsigned long
wrappedRipToRip(unsigned long r)
{
	return r;
}

template <typename t> StateMachine *
CFGtoStoreMachine(unsigned tid, AddressSpace *as, CFGNode<t> *cfg, std::map<CFGNode<t> *, StateMachine *> &memo)
{
	if (!cfg)
		return StateMachineNoCrash::get();
	if (memo.count(cfg))
		return memo[cfg];
	StateMachine *res;
	IRSB *irsb = as->getIRSBForAddress(tid, wrappedRipToRip(cfg->my_rip));
	int endOfInstr;
	for (endOfInstr = 1; endOfInstr < irsb->stmts_used; endOfInstr++)
		if (irsb->stmts[endOfInstr]->tag == Ist_IMark)
			break;
	if (cfg->fallThrough || !cfg->branch) {
		res = CFGtoStoreMachine(tid, as, cfg->fallThrough, memo);
		int idx = endOfInstr;
		while (idx != 0) {
			IRStmt *stmt = irsb->stmts[idx-1];
			if (stmt->tag == Ist_Exit) {
				if (cfg->branch) {
					res = new StateMachineBifurcate(
						stmt->Ist.Exit.guard,
						CFGtoStoreMachine(tid, as, cfg->branch, memo),
						res);
				}
			} else {
				res = backtrackStateMachineOneStatement(res, stmt, wrappedRipToRip(cfg->my_rip));
			}
			idx--;
		}
	} else {
		assert(cfg->branch);
		res = CFGtoStoreMachine(tid, as, cfg->branch, memo);
		int idx;
		for (idx = endOfInstr - 1; idx >= 0; idx--)
			if (irsb->stmts[idx]->tag == Ist_Exit)
				break;
		assert(idx > 0);
		while (idx != 0) {
			IRStmt *stmt = irsb->stmts[idx-1];
			res = backtrackStateMachineOneStatement(res, stmt, wrappedRipToRip(cfg->my_rip));
		}
	}
	memo[cfg] = res;
	return res;		
}

template <typename t> StateMachine *
CFGtoStoreMachine(unsigned tid, AddressSpace *as, CFGNode<t> *cfg)
{
	std::map<CFGNode<t> *, StateMachine *> memo;
	return CFGtoStoreMachine(tid, as, cfg, memo);
}

class StateMachineEvalContext {
public:
	std::vector<StateMachineSideEffectStore *> stores;
	std::map<Int, IRExpr *> binders;
	IRExpr *pathConstraint;
};

static IRExpr *
specialiseIRExpr(IRExpr *iex, std::map<Int,IRExpr *> &binders)
{
	switch (iex->tag) {
	case Iex_Binder:
		assert(binders[iex->Iex.Binder.binder]);
		return binders[iex->Iex.Binder.binder];
	case Iex_Get:
		return iex;
	case Iex_GetI:
		return IRExpr_GetI(
			iex->Iex.GetI.descr,
			specialiseIRExpr(iex->Iex.GetI.ix, binders),
			iex->Iex.GetI.bias,
			iex->Iex.GetI.tid);
	case Iex_RdTmp:
		return iex;
	case Iex_Qop:
		return IRExpr_Qop(
			iex->Iex.Qop.op,
			specialiseIRExpr(iex->Iex.Qop.arg1, binders),
			specialiseIRExpr(iex->Iex.Qop.arg2, binders),
			specialiseIRExpr(iex->Iex.Qop.arg3, binders),
			specialiseIRExpr(iex->Iex.Qop.arg4, binders));
	case Iex_Triop:
		return IRExpr_Triop(
			iex->Iex.Triop.op,
			specialiseIRExpr(iex->Iex.Triop.arg1, binders),
			specialiseIRExpr(iex->Iex.Triop.arg2, binders),
			specialiseIRExpr(iex->Iex.Triop.arg3, binders));
	case Iex_Binop:
		return IRExpr_Binop(
			iex->Iex.Binop.op,
			specialiseIRExpr(iex->Iex.Binop.arg1, binders),
			specialiseIRExpr(iex->Iex.Binop.arg2, binders));
	case Iex_Unop:
		return IRExpr_Unop(
			iex->Iex.Unop.op,
			specialiseIRExpr(iex->Iex.Unop.arg, binders));
	case Iex_Load:
		return IRExpr_Load(
			iex->Iex.Load.isLL,
			iex->Iex.Load.end,
			iex->Iex.Load.ty,
			specialiseIRExpr(iex->Iex.Load.addr, binders));
	case Iex_Const:
		return iex;
	case Iex_CCall: {
		IRExpr **args;
		int n;
		for (n = 0; iex->Iex.CCall.args[n]; n++)
			;
		args = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, n + 1);
		for (n = 0; iex->Iex.CCall.args[n]; n++)
			args[n] = specialiseIRExpr(iex->Iex.CCall.args[n], binders);
		return IRExpr_CCall(
			iex->Iex.CCall.cee,
			iex->Iex.CCall.retty,
			args);
	}
	case Iex_Mux0X:
		return IRExpr_Mux0X(
			specialiseIRExpr(iex->Iex.Mux0X.cond, binders),
			specialiseIRExpr(iex->Iex.Mux0X.expr0, binders),
			specialiseIRExpr(iex->Iex.Mux0X.exprX, binders));
	case Iex_Associative: {
		IRExpr *res = IRExpr_Associative(iex);
		for (int it = 0;
		     it < res->Iex.Associative.nr_arguments;
		     it++)
			res->Iex.Associative.contents[it] =
				specialiseIRExpr(res->Iex.Associative.contents[it],
						 binders);
		return res;
	}
	}
	abort();
}

static bool
expressionIsTrue(IRExpr *exp, NdChooser &chooser, std::map<Int, IRExpr *> &binders, IRExpr **assumption)
{
	exp = optimiseIRExpr(
		specialiseIRExpr(exp, binders),
		AllowableOptimisations::defaultOptimisations);

	/* Combine the path constraint with the new expression and see
	   if that produces a contradiction.  If it does then we know
	   for sure that the new expression is false. */
	IRExpr *e =
		optimiseIRExpr(
			IRExpr_Binop(
				Iop_And1,
				*assumption,
				exp),
			AllowableOptimisations::defaultOptimisations);
	if (e->tag == Iex_Const) {
		/* That shouldn't produce the constant 1 very often.
		   If it does, it indicates that the path constraint
		   is definitely true, and the new expression is
		   definitely true, but for some reason we weren't
		   able to simplify the path constraint down to 1
		   earlier.  Consider that a lucky break and simplify
		   it now. */
		if (e->Iex.Const.con->Ico.U1) {
			assertUnoptimisable(e, AllowableOptimisations::defaultOptimisations);
			*assumption = e;
			return true;
		} else {
			return false;
		}
	}

	/* Now try it the other way around, by combining the path
	   constraint with ¬exp.  If we had a perfect theorem prover
	   this would be redundant with the previous version, but we
	   don't, so it isn't. */
	IRExpr *e2 =
		optimiseIRExpr(
			IRExpr_Binop(
				Iop_And1,
				*assumption,
				IRExpr_Unop(
					Iop_Not1,
					exp)),
			AllowableOptimisations::defaultOptimisations);
	if (e2->tag == Iex_Const) {
		/* If X & ¬Y is definitely true, Y is definitely
		 * false and X is definitely true. */
		if (e2->Iex.Const.con->Ico.U1) {
			*assumption = IRExpr_Const(IRConst_U1(1));
			return false;
		}

		/* So now we know that X & ¬Y is definitely false, and
		 * we assume that X is true.  Therefore ¬Y is false
		 * and Y is true. */
		return true;
	}

	/* Can't prove it one way or another.  Use the
	   non-deterministic chooser to guess. */
	int res;
	bool isNewChoice;
	res = chooser.nd_choice(2, &isNewChoice);
#if 0
	if (isNewChoice) {
		printf("Having to use state split to check whether ");
		ppIRExpr(exp, stdout);
		printf(" is true under assumption ");
		ppIRExpr(*assumption, stdout);
		printf("\n");
	}
#endif
	if (res == 0) {
		assertUnoptimisable(e, AllowableOptimisations::defaultOptimisations);
		*assumption = e;
		return true;
	} else {
		assertUnoptimisable(e2, AllowableOptimisations::defaultOptimisations);
		*assumption = e2;
		return false;
	}
}

static bool
evalExpressionsEqual(IRExpr *exp1, IRExpr *exp2, NdChooser &chooser, std::map<Int, IRExpr *> &binders,
		     IRExpr **assumption)
{
	return expressionIsTrue(IRExpr_Binop(
					Iop_CmpEQ64,
					exp1,
					exp2),
				chooser,
				binders,
				assumption);
}

static void evalStateMachine(StateMachine *sm,
			     bool *crashes,
			     NdChooser &chooser,
			     Oracle *oracle,
			     StateMachineEvalContext &ctxt);

static void
evalStateMachineSideEffect(StateMachineSideEffect *smse,
			   NdChooser &chooser,
			   Oracle *oracle,
			   std::map<Int, IRExpr *> &binders,
			   std::vector<StateMachineSideEffectStore *> &stores,
			   IRExpr **assumption)
{
	if (StateMachineSideEffectStore *smses =
	    dynamic_cast<StateMachineSideEffectStore *>(smse)) {
		stores.push_back(
			new StateMachineSideEffectStore(
				specialiseIRExpr(smses->addr, binders),
				specialiseIRExpr(smses->data, binders),
				smses->rip
				)
				);
	} else if (StateMachineSideEffectLoad *smsel =
		   dynamic_cast<StateMachineSideEffectLoad *>(smse)) {
		IRExpr *val;
		val = NULL;
		for (std::vector<StateMachineSideEffectStore *>::reverse_iterator it = stores.rbegin();
		     !val && it != stores.rend();
		     it++) {
			StateMachineSideEffectStore *smses = *it;
			if (!oracle->memoryAccessesMightAlias(smsel, smses))
				continue;
			if (evalExpressionsEqual(smses->addr, smsel->smsel_addr, chooser, binders, assumption))
				val = smses->data;
		}
		if (!val)
			val = IRExpr_Load(False, Iend_LE, Ity_I64, smsel->smsel_addr);
		binders[smsel->key] = val;
	} else if (StateMachineSideEffectCopy *smsec =
		   dynamic_cast<StateMachineSideEffectCopy *>(smse)) {
		binders[smsec->key] =
			specialiseIRExpr(smsec->value, binders);
	} else {
		abort();
	}
}

static void
evalStateMachineEdge(StateMachineEdge *sme,
		     bool *crashes,
		     NdChooser &chooser,
		     Oracle *oracle,
		     StateMachineEvalContext &ctxt)
{
	for (std::vector<StateMachineSideEffect *>::iterator it = sme->sideEffects.begin();
	     it != sme->sideEffects.end();
	     it++)
		evalStateMachineSideEffect(*it, chooser, oracle, ctxt.binders,
					   ctxt.stores, &ctxt.pathConstraint);
	evalStateMachine(sme->target, crashes, chooser, oracle, ctxt);
}

/* Walk the state machine and figure out whether it's going to crash.
   If we hit something which we can't solve statically or via the
   oracle, ask the chooser which way we should go, and then emit a
   path constraint saying which way we went.  Stubs are assumed to
   never crash. */
static void
evalStateMachine(StateMachine *sm,
		 bool *crashes,
		 NdChooser &chooser,
		 Oracle *oracle,
		 StateMachineEvalContext &ctxt)
{
	if (dynamic_cast<StateMachineCrash *>(sm)) {
		*crashes = true;
		return;
	}
	if (dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm)) {
		*crashes = false;
		return;
	}
	if (StateMachineProxy *smp =
	    dynamic_cast<StateMachineProxy *>(sm)) {
		evalStateMachineEdge(smp->target, crashes, chooser, oracle, ctxt);
		return;
	}
	if (StateMachineBifurcate *smb =
	    dynamic_cast<StateMachineBifurcate *>(sm)) {
		if (expressionIsTrue(smb->condition, chooser, ctxt.binders, &ctxt.pathConstraint)) {
			printf("At %p, go true\n", smb);
			evalStateMachineEdge(smb->trueTarget, crashes, chooser, oracle, ctxt);
		} else {
			printf("At %p, go false\n", smb);
			evalStateMachineEdge(smb->falseTarget, crashes, chooser, oracle, ctxt);
		}
		return;
	}
	abort();
}

/* Assume that @sm executes atomically.  Figure out a constraint on
   the initial state which will lead to it not crashing. */
static IRExpr *
survivalConstraintIfExecutedAtomically(VexPtr<StateMachine, &ir_heap> &sm,
				       VexPtr<Oracle> &oracle,
				       GarbageCollectionToken token)
{
	NdChooser chooser;
	VexPtr<IRExpr, &ir_heap> currentConstraint(IRExpr_Const(IRConst_U1(1)));
	bool crashes;

	do {
		LibVEX_maybe_gc(token);
		StateMachineEvalContext ctxt;
		ctxt.pathConstraint = IRExpr_Const(IRConst_U1(1));
		evalStateMachine(sm, &crashes, chooser, oracle, ctxt);
		if (crashes) {
			/* This path leads to a crash, so the
			   constraint should include something to make
			   sure that we don't go down here. */
			IRExpr *newConstraint =
				IRExpr_Binop(
					Iop_And1,
					currentConstraint,
					IRExpr_Unop(
						Iop_Not1,
						ctxt.pathConstraint));
#if 0
			printf("Add ");
			ppIRExpr(ctxt.pathConstraint, stdout);
			printf(" to ");
			ppIRExpr(currentConstraint, stdout);
			printf(" -> ");
			ppIRExpr(newConstraint, stdout);
			printf("\n");
#endif
			currentConstraint = newConstraint;
		}
	} while (chooser.advance());

	return currentConstraint;
}

static IROp
random_irop(void)
{
	return (IROp)((unsigned long)Iop_Add8 + random() % (Iop_Perm8x16 - Iop_Add8 + 1));
}

static IRType
random_irtype(void)
{
	return (IRType)((unsigned long)Ity_I8 + random() % 7);
}

static IRConst *
random_irconst(void)
{
	switch (random_irtype()) {
	case Ity_I8:
		return IRConst_U8(random() % 256);
	case Ity_I16:
		return IRConst_U16(random() % 65536);
	case Ity_I32:
		return IRConst_U32(random());
	case Ity_I64:
		return IRConst_U64(random());
	case Ity_F32:
	case Ity_I128:
		return random_irconst();
	case Ity_F64:
		return IRConst_F64(random() / (double)random());
	case Ity_V128:
		return IRConst_V128(random());
	default:
		abort();
	}
}

static IRRegArray *
random_irregarray(void)
{
	return mkIRRegArray( (random() % 10) * 8,
			     random_irtype(),
			     random() % 16 );
}

static IRExpr *
random_irexpr(unsigned depth)
{
	if (!depth)
		return IRExpr_Const(random_irconst());
	switch (random() % 8) {
	case 0:
		return IRExpr_Binder(random() % 30);
	case 1:
		return IRExpr_Get((random() % 40) * 8,
				  random_irtype(),
				  73);
	case 2:
		return IRExpr_RdTmp(random() % 5, 73);
	case 3:
		switch (random() % 5) {
		case 0:
			return IRExpr_Unop(random_irop(), random_irexpr(depth - 1));
		case 1:
			return IRExpr_Binop(
				random_irop(),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1));
		case 2:
			return IRExpr_Triop(
				random_irop(),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1));
		case 3:
			return IRExpr_Qop(
				random_irop(),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1));
		case 4: {
			IRExpr *e = IRExpr_Associative(
				random_irop(),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1),
				NULL);
			while (random() % 2)
				addArgumentToAssoc(e, random_irexpr(depth - 1));
			return e;
		}
		default:
			abort();
		}
	case 4:
		return IRExpr_Load(
			False,
			Iend_LE,
			random_irtype(),
			random_irexpr(depth - 1));
	case 5:
		return IRExpr_Const(random_irconst());
	case 6: {
		IRExpr **args;
		switch (random() % 4) {
		case 0:
			args = mkIRExprVec_0();
			break;
		case 1:
			args = mkIRExprVec_1(random_irexpr(depth - 1));
			break;
		case 2:
			args = mkIRExprVec_2(random_irexpr(depth - 1), random_irexpr(depth - 1));
			break;
		case 3:
			args = mkIRExprVec_3(random_irexpr(depth - 1), random_irexpr(depth - 1), random_irexpr(depth - 1));
			break;
		default:
			abort();
		}
		return IRExpr_CCall(mkIRCallee(0, "random_ccall", (void *)0x52),
				    random_irtype(),
				    args);
	}
	case 7:
		return IRExpr_Mux0X(random_irexpr(depth - 1), random_irexpr(depth - 1), random_irexpr(depth - 1));
	case 8:
		return IRExpr_GetI(random_irregarray(), random_irexpr(depth - 1), (random() % 20) * 8, 98);
	default:
		abort();
	}		
}

/* Check that sortIRExprs() produces vaguely sane results. */
static void
sanity_check_irexpr_sorter(void)
{
	srandom(time(NULL));
#define NR_EXPRS 10000
	IRExpr *exprs[NR_EXPRS];
	int x;
	int y;

	printf("Generating %d random expressions\n", NR_EXPRS);
	for (x = 0; x < NR_EXPRS; x++)
		exprs[x] = random_irexpr(3);

	printf("Ordering should be anti-reflexive.\n");
	for (x = 0; x < NR_EXPRS; x++)
		assert(!sortIRExprs(exprs[x], exprs[x]));

	printf("Ordering should be anti-symmetric.\n");
	for (x = 0; x < NR_EXPRS; x++) {
		for (y = x + 1; y < NR_EXPRS; y++) {
			if (sortIRExprs(exprs[x], exprs[y]))
				assert(!sortIRExprs(exprs[y], exprs[x]));
		}
	}

	/* Ordering must be transitive and total.  We check this by
	 * performing a naive topological sort on the expressions and
	 * then checking that whenever x < y exprs[x] < exprs[y]. */
	IRExpr *exprs2[NR_EXPRS];

	int nr_exprs2 = 0;
	int candidate;
	int probe;
	bool progress = true;
	printf("Toposorting...\n");
	while (nr_exprs2 < NR_EXPRS) {
		/* Try to find an ordering-minimal entry in the
		 * array.  */
		assert(progress);
		progress = false;
		for (candidate = 0; candidate < NR_EXPRS; candidate++) {
			if (!exprs[candidate])
				continue;
			for (probe = 0; probe < NR_EXPRS; probe++) {
				if (!exprs[probe])
					continue;
				if (sortIRExprs(exprs[probe], exprs[candidate])) {
					/* probe is less than
					   candidate, so candidate
					   fails. */
					break;
				}
			}
			if (probe == NR_EXPRS) {
				/* This candidate passes.  Add it to
				   the list. */
				exprs2[nr_exprs2] = exprs[candidate];
				exprs[candidate] = NULL;
				nr_exprs2++;
				progress = true;
			}
		}
	}

	/* Okay, have a topo sort.  The ordering is supposed to be
	   total, so that should have just been an O(n^3) selection
	   sort, and the array should now be totally sorted.  check
	   it. */
	printf("Check toposort is total...\n");
	for (x = 0; x < NR_EXPRS; x++)
		for (y = x + 1; y < NR_EXPRS; y++)
			assert(!sortIRExprs(exprs2[y], exprs2[x]));
}

static void
sanity_check_optimiser(void)
{
	/* x + -x -> 0 */
	IRExpr *start =
		IRExpr_Associative(
			Iop_Add64,
			IRExpr_Get(0, Ity_I64, 0),
			IRExpr_Unop(
				Iop_Neg64,
				IRExpr_Get(0, Ity_I64, 0)),
			NULL);
	IRExpr *end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	assert(physicallyEqual(end, IRExpr_Const(IRConst_U64(0))));
	/* x & ~x -> 0 */
	start = IRExpr_Associative(
		Iop_And1,
		IRExpr_Unop(
			Iop_Not1,
			IRExpr_Get(0, Ity_I64, 0)),
		IRExpr_Get(0, Ity_I64, 0),
		NULL);
	end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	assert(physicallyEqual(end, IRExpr_Const(IRConst_U1(0))));
}

static void
evalMachineUnderAssumption(VexPtr<StateMachine, &ir_heap> &sm, VexPtr<Oracle> &oracle,
			   VexPtr<IRExpr, &ir_heap> assumption,
			   bool *mightSurvive, bool *mightCrash,
			   GarbageCollectionToken token)
{
	NdChooser chooser;
	bool crashes;

	assertUnoptimisable(assumption, AllowableOptimisations::defaultOptimisations);
	*mightSurvive = false;
	*mightCrash = false;
	while (!*mightCrash || !*mightSurvive) {
		LibVEX_maybe_gc(token);
		StateMachineEvalContext ctxt;
		assertUnoptimisable(assumption, AllowableOptimisations::defaultOptimisations);
		ctxt.pathConstraint = assumption;
		evalStateMachine(sm, &crashes, chooser, oracle, ctxt);
		assertUnoptimisable(assumption, AllowableOptimisations::defaultOptimisations);
		if (crashes)
			*mightCrash = true;
		else
			*mightSurvive = true;
		if (!chooser.advance())
			break;
	}
}

class CrossEvalState {
public:
	StateMachineEdge *currentEdge;
	unsigned nextEdgeSideEffectIdx;
	bool finished;
	bool crashed;
	std::map<Int, IRExpr *> binders;
	CrossEvalState(StateMachineEdge *_e, int _i)
		: currentEdge(_e), nextEdgeSideEffectIdx(_i), finished(false),
		  crashed(false)
	{}
};

class CrossMachineEvalContext {
public:
	IRExpr *pathConstraint;
	std::vector<StateMachineSideEffectStore *> stores;
	CrossEvalState *states[2];
	std::vector<StateMachineSideEffect *> history;
	void advanceMachine(unsigned tid, NdChooser &chooser, Oracle *oracle);
	void dumpHistory(void) const;
};

void
CrossMachineEvalContext::dumpHistory(void) const
{
	for (std::vector<StateMachineSideEffect *>::const_iterator it = history.begin();
	     it != history.end();
	     it++) {
		printf("\t");
		(*it)->prettyPrint(stdout);
		printf("\n");
	}
}

void
CrossMachineEvalContext::advanceMachine(unsigned tid,
					NdChooser &chooser,
					Oracle *oracle)
{
	CrossEvalState *machine = states[tid];
	StateMachine *s;
top:
	if (machine->finished)
		return;
	if (machine->nextEdgeSideEffectIdx == machine->currentEdge->sideEffects.size()) {
		/* We've hit the end of the edge.  Move to the next
		 * state. */
		s = machine->currentEdge->target;
		assert(!dynamic_cast<StateMachineUnreached *>(s));
		if (dynamic_cast<StateMachineCrash *>(s)) {
			machine->finished = true;
			machine->crashed = true;
			return;
		}
		if (dynamic_cast<StateMachineNoCrash *>(s) ||
		    dynamic_cast<StateMachineStub *>(s)) {
			machine->finished = true;
			return;
		}
		if (StateMachineProxy *smp =
		    dynamic_cast<StateMachineProxy *>(s)) {
			machine->currentEdge = smp->target;
			machine->nextEdgeSideEffectIdx = 0;
			goto top;
		}
		if (StateMachineBifurcate *smb =
		    dynamic_cast<StateMachineBifurcate *>(s)) {
			if (expressionIsTrue(smb->condition, chooser, machine->binders, &pathConstraint))
				machine->currentEdge = smb->trueTarget;
			else
				machine->currentEdge = smb->falseTarget;
			machine->nextEdgeSideEffectIdx = 0;
			goto top;
		}
	}

	StateMachineSideEffect *se;
	se = machine->currentEdge->sideEffects[machine->nextEdgeSideEffectIdx];
	evalStateMachineSideEffect(se, chooser, oracle, machine->binders, stores, &pathConstraint);
	history.push_back(se);
	machine->nextEdgeSideEffectIdx++;

	/* You don't need to context switch after a copy, because
	   they're purely local. */
	if (dynamic_cast<StateMachineSideEffectCopy *>(se))
		goto top;
}

/* Run sm1 and sm2 in parallel, ***stopping as soon as sm1
 * terminates***.  Consider every possible interleaving of the
 * machines, and every possible aliasing pattern.  Set *mightSurvive
 * to true if any run caused sm1 to reach a NoCrash state, otherwise
 * set it to false; likewise *mightCrash for Crash states. */
static void
evalCrossProductMachine(StateMachine *sm1,
			StateMachine *sm2,
			Oracle *oracle,
			IRExpr *initialStateCondition,
			bool *mightSurvive,
			bool *mightCrash)
{
	NdChooser chooser;

	*mightSurvive = false;
	*mightCrash = false;

	StateMachineEdge *sme1 = new StateMachineEdge(sm1);
	StateMachineEdge *sme2 = new StateMachineEdge(sm2);
	while (!*mightCrash || !*mightSurvive) {
		CrossMachineEvalContext ctxt;
		assert(ctxt.stores.size() == 0);
		ctxt.pathConstraint = initialStateCondition;
		CrossEvalState s1(sme1, 0);
		CrossEvalState s2(sme2, 0);
		ctxt.states[0] = &s1;
		ctxt.states[1] = &s2;
		while (!s1.finished && !s2.finished)
			ctxt.advanceMachine(chooser.nd_choice(2),
					    chooser,
					    oracle);
		while (!s1.finished)
			ctxt.advanceMachine(0, chooser, oracle);
		if (s1.crashed) {
			if (!*mightCrash) {
				printf("First crashing history:\n");
				ctxt.dumpHistory();
			}
			*mightCrash = true;
		} else {
			if (!*mightSurvive) {
				printf("First surviving history:\n");
				ctxt.dumpHistory();
			}
			*mightSurvive = true;
		}
		if (!chooser.advance())
			break;
	}
}

/* Run the write machine, covering every possible schedule and
 * aliasing pattern.  After every store, run the read machine
 * atomically.  Find ranges of the store machine where the read
 * machine predicts a crash; these ranges are the remote macro
 * sections (as opposed to remote micro sections, which are just the
 * individual stores).  We assume that @assumption holds before
 * either machine starts running. */
/* Returns false if we discover something which suggests that this is
 * a bad choice of write machine, or true otherwise. */
static bool
findRemoteMacroSections(StateMachine *readMachine,
			StateMachine *writeMachine,
			IRExpr *assumption,
			Oracle *oracle,
			std::set<std::pair<StateMachineSideEffectStore *,
			                   StateMachineSideEffectStore *> > &output)
{
	NdChooser chooser;

	StateMachineEdge *writeStartEdge = new StateMachineEdge(writeMachine);
	do {
		std::vector<StateMachineSideEffectStore *> storesIssuedByWriter;
		std::map<Int, IRExpr *> writerBinders;
		StateMachineEdge *writerEdge;
		unsigned writeEdgeIdx;
		IRExpr *pathConstraint;
		StateMachineSideEffectStore *sectionStart;

		writeEdgeIdx = 0;
		pathConstraint = assumption;
		writerEdge = writeStartEdge;
		sectionStart = NULL;
		while (1) {
			/* Have we hit the end of the current writer edge? */
			if (writeEdgeIdx == writerEdge->sideEffects.size()) {
				/* Yes, move to the next state. */
				StateMachine *s = writerEdge->target;
				assert(!dynamic_cast<StateMachineUnreached *>(s));
				if (dynamic_cast<StateMachineCrash *>(s) ||
				    dynamic_cast<StateMachineNoCrash *>(s) ||
				    dynamic_cast<StateMachineStub *>(s)) {
					/* Hit the end of the writer
					 * -> we're done. */
					break;
				}
				if (StateMachineProxy *smp =
				    dynamic_cast<StateMachineProxy *>(s)) {
					writerEdge = smp->target;
					writeEdgeIdx = 0;
					continue;
				}
				StateMachineBifurcate *smb =
					dynamic_cast<StateMachineBifurcate *>(s);
				assert(smb);
				if (expressionIsTrue(smb->condition, chooser, writerBinders, &pathConstraint))
					writerEdge = smb->trueTarget;
				else
					writerEdge = smb->falseTarget;
				writeEdgeIdx = 0;
				continue;				
			}

			/* Advance the writer by one state.  Note that
			   we *don't* consider running the read before
			   any write states, as that's already been
			   handled and is known to lead to
			   no-crash. */
			StateMachineSideEffect *se;
			se = writerEdge->sideEffects[writeEdgeIdx];
			evalStateMachineSideEffect(se, chooser, oracle, writerBinders, storesIssuedByWriter, &pathConstraint);
			writeEdgeIdx++;

			/* Advance to a store */
			StateMachineSideEffectStore *smses =
				dynamic_cast<StateMachineSideEffectStore *>(se);
			if (!smses)
				continue;

			/* The writer just issued a store, so we
			   should now try running the reader
			   atomically.  We discard any stores issued
			   by the reader once it's finished, but we
			   need to track them while it's running, so
			   need a fresh eval ctxt and a fresh copy of
			   the stores list every time around the
			   loop. */
			StateMachineEvalContext readEvalCtxt;
			readEvalCtxt.pathConstraint = pathConstraint;
			readEvalCtxt.stores = storesIssuedByWriter;
			bool crashes;
			evalStateMachine(readMachine, &crashes, chooser, oracle, readEvalCtxt);
			if (crashes) {
				if (!sectionStart) {
					/* The previous attempt at
					   evaluating the read machine
					   didn't lead to a crash, so
					   this is the start of a
					   critical section. */
					sectionStart = smses;
				} else {
					/* Critical section
					 * continues. */
				}
			} else {
				if (sectionStart) {
					/* Previous attempt did crash
					   -> this is the end of the
					   section. */
					output.insert(std::pair<StateMachineSideEffectStore *,
						                StateMachineSideEffectStore *>(sectionStart, smses));
					sectionStart = NULL;
				}
			}
		}
		if (sectionStart) {
			/* We get a crash if we evaluate the read
			   machine after running the store machine to
			   completion -> this is a poor choice of
			   store machines. */
			return false;
		}
	} while (chooser.advance());
	return true;
}

/* Build up a static call graph which covers, at a minimum, all of the
 * RIPs included in the input set.  Functions in the graph are
 * represented by a combination of the set of RIPs in the function,
 * plus a set of functions which are statically called from that
 * function. */
/* Tail calls are a fairly major complication here.  If you see a call
 * to X, and another call to Y where Y tail calls into X, it would
 * naturally look like X and Y overlap, which confuses things.  In
 * that case, we have to split Y so that they no longer overlap.  If X
 * is discovered first then that's actually trivial (you just stop
 * exploring Y when you hit X's head), but if Y is discovered first
 * then it's quite messy.  We give up at that point, removing Y from
 * the known set, exploring X, and then re-exploring Y.
 */
/* There's also a bit of a bootstrapping problem.  We're given a bunch
 * of RIPs, but function heads to start from.  We start by picking a
 * RIP pretty much at random and assuming that it's a function head.
 * That mostly works reasonably well, even if it isn't, because we
 * effectively just cut off the part of the function before that
 * instruction.  The problem comes if there's another root instruction
 * in the same ``real'' function from which the speculative head is
 * reachable.  In that case, we'll insert a function boundary where
 * there isn't one (due to the tail-call elimination heuristic
 * discussed above), which can in turn lead to the introduction of
 * bogus recursion, which screws with the cycle breaking heuristic.
 * The fix for that is to purge the function which we derived from the
 * assumed head and continue.
 *
 * Note that this is pretty much the opposite to what we do if we
 * suspect a tail call, so we need to track whether a head is real
 * (obtained from following a call instruction) or assumed (obtained
 * directly from a root).  Note also that we *don't* purge the
 * functions which were obtained by tracing from the assumed head, as
 * the new subsuming head is guaranteed to find them again, and
 * this makes things a little bit quicker.
 */
class CallGraphEntry : public GarbageCollected<CallGraphEntry, &ir_heap> {
public:
	CallGraphEntry(unsigned long r)
		: headRip(r),
		  callees(new gc_pair_ulong_set_t()),
		  instructions(new RangeSet()),
		  calls(new gc_heap_map<unsigned long, CallGraphEntry, &ir_heap>::type())
	{}
	unsigned long headRip;
	bool isRealHead; /* Head is derived from a call instruction,
			    as opposed to one of the exploration
			    roots. */

	/* Pair of call instruction and callee address */
	gc_pair_ulong_set_t *callees;
	RangeSet *instructions;

	/* The same information as callees in a slightly different
	   format. */
	typedef gc_heap_map<unsigned long, CallGraphEntry, &ir_heap>::type calls_t;
	calls_t *calls;

	void visit(HeapVisitor &hv) {
		hv(instructions);
		hv(calls);
		hv(callees);
	}
	NAMED_CLASS
};
static unsigned long
getInstrLength(AddressSpace *as, unsigned long a)
{
	IRSB *irsb;
	try {
		irsb = as->getIRSBForAddress(0xabcde, a);
	} catch (BadMemoryException &e) {
		return 0;
	}
	assert(irsb != NULL);
	assert(irsb->stmts_used > 0);
	assert(irsb->stmts[0]->tag == Ist_IMark);
	return irsb->stmts[0]->Ist.IMark.len;
}
static CallGraphEntry *
exploreOneFunctionForCallGraph(unsigned long head, bool isRealHead,
			       RangeTree<CallGraphEntry> *instrsToCGEntries,
			       AddressSpace *as,
			       std::set<unsigned long> &realFunctionHeads)
{
	CallGraphEntry *cge;

	cge = new CallGraphEntry(head);
	cge->isRealHead = isRealHead;

	std::vector<unsigned long> unexploredInstrsThisFunction;
	unexploredInstrsThisFunction.push_back(head);
	unsigned long prev = head;
	while (!unexploredInstrsThisFunction.empty()) {
		unsigned long i = unexploredInstrsThisFunction.back();
		unexploredInstrsThisFunction.pop_back();

		if (cge->instructions->test(i)) {
			/* Done this instruction already -> move
			 * on. */
			continue;
		}
		if (i != head && realFunctionHeads.count(i)) {
			/* This is a tail call. */
			cge->callees->set(std::pair<unsigned long, unsigned long>(prev, i), true);
			continue;
		}
		CallGraphEntry *old = instrsToCGEntries->get(i);
		if (old) {
			assert(old != cge);
			assert(old->headRip != cge->headRip);
			if (old->isRealHead) {
				/* This is a tail call. */
				cge->callees->set(std::pair<unsigned long, unsigned long>(prev, i), true);
				continue;
			} else {
				/* We have a branch from the current
				   function to a previous assumed
				   function head.  That means that the
				   assumed function head wasn't
				   actually a function head at all.
				   Kill it. */
				instrsToCGEntries->purgeByValue(old);
				printf("Purge %lx for %lx\n", old->headRip, i);
			}
		}

		unsigned long end = i + getInstrLength(as, i);
		if (end == i) {
			/* Valgrind occasionally gets confused and
			   returns empty instructions.  Treat them as
			   single-byte ones for these purposes. */
			end = i + 1;
		}

		/* Add this instruction to the current function. */
		cge->instructions->set(i, end);
		instrsToCGEntries->set(i, end, cge);

		/* Where are we going next? */
		findInstrSuccessorsAndCallees(as, i, unexploredInstrsThisFunction,
					      cge->callees);
		prev = i;
	}
	return cge;
}
static unsigned
countReachableCGEs(CallGraphEntry *s)
{
	std::set<CallGraphEntry *> reachable;
	std::queue<CallGraphEntry *> toExplore;
	toExplore.push(s);
	while (!toExplore.empty()) {
		s = toExplore.front();
		toExplore.pop();
		if (reachable.count(s))
			continue;
		reachable.insert(s);
		for (gc_heap_map<unsigned long,CallGraphEntry,&ir_heap>::type::iterator it = s->calls->begin();
		     it != s->calls->end();
		     it++)
			toExplore.push(it.value());
	}
	return reachable.size();
}
static void
purgeCGFromCGESet(std::set<CallGraphEntry *> &s, CallGraphEntry *root)
{
	if (!s.count(root))
		return;
	s.erase(root);
	for (gc_heap_map<unsigned long, CallGraphEntry, &ir_heap>::type::iterator it = root->calls->begin();
	     it != root->calls->end();
	     it++)
		purgeCGFromCGESet(s, it.value());
}
static void
buildCallGraphForRipSet(AddressSpace *as, const std::set<unsigned long> &rips,
			std::set<CallGraphEntry *> &roots)
{
	std::set<unsigned long> unexploredRips(rips);
	RangeTree<CallGraphEntry> *instrsToCGEntries = new RangeTree<CallGraphEntry>();
	std::set<unsigned long> realFunctionHeads;

	while (!unexploredRips.empty()) {
		std::set<unsigned long>::iterator it = unexploredRips.begin();
		unsigned long head = *it;
		unexploredRips.erase(it);

		CallGraphEntry *cge;
		cge = instrsToCGEntries->get(head);
		if (cge) {
			/* We already have a function which contains
			   this instruction, so we're finished. */
			continue;			
		}

		/* Explore the current function, starting from this
		 * instruction. */
		cge = exploreOneFunctionForCallGraph(head, false, instrsToCGEntries, as, realFunctionHeads);
		assert(instrsToCGEntries->get(head) == cge);

		/* Now explore the functions which were called by that
		 * root. */
		/* Only really need the second half of the pair, but,
		   frankly, I can't be bothered to write all the
		   boiler plate for a C++ map operation. */
		gc_pair_ulong_set_t *unexploredRealHeads = new gc_pair_ulong_set_t(*cge->callees);
		while (!unexploredRealHeads->empty()) {
			gc_pair_ulong_set_t::iterator it = unexploredRealHeads->begin();
			unsigned long h = it.key().second;
			unexploredRealHeads->erase(it);

			realFunctionHeads.insert(h);

			CallGraphEntry *old = instrsToCGEntries->get(h);
			if (old) {
				/* Already have a CG node for this
				   instruction.  What kind of node? */
				if (!old->isRealHead) {
					/* It was an inferred head
					   from an earlier pass, so we
					   need to get rid of it. */
					printf("%lx was a pseudo-root; purge.\n", h);
					instrsToCGEntries->purgeByValue(old);
				} else if (old->headRip == h) {
					/* It's the head of an
					   existing function ->
					   everything is fine and we
					   don't need to do
					   anything. */
					continue;
				} else {
					/* Urk.  We previously saw a
					   tail call to this location,
					   and now we're seeing a real
					   call.  The result is that
					   we need to purge the old
					   call and introduce a new
					   one. */
					instrsToCGEntries->purgeByValue(old);
					/* Need to re-explore whatever
					   it was that tail-called
					   into this function. */
					unexploredRealHeads->set(std::pair<unsigned long, unsigned long>(0xf001dead, old->headRip), true);
				}
			}

			/* Now explore that function */
			cge = exploreOneFunctionForCallGraph(h, true,
							     instrsToCGEntries,
							     as,
							     realFunctionHeads);
			mergeUlongSets(unexploredRealHeads, cge->callees);
			assert(instrsToCGEntries->get(h) == cge);
		}
	}

	/* Build a set of all of the CGEs which still exist */
	std::set<CallGraphEntry *> allCGEs;
	for (RangeTree<CallGraphEntry>::iterator it = instrsToCGEntries->begin();
	     it != instrsToCGEntries->end();
	     it++) {
		assert(it->value);
		allCGEs.insert(it->value);
	}

	/* Figure out which call graph entries are actually
	 * interesting. */
	std::set<CallGraphEntry *> interesting;

	/* Anything which contains one of the root RIPs is
	 * automatically interesting. */
	for (std::set<unsigned long>::iterator it = rips.begin();
	     it != rips.end();
	     it++) {
		CallGraphEntry *i = instrsToCGEntries->get(*it);
		assert(i != NULL);
		interesting.insert(i);
	}
	/* Tarski iteration: anything which calls an interesting
	   function is itself interesting. */
	bool done_something;
	do {
		done_something = false;
		for (std::set<CallGraphEntry *>::iterator it = allCGEs.begin();
		     it != allCGEs.end();
		     it++) {
			if (interesting.count(*it))
				continue;
			for (gc_pair_ulong_set_t::iterator it2 = (*it)->callees->begin();
			     it2 != (*it)->callees->end();
			     it2++) {
				CallGraphEntry *callee = instrsToCGEntries->get(it2.key().second);
				if (interesting.count(callee)) {
					/* Uninteresting function
					   calling an interesting ->
					   not allowed.  Fix it. */
					interesting.insert(*it);
					done_something = true;
					break;
				}
			}
		}
	} while (done_something);

	/* Now strip anything which isn't interesting. */
	/* Strip the uninteresting entries from the allCGEs set.  At
	   the same time, remove them from the callee lists. */
	for (std::set<CallGraphEntry *>::iterator it = allCGEs.begin();
	     it != allCGEs.end();
		) {
		CallGraphEntry *cge = *it;
		if (!interesting.count(cge)) {
			allCGEs.erase(it++);
		} else {
			for (gc_pair_ulong_set_t::iterator it2 = cge->callees->begin();
			     it2 != cge->callees->end();
				) {
				if (!interesting.count(instrsToCGEntries->get(it2.key().second))) {
					it2 = cge->callees->erase(it2);
				} else {
					it2++;
				}
			}
			it++;
		}
	}
	/* And now drop them from the instructions map */
	for (RangeTree<CallGraphEntry>::iterator it = instrsToCGEntries->begin();
	     it != instrsToCGEntries->end();
		) {
		if (!interesting.count(it->value))
			it = instrsToCGEntries->erase(it);
		else
			it++;
	}

	/* Resolve any remaining edges into pointers. */
	for (std::set<CallGraphEntry *>::iterator it = allCGEs.begin();
	     it != allCGEs.end();
	     it++) {
		for (gc_pair_ulong_set_t::iterator it2 = (*it)->callees->begin();
		     it2 != (*it)->callees->end();
		     it2++) {
			CallGraphEntry *cge = instrsToCGEntries->get(it2.key().second);
			assert(cge != NULL);
			(*it)->calls->set(it2.key().first, cge);
		}
	}

	/* Build the root set. */
	while (!allCGEs.empty()) {
		/* Pick a new root.  If there's anything with no
		   parents, we make that our root. */
		CallGraphEntry *res = NULL;
		for (std::set<CallGraphEntry *>::iterator it = allCGEs.begin();
		     !res && it != allCGEs.end();
		     it++) {
			bool hasParent = false;
			for (std::set<CallGraphEntry *>::iterator it2 = allCGEs.begin();
			     !hasParent && it2 != allCGEs.end();
			     it2++) {
				if ( (*it2)->calls->hasKey( (*it)->headRip) )
					hasParent = true;
			}
			if (!hasParent)
				res = *it;
		}
		if (!res) {
			/* Okay, every node we have left has a parent.
			   That means that they're either in a cycle
			   or reachable from a cycle.  In that case,
			   we pick whichever node has the most
			   reachable nodes. */
			std::map<CallGraphEntry *, int> nrReachable;
			std::set<CallGraphEntry *> unexaminedCGEs(allCGEs);
			while (!unexaminedCGEs.empty()) {
				CallGraphEntry *t = *unexaminedCGEs.begin();
				unexaminedCGEs.erase(unexaminedCGEs.begin());
				nrReachable[t] = countReachableCGEs(t);
			}
			CallGraphEntry *best = NULL;
			for (std::map<CallGraphEntry *, int>::iterator it = nrReachable.begin();
			     it != nrReachable.end();
			     it++) {
				if (!best || it->second > nrReachable[best])
					best = it->first;
			}
			assert(best != NULL);
			res = best;
		}

		roots.insert(res);

		purgeCGFromCGESet(allCGEs, res);
	}
}

static void
printCallGraph(CallGraphEntry *root, FILE *f, std::set<CallGraphEntry *> &memo)
{
	if (memo.count(root))
		return;
	memo.insert(root);
	fprintf(f, "%p: %#lx%s {", root, root->headRip, root->isRealHead ? "" : " (fake)");
	for (RangeSet::iterator it = root->instructions->begin();
	     it != root->instructions->end();
	     it++)
		fprintf(f, "%#lx-%#lx, ", it->start, it->end1);
	fprintf(f, "} (");
	for (gc_heap_map<unsigned long, CallGraphEntry, &ir_heap>::type::iterator it = root->calls->begin();
	     it != root->calls->end();
	     it++)
		fprintf(f, "%#lx:%p; ", it.key(), it.value());
	fprintf(f, ")\n");
	for (gc_heap_map<unsigned long, CallGraphEntry, &ir_heap>::type::iterator it = root->calls->begin();
	     it != root->calls->end();
	     it++)
		printCallGraph(it.value(), f, memo);
}
static void
printCallGraph(CallGraphEntry *root, FILE *f)
{
	std::set<CallGraphEntry *> alreadyDone;
	printCallGraph(root, f, alreadyDone);
}

class StackRip {
public:
	unsigned long rip;
	std::vector<unsigned long> callStack;
	bool valid;
	StackRip(unsigned long _rip) : rip(_rip), valid(true) {}
	StackRip() : valid(false) {}

	StackRip jump(unsigned long r) {
		StackRip w(*this);
		w.rip = r;
		return w;
	}
	StackRip call(unsigned long target, unsigned long rtrn) {
		StackRip w(*this);
		w.callStack.push_back(rtrn);
		w.rip = target;
		return w;
	}
	StackRip rtrn(void) {
		StackRip w(*this);
		w.rip = w.callStack.back();
		w.callStack.pop_back();
		return w;
	}
};

static unsigned long
wrappedRipToRip(const StackRip &r)
{
	return r.rip;
}

static bool
instructionIsInteresting(const InstructionSet &i, const StackRip &r)
{
	return i.rips.count(r.rip) != 0;
}

static bool
operator<(const StackRip &a, const StackRip &b)
{
	if (!b.valid)
		return false;
	if (!a.valid)
		return true;
	if (a.rip < b.rip)
		return true;
	else if (a.rip > b.rip)
		return false;
	if (a.callStack.size() < b.callStack.size())
		return true;
	else if (a.callStack.size() > b.callStack.size())
		return false;
	for (unsigned x = 0; x < a.callStack.size(); x++)
		if (a.callStack[x] < b.callStack[x])
			return true;
		else if (a.callStack[x] > b.callStack[x])
			return false;
	return false;
}

static CFGNode<StackRip> *
buildCFGForCallGraph(AddressSpace *as,
		     CallGraphEntry *root)
{
	/* Build a map from instruction RIPs to CGEs. */
	std::set<CallGraphEntry *> explored;
	std::queue<CallGraphEntry *> toExplore;
	RangeTree<CallGraphEntry> *ripToCFGNode = new RangeTree<CallGraphEntry>();
	toExplore.push(root);
	while (!toExplore.empty()) {
		CallGraphEntry *cge = toExplore.front();
		toExplore.pop();
		if (explored.count(cge))
			continue;
		explored.insert(cge);
		for (RangeSet::iterator it = cge->instructions->begin();
		     it != cge->instructions->end();
		     it++) {
			ripToCFGNode->set(it->start, it->end1, cge);
		}
		for (CallGraphEntry::calls_t::iterator it = cge->calls->begin();
		     it != cge->calls->end();
		     it++)
			toExplore.push(it.value());
	}

	/* Now, starting from the head of the root node, work our way
	 * forwards and build up the state machine.  We identify
	 * instructions by a combination of the RIP and call stack,
	 * encapsulated as a StackRip; this effectively allows us to
	 * inline chosen functions. */
	std::map<StackRip, CFGNode<StackRip> *> builtSoFar;
	std::queue<StackRip> needed;

	needed.push(StackRip(root->headRip));
	while (!needed.empty()) {
		StackRip &r(needed.front());
		assert(ripToCFGNode->get(r.rip) != NULL);
		if (builtSoFar.count(r)) {
			needed.pop();
			continue;
		}
		CFGNode<StackRip> *work = new CFGNode<StackRip>(r);
		builtSoFar[r] = work;
		IRSB *irsb = as->getIRSBForAddress(-1, r.rip);
		int x;
		for (x = 1; x < irsb->stmts_used; x++) {
			if (irsb->stmts[x]->tag == Ist_IMark) {
				work->fallThroughRip = r.jump(irsb->stmts[x]->Ist.IMark.addr);
				break;
			}
			if (irsb->stmts[x]->tag == Ist_Exit) {
				assert(!work->branchRip.valid);
				work->branchRip = r.jump(irsb->stmts[x]->Ist.Exit.dst->Ico.U64);
				assert(work->branchRip.valid);
				needed.push(work->branchRip);
			}
		}
		if (x == irsb->stmts_used) {
			if (irsb->jumpkind == Ijk_Call) {
				if (ripToCFGNode->get(r.rip)->calls->hasKey(r.rip)) {
					/* We should inline this call. */
					work->fallThroughRip = r.call(
						ripToCFGNode->get(r.rip)->calls->get(r.rip)->headRip,
						extract_call_follower(irsb));
				} else {
					/* Skip over this call. */
					work->fallThroughRip = r.jump(extract_call_follower(irsb));
				}
			} else if (irsb->jumpkind == Ijk_Ret) {
				if (r.callStack.size() == 0) {
					/* End of the line. */
					work->accepting = true;
				} else {
					/* Return to calling function. */
					work->fallThroughRip = r.rtrn();
				}
			} else if (irsb->next->tag == Iex_Const) {
				work->fallThroughRip = r.jump(irsb->next->Iex.Const.con->Ico.U64);
			} else {
				/* Don't currently try to trace across indirect branches. */
			}
		}
		needed.pop();
		if (work->fallThroughRip.valid)
			needed.push(work->fallThroughRip);
	}

	/* We have now built all of the needed CFG nodes.  Resolve
	 * references. */
	for (std::map<StackRip, CFGNode<StackRip> *>::iterator it = builtSoFar.begin();
	     it != builtSoFar.end();
	     it++) {
		if (it->second->fallThroughRip.valid) {
			it->second->fallThrough = builtSoFar[it->second->fallThroughRip];
			assert(it->second->fallThrough);
		}
		if (it->second->branchRip.valid) {
			it->second->branch = builtSoFar[it->second->branchRip];
			assert(it->second->branch);
		}
	}

	/* All done */
	CFGNode<StackRip> *res = builtSoFar[StackRip(root->headRip)];
	assert(res != NULL);
	return res;
}

#define CRASHING_THREAD 73
#define STORING_THREAD 97

static void
considerStoreCFG(CFGNode<StackRip> *cfg, AddressSpace *as, Oracle *oracle,
		 IRExpr *assumption, StateMachine *probeMachine)
{
	StateMachine *sm = CFGtoStoreMachine(STORING_THREAD, as, cfg);

	AllowableOptimisations opt2 =
		AllowableOptimisations::defaultOptimisations
		.enableassumePrivateStack();
	bool done_something;
	do {
		done_something = false;
		sm = sm->optimise(opt2, oracle, &done_something);
	} while (done_something);
	sm = availExpressionAnalysis(sm, opt2, oracle);
	sm = bisimilarityReduction(sm, opt2);
	do {
		done_something = false;
		sm = sm->optimise(opt2, oracle, &done_something);
	} while (done_something);
	printf("Turns into state machine:\n");
	printStateMachine(sm, stdout);
	
	/* Now try running that in parallel with the probe machine,
	   and see if it might lead to a crash. */
	printf("Running cross-product machine...\n");
	bool mightSurvive;
	bool mightCrash;
	evalCrossProductMachine(probeMachine,
				sm,
				oracle,
				assumption,
				&mightSurvive,
				&mightCrash);
	printf("Run in parallel with the probe machine, might survive %d, might crash %d\n",
	       mightSurvive, mightCrash);
	
	/* We know that mightSurvive is true when the load machine is
	 * run atomically, so if mightSurvive is now false then that
	 * means that evalCrossProductMachine didn't consider that
	 * case, which is a bug. */
	assert(mightSurvive);

	if (!mightCrash) {
		/* Executing in parallel with this machine cannot lead
		 * to a crash, so there's no point in doing any more
		 * work with it. */
		return;
	}

	std::set<std::pair<StateMachineSideEffectStore *,
		StateMachineSideEffectStore *> >
		remoteMacroSections;
	if (!findRemoteMacroSections(probeMachine, sm, assumption, oracle, remoteMacroSections)) {
		printf("Chose a bad write machine...\n");
		return;
	}
	for (std::set<std::pair<StateMachineSideEffectStore *,
		     StateMachineSideEffectStore *> >::iterator it =
		     remoteMacroSections.begin();
	     it != remoteMacroSections.end();
	     it++) {
		printf("Remote macro section ");
		it->first->prettyPrint(stdout);
		printf(" -> ");
		it->second->prettyPrint(stdout);
		printf("\n");
	}
}

struct tag_hdr {
	int nr_loads;
	int nr_stores;
};

void
Oracle::loadTagTable(const char *path)
{

	FILE *f = fopen(path, "r");
	if (!f)
		err(1, "opening %s", path);
	while (!feof(f)) {
		struct tag_hdr hdr;
		if (fread(&hdr, sizeof(hdr), 1, f) < 1) {
			if (ferror(f)) 
				err(1, "reading %s", path);
			assert(feof(f));
			continue;
		}
		tag_entry t;
		for (int x = 0; x < hdr.nr_loads; x++) {
			unsigned long buf;
			if (fread(&buf, sizeof(buf), 1, f) != 1)
				err(1, "reading load address from %s", path);
			t.loads.insert(buf);
		}
		for (int x = 0; x < hdr.nr_stores; x++) {
			unsigned long buf;
			if (fread(&buf, sizeof(buf), 1, f) != 1)
				err(1, "reading load address from %s", path);
			t.stores.insert(buf);
		}
		tag_table.push_back(t);
	}
}

static bool
isBadAddress(IRExpr *e, const AllowableOptimisations &opt, Oracle *oracle)
{
	return e->tag == Iex_Const &&
		(long)e->Iex.Const.con->Ico.U64 < 4096;
}

static bool
definitelyUnevaluatable(IRExpr *e, const AllowableOptimisations &opt, Oracle *oracle)
{
	switch (e->tag) {
	case Iex_Binder:
	case Iex_Get:
	case Iex_RdTmp:
	case Iex_Const:
		return false;
	case Iex_GetI:
		return definitelyUnevaluatable(e->Iex.GetI.ix, opt, oracle);
	case Iex_Qop:
		if (definitelyUnevaluatable(e->Iex.Qop.arg4, opt, oracle))
			return true;
	case Iex_Triop:
		if (definitelyUnevaluatable(e->Iex.Qop.arg3, opt, oracle))
			return true;
	case Iex_Binop:
		if (definitelyUnevaluatable(e->Iex.Qop.arg2, opt, oracle))
			return true;
	case Iex_Unop:
		if (definitelyUnevaluatable(e->Iex.Qop.arg1, opt, oracle))
			return true;
		return false;
	case Iex_CCall:
		for (int x = 0; e->Iex.CCall.args[x]; x++)
			if (definitelyUnevaluatable(e->Iex.CCall.args[x], opt, oracle))
				return true;
		return false;
	case Iex_Mux0X:
		return definitelyUnevaluatable(e->Iex.Mux0X.cond, opt, oracle);
	case Iex_Associative:
		for (int x = 0; x < e->Iex.Associative.nr_arguments; x++)
			if (definitelyUnevaluatable(e->Iex.Associative.contents[x], opt, oracle))
				return true;
		return false;
	case Iex_Load:
		return isBadAddress(e->Iex.Load.addr, opt, oracle) ||
			definitelyUnevaluatable(e->Iex.Load.addr, opt, oracle);
	}
	abort();
}

int
main(int argc, char *argv[])
{
	if (argc <= 1)
		errx(1, "need at least one argument");

	init_sli();

	if (!strcmp(argv[1], "--check-sorter")) {
		sanity_check_irexpr_sorter();
		return 0;
	}
	if (!strcmp(argv[1], "--check-optimiser")) {
		sanity_check_optimiser();
		return 0;
	}

	VexPtr<MachineState> ms(MachineState::readCoredump(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(CRASHED_THREAD)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));

	VexPtr<CrashReason, &ir_heap> proximal(getProximalCause(ms, thr));
	if (!proximal)
		errx(1, "cannot get proximal cause of crash");
	proximal = backtrackToStartOfInstruction(CRASHING_THREAD, proximal, ms->addressSpace);

	VexPtr<InferredInformation> ii(new InferredInformation(oracle));
	ii->addCrashReason(proximal);

	std::vector<unsigned long> previousInstructions;
	oracle->findPreviousInstructions(previousInstructions);
	for (std::vector<unsigned long>::iterator it = previousInstructions.begin();
	     it != previousInstructions.end();
	     it++) {
		LibVEX_maybe_gc(ALLOW_GC);

		std::set<unsigned long> terminalFunctions;
		terminalFunctions.insert(0x757bf0);
		VexPtr<CFGNode<unsigned long>, &ir_heap> cfg(
			ii->CFGFromRip(*it, terminalFunctions));
		InstructionSet interesting;
		interesting.rips.insert(proximal->rip.rip);
		trimCFG(cfg.get(), interesting);
		breakCycles(cfg.get());

		VexPtr<CrashReason, &ir_heap> cr(
			ii->CFGtoCrashReason(CRASHING_THREAD, cfg));
		AllowableOptimisations opt =
			AllowableOptimisations::defaultOptimisations
			.enableassumePrivateStack()
			.enableignoreSideEffects();
		bool done_something;
		do {
			done_something = false;
			cr->sm = cr->sm->optimise(opt, oracle, &done_something);
		} while (done_something);
		cr->sm = availExpressionAnalysis(cr->sm, opt, oracle);
		cr->sm = bisimilarityReduction(cr->sm, opt);
		printf("Crash reason %s:\n", cr->rip.name());
		printStateMachine(cr->sm, stdout);

		printf("Survival constraint: \n");
		VexPtr<IRExpr, &ir_heap> survive;
		{
			VexPtr<StateMachine, &ir_heap> crSm(cr->sm);
			survive =
				optimiseIRExpr(
					survivalConstraintIfExecutedAtomically(crSm, oracle, ALLOW_GC),
					opt);
		}
		ppIRExpr(survive, stdout);
		printf("\n");

		/* Quick check that that vaguely worked.  If this
		   reports mightCrash == true then that probably means
		   that the theorem prover bits need more work.  If it
		   reports mightSurvive == false then the program is
		   doomed and it's not possible to fix it from this
		   point. */
		bool mightSurvive, mightCrash;
		{
			VexPtr<StateMachine, &ir_heap> crSm(cr->sm);
			evalMachineUnderAssumption(crSm, oracle, survive, &mightSurvive, &mightCrash, ALLOW_GC);
		}
		printf("Might survive: %d, might crash: %d\n", mightSurvive,
		       mightCrash);

		if (!mightSurvive)
			continue;
		if (mightCrash)
			printf("WARNING: Cannot determine any condition which will definitely ensure that we don't crash, even when executed atomically -> probably won't be able to fix this\n");

		std::set<StateMachineSideEffectLoad *> allLoads;
		findAllLoads(cr->sm, allLoads);
		std::set<unsigned long> potentiallyConflictingStores;
		for (std::set<StateMachineSideEffectLoad *>::iterator it = allLoads.begin();
		     it != allLoads.end();
		     it++)
			oracle->findConflictingStores(*it, potentiallyConflictingStores);
		std::set<InstructionSet> conflictClusters;
		oracle->clusterRips(potentiallyConflictingStores, conflictClusters);
		for (std::set<InstructionSet>::iterator it = conflictClusters.begin();
		     it != conflictClusters.end();
		     it++) {
			printf("Cluster:");
			for (std::set<unsigned long>::iterator it2 = it->rips.begin();
			     it2 != it->rips.end();
			     it2++)
				printf(" %lx", *it2);
			printf("\n");

			std::set<CallGraphEntry *> cgRoots;
			buildCallGraphForRipSet(ms->addressSpace, it->rips, cgRoots);
			for (std::set<CallGraphEntry *>::iterator it2 = cgRoots.begin();
			     it2 != cgRoots.end();
			     it2++) {
				printf("Possible call graph:\n");
				printCallGraph(*it2, stdout);

				CFGNode<StackRip> *storeCFG;
				storeCFG = buildCFGForCallGraph(ms->addressSpace, *it2);
				trimCFG(storeCFG, *it);
				breakCycles(storeCFG);

				considerStoreCFG(storeCFG, ms->addressSpace, oracle,
						 survive, cr->sm);
			}
		}
	}

	return 0;
}
