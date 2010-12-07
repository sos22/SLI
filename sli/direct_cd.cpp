/* Re-implementation of direct which tries to work off of just a core
   dump, rather than needing the full trace. */
#include <err.h>
#include <time.h>

#include <queue>
#include <map>
#include <set>

#include "sli.h"
#include "nd_chooser.h"

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
	void prettyPrint(void) const { prettyPrint(stdout); }
	virtual void prettyPrint(FILE *f) const = 0;
};

/* Perform simple peephole optimisation on the IRExpr.  The resulting
   expression is guaranteed to be equivalent to the old one in any
   context.  We may mutate the expression in-place, which is okay
   because there are no semantic changes. */
static IRExpr *optimiseIRExpr(IRExpr *e, const AllowableOptimisations &, IRExpr *assumption = NULL);

static void findUsedBinders(IRExpr *e, std::set<Int> &, const AllowableOptimisations &);

class StateMachine : public GarbageCollected<StateMachine>, public PrettyPrintable {
public:
	/* Another peephole optimiser.  Again, must be
	   context-independent and result in no changes to the
	   semantic value of the machine, and can mutate in-place. */
	virtual StateMachine *optimise(const AllowableOptimisations &, Oracle *) = 0;
	virtual void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) = 0;
	virtual void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) = 0;
	NAMED_CLASS
};

class StateMachineSideEffect : public GarbageCollected<StateMachineSideEffect>, public PrettyPrintable {
public:
	virtual void optimise(const AllowableOptimisations &, Oracle *) = 0;
	virtual void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) = 0;
	virtual void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) = 0;
	NAMED_CLASS
};

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
	void optimise(const AllowableOptimisations &opt, Oracle *) {
		addr = optimiseIRExpr(addr, opt);
		data = optimiseIRExpr(data, opt);
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
public:
	StateMachineSideEffectLoad(IRExpr *_addr, unsigned long _rip)
		: addr(_addr), rip(_rip)
	{
		key = next_key++;
	}
	StateMachineSideEffectLoad(Int k, IRExpr *_addr, unsigned long _rip)
		: key(k), addr(_addr), rip(_rip)
	{
	}
	Int key;
	IRExpr *addr;
	unsigned long rip;
	void prettyPrint(FILE *f) const {
		fprintf(f, "B%d <- *(", key);
		ppIRExpr(addr, f);
		fprintf(f, ")@%lx", rip);
	}
	void visit(HeapVisitor &hv) {
		hv(addr);
	}
	void optimise(const AllowableOptimisations &opt, Oracle *) {
		addr = optimiseIRExpr(addr, opt);
	}
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {
		l.insert(addr);
	}
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt) {
		s.erase(key);
		::findUsedBinders(addr, s, opt);
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
	void optimise(const AllowableOptimisations &opt, Oracle *) {
		value = optimiseIRExpr(value, opt);
	}
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) { }
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt) {
		s.erase(key);
		::findUsedBinders(value, s, opt);
	}
};

class StateMachineEdge : public GarbageCollected<StateMachineEdge>, public PrettyPrintable {
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
	StateMachineEdge *optimise(const AllowableOptimisations &, Oracle *);
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

class StateMachineCrash : public StateMachine {
	StateMachineCrash() {}
	static VexPtr<StateMachineCrash> _this;
public:
	static StateMachineCrash *get() {
		if (!_this) _this = new StateMachineCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<crash>"); }
	StateMachine *optimise(const AllowableOptimisations &, Oracle *) { return this; }
	void visit(HeapVisitor &hv) {}
	void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) {}
};
VexPtr<StateMachineCrash> StateMachineCrash::_this;

class StateMachineNoCrash : public StateMachine {
	StateMachineNoCrash() {}
	static VexPtr<StateMachineNoCrash> _this;
public:
	static StateMachineNoCrash *get() {
		if (!_this) _this = new StateMachineNoCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<survive>"); }
	StateMachine *optimise(const AllowableOptimisations &, Oracle *) { return this; }
	void visit(HeapVisitor &hv) {}
	void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) {}
};
VexPtr<StateMachineNoCrash> StateMachineNoCrash::_this;

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
	StateMachine *optimise(const AllowableOptimisations &opt, Oracle *oracle)
	{
		condition = optimiseIRExpr(condition, opt);
		trueTarget = trueTarget->optimise(opt, oracle);
		falseTarget = falseTarget->optimise(opt, oracle);
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
	StateMachine *optimise(const AllowableOptimisations &opt, Oracle *oracle)
	{
		if (target->sideEffects.size() == 0)
			return target->target->optimise(opt, oracle);
		target = target->optimise(opt, oracle);
		return this;
	}
	void findLoadedAddresses(std::set<IRExpr *> &s, const AllowableOptimisations &opt) {
		target->findLoadedAddresses(s, opt);
	}
	void findUsedBinders(std::set<Int> &s, const AllowableOptimisations &opt) {
		target->findUsedBinders(s, opt);
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
	StateMachine *optimise(const AllowableOptimisations &, Oracle *) { return this; }
	void findLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void findUsedBinders(std::set<Int> &, const AllowableOptimisations &) { }
};

/* All of the information from sources other than the main crash dump.
 * Information from the oracle will be true of some executions but not
 * necessarily all of them, so should only really be used where static
 * analysis is insufficient. */
class Oracle : public GarbageCollected<Oracle> {
public:
	MachineState *ms;
	Thread *crashedThread;

	void findPreviousInstructions(std::vector<unsigned long> &output);
	void findConflictingStores(StateMachineSideEffectLoad *smsel,
				   std::set<unsigned long> &out);
	void clusterRips(const std::set<unsigned long> &inputRips,
			 std::set<std::set<unsigned long> > &outputClusters);
	bool storeIsThreadLocal(StateMachineSideEffectStore *s);
	bool memoryAccessesMightAlias(StateMachineSideEffectLoad *, StateMachineSideEffectStore *);

	Oracle(MachineState *_ms, Thread *_thr)
		: ms(_ms), crashedThread(_thr)
	{
	}
	void visit(HeapVisitor &hv) {
		hv(ms);
		hv(crashedThread);
	}
	NAMED_CLASS
};

StateMachineEdge *
StateMachineEdge::optimise(const AllowableOptimisations &opt,
			   Oracle *oracle)
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
		return sme->optimise(opt, oracle);
	}
	target = target->optimise(opt, oracle);

	std::vector<StateMachineSideEffect *>::iterator it;

	for (it = sideEffects.begin(); it != sideEffects.end(); it++)
		(*it)->optimise(opt, oracle);

	/* Try to forward stuff from stores to loads wherever
	   possible.  We don't currently do this inter-state, because
	   that's moderately tricky. */
	if (opt.assumeExecutesAtomically) {
		std::set<std::pair<IRExpr *, IRExpr *> > availExpressions;
		for (it = sideEffects.begin(); it != sideEffects.end(); it++) {
			if (StateMachineSideEffectStore *smses =
			    dynamic_cast<StateMachineSideEffectStore *>(*it)) {
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
					if (definitelyEqual(it2->first, smsel->addr, opt)) {
						*it = new StateMachineSideEffectCopy(smsel->key,
										     it2->second);
						break;
					}
				}			
			} else {
				assert(dynamic_cast<StateMachineSideEffectCopy *>(*it));
			}
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
		(*it)->optimise(opt, oracle);
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
	bool operator<(const VexRip &a) const {
		return rip < a.rip || (rip == a.rip && idx < a.idx);
	}
	bool operator==(const VexRip &a) const {
		return rip == a.rip && idx == a.idx;
	}
};

class CrashReason : public GarbageCollected<CrashReason>,
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

	/* Don't really understand why this is necessary... */
	void prettyPrint() const { PrettyPrintable::prettyPrint(); }

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
		irsb = ms->addressSpace->getIRSBForAddress(rip);
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
	} else {
		return NULL;
	}
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
	virtual IRExpr *transformIRExpr(IRExpr *e);

	virtual IRExpr *transformIexGet(IRExpr *e) { return e; }
	virtual IRExpr *transformIexGetI(IRExpr *e)
	{
		return IRExpr_GetI(e->Iex.GetI.descr,
				   transformIRExpr(e->Iex.GetI.ix),
				   e->Iex.GetI.bias);
	}
	virtual IRExpr *transformIexRdTmp(IRExpr *e) { return e; }
	virtual IRExpr *transformIexQop(IRExpr *e)
	{
		return IRExpr_Qop(e->Iex.Qop.op,
				  transformIRExpr(e->Iex.Qop.arg1),
				  transformIRExpr(e->Iex.Qop.arg2),
				  transformIRExpr(e->Iex.Qop.arg3),
				  transformIRExpr(e->Iex.Qop.arg4));
	}
	virtual IRExpr *transformIexTriop(IRExpr *e)
	{
		return IRExpr_Triop(e->Iex.Triop.op,
				    transformIRExpr(e->Iex.Triop.arg1),
				    transformIRExpr(e->Iex.Triop.arg2),
				    transformIRExpr(e->Iex.Triop.arg3));
	}
	virtual IRExpr *transformIexBinop(IRExpr *e)
	{
		return IRExpr_Binop(e->Iex.Binop.op,
				    transformIRExpr(e->Iex.Binop.arg1),
				    transformIRExpr(e->Iex.Binop.arg2));
	}
	virtual IRExpr *transformIexUnop(IRExpr *e)
	{
		return IRExpr_Unop(e->Iex.Unop.op,
				   transformIRExpr(e->Iex.Unop.arg));
	}
	virtual IRExpr *transformIexLoad(IRExpr *e)
	{
		return IRExpr_Load(e->Iex.Load.isLL,
				   e->Iex.Load.end,
				   e->Iex.Load.ty,
				   transformIRExpr(e->Iex.Load.addr));
	}
	virtual IRExpr *transformIexConst(IRExpr *e)
	{
		return e;
	}
	virtual IRExpr *transformIexMux0X(IRExpr *e)
	{
		return IRExpr_Mux0X(
			transformIRExpr(e->Iex.Mux0X.cond),
			transformIRExpr(e->Iex.Mux0X.expr0),
			transformIRExpr(e->Iex.Mux0X.exprX));
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
	} else if (StateMachineBifurcate *smb =
		   dynamic_cast<StateMachineBifurcate *>(inp)) {
		StateMachineEdge *t = doit(smb->trueTarget);
		StateMachineEdge *f = doit(smb->falseTarget);
		IRExpr *cond = transformIRExpr(smb->condition);
		out = new StateMachineBifurcate(cond, t, f);
	} else if (StateMachineProxy *smp =
		   dynamic_cast<StateMachineProxy *>(inp)) {
		StateMachineEdge *t = doit(smp->target);
		out = new StateMachineProxy(t);
	} else if (StateMachineStub *sms =
		   dynamic_cast<StateMachineStub *>(inp)) {
		IRExpr *target = transformIRExpr(sms->target);
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
	for (std::vector<StateMachineSideEffect *>::iterator it = inp->sideEffects.begin();
	     it != inp->sideEffects.end();
	     it++) {
		if (StateMachineSideEffectStore *smses =
		    dynamic_cast<StateMachineSideEffectStore *>(*it)) {
			res->sideEffects.push_back(
				new StateMachineSideEffectStore(
					transformIRExpr(smses->addr),
					transformIRExpr(smses->data),
					smses->rip));
		} else if (StateMachineSideEffectLoad *smsel =
			   dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			res->sideEffects.push_back(
				new StateMachineSideEffectLoad(
					smsel->key,
					transformIRExpr(smsel->addr),
					smsel->rip));
		} else if (StateMachineSideEffectCopy *smsec =
			   dynamic_cast<StateMachineSideEffectCopy *>(*it)) {
			res->sideEffects.push_back(
				new StateMachineSideEffectCopy(
					smsec->key,
					transformIRExpr(smsec->value)));
		} else {
			abort();
		}
	}
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

	for (nr_args = 0; e->Iex.CCall.args[nr_args]; nr_args++)
		;
	newArgs = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_args + 1);
	for (x = 0; x < nr_args; x++)
		newArgs[x] = transformIRExpr(e->Iex.CCall.args[x]);
	newArgs[nr_args] = NULL;
	return IRExpr_CCall(e->Iex.CCall.cee,
			    e->Iex.CCall.retty,
			    newArgs);
}

IRExpr *
StateMachineTransformer::transformIexAssociative(IRExpr *e)
{
	IRExpr *r = IRExpr_Associative(e);
	for (int x = 0; x < r->Iex.Associative.nr_arguments; x++)
		r->Iex.Associative.contents[x] =
			transformIRExpr(r->Iex.Associative.contents[x]);
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
backtrackToStartOfInstruction(CrashReason *cr, AddressSpace *as)
{
	IRSB *irsb = as->getIRSBForAddress(cr->rip.rip);
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

class CFGNode : public GarbageCollected<CFGNode>, public PrettyPrintable {
public:
	unsigned long fallThroughRip;
	unsigned long branchRip;
	CFGNode *fallThrough;
	CFGNode *branch;

	unsigned long my_rip;

	CFGNode(unsigned long rip) : my_rip(rip) {}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%#lx: %#lx(%p), %#lx(%p)",
			my_rip, fallThroughRip, fallThrough,
			branchRip, branch);
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
	std::map<VexRip, CrashReason *> crashReasons;

	InferredInformation(Oracle *_oracle) : oracle(_oracle) {}
	void addCrashReason(CrashReason *cr) { crashReasons[cr->rip] = cr; }
	CFGNode *CFGFromRip(unsigned long rip);
	CrashReason *CFGtoCrashReason(CFGNode *cfg);

	void visit(HeapVisitor &hv) {
		hv(oracle);
		for (std::map<VexRip, CrashReason *>::iterator it =
			     crashReasons.begin();
		     it != crashReasons.end();
		     it++)
			hv(it->second);
	}
	NAMED_CLASS
};

static void
enumerateReachableStates(CFGNode *from, std::set<CFGNode *> &out)
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
		  std::set<CFGNode *> &output)
{
	std::map<unsigned long, CFGNode *> builtSoFar;
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
		IRSB *irsb = as->getIRSBForAddress(rip);
		CFGNode *work = new CFGNode(rip);
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
				needed.push_back(work->fallThroughRip);
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
	for (std::map<unsigned long, CFGNode *>::iterator it = builtSoFar.begin();
	     it != builtSoFar.end();
	     it++) {
		if (it->second) {
			it->second->fallThrough = builtSoFar[it->second->fallThroughRip];
			it->second->branch = builtSoFar[it->second->branchRip];
		}
	}

	/* Extract the start states.  These will be some subset of the
	   input root nodes. */
	std::set<CFGNode *> outputSoFar;
	for (std::set<unsigned long>::const_iterator it = rips.begin();
	     it != rips.end();
	     it++) {
		CFGNode *startnode = builtSoFar[*it];
		if (outputSoFar.count(startnode))
			continue;
		output.insert(startnode);

		enumerateReachableStates(startnode, outputSoFar);
	}
}

/* Special case of buildCFGForRipSet() when you only have one entry
 * RIP */
CFGNode *
InferredInformation::CFGFromRip(unsigned long start)
{
	std::set<unsigned long> rips;
	std::set<CFGNode *> out;
	rips.insert(start);
	buildCFGForRipSet(oracle->ms->addressSpace, rips, out);
	if (out.size() == 0)
		return NULL;
	assert(out.size() == 1);
	return *out.begin();
}

CrashReason *
InferredInformation::CFGtoCrashReason(CFGNode *cfg)
{
	VexRip finalRip(cfg->my_rip, 0);
	if (crashReasons.count(finalRip)) {
		assert(crashReasons[finalRip]);
		return crashReasons[finalRip];
	}
	CrashReason *res;
	if (!cfg->branch && !cfg->fallThrough) {
		res = new CrashReason(finalRip, StateMachineNoCrash::get());
	} else {
		IRSB *irsb = oracle->ms->addressSpace->getIRSBForAddress(finalRip.rip);
		int x;
		for (x = 1; x < irsb->stmts_used; x++)
			if (irsb->stmts[x]->tag == Ist_IMark)
				break;
		if (cfg->fallThrough) {
			CrashReason *ft = CFGtoCrashReason(cfg->fallThrough);

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
								CFGtoCrashReason(cfg->branch)->sm,
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
			res = ft;
		} else {
			assert(cfg->branch);
			CrashReason *b = CFGtoCrashReason(cfg->branch);
			for (; x >= 0; x--)
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
	crashReasons[finalRip] = res;
	return res;
}

static void
printCFG(const CFGNode *cfg)
{
	std::vector<const CFGNode *> pending;
	std::set<const CFGNode *> done;

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

/* Try to find the RIPs of some stores which might conceivably have
   interfered with the observed load.  Stack accesses are not tracked
   by this mechanism. */
/* We do this using a profiling-based scheme.  There's some initial
   training phase during which we log, for every memory location, the
   set of loads and stores which access it, and we then just return
   the union of the store sets for all the locations whose load set
   includes the observed address. */
/* XXX or we will do, eventually.  For now just hard-code a few known
   values. */
void
Oracle::findConflictingStores(StateMachineSideEffectLoad *smsel,
			      std::set<unsigned long> &out)
{
#warning Do this properly
	switch (smsel->rip) {
	case 0x40063a: /* Load of gcc_s_forcedunwind */
	case 0x400661:
		out.insert(0x400656);
		out.insert(0x4006fc);
		break;
	case 0x40064c: /* Load of done_init */
		out.insert(0x40066c);
		out.insert(0x4006f2);
		break;
	case 0x400645: /* stack access */
	case 0x400676:
		break;
	default:
		abort();
	}
}

/* Try to guess whether this store might ever be consumed by another
   thread.  We approximate this by saying that anything not included
   in our database of dynamic information is thread-local. */
bool
Oracle::storeIsThreadLocal(StateMachineSideEffectStore *s)
{
#warning Do this properly as well.
	switch (s->rip) {
	case 0x400656:
	case 0x40066c:
	case 0x4006fc:
	case 0x4006f2:
	case 0x4006ec:
		return false;
	case 0x400668:
	case 0x40070c:
	case 0x400711:
	case 0x40071b:
		return true;
	default:
		abort();
	}
}

bool
Oracle::memoryAccessesMightAlias(StateMachineSideEffectLoad *smsel,
				 StateMachineSideEffectStore *smses)
{
	switch (smsel->rip) {
	case 0x400676:
	case 0x400645:
		return true;
	case 0x400661:
	case 0x40063a:
		switch (smses->rip) {
		case 0x400656:
		case 0x4006fc:
			return true;
		case 0x400632:
		case 0x400641:
			return false;
		default:
			abort();
		}
	case 0x40064c:
		switch (smses->rip) {
		case 0x40066c:
		case 0x4006f2:
			return true;
		case 0x400641:
		case 0x400632:
			return false;
		default:
			abort();
		}
		abort();
	default:
		abort();
	}
}

static void
enumerateCFG(CFGNode *root, std::map<unsigned long, CFGNode *> &rips)
{
	if (!root)
		return;
	if (rips.count(root->my_rip))
		return;
	rips[root->my_rip] = root;
	enumerateCFG(root->branch, rips);
	enumerateCFG(root->fallThrough, rips);
}

/* Remove all of the nodes which appear to be uninteresting.  A node
   is uninteresting if it is not in the initial interesting set and
   there are no paths from it to an interesting node. */
static void
trimCFG(CFGNode *root, std::set<unsigned long> interestingAddresses)
{
	std::map<unsigned long, CFGNode *> uninteresting;
	std::map<unsigned long, CFGNode *> interesting;
	/* Start on the assumption that everything is uninteresting. */
	enumerateCFG(root, uninteresting);
	/* addresses which are explicitly flagged as interesting are
	   not uninteresting. */
	for (std::set<unsigned long>::iterator it = interestingAddresses.begin();
	     it != interestingAddresses.end();
	     it++) {
		assert(uninteresting[*it]);
		interesting[*it] = uninteresting[*it];
		uninteresting.erase(*it);
	}

	/* Tarski iteration */
	bool progress;
	do {
		progress = false;
		for (std::map<unsigned long, CFGNode *>::iterator it = uninteresting.begin();
		     it != uninteresting.end();
			) {
			CFGNode *n = it->second;
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
	for (std::map<unsigned long, CFGNode *>::iterator it = interesting.begin();
	     it != interesting.end();
	     it++) {
		CFGNode *n = it->second;
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
static bool
breakCycles(CFGNode *cfg, std::map<CFGNode *, unsigned> &numbering,
	    CFGNode **lastBackEdge, std::set<CFGNode *> &onPath)
{
	if (onPath.count(cfg)) {
		/* We have a cycle.  Break it. */
		assert(lastBackEdge);
		*lastBackEdge = NULL;
		return false;
	}

	onPath.insert(cfg);
	if (cfg->branch) {
		CFGNode **p = lastBackEdge;
		if (numbering[cfg->branch] < numbering[cfg])
			p = &cfg->branch;
		if (!breakCycles(cfg->branch, numbering, p, onPath))
			return false;
	}
	if (cfg->fallThrough) {
		CFGNode **p = lastBackEdge;
		if (numbering[cfg->fallThrough] < numbering[cfg])
			p = &cfg->fallThrough;
		if (!breakCycles(cfg->fallThrough, numbering, p, onPath))
			return false;
	}

	onPath.erase(cfg);

	return true;
}

/* We use a breadth first search to number the nodes and then use a
   variant of Tarjan's algorithm to detect cycles.  When we detect a
   cycle, we use the numbering scheme to identify a back edge and
   eliminate it. */
static void
breakCycles(CFGNode *cfg)
{
	std::map<CFGNode *, unsigned> numbering;
	std::queue<CFGNode *> queue;
	CFGNode *t;

	/* Assign numbering */
	unsigned idx;
	idx = 0;
	queue.push(cfg);
	while (!queue.empty()) {
		t = queue.front();
		queue.pop();
		if (numbering.count(t))
			continue;
		numbering[t] = idx;
		idx++;
		if (t->branch)
			queue.push(t->branch);
		if (t->fallThrough)
			queue.push(t->fallThrough);
	}

	std::set<CFGNode *> visited;
	while (!breakCycles(cfg, numbering, NULL, visited))
		visited.clear();
}

/* Returns true if the operation definitely commutes, or false if
 * we're not sure. */
static bool
operationCommutes(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) ||
		(op >= Iop_CmpEQ8 && op <= Iop_CmpEQ64) ||
		(op == Iop_And1);
}

/* Returns true if the operation definitely associates in the sense
 * that (a op b) op c == a op (b op c), or false if we're not sure. */
static bool
operationAssociates(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) || (op == Iop_And1) ||
		(op >= Iop_And8 && op <= Iop_And64);
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
			LibVEX_realloc(&main_heap,
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
optimiseIRExpr(IRExpr *src, const AllowableOptimisations &opt, IRExpr *assumption)
{
	/* First, recursively optimise our arguments. */
	switch (src->tag) {
	case Iex_Qop:
		src->Iex.Qop.arg4 = optimiseIRExpr(src->Iex.Qop.arg4, opt, assumption);
	case Iex_Triop:
		src->Iex.Triop.arg3 = optimiseIRExpr(src->Iex.Triop.arg3, opt, assumption);
	case Iex_Binop:
		src->Iex.Binop.arg2 = optimiseIRExpr(src->Iex.Binop.arg2, opt, assumption);
	case Iex_Unop:
		src->Iex.Unop.arg = optimiseIRExpr(src->Iex.Unop.arg, opt, assumption);
		break;
	case Iex_Load:
		src->Iex.Load.addr = optimiseIRExpr(src->Iex.Load.addr, opt, assumption);
		break;
	case Iex_CCall: {
		for (int x = 0; src->Iex.CCall.args[x]; x++) {
			src->Iex.CCall.args[x] =
				optimiseIRExpr(src->Iex.CCall.args[x], opt, assumption);
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
			if (e)
				src = e;
		}
		break;
	}
	case Iex_Mux0X:
		src->Iex.Mux0X.cond = optimiseIRExpr(src->Iex.Mux0X.cond, opt, assumption);
		src->Iex.Mux0X.expr0 = optimiseIRExpr(src->Iex.Mux0X.expr0, opt, assumption);
		src->Iex.Mux0X.exprX = optimiseIRExpr(src->Iex.Mux0X.exprX, opt, assumption);
		break;
	case Iex_Associative:
		for (int x = 0; x < src->Iex.Associative.nr_arguments; x++)
			src->Iex.Associative.contents[x] =
				optimiseIRExpr(src->Iex.Associative.contents[x], opt, assumption);
		break;
	default:
		break;
	}

	if (assumption && definitelyEqual(src, assumption, opt))
		return IRExpr_Const(IRConst_U1(1));

	if (src->tag == Iex_Associative) {
		/* Drag up nested associatives. */
		bool haveNestedAssocs = false;
		for (int x = 0; !haveNestedAssocs && x < src->Iex.Associative.nr_arguments; x++)
			if (src->Iex.Associative.contents[x]->tag == Iex_Associative)
				haveNestedAssocs = true;
		if (haveNestedAssocs) {
			IRExpr *e = IRExpr_Associative(src->Iex.Associative.op, NULL);
			for (int x = 0; x < src->Iex.Associative.nr_arguments; x++) {
				IRExpr *arg = src->Iex.Associative.contents[x];
				if (arg->tag == Iex_Associative) {
					for (int y = 0; y < arg->Iex.Associative.nr_arguments; y++)
						addArgumentToAssoc(e, arg->Iex.Associative.contents[y]);
				} else {
					addArgumentToAssoc(e, arg);
				}
			}
			src = e;
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
				default:
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
				}
			}
		}
		/* Some special cases for And1: 1 & x -> x, 0 & x -> 0 */
		if (src->Iex.Associative.op == Iop_And1) {
			/* If there are any constants, they'll be at the start. */
			while (src->Iex.Associative.nr_arguments > 1 &&
			       src->Iex.Associative.contents[0]->tag == Iex_Const) {
				IRConst *c = src->Iex.Associative.contents[0]->Iex.Const.con;
				if (c->Ico.U1) {
					purgeAssocArgument(src, 0);
				} else {
					return src->Iex.Associative.contents[0];
				}
			}
			
			/* Also: in x & y, when optimising y, you can
			   assume that y is true. */
			for (int it1 = 0;
			     it1 < src->Iex.Associative.nr_arguments;
			     it1++) {
				for (int it2 = it1 + 1;
				     it2 < src->Iex.Associative.nr_arguments;
				     it2++)
					src->Iex.Associative.contents[it2] =
						optimiseIRExpr(src->Iex.Associative.contents[it2],
							       opt,
							       src->Iex.Associative.contents[it1]);
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
						purgeAssocArgument(src, it2);
					} else {
						it2++;
					}
				}
			}
		}

		/* x + -x -> 0, for any plus-like operator, so remove
		 * both x and -x from the list. */
		/* Also do x & ~x -> 0, while we're here. */
		if (opt.xPlusMinusX) {
			bool plus_like;
			bool and_like;
			plus_like = src->Iex.Associative.op >= Iop_Add8 && src->Iex.Associative.op <= Iop_Add64;
			and_like = (src->Iex.Associative.op >= Iop_And8 && src->Iex.Associative.op <= Iop_And64) ||
				src->Iex.Associative.op == Iop_And1;
			if (plus_like || and_like) {
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
						if (r->tag == Iex_Unop &&
						    ((plus_like &&
						      r->Iex.Unop.op >= Iop_Neg8 &&
						      r->Iex.Unop.op <= Iop_Neg64) ||
						     (and_like &&
						      ((r->Iex.Unop.op >= Iop_Not8 &&
							r->Iex.Unop.op <= Iop_Not64) ||
						       r->Iex.Unop.op == Iop_Not1))) &&
						    definitelyEqual(l, r->Iex.Unop.arg, opt.disablexPlusMinusX())) {
							/* Careful: do the largest index first so that the
							   other index remains valid. */
							if (it1 < it2) {
								purgeAssocArgument(src, it2);
								purgeAssocArgument(src, it1);
							} else {
								purgeAssocArgument(src, it1);
								purgeAssocArgument(src, it2);
							}
							break;
						}
					}
					if (it2 == src->Iex.Associative.nr_arguments)
						it1++;
				}
			}
			if (src->Iex.Associative.nr_arguments == 0) {
				switch (src->Iex.Associative.op) {
				case Iop_And1:
					return IRExpr_Const(IRConst_U1(0));
				case Iop_Add8:
				case Iop_And8:
					return IRExpr_Const(IRConst_U8(0));
				case Iop_Add16:
				case Iop_And16:
					return IRExpr_Const(IRConst_U16(0));
				case Iop_Add32:
				case Iop_And32:
					return IRExpr_Const(IRConst_U32(0));
				case Iop_Add64:
				case Iop_And64:
					return IRExpr_Const(IRConst_U64(0));
				default:
					abort();
				}
			}
		}
		/* If the size is reduced to one, eliminate the assoc list */
		if (src->Iex.Associative.nr_arguments == 1)
			return src->Iex.Associative.contents[0];
	}

	/* Now use some special rules to simplify a few classes of binops and unops. */
	if (src->tag == Iex_Unop) {
		if (src->Iex.Unop.op == Iop_64to1 &&
		    src->Iex.Unop.arg->tag == Iex_Binop &&
		    src->Iex.Unop.arg->Iex.Binop.op == Iop_CmpEQ64) {
			/* This can happen sometimes because of the
			   way we simplify condition codes.  Very easy
			   fix: strip off the outer 64to1. */
			return src->Iex.Unop.arg;
		}

		if (src->Iex.Unop.op >= Iop_8Uto16 &&
		    src->Iex.Unop.op <= Iop_32Uto64 &&
		    src->Iex.Unop.arg->tag == Iex_Binder) {
			/* Binders don't have any type information, so
			   trying to upcast them is a bit silly.
			   Don't do this for signed upcasts, though,
			   as they have effects beyond the type
			   level. */
			return src->Iex.Unop.arg;
		}

		if (src->Iex.Unop.arg->tag == Iex_Const) {
			IRConst *c = src->Iex.Unop.arg->Iex.Const.con;
			switch (src->Iex.Unop.op) {
			case Iop_Neg8:
				return IRExpr_Const(IRConst_U8(-c->Ico.U8));
			case Iop_Neg16:
				return IRExpr_Const(IRConst_U16(-c->Ico.U16));
			case Iop_Neg32:
				return IRExpr_Const(IRConst_U32(-c->Ico.U32));
			case Iop_Neg64:
				return IRExpr_Const(IRConst_U64(-c->Ico.U64));
			case Iop_Not1:
				return IRExpr_Const(IRConst_U1(c->Ico.U1 ^ 1));
			default:
				break;
			}
		}
	} else if (src->tag == Iex_Binop) {
		IRExpr *l = src->Iex.Binop.arg1;
		IRExpr *r = src->Iex.Binop.arg2;
		if (operationAssociates(src->Iex.Binop.op)) {
			/* Convert to an associative operation. */
			return optimiseIRExpr(
				IRExpr_Associative(
					src->Iex.Binop.op,
					l,
					r,
					NULL),
				opt,
				assumption);
		}
		if (src->Iex.Binop.op >= Iop_Sub8 &&
		    src->Iex.Binop.op <= Iop_Sub64) {
			/* Replace a - b with a + (-b), so as to
			   eliminate binary -. */
			src->Iex.Binop.op = (IROp)(src->Iex.Binop.op - Iop_Sub8 + Iop_Add8);
			src->Iex.Binop.arg2 =
				optimiseIRExpr(
					IRExpr_Unop( (IROp)((src->Iex.Binop.op - Iop_Add8) + Iop_Neg8),
						     r ),
					opt,
					assumption);
		}
		/* If a op b commutes, sort the arguments. */
		if (operationCommutes(src->Iex.Binop.op) &&
		    sortIRExprs(r, l)) {
			src->Iex.Binop.arg1 = r;
			src->Iex.Binop.arg2 = l;
			l = src->Iex.Binop.arg1;
			r = src->Iex.Binop.arg2;
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
				l = src->Iex.Binop.arg1 = optimiseIRExpr(newLeft, opt, assumption);
				r = src->Iex.Binop.arg2 = optimiseIRExpr(newRight, opt, assumption);
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
				r = src->Iex.Binop.arg2 = optimiseIRExpr(newR, opt, assumption);
			}
			/* If, in a == b, a and b are physically
			 * identical, the result is a constant 1. */
			if (physicallyEqual(l, r))
				return IRExpr_Const(IRConst_U1(1));

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
				return optimiseIRExpr(src, opt, assumption);
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
			return optimiseIRExpr(src, opt, assumption);
		}

		/* If enabled, assume that the stack is ``private'',
		   in the sense that it doesn't alias with any global
		   variables, and is therefore never equal to any
		   constants which are present in the machine code. */
		if (opt.assumePrivateStack &&
		    src->Iex.Binop.op == Iop_CmpEQ64 &&
		    src->Iex.Binop.arg1->tag == Iex_Get &&
		    src->Iex.Binop.arg1->Iex.Get.offset == OFFSET_amd64_RSP &&
		    src->Iex.Binop.arg2->tag == Iex_Const)
			return IRExpr_Const(IRConst_U1(0));

		/* If both arguments are constant, try to constant
		 * fold everything away. */
		if (src->Iex.Binop.arg1->tag == Iex_Const &&
		    src->Iex.Binop.arg2->tag == Iex_Const) {
			switch (src->Iex.Binop.op) {
			case Iop_CmpEQ64:
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
	    dynamic_cast<StateMachineStub *>(sm))
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
	const AllowableOptimisations &opt);

static StateMachineEdge *
buildNewStateMachineWithLoadsEliminated(
	StateMachineEdge *sme,
	std::set<StateMachineSideEffectStore *> &initialAvail,
	std::map<StateMachine *,
	               std::set<StateMachineSideEffectStore *> > &availMap,
	std::map<StateMachine *, StateMachine *> &memo,
	const AllowableOptimisations &opt)
{
	StateMachineEdge *res =
		new StateMachineEdge(buildNewStateMachineWithLoadsEliminated(sme->target, availMap, memo, opt));

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
			currentlyAvailable.insert(smses);
			res->sideEffects.push_back(*it);
		} else if (StateMachineSideEffectLoad *smsel =
			   dynamic_cast<StateMachineSideEffectLoad *>(*it)) {
			bool done = false;
			for (std::set<StateMachineSideEffectStore *>::iterator it2 =
				     currentlyAvailable.begin();
			     !done && it2 != currentlyAvailable.end();
			     it2++) {
				if ( definitelyEqual((*it2)->addr, smsel->addr, opt) ) {
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
			assert(dynamic_cast<StateMachineSideEffectCopy *>(*it));
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
	const AllowableOptimisations &opt)
{
	if (dynamic_cast<StateMachineCrash *>(sm) ||
	    dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm))
		return sm;
	if (memo.count(sm))
		return memo[sm];
	if (StateMachineBifurcate *smb =
	    dynamic_cast<StateMachineBifurcate *>(sm)) {
		StateMachineBifurcate *res;
		res = new StateMachineBifurcate(smb->condition, (StateMachineEdge *)NULL, NULL);
		memo[sm] = res;
		res->trueTarget = buildNewStateMachineWithLoadsEliminated(
			smb->trueTarget, availMap[sm], availMap, memo, opt);
		res->falseTarget = buildNewStateMachineWithLoadsEliminated(
			smb->falseTarget, availMap[sm], availMap, memo, opt);
		return res;
	} if (StateMachineProxy *smp =
	      dynamic_cast<StateMachineProxy *>(sm)) {
		StateMachineProxy *res;
		res = new StateMachineProxy((StateMachineEdge *)NULL);
		memo[sm] = res;
		res->target = buildNewStateMachineWithLoadsEliminated(
			smp->target, availMap[sm], availMap, memo, opt);
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
	const AllowableOptimisations &opt)
{
	std::map<StateMachine *, StateMachine *> memo;
	return buildNewStateMachineWithLoadsEliminated(sm, availMap, memo, opt);
}

/* Available expression analysis on memory locations.  This isn't
   included in the normal optimise() operation because it's
   context-sensitive, and therefore isn't allowed to mutate nodes
   in-place. */
static StateMachine *
availExpressionAnalysis(StateMachine *sm, const AllowableOptimisations &opt)
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
		for (std::set<StateMachine *>::iterator it = allStates.begin();
		     it != allStates.end();
		     it++) {
			if (dynamic_cast<StateMachineCrash *>(*it) ||
			    dynamic_cast<StateMachineNoCrash *>(*it) ||
			    dynamic_cast<StateMachineStub *>(*it))
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
	} while (progress);

	/* So after all that we now have a complete map of what's
	   available where.  Given that, we should be able to
	   construct a new state machine with redundant loads replaced
	   with copy side effects. */
	return buildNewStateMachineWithLoadsEliminated(
		sm,
		availOnEntry,
		opt);
}

typedef std::pair<StateMachine *, StateMachine *> st_pair_t;

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
			definitelyEqual(smsel1->addr, smsel2->addr, opt);
	} else if (StateMachineSideEffectCopy *smsec1 =
		   dynamic_cast<StateMachineSideEffectCopy *>(smse1)) {
		StateMachineSideEffectCopy *smsec2 =
			dynamic_cast<StateMachineSideEffectCopy *>(smse2);
		if (!smsec2)
			return false;
		return smsec1->key == smsec2->key &&
			definitelyEqual(smsec1->value, smsec2->value, opt);
	} else {
		abort();
	}
}

static bool
edgesLocallyBisimilar(StateMachineEdge *sme1,
		      StateMachineEdge *sme2,
		      const std::set<st_pair_t> &others,
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
	if (others.count(st_pair_t(sme1->target, sme2->target)))
		return true;
	else
		return false;
}

static bool
statesLocallyBisimilar(StateMachine *sm1,
		       StateMachine *sm2,
		       const std::set<st_pair_t> &others,
		       const AllowableOptimisations &opt)
{
	/* Sort our arguments by type.  Ordering is:

	   Crash
	   NoCrash
	   Stub
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
				} else if (!dynamic_cast<StateMachineProxy *>(sm1)) {
					assert(dynamic_cast<StateMachineBifurcate *>(sm1));
					if (dynamic_cast<StateMachineProxy *>(sm2)) {
						swapArgs = true;
					}
				}
			}
		}
	}
	if (swapArgs)
		return statesLocallyBisimilar(sm2, sm1, others, opt);

	if (dynamic_cast<StateMachineCrash *>(sm1)) {
		if (dynamic_cast<StateMachineCrash *>(sm2)) {
			return true;
		} else if (dynamic_cast<StateMachineNoCrash *>(sm2)) {
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
			return edgesLocallyBisimilar(smp1->target,
						     smp2->target,
						     others,
						     opt);
		} else if (StateMachineBifurcate *smb2 =
			   dynamic_cast<StateMachineBifurcate *>(sm2)) {
			return edgesLocallyBisimilar(smp1->target,
						     smb2->trueTarget,
						     others,
						     opt) &&
				edgesLocallyBisimilar(smp1->target,
						      smb2->falseTarget,
						      others,
						      opt);
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
		edgesLocallyBisimilar(smb1->trueTarget, smb2->trueTarget, others, opt) &&
		edgesLocallyBisimilar(smb1->falseTarget, smb2->falseTarget, others, opt) &&
		definitelyEqual(smb1->condition, smb2->condition, opt);
}

static StateMachine *
rewriteStateMachine(StateMachine *sm,
		    std::map<StateMachine *, StateMachine *> &rules,
		    std::set<StateMachine *> &memo)
{
	if (rules.count(sm) && rules[sm] != sm)
		return rewriteStateMachine(rules[sm], rules, memo);
	if (dynamic_cast<StateMachineCrash *>(sm) ||
	    dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm))
		return sm;
	memo.insert(sm);
	if (StateMachineBifurcate *smb =
	    dynamic_cast<StateMachineBifurcate *>(sm)) {
		smb->trueTarget->target = rewriteStateMachine(
			smb->trueTarget->target,
			rules,
			memo);
		smb->falseTarget->target = rewriteStateMachine(
			smb->falseTarget->target,
			rules,
			memo);
		return sm;
	}
	if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(sm)) {
		smp->target->target = rewriteStateMachine(
			smp->target->target,
			rules,
			memo);
		return sm;
	}

	abort();
}

static StateMachine *
rewriteStateMachine(StateMachine *sm, std::map<StateMachine *, StateMachine *> &rules)
{
	std::set<StateMachine *> memo;
	return rewriteStateMachine(sm, rules, memo);
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

	std::set<st_pair_t> bisimilarStates;

	/* Initially, everything is bisimilar to everything else. */
	for (std::set<StateMachine *>::iterator it = allStates.begin();
	     it != allStates.end();
	     it++)
		for (std::set<StateMachine *>::iterator it2 = allStates.begin();
		     it2 != allStates.end();
		     it2++)
			bisimilarStates.insert(st_pair_t(*it, *it2));

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
			if (statesLocallyBisimilar(it->first, it->second, bisimilarStates, opt)) {
				it++;
			} else {
				bisimilarStates.erase(it++);
				progress = true;
			}
		}
	} while (progress);

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
	std::map<StateMachine *, StateMachine *> canonMap;

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

	/* Perform the rewrite.  We do this in-place, because it's not
	   context-dependent. */
	return rewriteStateMachine(sm, canonMap);
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
findSuccessors(AddressSpace *as, unsigned long rip, std::vector<unsigned long> &out)
{
	IRSB *irsb = as->getIRSBForAddress(rip);
	int i;

	for (i = 1; i < irsb->stmts_used; i++) {
		if (irsb->stmts[i]->tag == Ist_IMark) {
			/* That's the end of this instruction */
			out.push_back(irsb->stmts[i]->Ist.IMark.addr);
			return;
		}
		if (irsb->stmts[i]->tag == Ist_Exit)
			out.push_back(irsb->stmts[i]->Ist.Exit.dst->Ico.U64);
	}

	/* If we get here then there are no other marks in the IRSB,
	   so we need to look at the fall through addresses. */
	if (irsb->jumpkind == Ijk_Call) {
		out.push_back(extract_call_follower(irsb));
		/* Emit the target as well, if possible. */

#warning This is arguably wrong
		/* Actually, don't bother: the state machine inferring
		   bits don't do so, and get very confused when they
		   can't match everything up properly. */
		return;
	}

	if (irsb->next->tag == Iex_Const) {
		out.push_back(irsb->next->Iex.Const.con->Ico.U64);
	} else {
		/* Should really do something more clever here,
		   possibly based on dynamic analysis. */
	}
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
		    std::set<std::set<unsigned long> > &outputClusters)
{
	union_find<unsigned long> output;
	std::set<unsigned long> explored;

	for (std::set<unsigned long>::const_iterator it = inputRips.begin();
	     it != inputRips.end();
	     it++) {
		unsigned long r = *it;
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

		std::set<unsigned long> thisSet;
		unsigned long representative = output.representative(r);
		for (std::set<unsigned long>::iterator it = unprocessedInput.begin();
		     it != unprocessedInput.end();
			) {
			if (output.representative(*it) == representative) {
				thisSet.insert(*it);
				unprocessedInput.erase(it++);
			} else {
				it++;
			}
		}
		outputClusters.insert(thisSet);
	}
}

static StateMachine *
CFGtoStoreMachine(AddressSpace *as, CFGNode *cfg, std::map<CFGNode *, StateMachine *> &memo)
{
	if (!cfg)
		return StateMachineNoCrash::get();
	if (memo.count(cfg))
		return memo[cfg];
	StateMachine *res;
	IRSB *irsb = as->getIRSBForAddress(cfg->my_rip);
	int endOfInstr;
	for (endOfInstr = 1; endOfInstr < irsb->stmts_used; endOfInstr++)
		if (irsb->stmts[endOfInstr]->tag == Ist_IMark)
			break;
	if (cfg->fallThrough || !cfg->branch) {
		res = CFGtoStoreMachine(as, cfg->fallThrough, memo);
		int idx = endOfInstr;
		while (idx != 0) {
			IRStmt *stmt = irsb->stmts[idx-1];
			if (stmt->tag == Ist_Exit) {
				if (cfg->branch) {
					res = new StateMachineBifurcate(
						stmt->Ist.Exit.guard,
						CFGtoStoreMachine(as, cfg->branch, memo),
						res);
				}
			} else {
				res = backtrackStateMachineOneStatement(res, stmt, cfg->my_rip);
			}
			idx--;
		}
	} else {
		assert(cfg->branch);
		res = CFGtoStoreMachine(as, cfg->branch, memo);
		int idx;
		for (idx = endOfInstr - 1; idx >= 0; idx--)
			if (irsb->stmts[idx]->tag == Ist_Exit)
				break;
		assert(idx > 0);
		while (idx != 0) {
			IRStmt *stmt = irsb->stmts[idx-1];
			res = backtrackStateMachineOneStatement(res, stmt, cfg->my_rip);
		}
	}
	memo[cfg] = res;
	return res;		
}

static StateMachine *
CFGtoStoreMachine(AddressSpace *as, CFGNode *cfg)
{
	std::map<CFGNode *, StateMachine *> memo;
	return CFGtoStoreMachine(as, cfg, memo);
}

class StateMachineEvalContext {
public:
	std::vector<StateMachineSideEffectStore *> stores;
	std::map<Int, IRExpr *> binders;
	IRExpr *pathConstraint;
};

static IRExpr *
specialiseIRExpr(IRExpr *iex, StateMachineEvalContext &ctxt)
{
	switch (iex->tag) {
	case Iex_Binder:
		assert(ctxt.binders[iex->Iex.Binder.binder]);
		return ctxt.binders[iex->Iex.Binder.binder];
	case Iex_Get:
		return iex;
	case Iex_GetI:
		return IRExpr_GetI(
			iex->Iex.GetI.descr,
			specialiseIRExpr(iex->Iex.GetI.ix, ctxt),
			iex->Iex.GetI.bias);
	case Iex_RdTmp:
		return iex;
	case Iex_Qop:
		return IRExpr_Qop(
			iex->Iex.Qop.op,
			specialiseIRExpr(iex->Iex.Qop.arg1, ctxt),
			specialiseIRExpr(iex->Iex.Qop.arg2, ctxt),
			specialiseIRExpr(iex->Iex.Qop.arg3, ctxt),
			specialiseIRExpr(iex->Iex.Qop.arg4, ctxt));
	case Iex_Triop:
		return IRExpr_Triop(
			iex->Iex.Triop.op,
			specialiseIRExpr(iex->Iex.Triop.arg1, ctxt),
			specialiseIRExpr(iex->Iex.Triop.arg2, ctxt),
			specialiseIRExpr(iex->Iex.Triop.arg3, ctxt));
	case Iex_Binop:
		return IRExpr_Binop(
			iex->Iex.Binop.op,
			specialiseIRExpr(iex->Iex.Binop.arg1, ctxt),
			specialiseIRExpr(iex->Iex.Binop.arg2, ctxt));
	case Iex_Unop:
		return IRExpr_Unop(
			iex->Iex.Unop.op,
			specialiseIRExpr(iex->Iex.Unop.arg, ctxt));
	case Iex_Load:
		return IRExpr_Load(
			iex->Iex.Load.isLL,
			iex->Iex.Load.end,
			iex->Iex.Load.ty,
			specialiseIRExpr(iex->Iex.Load.addr, ctxt));
	case Iex_Const:
		return iex;
	case Iex_CCall: {
		IRExpr **args;
		int n;
		for (n = 0; iex->Iex.CCall.args[n]; n++)
			;
		args = (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, n + 1);
		for (n = 0; iex->Iex.CCall.args[n]; n++)
			args[n] = specialiseIRExpr(iex->Iex.CCall.args[n], ctxt);
		return IRExpr_CCall(
			iex->Iex.CCall.cee,
			iex->Iex.CCall.retty,
			args);
	}
	case Iex_Mux0X:
		return IRExpr_Mux0X(
			specialiseIRExpr(iex->Iex.Mux0X.cond, ctxt),
			specialiseIRExpr(iex->Iex.Mux0X.expr0, ctxt),
			specialiseIRExpr(iex->Iex.Mux0X.exprX, ctxt));
	case Iex_Associative: {
		IRExpr *res = IRExpr_Associative(iex);
		for (int it = 0;
		     it < res->Iex.Associative.nr_arguments;
		     it++)
			res->Iex.Associative.contents[it] =
				specialiseIRExpr(res->Iex.Associative.contents[it],
						 ctxt);
		return res;
	}
	}
	abort();
}

static bool
expressionIsTrue(IRExpr *exp, NdChooser &chooser, StateMachineEvalContext &ctxt)
{
	exp = optimiseIRExpr(
		specialiseIRExpr(exp, ctxt),
		AllowableOptimisations::defaultOptimisations);

	/* Combine the path constraint with the new expression and see
	   if that produces a contradiction.  If it does then we know
	   for sure that the new expression is false. */
	IRExpr *e =
		optimiseIRExpr(
			IRExpr_Binop(
				Iop_And1,
				ctxt.pathConstraint,
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
			ctxt.pathConstraint = e;
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
				ctxt.pathConstraint,
				IRExpr_Unop(
					Iop_Not1,
					exp)),
			AllowableOptimisations::defaultOptimisations);
	if (e2->tag == Iex_Const) {
		/* If X & ¬Y is definitely true, Y is definitely
		 * false and X is definitely true. */
		if (e2->Iex.Const.con->Ico.U1) {
			ctxt.pathConstraint = IRExpr_Const(IRConst_U1(1));
			return false;
		}

		/* So now we know that X & ¬Y is definitely false, and
		 * we assume that X is true.  Therefore ¬Y is false
		 * and Y is true. */
		return true;
	}

	/* Can't prove it one way or another.  Use the
	   non-deterministic chooser to guess. */
	if (chooser.nd_choice(2) == 0) {
		ctxt.pathConstraint = e;
		return true;
	} else {
		ctxt.pathConstraint = e2;
		return false;
	}
}

static bool
evalExpressionsEqual(IRExpr *exp1, IRExpr *exp2, NdChooser &chooser, StateMachineEvalContext &ctxt)
{
	return expressionIsTrue(IRExpr_Binop(
					Iop_CmpEQ64,
					exp1,
					exp2),
				chooser,
				ctxt);
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
			   StateMachineEvalContext &ctxt)
{
	if (StateMachineSideEffectStore *smses =
	    dynamic_cast<StateMachineSideEffectStore *>(smse)) {
		ctxt.stores.push_back(
			new StateMachineSideEffectStore(
				specialiseIRExpr(smses->addr, ctxt),
				specialiseIRExpr(smses->data, ctxt),
				smses->rip
				)
				);
	} else if (StateMachineSideEffectLoad *smsel =
		   dynamic_cast<StateMachineSideEffectLoad *>(smse)) {
		IRExpr *val;
		val = NULL;
		for (std::vector<StateMachineSideEffectStore *>::reverse_iterator it = ctxt.stores.rbegin();
		     !val && it != ctxt.stores.rend();
		     it++) {
			StateMachineSideEffectStore *smses = *it;
			if (!oracle->memoryAccessesMightAlias(smsel, smses))
				continue;
			if (evalExpressionsEqual(smses->addr, smsel->addr, chooser, ctxt))
				val = smses->data;
		}
		if (!val)
			val = IRExpr_Load(False, Iend_LE, Ity_I64, smsel->addr);
		ctxt.binders[smsel->key] = val;
	} else if (StateMachineSideEffectCopy *smsec =
		   dynamic_cast<StateMachineSideEffectCopy *>(smse)) {
		ctxt.binders[smsec->key] =
			specialiseIRExpr(smsec->value, ctxt);
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
		evalStateMachineSideEffect(*it, chooser, oracle, ctxt);
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
		if (expressionIsTrue(smb->condition, chooser, ctxt)) {
			evalStateMachineEdge(smb->trueTarget, crashes, chooser, oracle, ctxt);
		} else {
			evalStateMachineEdge(smb->falseTarget, crashes, chooser, oracle, ctxt);
		}
		return;
	}
	abort();
}

/* Assume that @sm executes atomically.  Figure out a constraint on
   the initial state which will lead to it not crashing. */
static IRExpr *
survivalConstraintIfExecutedAtomically(StateMachine *sm, Oracle *oracle)
{
	NdChooser chooser;
	IRExpr *currentConstraint = IRExpr_Const(IRConst_U1(1));
	bool crashes;

	do {
		StateMachineEvalContext ctxt;
		ctxt.pathConstraint = IRExpr_Const(IRConst_U1(1));
		evalStateMachine(sm, &crashes, chooser, oracle, ctxt);
		if (crashes) {
			/* This path leads to a crash, so the
			   constraint should include something to make
			   sure that we don't go down here. */
			currentConstraint =
				IRExpr_Binop(
					Iop_And1,
					currentConstraint,
					IRExpr_Unop(
						Iop_Not1,
						ctxt.pathConstraint));
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
				  random_irtype());
	case 2:
		return IRExpr_RdTmp(random() % 5);
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
		return IRExpr_GetI(random_irregarray(), random_irexpr(depth - 1), (random() % 20) * 8);
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
			IRExpr_Get(0, Ity_I64),
			IRExpr_Unop(
				Iop_Neg64,
				IRExpr_Get(0, Ity_I64)),
			NULL);
	IRExpr *end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	assert(physicallyEqual(end, IRExpr_Const(IRConst_U64(0))));
	/* x & ~x -> 0 */
	start = IRExpr_Associative(
		Iop_And1,
		IRExpr_Unop(
			Iop_Not1,
			IRExpr_Get(0, Ity_I64)),
		IRExpr_Get(0, Ity_I64),
		NULL);
	end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	assert(physicallyEqual(end, IRExpr_Const(IRConst_U1(0))));
}

static void
evalMachineUnderAssumption(StateMachine *sm, Oracle *oracle, IRExpr *assumption,
			   bool *mightSurvive, bool *mightCrash)
{
	NdChooser chooser;
	bool crashes;

	*mightSurvive = false;
	*mightCrash = false;
	while (!*mightCrash || !*mightSurvive) {
		StateMachineEvalContext ctxt;
		ctxt.pathConstraint = assumption;
		evalStateMachine(sm, &crashes, chooser, oracle, ctxt);
		if (crashes) {
			*mightCrash = true;
			printf("Eventual crash, path constraint ");
			ppIRExpr(ctxt.pathConstraint, stdout);
			printf("\n");
		} else
			*mightSurvive = true;
		if (!chooser.advance())
			break;
	}
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
	VexPtr<Oracle> oracle(new Oracle(ms, thr));

	CrashReason *proximal = getProximalCause(ms, thr);
	if (!proximal)
		errx(1, "cannot get proximal cause of crash");
	proximal = backtrackToStartOfInstruction(proximal, ms->addressSpace);

	VexPtr<InferredInformation> ii(new InferredInformation(oracle));
	ii->addCrashReason(proximal);

	std::vector<unsigned long> previousInstructions;
	oracle->findPreviousInstructions(previousInstructions);
	for (std::vector<unsigned long>::iterator it = previousInstructions.begin();
	     it != previousInstructions.end();
	     it++) {
		CFGNode *cfg = ii->CFGFromRip(*it);
		std::set<unsigned long> interesting;
		interesting.insert(proximal->rip.rip);
		trimCFG(cfg, interesting);
		breakCycles(cfg);

		CrashReason *cr = ii->CFGtoCrashReason(cfg);
		AllowableOptimisations opt =
			AllowableOptimisations::defaultOptimisations
			.enableassumePrivateStack()
			.enableassumeExecutesAtomically()
			.enableignoreSideEffects();
		cr->sm = cr->sm->optimise(opt, oracle);
		cr->sm = availExpressionAnalysis(cr->sm, opt);
		cr->sm = bisimilarityReduction(cr->sm, opt);
		printf("Crash reason %s:\n", cr->rip.name());
		printStateMachine(cr->sm, stdout);

		printf("Survival constraint: \n");
		IRExpr *survive =
			optimiseIRExpr(
				survivalConstraintIfExecutedAtomically(cr->sm, oracle),
				opt);
		ppIRExpr(survive, stdout);
		printf("\n");

		bool mightSurvive, mightCrash;
		evalMachineUnderAssumption(cr->sm, oracle, survive, &mightSurvive, &mightCrash);
		printf("Might survive: %d, might crash: %d\n", mightSurvive,
		       mightCrash);

		std::set<StateMachineSideEffectLoad *> allLoads;
		findAllLoads(cr->sm, allLoads);
		std::set<unsigned long> potentiallyConflictingStores;
		for (std::set<StateMachineSideEffectLoad *>::iterator it = allLoads.begin();
		     it != allLoads.end();
		     it++)
			oracle->findConflictingStores(*it, potentiallyConflictingStores);
		std::set<std::set<unsigned long> > conflictClusters;
		oracle->clusterRips(potentiallyConflictingStores, conflictClusters);
		for (std::set<std::set<unsigned long> >::iterator it = conflictClusters.begin();
		     it != conflictClusters.end();
		     it++) {
			printf("Cluster:");
			for (std::set<unsigned long>::iterator it2 = it->begin();
			     it2 != it->end();
			     it2++)
				printf(" %lx", *it2);
			printf("\n");

			std::set<CFGNode *> storeCFGs;
			buildCFGForRipSet(ms->addressSpace, *it, storeCFGs);
			for (std::set<CFGNode *>::iterator it2 = storeCFGs.begin();
			     it2 != storeCFGs.end();
			     it2++) {
				trimCFG(*it2, *it);
				breakCycles(*it2);

				StateMachine *sm = CFGtoStoreMachine(ms->addressSpace, *it2);

				AllowableOptimisations opt2 =
					AllowableOptimisations::defaultOptimisations
					.enableassumePrivateStack();
				sm = sm->optimise(opt2, oracle);
				sm = availExpressionAnalysis(sm, opt2);
				sm = bisimilarityReduction(sm, opt2);
				sm = sm->optimise(opt2, oracle);
				printf("Turns into state machine:\n");
				printStateMachine(sm, stdout);
			}
		}
	}

	return 0;
}
