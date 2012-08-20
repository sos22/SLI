#ifndef STATEMACHINE_HPP__
#define STATEMACHINE_HPP__

#include <map>
#include <set>
#include <queue>

#include "simplify_irexpr.hpp"
#include "oracle_rip.hpp"
#include "typesdb.hpp"
#include "libvex_parse.h"
#include "cfgnode.hpp"

class StateMachine;
class StateMachineSideEffect;

#ifdef NDEBUG
static inline
#endif
void sanityCheckIRExpr(IRExpr *, const std::set<threadAndRegister, threadAndRegister::fullCompare> *)
#ifdef NDEBUG
{}
#else
;
#endif

class FrameId : public Named {
	unsigned id;
public:
	unsigned tid;
private:
	char *mkName() const {
		return my_asprintf("frame%d:%d", tid, id);
	}
public:
	FrameId(unsigned _id, unsigned _tid)
		: id(_id), tid(_tid)
	{}
	static FrameId invalid()
	{
		return FrameId(-1, -1);
	}
	static bool parse(FrameId *out, const char *str, const char **suffix)
	{
		unsigned id;
		unsigned tid;
		if (parseThisString("frame", str, &str) &&
		    parseDecimalUInt(&tid, str, &str) &&
		    parseThisChar(':', str, &str) &&
		    parseDecimalUInt(&id, str, suffix)) {
			*out = FrameId(id, tid);
			return true;
		}
		return false;
	}
	bool operator==(const FrameId &o) const {
		return id == o.id && tid == o.tid;
	}
	bool operator!=(const FrameId &o) const {
		return !(*this == o);
	}
	bool operator<(const FrameId &o) const {
		/* Just here so that you can make sets of them; no
		 * other meaning. */
		return id < o.id || (id == o.id && tid < o.tid);
	}
};

/* Pointer aliasing stuff.  Note that ``stack'' in this
   context means the *current* stack frame: a pointer without
   the stack bit set could still point into a *calling*
   functions' stack frame, and that wouldn't be a bug. */
class PointerAliasingSet : public Named {
	bool nonPointer;
	bool nonStckPointer;
public:
	bool otherStackPointer;
private:
	bool valid;
	std::vector<FrameId> stackPointers;
	char *mkName() const {
		if (!valid) {
			return strdup("(<invalid>)");
		} else {
			std::vector<const char *> fragments;
			if (nonPointer)
				fragments.push_back("non-pointer");
			if (nonStckPointer)
				fragments.push_back("non-stack-pointer");
			if (otherStackPointer) {
				fragments.push_back("any-stack");
			} else {
				for (auto it = stackPointers.begin();
				     it != stackPointers.end();
				     it++)
					fragments.push_back(it->name());
			}
			return flattenStringFragmentsMalloc(fragments, "|", "(", ")");
		}
	}
	/* Only used for setting up the pre-defined default sets */
	PointerAliasingSet(int k)
		: valid(true)
	{
		nonPointer = nonStckPointer = otherStackPointer = false;
		switch (k) {
		case 0:
			break;
		case 1:
			nonPointer = true;
			break;
		case 2:
			otherStackPointer = true;
			break;
		case 3:
			nonStckPointer = true;
			break;
		case 4:
			nonPointer = otherStackPointer = nonStckPointer = true;
			break;
		default:
			abort();
		}
	}
public:
	PointerAliasingSet()
		: valid(false)
	{
	}
	static const PointerAliasingSet notAPointer;
	static const PointerAliasingSet nonStackPointer;
	static const PointerAliasingSet stackPointer;
	static const PointerAliasingSet anything;
	static const PointerAliasingSet nothing;
	static PointerAliasingSet frame(const FrameId &fid) {
		PointerAliasingSet res(nothing);
		res.stackPointers.push_back(fid);
		return res;
	}
	static PointerAliasingSet frames(const std::set<FrameId> &inp);
	PointerAliasingSet operator |(const PointerAliasingSet &o) const;
	PointerAliasingSet operator &(const PointerAliasingSet &o) const;
	bool overlaps(const PointerAliasingSet &o) const;
	bool operator !=(const PointerAliasingSet &o) const { return !(*this == o); }
	bool operator ==(const PointerAliasingSet &o) const;
	/* Extend this set such that anything which satisfies @o would
	   also satisfy this one.  Returns true if we do anything or
	   false otherwise. */
	bool operator |=(const PointerAliasingSet &o);

	bool mightPointAt(const FrameId fid) const {
		if (!valid || otherStackPointer)
			return true;
		for (auto it = stackPointers.begin(); it != stackPointers.end(); it++)
			if (*it == fid)
				return true;
		return false;
	}
	bool mightPointAtStack() const {
		return !valid || otherStackPointer || !stackPointers.empty();
	}
	bool mightPointAtNonStack() const {
		return !valid || nonStckPointer;
	}
	bool mightBeNonPointer() const {
		return !valid || nonPointer;
	}
	bool mightPoint() const {
		return !valid || nonStckPointer || otherStackPointer || !stackPointers.empty();
	}
	bool pointsAtFrames() const {
		return !valid || !stackPointers.empty();
	}
	bool parse(const char *str, const char **suffix) {
		bool nonPointer = false;
		bool nonStackPointer = false;
		bool anyStack = false;
		bool valid;
		std::vector<FrameId> stackPointers;
		if (parseThisString("(<invalid>)", str, suffix)) {
			valid = false;
		} else {
			valid = true;
			if (!parseThisChar('(', str, &str))
				return false;
			if (!parseThisChar(')', str, suffix)) {
				while (1) {
					if (parseThisString("non-pointer", str, &str)) {
						if (nonPointer)
							return false;
						nonPointer = true;
					} else if (parseThisString("non-stack-pointer", str, &str)) {
						if (nonStackPointer)
							return false;
						nonStackPointer = true;
					} else if (parseThisString("any-stack", str, &str)) {
						if (anyStack || !stackPointers.empty())
							return false;
						anyStack = true;
					} else {
						FrameId f(FrameId::invalid());
						if (FrameId::parse(&f, str, &str)) {
							if (anyStack)
								return false;
							for (auto it = stackPointers.begin();
							     it != stackPointers.end();
							     it++)
								if (*it == f)
									return false;
							if (!stackPointers.empty() &&
							    f < stackPointers.back())
								return false;
							stackPointers.push_back(f);
						} else {
							return false;
						}
					}
					if (parseThisChar(')', str, suffix))
						break;
					if (!parseThisChar('|', str, &str))
						return false;
				}
			}
		}
		this->nonPointer = nonPointer;
		this->nonStckPointer = nonStackPointer;
		this->otherStackPointer = anyStack;
		this->stackPointers = stackPointers;
		this->valid = valid;
		clearName();
		return true;
	}
};

class IRExprTransformer;
class StateMachineState;

class StateMachine : public GarbageCollected<StateMachine, &ir_heap> {
public:
	StateMachineState *root;
	std::vector<std::pair<unsigned, const CFGNode *> > cfg_roots;

	static bool parse(StateMachine **out, const char *str, const char **suffix);

	StateMachine(StateMachineState *_root,
		     const std::vector<std::pair<unsigned, const CFGNode *> > &_cfg_roots)
		: root(_root), cfg_roots(_cfg_roots)
	{
	}
	StateMachine(StateMachine *parent)
		: root(parent->root), cfg_roots(parent->cfg_roots)
	{}
	StateMachine(StateMachine *parent, StateMachineState *_root)
		: root(_root), cfg_roots(parent->cfg_roots)
	{}
	StateMachine *optimise(const AllowableOptimisations &opt,
			       bool *done_something);
	void visit(HeapVisitor &hv) {
		hv(root);
		for (auto it = cfg_roots.begin(); it != cfg_roots.end(); it++)
			hv(it->second);
	}
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
	virtual StateMachineState *optimise(const AllowableOptimisations &, bool *) = 0;
	void findLoadedAddresses(std::set<IRExpr *> &out, const AllowableOptimisations &opt);
	bool canCrash(std::set<const StateMachineState *> &memo) const {
		if (type == Crash)
			return true;
		if (!memo.insert(this).second)
			return false;
		std::vector<const StateMachineState *> s;
		targets(s);
		for (auto it = s.begin(); it != s.end(); it++)
			if ((*it)->canCrash(memo))
				return true;
		return false;
	}
	virtual void targets(std::vector<StateMachineState **> &) = 0;
	virtual void targets(std::vector<const StateMachineState *> &) const = 0;
	void targets(std::vector<StateMachineState *> &out) {
		std::vector<StateMachineState **> r;
		targets(r);
		out.reserve(r.size());
		for (auto it = r.begin(); it != r.end(); it++)
			out.push_back(**it);
	}
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
	void enumerateMentionedMemoryAccesses(std::set<MemoryAccessIdentifier> &out);
	virtual void prettyPrint(
		FILE *f,
		std::map<const StateMachineState *, int> &labels) const = 0;

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

class StateMachineSideEffect : public GarbageCollected<StateMachineSideEffect, &ir_heap> {
	StateMachineSideEffect(); /* DNE */
public:
#define all_side_effect_types(f)		\
	f(Load)					\
	f(Store)				\
	f(Copy)					\
	f(Unreached)				\
	f(AssertFalse)				\
	f(Phi)					\
	f(StartAtomic)				\
	f(EndAtomic)				\
	f(StartFunction)			\
	f(EndFunction)				\
	f(StackUnescaped)			\
	f(PointerAliasing)			\
	f(StackLayout)
	enum sideEffectType {
#define mk_one(n) n,
		all_side_effect_types(mk_one)
#undef mk_one
	} type;
protected:
	StateMachineSideEffect(enum sideEffectType _type)
		: type(_type)
	{}
public:
	virtual StateMachineSideEffect *optimise(const AllowableOptimisations &, bool *) = 0;
	virtual void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) = 0;
	virtual void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live = NULL) const = 0;
	virtual bool definesRegister(threadAndRegister &res) const = 0;
	virtual void inputExpressions(std::vector<IRExpr *> &exprs) = 0;
	virtual void prettyPrint(FILE *f) const = 0;
	static bool parse(StateMachineSideEffect **out, const char *str, const char **suffix);
	NAMED_CLASS
};

class StateMachineTerminal : public StateMachineState {
protected:
	virtual void prettyPrint(FILE *f) const = 0;
	StateMachineTerminal(const VexRip &rip, StateMachineState::stateType type) : StateMachineState(rip, type) {}
public:
	StateMachineState *optimise(const AllowableOptimisations &, bool *)
	{ return this; }
	virtual void visit(HeapVisitor &) {}
	void targets(std::vector<StateMachineState **> &) { }
	void targets(std::vector<const StateMachineState *> &) const { }
	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &) const { prettyPrint(f); }
	StateMachineSideEffect *getSideEffect() { return NULL; }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *) const { return; }
};

class StateMachineUnreached : public StateMachineTerminal {
	StateMachineUnreached() : StateMachineTerminal(VexRip(), StateMachineState::Unreached) {}
	static VexPtr<StateMachineUnreached, &ir_heap> _this;
	void prettyPrint(FILE *f) const { fprintf(f, "<unreached>"); }
public:
	static StateMachineUnreached *get() {
		if (!_this) _this = new StateMachineUnreached();
		return _this;
	}
	static bool parse(StateMachineUnreached **out, const char *str, const char **suffix)
	{
		if (parseThisString("<unreached>", str, suffix)) {
			*out = StateMachineUnreached::get();
			return true;
		}
		return false;
	}
};

class StateMachineCrash : public StateMachineTerminal {
	StateMachineCrash() : StateMachineTerminal(VexRip(), StateMachineState::Crash) {}
	static VexPtr<StateMachineCrash, &ir_heap> _this;
	void prettyPrint(FILE *f) const { fprintf(f, "<crash>"); }
public:
	static StateMachineCrash *get() {
		if (!_this) _this = new StateMachineCrash();
		return _this;
	}
	static bool parse(StateMachineCrash **out, const char *str, const char **suffix)
	{
		if (parseThisString("<crash>", str, suffix)) {
			*out = StateMachineCrash::get();
			return true;
		}
		return false;
	}
};

class StateMachineNoCrash : public StateMachineTerminal {
	StateMachineNoCrash() : StateMachineTerminal(VexRip(), StateMachineState::NoCrash) {}
	static VexPtr<StateMachineNoCrash, &ir_heap> _this;
	void prettyPrint(FILE *f) const { fprintf(f, "<survive>"); }
public:
	static StateMachineNoCrash *get() {
		if (!_this) _this = new StateMachineNoCrash();
		return _this;
	}
	static bool parse(StateMachineNoCrash **out, const char *str, const char **suffix)
	{
		if (parseThisString("<survive>", str, suffix)) {
			*out = StateMachineNoCrash::get();
			return true;
		}
		return false;
	}
};

class StateMachineSideEffecting : public StateMachineState {
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
	static bool parse(StateMachineSideEffecting **out, const char *str, const char **suffix)
	{
		VexRip origin;
		int target;
		StateMachineSideEffect *sme;
		if (parseThisString("{", str, &str) &&
		    parseVexRip(&origin, str, &str) &&
		    parseThisChar(':', str, &str) &&
		    StateMachineSideEffect::parse(&sme, str, &str) &&
		    parseThisString(" then l", str, &str) &&
		    parseDecimalInt(&target, str, &str) &&
		    parseThisChar('}', str, suffix)) {
			*out = new StateMachineSideEffecting(origin, sme, (StateMachineState *)target);
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &hv)
	{
		hv(target);
		hv(sideEffect);
	}
	void prependSideEffect(StateMachineSideEffect *sideEffect);

	StateMachineState *optimise(const AllowableOptimisations &opt, bool *done_something);
	void targets(std::vector<StateMachineState **> &out) { out.push_back(&target); }
	void targets(std::vector<const StateMachineState *> &out) const { out.push_back(target); }
	StateMachineSideEffect *getSideEffect() { return sideEffect; }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const
	{
		if (sideEffect)
			sideEffect->sanityCheck(live);
	}
};

class StateMachineBifurcate : public StateMachineState {
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

	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const
	{
		fprintf(f, "%s: if (", origin.name());
		ppIRExpr(condition, f);
		fprintf(f, ") then l%d else l%d",
			labels[trueTarget], labels[falseTarget]);
	}
	static bool parse(StateMachineBifurcate **out, const char *str, const char **suffix)
	{
		VexRip origin;
		IRExpr *condition;
		int target1;
		int target2;
		if (parseVexRip(&origin, str, &str) &&
		    parseThisString(": if (", str, &str) &&
		    parseIRExpr(&condition, str, &str) &&
		    parseThisString(") then l", str, &str) &&
		    parseDecimalInt(&target1, str, &str) &&
		    parseThisString(" else l", str, &str) &&
		    parseDecimalInt(&target2, str, suffix)) {
			*out = new StateMachineBifurcate(origin, condition,
							 (StateMachineState *)target1,
							 (StateMachineState *)target2);
			return true;
		}
		return false;
	}

	void visit(HeapVisitor &hv)
	{
		hv(trueTarget);
		hv(falseTarget);
		hv(condition);
	}
	StateMachineState *optimise(const AllowableOptimisations &opt, bool *done_something);
	void targets(std::vector<StateMachineState **> &out) {
		out.push_back(&falseTarget);
		out.push_back(&trueTarget);
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
public:
	VexRip target;

	StateMachineStub(const VexRip &origin, const VexRip &t) : StateMachineTerminal(origin, StateMachineState::Stub), target(t) {}

	void prettyPrint(FILE *f) const
	{
		fprintf(f, "<%s: jmp %s>", origin.name(), target.name());
	}
	static bool parse(StateMachineStub **out, const char *str, const char **suffix)
	{
		VexRip origin;
		VexRip target;
		if (parseThisChar('<', str, &str) &&
		    parseVexRip(&origin, str, &str) &&
		    parseThisString(": jmp ", str, &str) &&
		    parseVexRip(&target, str, &str) &&
		    parseThisChar('>', str, suffix)) {
			*out = new StateMachineStub(origin, target);
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &) { }
};


class StateMachineSideEffectUnreached : public StateMachineSideEffect {
	static VexPtr<StateMachineSideEffectUnreached, &ir_heap> _this;
	StateMachineSideEffectUnreached() : StateMachineSideEffect(StateMachineSideEffect::Unreached) {}
	void inputExpressions(std::vector<IRExpr *> &) {}
public:
	static StateMachineSideEffectUnreached *get() {
		if (!_this) _this = new StateMachineSideEffectUnreached();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<unreached>"); }
	static bool parse(StateMachineSideEffectUnreached **out, const char *str, const char **suffix)
	{
		if (parseThisString("<unreached>", str, suffix)) {
			*out = StateMachineSideEffectUnreached::get();
			return true;
		}
		return false;
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &, bool *) { return this; }
	void updateLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void visit(HeapVisitor &) {}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *) const {}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
};

class StateMachineSideEffectMemoryAccess : public StateMachineSideEffect {
	virtual void _inputExpressions(std::vector<IRExpr *> &exprs) = 0;
protected:
	void inputExpressions(std::vector<IRExpr *> &exprs) { _inputExpressions(exprs); exprs.push_back(addr); }
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
		rip.sanity_check();
	}
	virtual IRType _type() const = 0;
};
class StateMachineSideEffectStore : public StateMachineSideEffectMemoryAccess {
	void _inputExpressions(std::vector<IRExpr *> &exprs) { exprs.push_back(data); }
public:
	StateMachineSideEffectStore(IRExpr *_addr, IRExpr *_data, const MemoryAccessIdentifier &_rip)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, StateMachineSideEffect::Store),
		  data(_data)
	{
	}
	StateMachineSideEffectStore(const StateMachineSideEffectStore *base, IRExpr *_addr, IRExpr *_data)
		: StateMachineSideEffectMemoryAccess(_addr, base->rip, StateMachineSideEffect::Store),
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
	static bool parse(StateMachineSideEffectStore **out,
			  const char *str,
			  const char **suffix)
	{
		IRExpr *addr;
		IRExpr *data;
		MemoryAccessIdentifier rip(MemoryAccessIdentifier::uninitialised());
		if (parseThisString("*(", str, &str) &&
		    parseIRExpr(&addr, str, &str) &&
		    parseThisString(") <- ", str, &str) &&
		    parseIRExpr(&data, str, &str) &&
		    parseThisString(" @ ", str, &str) &&
		    parseMemoryAccessIdentifier(&rip, str, suffix)) {
			*out = new StateMachineSideEffectStore(addr, data, rip);
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &hv) {
		StateMachineSideEffectMemoryAccess::visit(hv);
		hv(data);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &opt);
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		StateMachineSideEffectMemoryAccess::sanityCheck(live);
		sanityCheckIRExpr(data, live);
	}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
	IRType _type() const { return data->type(); }
};

template <typename ret>
class nullaryFunction {
public:
	virtual ret operator()() = 0;
};
typedef nullaryFunction<threadAndRegister> threadAndRegisterAllocator;
class StateMachineSideEffectLoad : public StateMachineSideEffectMemoryAccess {
	void _inputExpressions(std::vector<IRExpr *> &) {}
public:
	StateMachineSideEffectLoad(threadAndRegisterAllocator &alloc, IRExpr *_addr, const MemoryAccessIdentifier &_rip, IRType _type)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, StateMachineSideEffect::Load),
		  target(alloc()), type(_type)
	{
	}
	StateMachineSideEffectLoad(threadAndRegister reg, IRExpr *_addr, const MemoryAccessIdentifier &_rip, IRType _type)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, StateMachineSideEffect::Load),
		  target(reg), type(_type)
	{
	}
	StateMachineSideEffectLoad(StateMachineSideEffectLoad *base, const threadAndRegister &_reg)
		: StateMachineSideEffectMemoryAccess(base->addr, base->rip, StateMachineSideEffect::Load),
		  target(_reg), type(base->type)
	{}
	StateMachineSideEffectLoad(const StateMachineSideEffectLoad *base, IRExpr *_addr)
		: StateMachineSideEffectMemoryAccess(_addr, base->rip, StateMachineSideEffect::Load),
		  target(base->target), type(base->type)
	{}
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
	static bool parse(StateMachineSideEffectLoad **out,
			  const char *str,
			  const char **suffix)
	{
		IRExpr *addr;
		threadAndRegister key(threadAndRegister::invalid());
		IRType type;
		MemoryAccessIdentifier rip(MemoryAccessIdentifier::uninitialised());
		if (parseThisString("LOAD ", str, &str) &&
		    parseThreadAndRegister(&key, str, &str) &&
		    parseThisString(":", str, &str) &&
		    parseIRType(&type, str, &str) &&
		    parseThisString(" <- *(", str, &str) &&
		    parseIRExpr(&addr, str, &str) &&
		    parseThisString(")@", str, &str) &&
		    parseMemoryAccessIdentifier(&rip, str, suffix)) {
			*out = new StateMachineSideEffectLoad(key, addr, rip, type);
			return true;
		}
		return false;
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &l, const AllowableOptimisations &) {
		l.insert(addr);
	}
	bool definesRegister(threadAndRegister &reg) const {
		reg = target;
		return true;
	}
	IRType _type() const { return type; }
};
class StateMachineSideEffectCopy : public StateMachineSideEffect {
	void inputExpressions(std::vector<IRExpr *> &exprs) { exprs.push_back(value); }
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
	static bool parse(StateMachineSideEffectCopy **out, const char *str, const char **suffix)
	{
		IRExpr *data;
		threadAndRegister key(threadAndRegister::invalid());
		if (parseThisString("COPY ", str, &str) &&
		    parseThreadAndRegister(&key, str, &str) &&
		    parseThisString(" = ", str, &str) &&
		    parseIRExpr(&data, str, suffix)) {
			*out = new StateMachineSideEffectCopy(key, data);
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &hv) {
		hv(value);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) { }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		sanityCheckIRExpr(value, live);
	}
	bool definesRegister(threadAndRegister &reg) const {
		reg = target;
		return true;
	}
};
class StateMachineSideEffectAssertFalse : public StateMachineSideEffect {
	void inputExpressions(std::vector<IRExpr *> &exprs) { exprs.push_back(value); }
public:
	StateMachineSideEffectAssertFalse(IRExpr *_value, bool _reflectsActualProgram)
		: StateMachineSideEffect(StateMachineSideEffect::AssertFalse),
		  value(_value),
		  reflectsActualProgram(_reflectsActualProgram)
	{
	}
	IRExpr *value;
	bool reflectsActualProgram;
	void prettyPrint(FILE *f) const {
		fprintf(f, "Assert !(");
		ppIRExpr(value, f);
		fprintf(f, ") %s", reflectsActualProgram ? "REAL" : "FAKE");
	}
	static bool parse(StateMachineSideEffectAssertFalse **out, const char *str, const char **suffix)
	{
		IRExpr *data;
		if (parseThisString("Assert !(", str, &str) &&
		    parseIRExpr(&data, str, &str) &&
		    parseThisChar(')', str, &str)) {
			bool isReal;
			if (parseThisString(" REAL", str, suffix)) {
				isReal = true;
			} else if (parseThisString(" FAKE", str, suffix)) {
				isReal = false;
			} else {
				return false;
			}
			*out = new StateMachineSideEffectAssertFalse(data, isReal);
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &hv) {
		hv(value);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) { }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		assert(reflectsActualProgram == true ||
		       reflectsActualProgram == false);
		sanityCheckIRExpr(value, live);
		assert(value->type() == Ity_I1);
	}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
};
class StateMachineSideEffectStartAtomic : public StateMachineSideEffect {
	StateMachineSideEffectStartAtomic()
		: StateMachineSideEffect(StateMachineSideEffect::StartAtomic)
	{}
	static VexPtr<StateMachineSideEffectStartAtomic, &ir_heap> singleton;
	void inputExpressions(std::vector<IRExpr *> &) { }
public:
	static StateMachineSideEffectStartAtomic *get() {
		if (!singleton)
			singleton = new StateMachineSideEffectStartAtomic();
		return singleton;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "START_ATOMIC");
	}
	static bool parse(StateMachineSideEffectStartAtomic **out, const char *str, const char **suffix)
	{
		if (parseThisString("START_ATOMIC", str, suffix)) {
			*out = StateMachineSideEffectStartAtomic::get();
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &) {}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *) const {
	}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
};
class StateMachineSideEffectEndAtomic : public StateMachineSideEffect {
	StateMachineSideEffectEndAtomic()
		: StateMachineSideEffect(StateMachineSideEffect::EndAtomic)
	{}
	static VexPtr<StateMachineSideEffectEndAtomic, &ir_heap> singleton;
	void inputExpressions(std::vector<IRExpr *> &) { }
public:
	static StateMachineSideEffectEndAtomic *get() {
		if (!singleton)
			singleton = new StateMachineSideEffectEndAtomic();
		return singleton;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "END_ATOMIC");
	}
	static bool parse(StateMachineSideEffectEndAtomic **out, const char *str, const char **suffix)
	{
		if (parseThisString("END_ATOMIC", str, suffix)) {
			*out = StateMachineSideEffectEndAtomic::get();
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &) {}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *) const {
	}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
};
class StateMachineSideEffectPhi : public StateMachineSideEffect {
	void inputExpressions(std::vector<IRExpr *> &exprs) {
		for (auto it = generations.begin(); it != generations.end(); it++)
			if (it->second)
				exprs.push_back(it->second);
	}
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
	static bool parse(StateMachineSideEffectPhi **out, const char *str, const char **suffix)
	{
		threadAndRegister key(threadAndRegister::invalid());
		if (parseThisString("Phi", str, &str) &&
		    parseThreadAndRegister(&key, str, &str) &&
		    parseThisString("(", str, &str)) {
			std::vector<std::pair<unsigned, IRExpr *> > generations;
			if (!parseThisChar(')', str, suffix)) {
				while (1) {
					int x;
					IRExpr *val;
					if (!parseDecimalInt(&x, str, &str))
						return false;
					if (parseThisChar('=', str, &str)) {
						if (!parseIRExpr(&val, str, &str))
							return false;
					} else {
						val = NULL;
					}
					generations.push_back(std::pair<unsigned, IRExpr *>(x, val));
					if (parseThisChar(')', str, suffix))
						break;
					if (!parseThisString(", ", str, &str))
						return false;
				}
			}
			*out = new StateMachineSideEffectPhi(key, generations);
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &hv) {
		for (auto it = generations.begin(); it != generations.end(); it++)
			hv(it->second);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *) const {
		assert(generations.size() != 0);
	}
	bool definesRegister(threadAndRegister &reg) const {
		reg = this->reg;
		return true;
	}
};
class StateMachineSideEffectStartFunction : public StateMachineSideEffect {
	void inputExpressions(std::vector<IRExpr *> &exprs) {
		if (rsp)
			exprs.push_back(rsp);
	}
public:
	StateMachineSideEffectStartFunction(IRExpr *_rsp, FrameId _frame)
		: StateMachineSideEffect(StateMachineSideEffect::StartFunction),
		  rsp(_rsp), frame(_frame)
	{
	}
	IRExpr *rsp;
	FrameId frame;
	void prettyPrint(FILE *f) const {
		fprintf(f, "StartFunction(%s) rsp = ", frame.name());
		if (rsp)
			ppIRExpr(rsp, f);
		else
			fprintf(f, "<inf>");
	}
	static bool parse(StateMachineSideEffectStartFunction **out, const char *str, const char **suffix)
	{
		IRExpr *data;
		FrameId frame(FrameId::invalid());
		if (parseThisString("StartFunction(", str, &str) &&
		    FrameId::parse(&frame, str, &str) &&
		    parseThisString(") rsp = ", str, &str)) {
			if (parseThisString("<inf>", str, suffix))
				*out = new StateMachineSideEffectStartFunction(NULL, frame);
			else if (parseIRExpr(&data, str, suffix))
				*out = new StateMachineSideEffectStartFunction(data, frame);
			else
				return false;
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &hv) {
		hv(rsp);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) { }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		if (rsp) {
			sanityCheckIRExpr(rsp, live);
			assert(rsp->type() == Ity_I64);
		}
	}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
	bool operator==(const StateMachineSideEffectStartFunction &o) const {
		return rsp == o.rsp && frame == o.frame;
	}
};
class StateMachineSideEffectEndFunction : public StateMachineSideEffect {
	void inputExpressions(std::vector<IRExpr *> &exprs) { exprs.push_back(rsp); }
public:
	StateMachineSideEffectEndFunction(IRExpr *_rsp, FrameId _frame)
		: StateMachineSideEffect(StateMachineSideEffect::EndFunction),
		  rsp(_rsp), frame(_frame)
	{
	}
	IRExpr *rsp;
	FrameId frame;
	void prettyPrint(FILE *f) const {
		fprintf(f, "EndFunction(%s) rsp = ", frame.name());
		ppIRExpr(rsp, f);
	}
	static bool parse(StateMachineSideEffectEndFunction **out, const char *str, const char **suffix)
	{
		IRExpr *rsp;
		FrameId frame(FrameId::invalid());
		if (parseThisString("EndFunction(", str, &str) &&
		    FrameId::parse(&frame, str, &str) &&
		    parseThisString(") rsp = ", str, &str) &&
		    parseIRExpr(&rsp, str, suffix)) {
			*out = new StateMachineSideEffectEndFunction(rsp, frame);
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &hv) {
		hv(rsp);
	}
	StateMachineSideEffect *optimise(const AllowableOptimisations &opt, bool *done_something);
	void updateLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) { }
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const {
		sanityCheckIRExpr(rsp, live);
		assert(rsp->type() == Ity_I64);
	}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
	bool operator==(const StateMachineSideEffectEndFunction &o) const {
		return rsp == o.rsp && frame == o.frame;
	}
};
/* Note that for a particular frame X there are no pointers from
 * outside X to inside X. */
class StateMachineSideEffectStackUnescaped : public StateMachineSideEffect {
public:
	std::vector<FrameId> localFrames;
	StateMachineSideEffectStackUnescaped(std::vector<FrameId> &_localFrames)
		: StateMachineSideEffect(StateMachineSideEffect::StackUnescaped),
		  localFrames(_localFrames)
	{}
	void visit(HeapVisitor &) {}
	StateMachineSideEffect *optimise(const AllowableOptimisations&, bool*) {
		if (localFrames.empty())
			return NULL;
		else
			return this;
	}
	void updateLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare>*) const {}
	bool definesRegister(threadAndRegister &) const { return false; }
	void inputExpressions(std::vector<IRExpr *> &) {}
	void prettyPrint(FILE *f) const {
		fprintf(f, "STACKUNESCAPED(");
		for (auto it = localFrames.begin(); it != localFrames.end(); it++) {
			if (it != localFrames.begin())
				fprintf(f, ", ");
			fprintf(f, "%s", it->name());
		}
		fprintf(f, ")");
	}
	static bool parse(StateMachineSideEffectStackUnescaped **out,
			  const char *str,
			  const char **suffix)
	{
		std::vector<FrameId> frames;
		if (!parseThisString("STACKUNESCAPED(", str, &str))
			return false;
		if (!parseThisChar(')', str, suffix)) {
			while (1) {
				FrameId f(FrameId::invalid());
				if (!FrameId::parse(&f, str, &str))
					return false;
				frames.push_back(f);
				if (parseThisChar(')', str, suffix))
					break;
				if (!parseThisString(", ", str, &str))
					return false;
			}
		}
		*out = new StateMachineSideEffectStackUnescaped(frames);
		return true;
	}
	bool operator==(const StateMachineSideEffectStackUnescaped &o) const {
		return localFrames == o.localFrames;
	}
};
class StateMachineSideEffectPointerAliasing : public StateMachineSideEffect {
public:
	threadAndRegister reg;
	PointerAliasingSet set;
	StateMachineSideEffectPointerAliasing(
		const threadAndRegister &_reg,
		const PointerAliasingSet &_set)
		: StateMachineSideEffect(StateMachineSideEffect::PointerAliasing),
		  reg(_reg), set(_set)
	{}
	void visit(HeapVisitor &) {}
	StateMachineSideEffect *optimise(const AllowableOptimisations&, bool*) { return this; }
	void updateLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare>*) const {}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
	void inputExpressions(std::vector<IRExpr *> &) {}
	void prettyPrint(FILE *f) const {
		fprintf(f, "ALIAS %s = %s",
			reg.name(), set.name());
	}
	static bool parse(StateMachineSideEffectPointerAliasing **out, const char *str, const char **suffix)
	{
		threadAndRegister reg(threadAndRegister::invalid());
		PointerAliasingSet set(PointerAliasingSet::nothing);

		if (parseThisString("ALIAS ", str, &str) &&
		    parseThreadAndRegister(&reg, str, &str) &&
		    parseThisString(" = ", str, &str) &&
		    set.parse(str, suffix)) {
			*out = new StateMachineSideEffectPointerAliasing(reg, set);
			return true;
		}
		return false;
	}
	bool operator==(const StateMachineSideEffectPointerAliasing &o) const {
		return threadAndRegister::fullEq(reg, o.reg) && set == o.set;
	}

};
class StateMachineSideEffectStackLayout : public StateMachineSideEffect {
public:
	unsigned tid;
	/* Second element is whether there could be any pointers to
	 * that frame in initial memory. */
	std::vector<std::pair<FrameId, bool> > functions;
	StateMachineSideEffectStackLayout(
		unsigned _tid,
		const std::vector<std::pair<FrameId, bool> > &_functions)
		: StateMachineSideEffect(StateMachineSideEffect::StackLayout),
		  tid(_tid), functions(_functions)
	{}
	void visit(HeapVisitor &) {}
	StateMachineSideEffect *optimise(const AllowableOptimisations &, bool *) { return this; }
	void updateLoadedAddresses(std::set<IRExpr *> &, const AllowableOptimisations &) {}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *) const {
		/* No dupes */
		for (auto it1 = functions.begin();
		     it1 != functions.end();
		     it1++) {
			for (auto it2 = it1 + 1;
			     it2 != functions.end();
			     it2++)
				assert(it1->first != it2->first);
		}
	}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
	void inputExpressions(std::vector<IRExpr *> &) {
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "STACKLAYOUT(%d) = {", tid);
		for (auto it = functions.begin(); it != functions.end(); it++) {
			if (it != functions.begin())
				fprintf(f, ", ");
			fprintf(f, "%s%s", it->first.name(), it->second ? " <mem>" : "");
		}
		fprintf(f, "}");
	}
	static bool parse(StateMachineSideEffectStackLayout **out, const char *str, const char **suffix)
	{
		unsigned tid;
		std::vector<std::pair<FrameId, bool> > functions;

		if (!parseThisString("STACKLAYOUT(", str, &str) ||
		    !parseDecimalUInt(&tid, str, &str) ||
		    !parseThisString(") = {", str, &str))
			return false;
		while (1) {
			FrameId f(FrameId::invalid());
			bool regs;
			if (!FrameId::parse(&f, str, &str))
				return false;
			if (parseThisString(" <mem>", str, &str))
				regs = true;
			else
				regs = false;
			functions.push_back(std::pair<FrameId, bool>(f, regs));
			if (parseThisChar('}', str, suffix))
				break;
			if (!parseThisString(", ", str, &str))
				return false;
		}
		*out = new StateMachineSideEffectStackLayout(tid, functions);
		return true;
	}
	bool operator==(const StateMachineSideEffectStackLayout &o) const {
		return tid == o.tid && functions == o.functions;
	}

};

void printStateMachine(const StateMachine *sm, FILE *f);
void printStateMachine(const StateMachine *sm, FILE *f,
		       std::map<const StateMachineState *, int> &labels);
void printStateMachine(const StateMachineState *sm, FILE *f);
void printStateMachine(const StateMachineState *sm,
		       FILE *f,
		       std::map<const StateMachineState *, int> &labels);
bool sideEffectsBisimilar(StateMachineSideEffect *smse1,
			  StateMachineSideEffect *smse2,
			  const AllowableOptimisations &opt);
bool parseStateMachine(StateMachine **out,
		       const char *str, const char **suffix);
StateMachine *readStateMachine(int fd);

class MemoryAccessIdentifierAllocator;

StateMachine *duplicateStateMachine(const StateMachine *inp);

template <typename t> t
pop(std::set<t> &x)
{
	auto it = x.begin();
	if (it == x.end()) abort();
	t res = *it;
	x.erase(it);
	return res;
}

template <typename t>
class __enumStatesAdaptSet {
public:
	std::set<t> &underlying;
	__enumStatesAdaptSet(std::set<t> &_underlying)
		: underlying(_underlying)
	{}
	void insert(const t &what) {
		underlying.insert(what);
	}
};

template <typename t>
class __enumStatesAdaptQueue {
public:
	std::queue<t> &underlying;
	__enumStatesAdaptQueue(std::queue<t> &_underlying)
		: underlying(_underlying)
	{}
	void insert(const t &what) {
		underlying.push(what);
	}
};

template <typename t>
class __enumStatesAdaptVector {
public:
	std::vector<t> &underlying;
	__enumStatesAdaptVector(std::vector<t> &_underlying)
		: underlying(_underlying)
	{}
	void insert(const t &what) {
		underlying.push_back(what);
	}
};

template <typename stateType, typename containerType> void
__enumStates(StateMachineState *root, containerType &states)
{
	std::vector<StateMachineState *> toVisit;
	std::set<StateMachineState *> visited;

	toVisit.push_back(root);
	while (!toVisit.empty()) {
		StateMachineState *s = toVisit.back();
		toVisit.pop_back();
		assert(s);
		if (!visited.insert(s).second)
			continue;
		stateType *ss = dynamic_cast<stateType *>(s);
		if (ss)
			states.insert(ss);
		s->targets(toVisit);
	}
}

template <typename stateType, typename containerType> void
__enumStates(const StateMachineState *root, containerType &states)
{
	std::vector<const StateMachineState *> toVisit;
	std::set<const StateMachineState *> visited;

	toVisit.push_back(root);
	while (!toVisit.empty()) {
		const StateMachineState *s = toVisit.back();
		toVisit.pop_back();
		assert(s);
		if (!visited.insert(s).second)
			continue;
		const stateType *ss = dynamic_cast<stateType *>(s);
		if (ss)
			states.insert(ss);
		s->targets(toVisit);
	}
}

template <typename stateType> void
enumStates(StateMachine *sm, std::set<stateType *> *states)
{
	__enumStatesAdaptSet<stateType *> s(*states);
	__enumStates<stateType, __enumStatesAdaptSet<stateType *> >(sm->root, s);
}
template <typename stateType> void
enumStates(StateMachineState *root, std::set<stateType *> *states)
{
	__enumStatesAdaptSet<stateType *> s(*states);
	__enumStates<stateType, __enumStatesAdaptSet<stateType *> >(root, s);
}

template <typename stateType> void
enumStates(const StateMachine *sm, std::set<const stateType *> *states)
{
	__enumStatesAdaptSet<const stateType *> s(*states);
	__enumStates<const stateType, __enumStatesAdaptSet<const stateType *> >(sm->root, s);
}

template <typename stateType> void
enumStates(const StateMachineState *root, std::set<const stateType *> *states)
{
	__enumStatesAdaptSet<const stateType *> s(*states);
	__enumStates<const stateType, __enumStatesAdaptSet<const stateType *> >(root, s);
}

template <typename stateType> void
enumStates(StateMachine *sm, std::vector<stateType *> *states)
{
	__enumStatesAdaptVector<stateType *> s(*states);
	__enumStates<stateType, __enumStatesAdaptVector<stateType *> >(sm->root, s);
}

template <typename stateType> void
enumStates(const StateMachineState *sm, std::vector<const stateType *> *states)
{
	__enumStatesAdaptVector<const stateType *> s(*states);
	__enumStates<const stateType, __enumStatesAdaptVector<const stateType *> >(sm, s);
}
template <typename stateType> void
enumStates(const StateMachine *sm, std::vector<const stateType *> *states)
{
	__enumStatesAdaptVector<const stateType *> s(*states);
	__enumStates<const stateType, __enumStatesAdaptVector<const stateType *> >(sm->root, s);
}

template <typename stateType> void
enumStates(StateMachine *sm, std::queue<stateType *> *states)
{
	__enumStatesAdaptQueue<stateType *> s(*states);
	__enumStates<stateType, __enumStatesAdaptQueue<stateType *> >(sm->root, s);
}

template <typename seType> void
enumSideEffects(StateMachineState *root, std::set<seType *> &out)
{
	std::set<StateMachineSideEffecting *> states;
	enumStates<StateMachineSideEffecting>(root, &states);
	for (auto it = states.begin(); it != states.end(); it++) {
		if ( !(*it)->sideEffect )
			continue;
		seType *se = dynamic_cast<seType *>( (*it)->sideEffect );
		if (se)
			out.insert(se);
	}
}

template <typename seType> void
enumSideEffects(StateMachine *sm, std::set<seType *> &out)
{
	enumSideEffects(sm->root, out);
}

#endif /* !STATEMACHINE_HPP__ */
