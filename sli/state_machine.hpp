#ifndef STATEMACHINE_HPP__
#define STATEMACHINE_HPP__

#include <map>
#include <set>
#include <queue>

#include "simplify_irexpr.hpp"
#include "oracle_rip.hpp"
#include "typesdb.hpp"
#include "libvex_parse.h"

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

class IRExprTransformer;
class StateMachineState;

class StateMachine : public GarbageCollected<StateMachine, &ir_heap> {
public:
	StateMachineState *root;
	std::vector<std::pair<unsigned, VexRip> > origin;

	static bool parse(StateMachine **out, const char *str, const char **suffix);

	StateMachine(StateMachineState *_root, const std::vector<std::pair<unsigned, VexRip> > &_origin)
		: root(_root), origin(_origin)
	{
	}
	StateMachine(StateMachine *parent)
		: root(parent->root), origin(parent->origin)
	{}
	StateMachine *optimise(const AllowableOptimisations &opt,
			       bool *done_something);
	void visit(HeapVisitor &hv) { hv(root); }
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
	f(Unreached) f(Crash) f(NoCrash) f(Stub) f(Bifurcate) f(SideEffecting) f(NdChoice)
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
	virtual StateMachineState *optimise(const AllowableOptimisations &, bool *,
					    std::set<StateMachineState *> &done) = 0;
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
	f(EndFunction)
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
	static bool parse(StateMachineSideEffect **out, const char *str, const char **suffix);
	NAMED_CLASS
};

class StateMachineTerminal : public StateMachineState {
protected:
	virtual void prettyPrint(FILE *f) const = 0;
	StateMachineTerminal(const VexRip &rip, StateMachineState::stateType type) : StateMachineState(rip, type) {}
public:
	StateMachineState *optimise(const AllowableOptimisations &, bool *,
				    std::set<StateMachineState *> &) { return this; }
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
public:
	static StateMachineCrash *get() {
		if (!_this) _this = new StateMachineCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<crash>"); }
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
public:
	static StateMachineNoCrash *get() {
		if (!_this) _this = new StateMachineNoCrash();
		return _this;
	}
	void prettyPrint(FILE *f) const { fprintf(f, "<survive>"); }
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

	StateMachineState *optimise(const AllowableOptimisations &opt, bool *done_something,
				    std::set<StateMachineState *> &done);
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
	StateMachineState *optimise(const AllowableOptimisations &opt, bool *done_something,
				    std::set<StateMachineState *> &);
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

/* A special state which arbitrarily picks one of N possible successor
   states.  Used to model things like loop unrolling, where we use an
   ND choice to decide how many iterations we want to take. */
class StateMachineNdChoice : public StateMachineState {
public:
	std::vector<StateMachineState *> successors;
	StateMachineNdChoice(const VexRip &origin,
			     const std::vector<StateMachineState *> &content)
		: StateMachineState(origin, StateMachineState::NdChoice),
		  successors(content)
	{}
	StateMachineNdChoice(const VexRip &origin)
		: StateMachineState(origin, StateMachineState::NdChoice)
	{}

	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const
	{
		fprintf(f, "%s: ND {", origin.name());
		for (auto it = successors.begin(); it != successors.end(); it++) {
			if (it != successors.begin())
				fprintf(f, ", ");
			fprintf(f, "l%d", labels[*it]);
		}
		fprintf(f, "}");
	}
	static bool parse(StateMachineNdChoice **out, const char *str, const char **suffix)
	{
		VexRip origin;
		if (parseVexRip(&origin, str, &str) &&
		    parseThisString(": ND {", str, &str)) {
			std::vector<StateMachineState *> successors;
			while (1) {
				if (parseThisChar('}', str, suffix))
					break;
				if (successors.size() != 0 && !parseThisString(", ", str, &str))
					return false;
				if (!parseThisChar('l', str, &str))
					return false;
				int l;
				if (!parseDecimalInt(&l, str, &str))
					return false;
				successors.push_back((StateMachineState *)l);
			}
			*out = new StateMachineNdChoice(origin, successors);
			return true;
		}
		return false;
	}

	void visit(HeapVisitor &hv)
	{
		for (auto it = successors.begin(); it != successors.end(); it++)
			hv(*it);
	}

	StateMachineState *optimise(const AllowableOptimisations &opt, bool *done_something,
				    std::set<StateMachineState *> &);
	void targets(std::vector<StateMachineState **> &out) {
		out.reserve(out.size() + successors.size());
		for (auto it = successors.begin(); it != successors.end(); it++)
			out.push_back(&*it);
	}
	void targets(std::vector<const StateMachineState *> &out) const {
		out.insert(out.end(), successors.begin(), successors.end());
	}
	void sanityCheck(const std::set<threadAndRegister, threadAndRegister::fullCompare> *live) const
	{
		for (auto it = successors.begin(); it != successors.end(); it++) {
			assert(*it);
			(*it)->sanityCheck(live);
		}
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
	}
};
class StateMachineSideEffectStore : public StateMachineSideEffectMemoryAccess {
	void _inputExpressions(std::vector<IRExpr *> &exprs) { exprs.push_back(data); }
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
	static bool parse(StateMachineSideEffectStore **out, const char *str, const char **suffix)
	{
		IRExpr *addr;
		IRExpr *data;
		MemoryAccessIdentifier where(MemoryAccessIdentifier::uninitialised());
		if (parseThisString("*(", str, &str) &&
		    parseIRExpr(&addr, str, &str) &&
		    parseThisString(") <- ", str, &str) &&
		    parseIRExpr(&data, str, &str) &&
		    parseThisString(" @ ", str, &str) &&
		    parseMemoryAccessIdentifier(&where, str, suffix)) {
			*out = new StateMachineSideEffectStore(addr, data, where);
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
	static bool parse(StateMachineSideEffectLoad **out, const char *str, const char **suffix)
	{
		IRExpr *addr;
		threadAndRegister key(threadAndRegister::invalid());
		MemoryAccessIdentifier where(MemoryAccessIdentifier::uninitialised());
		IRType type;
		if (parseThisString("LOAD ", str, &str) &&
		    parseThreadAndRegister(&key, str, &str) &&
		    parseThisString(":", str, &str) &&
		    parseIRType(&type, str, &str) &&
		    parseThisString(" <- *(", str, &str) &&
		    parseIRExpr(&addr, str, &str) &&
		    parseThisString(")@", str, &str) &&
		    parseMemoryAccessIdentifier(&where, str, suffix)) {
			*out = new StateMachineSideEffectLoad(key, addr, where, type);
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
	void visit(HeapVisitor &) {}
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
	StateMachineSideEffectStartFunction(IRExpr *_rsp)
		: StateMachineSideEffect(StateMachineSideEffect::StartFunction),
		  rsp(_rsp)
	{
	}
	IRExpr *rsp;
	void prettyPrint(FILE *f) const {
		fprintf(f, "StartFunction rsp = ");
		if (rsp)
			ppIRExpr(rsp, f);
		else
			fprintf(f, "<inf>");
	}
	static bool parse(StateMachineSideEffectStartFunction **out, const char *str, const char **suffix)
	{
		IRExpr *data;
		if (parseThisString("StartFunction rsp = ", str, &str)) {
			if (parseThisString("<inf>", str, suffix))
				*out = new StateMachineSideEffectStartFunction(NULL);
			else if (parseIRExpr(&data, str, suffix))
				*out = new StateMachineSideEffectStartFunction(data);
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
		return rsp == o.rsp;
	}
};
class StateMachineSideEffectEndFunction : public StateMachineSideEffect {
	void inputExpressions(std::vector<IRExpr *> &exprs) { exprs.push_back(rsp); }
public:
	StateMachineSideEffectEndFunction(IRExpr *_rsp)
		: StateMachineSideEffect(StateMachineSideEffect::EndFunction),
		  rsp(_rsp)
	{
	}
	IRExpr *rsp;
	void prettyPrint(FILE *f) const {
		fprintf(f, "EndFunction rsp = ");
		ppIRExpr(rsp, f);
	}
	static bool parse(StateMachineSideEffectEndFunction **out, const char *str, const char **suffix)
	{
		IRExpr *rsp;
		if (parseThisString("EndFunction rsp = ", str, &str) &&
		    parseIRExpr(&rsp, str, suffix)) {
			*out = new StateMachineSideEffectEndFunction(rsp);
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
		return rsp == o.rsp;
	}
};

void printStateMachine(const StateMachine *sm, FILE *f);
void printStateMachine(const StateMachine *sm, FILE *f, std::map<const StateMachineState *, int> &labels);
bool sideEffectsBisimilar(StateMachineSideEffect *smse1,
			  StateMachineSideEffect *smse2,
			  const AllowableOptimisations &opt);
bool parseStateMachine(StateMachine **out, const char *str, const char **suffix);
StateMachine *readStateMachine(int fd);

class CFGNode;
class MemoryAccessIdentifierAllocator;
void probeCFGsToMachine(Oracle *oracle, unsigned tid, std::set<CFGNode *> &roots,
			const DynAnalysisRip &proximalRip,
			StateMachineState *proximalCause,
			MemoryAccessIdentifierAllocator &mai,
			std::set<StateMachine *> &out);
StateMachine *storeCFGToMachine(Oracle *oracle,
				unsigned tid,
				CFGNode *root,
				MemoryAccessIdentifierAllocator &mai);

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
__enumStates(StateMachine *sm, containerType &states)
{
	std::vector<StateMachineState *> toVisit;
	std::set<StateMachineState *> visited;

	toVisit.push_back(sm->root);
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
__enumStates(const StateMachine *sm, containerType &states)
{
	std::vector<const StateMachineState *> toVisit;
	std::set<const StateMachineState *> visited;

	toVisit.push_back(sm->root);
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
	__enumStates<stateType, __enumStatesAdaptSet<stateType *> >(sm, s);
}

template <typename stateType> void
enumStates(const StateMachine *sm, std::set<const stateType *> *states)
{
	__enumStatesAdaptSet<const stateType *> s(*states);
	__enumStates<const stateType, __enumStatesAdaptSet<const stateType *> >(sm, s);
}

template <typename stateType> void
enumStates(StateMachine *sm, std::vector<stateType *> *states)
{
	__enumStatesAdaptVector<stateType *> s(*states);
	__enumStates<stateType, __enumStatesAdaptVector<stateType *> >(sm, s);
}

template <typename stateType> void
enumStates(const StateMachine *sm, std::vector<const stateType *> *states)
{
	__enumStatesAdaptVector<const stateType *> s(*states);
	__enumStates<const stateType, __enumStatesAdaptVector<const stateType *> >(sm, s);
}

template <typename seType> void
enumSideEffects(StateMachine *sm, std::set<seType *> &out)
{
	std::set<StateMachineSideEffecting *> states;
	enumStates(sm, &states);
	for (auto it = states.begin(); it != states.end(); it++) {
		if ( !(*it)->sideEffect )
			continue;
		seType *se = dynamic_cast<seType *>( (*it)->sideEffect );
		if (se)
			out.insert(se);
	}
}

#endif /* !STATEMACHINE_HPP__ */
