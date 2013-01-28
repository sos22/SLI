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
#include "smr.hpp"
#include "bdd.hpp"

class StateMachine;
class StateMachineSideEffect;
class MaiMap;
class AllowableOptimisations;

struct SMScopes {
	bdd_ordering ordering;
	bbdd::scope bools;
	smrbdd::scope smrs;
	exprbdd::scope exprs;
	SMScopes()
		: bools(&ordering), smrs(&ordering), exprs(&ordering)
	{}
	bool read(const char *fname);
	bool parse(const char *buf, const char **end);
	void prettyPrint(FILE *f) const;
};

#if !CONFIG_NO_STATIC_ALIASING
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
	FrameId()
		: id(-1), tid(-1)
	{
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
#endif

class MemoryTag {
	int id;
	MemoryTag(int _id)
		: id(_id)
	{}
public:
	MemoryTag() : id(-1) {}
	static MemoryTag normal() { return MemoryTag(1); }
	static MemoryTag mutex() { return MemoryTag(2); }
	static MemoryTag last_free() { return MemoryTag(3); }
	const char *name() const {
		switch (id) {
		case -1: return "BadTag";
		case 1: return "normal";
		case 2: return "mutex";
		case 3: return "last_free";
		default: abort();
		}
	}
	void sanity_check() const {
		assert(id == 1 || id == 2 || id == 3);
	}
	bool parse(const char *str, const char **suffix) {
		if (parseThisString("BadTag", str, suffix)) {
			id = -1;
		} else if (parseThisString("normal", str, suffix)) {
			id = 1;
		} else if (parseThisString("mutex", str, suffix)) {
			id = 2;
		} else if (parseThisString("last_free", str, suffix)) {
			id = 3;
		} else {
			return false;
		}
		return true;
	}

	bool operator==(const MemoryTag &o) const { return id == o.id; }
	bool operator!=(const MemoryTag &o) const { return !(*this == o); }
};

#if !CONFIG_NO_STATIC_ALIASING
/* Pointer aliasing stuff.  Note that ``stack'' in this
   context means the *current* stack frame: a pointer without
   the stack bit set could still point into a *calling*
   functions' stack frame, and that wouldn't be a bug. */
class PointerAliasingSet : public Named {
	bool nonPointer;
	bool nonStckPointer;
public:
	bool otherStackPointer;
	bool valid;
	std::vector<FrameId> stackPointers;
private:
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

	bool operator <(const PointerAliasingSet &o) const;

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
						FrameId f;
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
#endif

class StateMachineState;

class StateMachine : public GarbageCollected<StateMachine, &ir_heap> {
public:
	StateMachineState *root;
	struct entry_point {
		unsigned thread;
		const CFGNode *node;
		entry_point(unsigned _thread, const CFGNode *_node)
			: thread(_thread), node(_node)
		{}
		bool operator ==(const entry_point &o) const {
			return thread == o.thread && node == o.node;
		}
		bool operator <(const entry_point &o) const {
			if (thread < o.thread)
				return true;
			if (thread > o.thread)
				return false;
			return node->label < o.node->label;
		}
	};
	class entry_point_ctxt : public Named {
		char *mkName() const { return my_asprintf("%ld", rsp_delta); }
	public:
		long rsp_delta;
		entry_point_ctxt(long _rsp_delta)
			: rsp_delta(_rsp_delta)
		{}
		static entry_point_ctxt uninitialised() {
			return entry_point_ctxt(-99);
		}
		bool operator !=(const entry_point_ctxt &o) const {
			return rsp_delta != o.rsp_delta;
		}
		bool parse(const char *buf, const char **end) {
			return parseDecimalLong(&rsp_delta, buf, end);
		}
	};
	/* Semantically, this is a map (i.e. no repeats on it->first),
	   but that can't be embedded in a GC'd structure. */
	std::vector<std::pair<entry_point, entry_point_ctxt> > cfg_roots;

	StateMachine(StateMachineState *_root,
		     const std::vector<std::pair<entry_point, entry_point_ctxt> > &_cfg_roots)
		: root(_root), cfg_roots(_cfg_roots)
	{
	}
	StateMachine(StateMachine *parent)
		: root(parent->root), cfg_roots(parent->cfg_roots)
	{}
	StateMachine(StateMachine *parent, StateMachineState *_root)
		: root(_root), cfg_roots(parent->cfg_roots)
	{}
	StateMachine *optimise(SMScopes *scopes,
			       const AllowableOptimisations &opt,
			       bool *done_something);
	void visit(HeapVisitor &hv) {
		hv(root);
		for (auto it = cfg_roots.begin(); it != cfg_roots.end(); it++) {
			hv(it->first.node);
		}
	}
#ifdef NDEBUG
	void sanityCheck(const MaiMap &, SMScopes * = NULL) const {}
	void assertAcyclic() const {}
	void assertSSA() const {}
#else
	void sanityCheck(const MaiMap &, SMScopes * = NULL) const;
	void assertAcyclic() const;
	void assertSSA() const;
#endif

	NAMED_CLASS
};

class StateMachineState : public GarbageCollected<StateMachineState, &ir_heap> {
public:
#define all_state_types(f)						\
	f(Terminal) f(Bifurcate) f(SideEffecting)
#define mk_state_type(name) name ,
	enum stateType {
		all_state_types(mk_state_type)
	};
#undef mk_state_type
protected:
	StateMachineState(const VexRip &_origin,
			  enum stateType _type)
		: last_optimisation_gen(0), type(_type), dbg_origin(_origin)
	{}
	unsigned last_optimisation_gen;
public:
	stateType type;
	VexRip dbg_origin; /* RIP we were looking at when we
			    * constructed the thing.  Not very
			    * meaningful, but occasionally provides
			    * useful hints for debugging.*/

	/* Another peephole optimiser.  Again, must be
	   context-independent and result in no changes to the
	   semantic value of the machine, and can mutate in-place. */
	virtual StateMachineState *optimise(SMScopes *, const AllowableOptimisations &, bool *) = 0;
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

#ifdef NDEBUG
	void sanityCheck(SMScopes *) const {}
#else
	virtual void sanityCheck(SMScopes *) const = 0;
#endif

#ifndef NDEBUG
	void assertAcyclic(std::vector<const StateMachineState *> &stack,
			   std::set<const StateMachineState *> &clean) const;
#endif

	NAMED_CLASS
};

class StateMachineSideEffect : public GarbageCollected<StateMachineSideEffect, &ir_heap> {
	StateMachineSideEffect(); /* DNE */
public:
#if CONFIG_NO_STATIC_ALIASING
#define all_side_effect_types(f)		\
	f(Load)					\
	f(Store)				\
	f(Copy)					\
	f(Unreached)				\
	f(AssertFalse)				\
	f(Phi)					\
	f(StartAtomic)				\
	f(EndAtomic)				\
	f(ImportRegister)
#else
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
	f(ImportRegister)			\
	f(StackLayout)
#endif
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
	virtual StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations &) = 0;
#ifdef NDEBUG
	void sanityCheck(SMScopes *) const {}
#else
	virtual void sanityCheck(SMScopes *) const = 0;
#endif
	virtual bool definesRegister(threadAndRegister &res) const = 0;
	virtual void prettyPrint(FILE *f) const = 0;
	static bool parse(SMScopes *scopes, StateMachineSideEffect **out, const char *str, const char **suffix);
	NAMED_CLASS
};

class StateMachineTerminal : public StateMachineState {
public:
	StateMachineTerminal(const VexRip &vr, smrbdd * _res)
		: StateMachineState(vr, StateMachineState::Terminal),
		  res(_res)
	{
		assert(res);
	}
	StateMachineTerminal(StateMachineTerminal *base, smrbdd *_res)
		: StateMachineState(base->dbg_origin, StateMachineState::Terminal),
		  res(_res)
	{
		assert(res);
	}
	smrbdd *const res;
	bool set_res(smrbdd *_res)
	{
		bool r = res != _res;
		assert(_res);
		*(smrbdd **)&res = _res;
		return r;
	}

	StateMachineState *optimise(SMScopes *, const AllowableOptimisations &, bool *);
	void visit(HeapVisitor &hv) {
		smrbdd *r = res;
		hv(r);
		set_res(r);
	}
	void targets(std::vector<StateMachineState **> &) { }
	void targets(std::vector<const StateMachineState *> &) const { }
	StateMachineSideEffect *getSideEffect() { return NULL; }
	void sanityCheck(SMScopes *scopes) const { res->sanity_check(&scopes->ordering); }

	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &) const;
	static bool parse(SMScopes *scopes, StateMachineTerminal **out, const char *str, const char **suffix);
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
	StateMachineSideEffecting(StateMachineSideEffecting *base, StateMachineSideEffect *smse)
		: StateMachineState(base->dbg_origin, StateMachineState::SideEffecting),
		  target(base->target),
		  sideEffect(smse)
	{
	}
	StateMachineSideEffecting(StateMachineSideEffecting *base)
		: StateMachineState(base->dbg_origin, StateMachineState::SideEffecting),
		  target(base->target),
		  sideEffect(base->sideEffect)
	{
	}
	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const
	{
		fprintf(f, "{%s:", dbg_origin.name());
		if (sideEffect)
			sideEffect->prettyPrint(f);
		fprintf(f, " then l%d}", labels[target]);
	}
	static bool parse(SMScopes *scopes, StateMachineSideEffecting **out, const char *str, const char **suffix)
	{
		VexRip origin;
		int target;
		StateMachineSideEffect *sme;
		if (!parseThisString("{", str, &str) ||
		    !parseVexRip(&origin, str, &str) ||
		    !parseThisChar(':', str, &str))
			return false;
		if (!StateMachineSideEffect::parse(scopes, &sme, str, &str))
			sme = NULL;
		/* Some side-effect parsers consume trailing space and
		   some don't.  Fix it up.  Bit of a hack. */
		parseThisChar(' ', str, &str);
		if (parseThisString("then l", str, &str) &&
		    parseDecimalInt(&target, str, &str) &&
		    parseThisString("}\n", str, suffix)) {
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

	StateMachineState *optimise(SMScopes *, const AllowableOptimisations &opt, bool *done_something);
	void targets(std::vector<StateMachineState **> &out) { out.push_back(&target); }
	void targets(std::vector<const StateMachineState *> &out) const { out.push_back(target); }
	StateMachineSideEffect *getSideEffect() { return sideEffect; }
	void sanityCheck(SMScopes *
#ifndef NDEBUG
			 scopes
#endif
			 ) const
	{
#ifndef NDEBUG
		if (sideEffect)
			sideEffect->sanityCheck(scopes);
		if (sideEffect && sideEffect->type == StateMachineSideEffect::EndAtomic &&
		    target && target->type == StateMachineState::SideEffecting &&
		    ((StateMachineSideEffecting *)target)->sideEffect &&
		    ((StateMachineSideEffecting *)target)->sideEffect->type == StateMachineSideEffect::EndAtomic)
			abort();
#endif
	}
};

class StateMachineBifurcate : public StateMachineState {
public:
	StateMachineBifurcate(const VexRip &origin,
			      bbdd *_condition,
			      StateMachineState *t,
			      StateMachineState *f)
		: StateMachineState(origin, StateMachineState::Bifurcate),
		  condition(_condition),
		  trueTarget(t),
		  falseTarget(f)
	{
		assert(condition || TIMEOUT);
	}
	StateMachineBifurcate(StateMachineBifurcate *base,
			      bbdd *_condition)
		: StateMachineState(base->dbg_origin, StateMachineState::Bifurcate),
		  condition(_condition),
		  trueTarget(base->trueTarget),
		  falseTarget(base->falseTarget)
	{
		assert(condition || TIMEOUT);
	}
	StateMachineBifurcate(StateMachineBifurcate *base)
		: StateMachineState(base->dbg_origin, StateMachineState::Bifurcate),
		  condition(base->condition),
		  trueTarget(base->trueTarget),
		  falseTarget(base->falseTarget)
	{
		assert(condition || TIMEOUT);
	}

	bbdd *const condition;
	bool set_condition(bbdd *_cond)
	{
		bool res = condition != _cond;
		assert(_cond);
		*(bbdd **)&condition = _cond;
		return res;
	}

	StateMachineState *trueTarget;
	StateMachineState *falseTarget;

	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels) const;
	static bool parse(SMScopes *scopes, StateMachineBifurcate **out, const char *str, const char **suffix);

	void visit(HeapVisitor &hv)
	{
		hv(trueTarget);
		hv(falseTarget);
		bbdd *cond = condition;
		hv(cond);
		set_condition(cond);
	}
	StateMachineState *optimise(SMScopes *, const AllowableOptimisations &opt, bool *done_something);
	void targets(std::vector<StateMachineState **> &out) {
		out.push_back(&falseTarget);
		out.push_back(&trueTarget);
	}
	void targets(std::vector<const StateMachineState *> &out) const {
		out.push_back(falseTarget);
		out.push_back(trueTarget);
	}
	void sanityCheck(SMScopes *scopes) const
	{
		condition->sanity_check(&scopes->ordering);
	}
	StateMachineSideEffect *getSideEffect() { return NULL; }
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
	static bool parse(SMScopes *, StateMachineSideEffectUnreached **out, const char *str, const char **suffix)
	{
		if (parseThisString("<unreached>", str, suffix)) {
			*out = StateMachineSideEffectUnreached::get();
			return true;
		}
		return false;
	}
	StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations &) { return this; }
	void visit(HeapVisitor &) {}
	void sanityCheck(SMScopes *) const {}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
};

class StateMachineSideEffectMemoryAccess : public StateMachineSideEffect {
public:
	exprbdd *const addr;
	MemoryAccessIdentifier const rip;
	MemoryTag const tag;
	StateMachineSideEffectMemoryAccess(exprbdd *_addr, const MemoryAccessIdentifier &_rip,
					   const MemoryTag &_tag,
					   StateMachineSideEffect::sideEffectType _type)
		: StateMachineSideEffect(_type), addr(_addr), rip(_rip), tag(_tag)
	{
	}
	virtual void visit(HeapVisitor &hv) {
		hv(addr);
	}
#ifndef NDEBUG
	virtual void sanityCheck(SMScopes *scopes) const {
		addr->sanity_check(&scopes->ordering);
		assert(addr->type() == Ity_I64);
		rip.sanity_check();
	}
#endif
	virtual IRType _type() const = 0;
};
class StateMachineSideEffectStore : public StateMachineSideEffectMemoryAccess {
public:
	StateMachineSideEffectStore(exprbdd *_addr, exprbdd *_data, const MemoryAccessIdentifier &_rip, const MemoryTag &_tag)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, _tag, StateMachineSideEffect::Store),
		  data(_data)
	{
	}
	StateMachineSideEffectStore(const StateMachineSideEffectStore *base, exprbdd *_addr, exprbdd *_data)
		: StateMachineSideEffectMemoryAccess(_addr, base->rip, base->tag, StateMachineSideEffect::Store),
		  data(_data)
	{
	}
	exprbdd *const data;
	void prettyPrint(FILE *f) const {
		fprintf(f, "STORE %s@%s\naddr = ", tag.name(), rip.name());
		addr->prettyPrint(f);
		fprintf(f, "data = ");
		data->prettyPrint(f);
	}
	static bool parse(SMScopes *scopes,
			  StateMachineSideEffectStore **out,
			  const char *str,
			  const char **suffix)
	{
		exprbdd *addr;
		exprbdd *data;
		MemoryAccessIdentifier rip(MemoryAccessIdentifier::uninitialised());
		MemoryTag tag;
		if (parseThisString("STORE ", str, &str) &&
		    tag.parse(str, &str) &&
		    parseThisChar('@', str, &str) &&
		    rip.parse(str, &str) &&
		    parseThisString("\naddr = ", str, &str) &&
		    exprbdd::parse(&scopes->exprs, &addr, str, &str) &&
		    parseThisString("data = ", str, &str) &&
		    exprbdd::parse(&scopes->exprs, &data, str, suffix)) {
			*out = new StateMachineSideEffectStore(addr, data, rip, tag);
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &hv) {
		StateMachineSideEffectMemoryAccess::visit(hv);
		hv(data);
	}
	StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations &opt);
	void sanityCheck(SMScopes *scopes) const {
		StateMachineSideEffectMemoryAccess::sanityCheck(scopes);
		data->sanity_check(&scopes->ordering);
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
public:
	StateMachineSideEffectLoad(threadAndRegisterAllocator &alloc, exprbdd *_addr, const MemoryAccessIdentifier &_rip, IRType _type, const MemoryTag &_tag)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, _tag, StateMachineSideEffect::Load),
		  target(alloc()), type(_type)
	{
	}
	StateMachineSideEffectLoad(threadAndRegister reg, exprbdd *_addr, const MemoryAccessIdentifier &_rip, IRType _type, const MemoryTag &_tag)
		: StateMachineSideEffectMemoryAccess(_addr, _rip, _tag, StateMachineSideEffect::Load),
		  target(reg), type(_type)
	{
	}
	StateMachineSideEffectLoad(StateMachineSideEffectLoad *base, const threadAndRegister &_reg)
		: StateMachineSideEffectMemoryAccess(base->addr, base->rip, base->tag, StateMachineSideEffect::Load),
		  target(_reg), type(base->type)
	{}
	StateMachineSideEffectLoad(const StateMachineSideEffectLoad *base, const threadAndRegister &_reg, exprbdd *_addr)
		: StateMachineSideEffectMemoryAccess(_addr, base->rip, base->tag, StateMachineSideEffect::Load),
		  target(_reg), type(base->type)
	{}
	StateMachineSideEffectLoad(const StateMachineSideEffectLoad *base, exprbdd *_addr)
		: StateMachineSideEffectMemoryAccess(_addr, base->rip, base->tag, StateMachineSideEffect::Load),
		  target(base->target), type(base->type)
	{}
	threadAndRegister const target;
	IRType const type;
	void prettyPrint(FILE *f) const {
		fprintf(f, "LOAD %s@%s to %s, type ", tag.name(), rip.name(), target.name());
		ppIRType(type, f);
		fprintf(f, "\naddr = ");
		addr->prettyPrint(f);
	}
	static bool parse(SMScopes *scopes,
			  StateMachineSideEffectLoad **out,
			  const char *str,
			  const char **suffix)
	{
		exprbdd *addr;
		threadAndRegister key(threadAndRegister::invalid());
		IRType type;
		MemoryAccessIdentifier rip(MemoryAccessIdentifier::uninitialised());
		MemoryTag tag;
		if (parseThisString("LOAD ", str, &str) &&
		    tag.parse(str, &str) &&
		    parseThisChar('@', str, &str) &&
		    rip.parse(str, &str) &&
		    parseThisString(" to ", str, &str) &&
		    parseThreadAndRegister(&key, str, &str) &&
		    parseThisString(", type ", str, &str) &&
		    parseIRType(&type, str, &str) &&
		    parseThisString("\naddr = ", str, &str) &&
		    exprbdd::parse(&scopes->exprs, &addr, str, suffix)) {
			*out = new StateMachineSideEffectLoad(key, addr, rip, type, tag);
			return true;
		}
		return false;
	}
	StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations &opt);
	bool definesRegister(threadAndRegister &reg) const {
		reg = target;
		return true;
	}
	IRType _type() const { return type; }
};
class StateMachineSideEffectCopy : public StateMachineSideEffect {
public:
	StateMachineSideEffectCopy(const threadAndRegister &k, exprbdd *_value)
		: StateMachineSideEffect(StateMachineSideEffect::Copy),
		  target(k), value(_value)
	{
	}
	StateMachineSideEffectCopy(const StateMachineSideEffectCopy *base, exprbdd *_value)
		: StateMachineSideEffect(StateMachineSideEffect::Copy),
		  target(base->target),
		  value(_value)
	{}
	threadAndRegister const target;
	exprbdd *const value;
	void prettyPrint(FILE *f) const {
		fprintf(f, "COPY ");
		target.prettyPrint(f);
		fprintf(f, " =\n");
		value->prettyPrint(f);
	}
	static bool parse(SMScopes *scopes, StateMachineSideEffectCopy **out, const char *str, const char **suffix)
	{
		exprbdd *data;
		threadAndRegister key(threadAndRegister::invalid());
		if (parseThisString("COPY ", str, &str) &&
		    parseThreadAndRegister(&key, str, &str) &&
		    parseThisString(" =\n", str, &str) &&
		    exprbdd::parse(&scopes->exprs, &data, str, suffix)) {
			*out = new StateMachineSideEffectCopy(key, data);
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &hv) {
		hv(value);
	}
	StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations &opt);
	void sanityCheck(SMScopes *scopes) const {
		value->sanity_check(&scopes->ordering);
	}
	bool definesRegister(threadAndRegister &reg) const {
		reg = target;
		return true;
	}
};
class StateMachineSideEffectAssertFalse : public StateMachineSideEffect {
public:
	StateMachineSideEffectAssertFalse(bbdd *_value, bool _reflectsActualProgram)
		: StateMachineSideEffect(StateMachineSideEffect::AssertFalse),
		  value(_value),
		  reflectsActualProgram(_reflectsActualProgram)
	{
	}
	StateMachineSideEffectAssertFalse(const StateMachineSideEffectAssertFalse *base,
					  bbdd *_value)
		: StateMachineSideEffect(StateMachineSideEffect::AssertFalse),
		  value(_value),
		  reflectsActualProgram(base->reflectsActualProgram)
	{
	}
	bbdd *const value;
	bool const reflectsActualProgram;
	void prettyPrint(FILE *f) const {
		fprintf(f, "ASSERT %s !", reflectsActualProgram ? "REAL" : "FAKE");
		value->prettyPrint(f);
	}
	static bool parse(SMScopes *scopes, StateMachineSideEffectAssertFalse **out, const char *str, const char **suffix)
	{
		bbdd *data;
		if (!parseThisString("ASSERT ", str, &str))
			return false;
		bool isReal;
		if (parseThisString("REAL ", str, &str)) {
			isReal = true;
		} else if (parseThisString("FAKE ", str, &str)) {
			isReal = false;
		} else {
			return false;
		}
		if (!parseThisChar('!', str, &str) ||
		    !bbdd::parse(&scopes->bools, &data, str, suffix))
			return false;
		*out = new StateMachineSideEffectAssertFalse(data, isReal);
		return true;
	}
	void visit(HeapVisitor &hv) {
		hv(value);
	}
	StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations &opt);
	void sanityCheck(SMScopes *scopes) const {
		assert(reflectsActualProgram == true ||
		       reflectsActualProgram == false);
		value->sanity_check(&scopes->ordering);
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
public:
	static StateMachineSideEffectStartAtomic *get() {
		if (!singleton)
			singleton = new StateMachineSideEffectStartAtomic();
		return singleton;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "START_ATOMIC");
	}
	static bool parse(SMScopes *, StateMachineSideEffectStartAtomic **out, const char *str, const char **suffix)
	{
		if (parseThisString("START_ATOMIC", str, suffix)) {
			*out = StateMachineSideEffectStartAtomic::get();
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &) {}
	StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations &opt);
	void sanityCheck(SMScopes *) const {
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
public:
	static StateMachineSideEffectEndAtomic *get() {
		if (!singleton)
			singleton = new StateMachineSideEffectEndAtomic();
		return singleton;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "END_ATOMIC");
	}
	static bool parse(SMScopes *, StateMachineSideEffectEndAtomic **out, const char *str, const char **suffix)
	{
		if (parseThisString("END_ATOMIC", str, suffix)) {
			*out = StateMachineSideEffectEndAtomic::get();
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &) {}
	StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations &opt);
	void sanityCheck(SMScopes *) const {
	}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
};
class StateMachineSideEffectPhi : public StateMachineSideEffect {
public:
	threadAndRegister const reg;
	IRType const ty;
	class input {
	public:
		threadAndRegister reg;
		exprbdd *val;
		bool operator==(const input &i) const {
			return reg == i.reg && val == i.val;
		}
		bool operator<(const input &o) const {
			if (val < o.val)
				return true;
			if (val > o.val)
				return false;
			return reg < o.reg;
		}
		input(const threadAndRegister &_reg, exprbdd *_val)
			: reg(_reg), val(_val)
		{}
		input()
			: reg(threadAndRegister::invalid()),
			  val(NULL)
		{}
	};
	std::vector<input> const generations;
	StateMachineSideEffectPhi(const threadAndRegister &_reg,
				  IRType _ty,
				  const std::vector<input> &_generations)
		: StateMachineSideEffect(StateMachineSideEffect::Phi),
		  reg(_reg), ty(_ty), generations(_generations)
	{
		for (auto it = generations.begin(); it != generations.end(); it++)
			assert(it->val);
	}
	StateMachineSideEffectPhi(const StateMachineSideEffectPhi *base,
				  const std::vector<input> &_generations)
		: StateMachineSideEffect(StateMachineSideEffect::Phi),
		  reg(base->reg), ty(base->ty), generations(_generations)
	{
		for (auto it = generations.begin(); it != generations.end(); it++)
			assert(it->val);
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "Phi");
		reg.prettyPrint(f);
		fprintf(f, ":%s:\n", nameIRType(ty));
		for (auto it = generations.begin(); it != generations.end(); it++) {
			fprintf(f, "%s --> ", it->reg.name());
			it->val->prettyPrint(f);
		}
	}
	static bool parse(SMScopes *scopes, StateMachineSideEffectPhi **out, const char *str, const char **suffix)
	{
		threadAndRegister key(threadAndRegister::invalid());
		IRType ty;
		if (parseThisString("Phi", str, &str) &&
		    parseThreadAndRegister(&key, str, &str) &&
		    parseThisChar(':', str, &str) &&
		    parseIRType(&ty, str, &str) &&
		    parseThisString(":\n", str, &str)) {
			std::vector<input> generations;
			while (1) {
				input item;
				if (!parseThreadAndRegister(&item.reg, str, &str) ||
				    !parseThisString(" --> ", str, &str) ||
				    !exprbdd::parse(&scopes->exprs, &item.val, str, &str))
					break;
				generations.push_back(item);
			}
			*suffix = str;
			*out = new StateMachineSideEffectPhi(key, ty, generations);
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &hv) {
		for (auto it = generations.begin(); it != generations.end(); it++)
			hv(it->val);
	}
	StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations &opt);
	void sanityCheck(SMScopes *) const {
		assert(generations.size() != 0);
	}
	bool definesRegister(threadAndRegister &reg) const {
		reg = this->reg;
		return true;
	}
};
#if !CONFIG_NO_STATIC_ALIASING
class StateMachineSideEffectStartFunction : public StateMachineSideEffect {
public:
	StateMachineSideEffectStartFunction(exprbdd *_rsp, FrameId _frame)
		: StateMachineSideEffect(StateMachineSideEffect::StartFunction),
		  rsp(_rsp), frame(_frame)
	{
	}
	StateMachineSideEffectStartFunction(StateMachineSideEffectStartFunction *base, exprbdd *_rsp)
		: StateMachineSideEffect(StateMachineSideEffect::StartFunction),
		  rsp(_rsp), frame(base->frame)
	{
	}
	exprbdd *const rsp;
	FrameId const frame;
	void prettyPrint(FILE *f) const {
		fprintf(f, "StartFunction(%s) rsp = ", frame.name());
		rsp->prettyPrint(f);
	}
	static bool parse(SMScopes *scopes, StateMachineSideEffectStartFunction **out, const char *str, const char **suffix)
	{
		exprbdd *data;
		FrameId frame;
		if (parseThisString("StartFunction(", str, &str) &&
		    FrameId::parse(&frame, str, &str) &&
		    parseThisString(") rsp = ", str, &str) &&
		    exprbdd::parse(&scopes->exprs, &data, str, suffix)) {
			*out = new StateMachineSideEffectStartFunction(data, frame);
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &hv) {
		hv(rsp);
	}
	StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations &opt);
	void sanityCheck(SMScopes *scopes) const {
		rsp->sanity_check(&scopes->ordering);
		assert(rsp->type() == Ity_I64);
	}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
	bool operator==(const StateMachineSideEffectStartFunction &o) const {
		return rsp == o.rsp && frame == o.frame;
	}
};
class StateMachineSideEffectEndFunction : public StateMachineSideEffect {
public:
	StateMachineSideEffectEndFunction(exprbdd *_rsp, FrameId _frame)
		: StateMachineSideEffect(StateMachineSideEffect::EndFunction),
		  rsp(_rsp), frame(_frame)
	{
	}
	StateMachineSideEffectEndFunction(StateMachineSideEffectEndFunction *base, exprbdd *_rsp)
		: StateMachineSideEffect(StateMachineSideEffect::EndFunction),
		  rsp(_rsp), frame(base->frame)
	{
	}
	exprbdd *const rsp;
	FrameId const frame;
	void prettyPrint(FILE *f) const {
		fprintf(f, "EndFunction(%s) rsp = ", frame.name());
		rsp->prettyPrint(f);
	}
	static bool parse(SMScopes *scopes, StateMachineSideEffectEndFunction **out, const char *str, const char **suffix)
	{
		exprbdd *rsp;
		FrameId frame;
		if (parseThisString("EndFunction(", str, &str) &&
		    FrameId::parse(&frame, str, &str) &&
		    parseThisString(") rsp = ", str, &str) &&
		    exprbdd::parse(&scopes->exprs, &rsp, str, suffix)) {
			*out = new StateMachineSideEffectEndFunction(rsp, frame);
			return true;
		}
		return false;
	}
	void visit(HeapVisitor &hv) {
		hv(rsp);
	}
	StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations &opt);
	void sanityCheck(SMScopes *scopes) const {
		rsp->sanity_check(&scopes->ordering);
		assert(rsp->type() == Ity_I64);
	}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
	bool operator==(const StateMachineSideEffectEndFunction &o) const {
		return rsp == o.rsp && frame == o.frame;
	}
};
#endif
class StateMachineSideEffectImportRegister : public StateMachineSideEffect {
public:
	threadAndRegister const reg;
	unsigned const tid;
	unsigned const vex_offset;
#if !CONFIG_NO_STATIC_ALIASING
	PointerAliasingSet const set;
#endif
	StateMachineSideEffectImportRegister(
		const threadAndRegister &_reg,
		unsigned _tid,
		unsigned _vex_offset
#if !CONFIG_NO_STATIC_ALIASING
		, const PointerAliasingSet &_set
#endif
					     )
		: StateMachineSideEffect(StateMachineSideEffect::ImportRegister),
		  reg(_reg), tid(_tid), vex_offset(_vex_offset)
#if !CONFIG_NO_STATIC_ALIASING
		, set(_set)
#endif
	{}
	StateMachineSideEffectImportRegister(
		const StateMachineSideEffectImportRegister *base,
		const threadAndRegister &_reg)
		: StateMachineSideEffect(StateMachineSideEffect::ImportRegister),
		  reg(_reg), tid(base->tid), vex_offset(base->vex_offset)
#if !CONFIG_NO_STATIC_ALIASING
		, set(base->set)
#endif
	{}
	void visit(HeapVisitor &) {}
	StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations&) { return this; }
	void sanityCheck(SMScopes *) const {}
	bool definesRegister(threadAndRegister &tr) const {
		tr = reg;
		return true;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "INITIALVALUE %s = %d:0x%x"
#if !CONFIG_NO_STATIC_ALIASING
			":%s"
#endif
			,reg.name(), tid, vex_offset
#if !CONFIG_NO_STATIC_ALIASING
			, set.name()
#endif
			);
	}
	static bool parse(SMScopes *, StateMachineSideEffectImportRegister **out, const char *str, const char **suffix)
	{
		threadAndRegister reg(threadAndRegister::invalid());
		unsigned tid;
		unsigned long vex_offset;
#if !CONFIG_NO_STATIC_ALIASING
		PointerAliasingSet set(PointerAliasingSet::nothing);
#endif
		if (parseThisString("INITIALVALUE ", str, &str) &&
		    parseThreadAndRegister(&reg, str, &str) &&
		    parseThisString(" = ", str, &str) &&
		    parseDecimalUInt(&tid, str, &str) &&
		    parseThisChar(':', str, &str) &&
#if !CONFIG_NO_STATIC_ALIASING
		    parseHexUlong(&vex_offset, str, &str) &&
		    parseThisChar(':', str, &str) &&
		    set.parse(str, suffix)
#else
		    parseHexUlong(&vex_offset, str, suffix)
#endif
		    ) {
			*out = new StateMachineSideEffectImportRegister(reg, tid, vex_offset
#if !CONFIG_NO_STATIC_ALIASING
									, set
#endif
									);
			return true;
		}
		return false;
	}
	bool operator==(const StateMachineSideEffectImportRegister &o) const {
		return reg == o.reg && tid == o.tid && vex_offset == o.vex_offset
#if !CONFIG_NO_STATIC_ALIASING
			&& set == o.set
#endif
			;
	}

};
#if !CONFIG_NO_STATIC_ALIASING
class StateMachineSideEffectStackLayout : public StateMachineSideEffect {
public:
	class entry : public Named {
		char *mkName() const {
			return my_asprintf("%s{%s%s%s}",
					   frame.name(),
					   pointsAtSelf ? "self" : "",
					   pointsAtSelf && pointedAtByOthers ? "," : "",
					   pointedAtByOthers ? "other" : "");
		}
	public:
		FrameId frame;
		bool pointsAtSelf;
		bool pointedAtByOthers;
		entry(const FrameId &_frame,
		      bool _pointsAtSelf,
		      bool _pointedAtByOthers)
			: frame(_frame), pointsAtSelf(_pointsAtSelf),
			  pointedAtByOthers(_pointedAtByOthers)
		{}
		entry() {}
		bool operator==(const entry &o) const {
			return frame == o.frame &&
				pointsAtSelf == o.pointsAtSelf &&
				pointedAtByOthers == o.pointedAtByOthers;
		}
		bool parse(const char *str, const char **end) {
			FrameId f;
			if (!FrameId::parse(&f, str, &str))
				return false;
			bool pas = false;
			bool pao = false;
			if (parseThisString("{", str, &str)) {
				if (parseThisString("self", str, &str)) {
					pas = true;
					if (parseThisString(",other", str, &str))
						pao = true;
				} else if (parseThisString("other", str, &str)) {
					pao = true;
				}
				if (!parseThisString("}", str, end))
					return false;
			} else if (parseThisString(" <mem>", str, end)) {
				/* Old format */
				pas = true;
				pao = true;
			} else if (str[0] == '}' || str[0] == ',') {
				/* Also old format */
				*end = str;
				pas = false;
				pao = false;
			} else {
				return false;
			}
			frame = f;
			pointsAtSelf = pas;
			pointedAtByOthers = pao;
			clearName();
			return true;
		}
	};
	std::vector<entry> const functions;
	StateMachineSideEffectStackLayout(
		const std::vector<entry> &_functions)
		: StateMachineSideEffect(StateMachineSideEffect::StackLayout),
		  functions(_functions)
	{}
	void visit(HeapVisitor &) {}
	StateMachineSideEffect *optimise(SMScopes *, const AllowableOptimisations &) { return this; }
	void sanityCheck(SMScopes *) const {
#ifndef NDEBUG
		/* No dupes */
		for (auto it1 = functions.begin();
		     it1 != functions.end();
		     it1++) {
			for (auto it2 = it1 + 1;
			     it2 != functions.end();
			     it2++)
				assert(it1->frame != it2->frame);
			assert(it1->pointsAtSelf == true ||
			       it1->pointsAtSelf == false);
			assert(it1->pointedAtByOthers == true ||
			       it1->pointedAtByOthers == false);
		}
#endif
	}
	bool definesRegister(threadAndRegister &) const {
		return false;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "STACKLAYOUT = {");
		for (auto it = functions.begin(); it != functions.end(); it++) {
			if (it != functions.begin())
				fprintf(f, ", ");
			fprintf(f, "%s", it->name());
		}
		fprintf(f, "}");
	}
	static bool parse(SMScopes *, StateMachineSideEffectStackLayout **out, const char *str, const char **suffix)
	{
		std::vector<entry> functions;

		if (!parseThisString("STACKLAYOUT", str, &str))
			return false;
		if (parseThisChar('(', str, &str)) {
			/* Old-style format includes some information
			 * we no longer need. */
			int d;
			if (!parseDecimalInt(&d, str, &str) ||
			    !parseThisChar(')', str, &str))
				return false;
		}
		if (!parseThisString(" = {", str, &str))
			return false;
		while (1) {
			entry f;
			if (!f.parse(str, &str))
				return false;
			functions.push_back(f);
			if (parseThisChar('}', str, suffix))
				break;
			if (!parseThisString(", ", str, &str))
				return false;
		}
		*out = new StateMachineSideEffectStackLayout(functions);
		return true;
	}
	bool operator==(const StateMachineSideEffectStackLayout &o) const {
		return functions == o.functions;
	}
};
#endif

void printStateMachine(const StateMachine *sm, FILE *f);
void printStateMachine(const StateMachine *sm, FILE *f,
		       std::map<const StateMachineState *, int> &labels);
void printStateMachinePair(const char *label1,
			   const StateMachine *sm1,
			   const char *label2,
			   const StateMachine *sm2,
			   FILE *f);
void printStateMachine(const StateMachineState *sm, FILE *f);
void printStateMachine(const StateMachineState *sm,
		       FILE *f,
		       std::map<const StateMachineState *, int> &labels);
void printStateMachine(const std::set<const StateMachineState *> &sm,
		       FILE *f,
		       std::map<const StateMachineState *, int> &labels);
bool sideEffectsBisimilar(StateMachineSideEffect *smse1,
			  StateMachineSideEffect *smse2,
			  const AllowableOptimisations &opt);
bool parseStateMachine(SMScopes *scopes,
		       StateMachine **out,
		       const char *str,
		       const char **suffix,
		       std::map<CfgLabel, const CFGNode *> &labels);
static inline bool parseStateMachine(SMScopes *scopes,
				     StateMachine **out,
				     const char *str,
				     const char **suffix)
{
	std::map<CfgLabel, const CFGNode *> labels;
	return parseStateMachine(scopes, out, str, suffix, labels);
}	
StateMachine *readStateMachine(SMScopes *scopes, int fd);
StateMachine *readStateMachine(SMScopes *scopes, const char *fname);

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
		if (!s)
			continue;
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
		if (!s)
			continue;
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
