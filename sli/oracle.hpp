#ifndef ORACLE_HPP__
#define ORACLE_HPP__

#include <set>
#include "state_machine.hpp"
#include "mapping.hpp"

#include "libvex_guest_offsets.h"

#include "oracle_rip.hpp"

class TypesDb;
class DynAnalysisRip;

class InstructionSet {
public:
	std::set<VexRip> rips;
};

class AllowableOptimisations;

/* Use these rather than VexRips for static analysis, because that
   leads to much better performance and general niceness.  It doesn't
   make any real difference to any of the static analyses which we
   actually perform, since they're all function-local anyway. */
class StaticRip : public Named {
	char *mkName() const { return my_asprintf("static_rip:%lx", rip); }
public:
	explicit StaticRip(unsigned long r) : rip(r) {}
	explicit StaticRip(const VexRip &r) : rip(r.isValid() ? r.unwrap_vexrip() : 0) {}
	explicit StaticRip(const DynAnalysisRip &r)
		: rip(r.rips[r.nr_rips-1])
	{}

	StaticRip() : rip(0) {}

	bool isValid() const { return rip != 0; }
	VexRip makeVexRip(const VexRip &useStackOf);

#define mk_operator(op)							\
	bool operator op (const StaticRip &r) const { return rip op r.rip; }
	mk_operator(==)
	mk_operator(!=)
	mk_operator(<)
	mk_operator(<=)
	mk_operator(>)
	mk_operator(>=)
#undef mk_operator

	unsigned long rip;
};

/* All of the information from sources other than the main crash dump.
 * Information from the oracle will be true of some executions but not
 * necessarily all of them, so should only really be used where static
 * analysis is insufficient. */
class Oracle : public GarbageCollected<Oracle> {
public:
	static const int NR_REGS = 16;

	class LivenessSet : public Named {
	public:
		unsigned long mask;

		LivenessSet() : mask(0) {}

		LivenessSet use(Int offset);
		LivenessSet define(threadAndRegister offset);

		void operator |=(const LivenessSet x) { mask |= x.mask; clearName(); }
		bool operator !=(const LivenessSet x) { return mask != x.mask; }
		LivenessSet operator &(const LivenessSet x) { return LivenessSet(mask & x.mask); }
		bool isLive(Int offset) const;
		static LivenessSet everything;
		static LivenessSet argRegisters;
		LivenessSet(unsigned long _m) : mask(_m) {}
	private:
		char *mkName() const {
			int i;
			char *acc;
			char *acc2;
			bool first = true;
			acc = strdup("<");
			for (i = 0; i < NR_REGS; i++) {
				if (!(mask & (1ul << i)))
					continue;
				if (!first) {
					acc2 = my_asprintf("%s|", acc);
					free(acc);
					acc = acc2;
				}
				first = false;
				switch (i * 8) {
#define do_reg(name) case OFFSET_amd64_ ## name : acc2 = my_asprintf("%s" #name , acc); break
					do_reg(RAX);
					do_reg(RDX);
					do_reg(RCX);
					do_reg(RBX);
					do_reg(RSP);
					do_reg(RBP);
					do_reg(RSI);
					do_reg(RDI);
					do_reg(R8);
					do_reg(R9);
					do_reg(R10);
					do_reg(R11);
					do_reg(R12);
					do_reg(R13);
					do_reg(R14);
					do_reg(R15);
#undef do_reg
				default:
					abort();
				}
				free(acc);
				acc = acc2;
			}
			acc2 = my_asprintf("%s>", acc);
			free(acc);
			return acc2;
		}
	};

	class ThreadRegisterAliasingConfiguration;

	class Function : public Named {
		friend class Oracle;

	public:
		StaticRip rip;
	private:
		void *operator new(size_t s); /* DNI */
		char *mkName() const { return my_asprintf("function_%s", rip.name()); }
		void getInstructionsInFunction(std::vector<StaticRip> &out) const;
		void updateLiveOnEntry(const StaticRip &rip, AddressSpace *as, bool *changed, Oracle *oracle);
		void updateRbpToRspOffset(const StaticRip &rip, AddressSpace *as, bool *changed, Oracle *oracle);
		void addPredecessorsDirect(const StaticRip &rip, std::vector<StaticRip> &out);
		void addPredecessorsNonCall(const StaticRip &rip, std::vector<StaticRip> &out);
		void addPredecessorsCall(const StaticRip &rip, std::vector<StaticRip> &out);
		void addPredecessorsReturn(const StaticRip &rip, std::vector<StaticRip> &out);
		void updateSuccessorInstructionsAliasing(const StaticRip &rip, AddressSpace *as, std::vector<StaticRip> *changed,
							 bool *done_something, Oracle *oracle);
		void getInstructionFallThroughs(const StaticRip &rip, std::vector<StaticRip> &out);
		void getInstructionCallees(const StaticRip &rip, std::vector<StaticRip> &out, Oracle *oracle);
		void getSuccessors(const StaticRip &rip, std::vector<StaticRip> &succ);
		void getFunctionCallers(std::vector<StaticRip> &out, Oracle *oracle);
		bool registerLivenessCorrect() const;
		void setRegisterLivenessCorrect(bool v);
		bool rbpToRspOffsetsCorrect() const;
		void setRbpToRspOffsetsCorrect(bool v);
		bool aliasingConfigCorrect() const;
		void setAliasingConfigCorrect(bool v);
	public:
		Function(const StaticRip &_rip)
			: rip(_rip)
		{}

		LivenessSet liveOnEntry(const StaticRip &, bool);
		bool aliasConfigOnEntryToInstruction(const StaticRip &rip, ThreadRegisterAliasingConfiguration *out);
		ThreadRegisterAliasingConfiguration aliasConfigOnEntryToInstruction(const StaticRip &rip);
		ThreadRegisterAliasingConfiguration aliasConfigOnEntryToInstruction(const StaticRip &rip, bool *b);
		void setAliasConfigOnEntryToInstruction(const StaticRip &rip, const ThreadRegisterAliasingConfiguration &config);
		void resolveCallGraph(Oracle *oracle);
		bool addInstruction(const StaticRip &rip,
				    bool isReturn,
				    const std::vector<StaticRip> &callees,
				    const std::vector<StaticRip> &fallThrough,
				    const std::vector<StaticRip> &callSucc,
				    const std::vector<StaticRip> &branch);
		void calculateRegisterLiveness(AddressSpace *as, bool *done_something, Oracle *oracle);
		void calculateRbpToRspOffsets(AddressSpace *as, Oracle *oracle);
		void calculateAliasing(AddressSpace *as, bool *done_something, Oracle *oracle);

		void visit(HeapVisitor &hv) { }
		NAMED_CLASS
	};

	/* Pointer aliasing stuff.  Note that ``stack'' in this
	   context means the *current* stack frame: a pointer without
	   the stack bit set could still point into a *calling*
	   functions' stack frame, and that wouldn't be a bug. */
	class PointerAliasingSet : public Named {
		friend class ThreadRegisterAliasingConfiguration;
		             
		int v;
		char *mkName() const {
			const char *r;
			switch (v) {
			case 0:
				r = "()";
				break;
			case 1:
				r = "not-a-pointer";
				break;
			case 2:
				r = "stack-pointer";
				break;
			case 3:
				r = "not-a-pointer|stack-pointer";
				break;
			case 4:
				r = "non-stack-pointer";
				break;
			case 5:
				r = "not-a-pointer|non-stack-pointer";
				break;
			case 6:
				r = "stack-pointer|non-stack-pointer";
				break;
			case 7:
				r = "*";
				break;
			default:
				abort();
			}
			return strdup(r);
		}
		PointerAliasingSet() : v(0xf001dead) {}
	public:
		PointerAliasingSet(int _v) : v(_v) {}

		static const PointerAliasingSet notAPointer;
		static const PointerAliasingSet stackPointer;
		static const PointerAliasingSet nonStackPointer;
		static const PointerAliasingSet anything;

		PointerAliasingSet operator |(PointerAliasingSet o) const { return PointerAliasingSet(v | o.v); }
		PointerAliasingSet operator &(PointerAliasingSet o) const { return PointerAliasingSet(v & o.v); }
		PointerAliasingSet operator ~() const { return PointerAliasingSet(~v); }
		bool operator !=(PointerAliasingSet o) const { return v != o.v; }
		operator bool() const { return v != 0; }
		operator unsigned long() const { return v; }
	};
	class ThreadRegisterAliasingConfiguration {
		friend ThreadRegisterAliasingConfiguration Function::aliasConfigOnEntryToInstruction(const StaticRip &rip,
											       bool *b);
		ThreadRegisterAliasingConfiguration(float x); /* initialise as function entry configuration */
		ThreadRegisterAliasingConfiguration(float x, int y); /* initialise as unknown configuration */
	public:
		ThreadRegisterAliasingConfiguration() : stackHasLeaked(false) {}
		bool stackHasLeaked;
		PointerAliasingSet v[NR_REGS];
		
		void operator|=(const ThreadRegisterAliasingConfiguration &src) {
			stackHasLeaked |= src.stackHasLeaked;
			for (int i = 0; i < NR_REGS; i++)
				v[i] = v[i] | src.v[i];
		}
		bool operator != (const ThreadRegisterAliasingConfiguration &x) const {
			if (stackHasLeaked != x.stackHasLeaked)
				return true;
			for (int i = 0; i < NR_REGS; i++)
				if (v[i] != x.v[i])
					return true;
			return false;
		}
		/* This should be const, but C++ can't quite manage the
		 * initialisation in that case, poor thing. */
		static ThreadRegisterAliasingConfiguration functionEntryConfiguration;

		/* Any aliasing pattern possible. */
		static ThreadRegisterAliasingConfiguration unknown;

		void prettyPrint(FILE *) const;
	};

	class RegisterAliasingConfiguration {
	public:
		std::vector<std::pair<unsigned, ThreadRegisterAliasingConfiguration> > content;

		PointerAliasingSet lookupRegister(const threadAndRegister &r) const;
		void set(const threadAndRegister &, const PointerAliasingSet &);
		void addConfig(unsigned tid, const ThreadRegisterAliasingConfiguration &config);

		/* Check whether a and b mght point at the same bit of
		   memory (i.e. have intersecting pointer aliasing
		   sets) given @this's register aliasing
		   configuration.  Note that this assumes that both @a
		   and @b are pointers i.e. it's not just asking
		   whether @a and @b might be equal. */
		bool ptrsMightAlias(IRExpr *a, IRExpr *b, bool) const;

		/* Check whether there's any possibility of @a being a
		   pointer to a non-stack location. */
		bool mightPointOutsideStack(IRExpr *a) const;
	};

	RegisterAliasingConfiguration getAliasingConfiguration(const std::vector<std::pair<unsigned, VexRip> > &rips);

	struct callgraph_entry {
		bool is_call;
		std::set<unsigned long> targets;
	};
	typedef std::map<StaticRip, callgraph_entry> callgraph_t;

	struct tag_entry {
		std::set<DynAnalysisRip> shared_loads;
		std::set<DynAnalysisRip> shared_stores;
		std::set<DynAnalysisRip> private_loads;
		std::set<DynAnalysisRip> private_stores;
	};
	TypesDb *type_index;
	Mapping raw_types_database;
	static unsigned long fetchTagEntry(tag_entry *te,
					   const Mapping &mapping,
					   unsigned long offset);

	static IRSB *getIRSBForRip(AddressSpace *as, const StaticRip &sr);
	static IRSB *getIRSBForRip(AddressSpace *as, const VexRip &sr);
	IRSB *getIRSBForRip(const VexRip &vr);

private:

	void discoverFunctionHead(const StaticRip &x, std::vector<StaticRip> &heads, const callgraph_t &callgraph_table);
	void buildReturnAddressTable();
	static void calculateRegisterLiveness(VexPtr<Oracle> &ths, GarbageCollectionToken token);
	static void calculateRbpToRspOffsets(VexPtr<Oracle> &ths, GarbageCollectionToken token);
	static void calculateAliasing(VexPtr<Oracle> &ths, GarbageCollectionToken token);
	void loadTagTable(const char *path);
	void findPossibleJumpTargets(const StaticRip &from, const callgraph_t &callgraph_table, std::vector<StaticRip> &targets);
	StaticRip functionHeadForInstruction(const StaticRip &rip);

	enum RbpToRspOffsetState {
		RbpToRspOffsetStateImpossible,
		RbpToRspOffsetStateValid,
		RbpToRspOffsetStateUnknown
	};
	void getRbpToRspOffset(const StaticRip &rip, RbpToRspOffsetState *state, unsigned long *offset);
	void setRbpToRspOffset(const StaticRip &rip, RbpToRspOffsetState state, unsigned long offset);

public:
	static void loadCallGraph(VexPtr<Oracle> &ths, const char *path, GarbageCollectionToken token);
	void visit(HeapVisitor &hv) {
		hv(ms);
		hv(crashedThread);
		hv(type_index);
	}

	MachineState *ms;
	Thread *crashedThread;

	static const unsigned STATIC_THREAD = 712;

	void findPreviousInstructions(std::vector<VexRip> &output);
	void findPreviousInstructions(std::vector<VexRip> &output, const VexRip &rip);
	void findConflictingStores(StateMachineSideEffectLoad *smsel,
				   std::set<DynAnalysisRip> &out);
	void clusterRips(const std::set<VexRip> &inputRips,
			 std::set<InstructionSet > &outputClusters);

	/* True if the access doesn't appear anywhere in the tag
	   table.  This usually indicates that the relevant
	   instruction is accessing the stack. */
	bool notInTagTable(StateMachineSideEffectMemoryAccess *access);
	/* True if any table entry which includes @access as a
	 * non-private entry also includes a non-private store
	 * entry. */
	/* i.e. this is true if there's some possibility that @access
	 * might alias with a store in a remote thread. */
	bool hasConflictingRemoteStores(StateMachineSideEffectMemoryAccess *access);

	bool memoryAccessesMightAlias(const AllowableOptimisations &, StateMachineSideEffectLoad *, StateMachineSideEffectLoad *);
	bool memoryAccessesMightAlias(const AllowableOptimisations &, StateMachineSideEffectLoad *, StateMachineSideEffectStore *);
	bool memoryAccessesMightAlias(const AllowableOptimisations &, StateMachineSideEffectStore *, StateMachineSideEffectStore *);
	void findRacingRips(const AllowableOptimisations &, StateMachineSideEffectLoad *, std::set<DynAnalysisRip> &);
	void findRacingRips(StateMachineSideEffectStore *, std::set<DynAnalysisRip> &);
	bool functionCanReturn(const VexRip &rip);

	static void discoverFunctionHeads(VexPtr<Oracle> &ths, std::vector<StaticRip> &heads,
					  const callgraph_t &callgraph,
					  GarbageCollectionToken token);

	void getFunctions(std::vector<StaticRip> &out);

	VexRip dominator(const std::set<VexRip> &instrs,
			    AddressSpace *as,
			    unsigned minimum_size);

	ThreadRegisterAliasingConfiguration getAliasingConfigurationForRip(const StaticRip &rip);
	LivenessSet liveOnEntryToFunction(const StaticRip &rip);

	bool getRbpToRspDelta(const StaticRip &rip, long *out);

	ThreadRegisterAliasingConfiguration getAliasingConfigurationForRip(const VexRip &rip);
	bool getRbpToRspDelta(const VexRip &rip, long *out);
	LivenessSet liveOnEntryToFunction(const VexRip &rip);

	void getInstrCallees(const VexRip &vr, std::vector<VexRip> &out);
	void getInstrFallThroughs(const VexRip &vr, std::vector<VexRip> &out);

	bool isFunctionHead(const VexRip &vr);
	void getPossibleStackTruncations(const VexRip &vr,
					 std::vector<unsigned long> &callers);
	void findPredecessors(const VexRip &vr, bool includeCallPredecessors, std::vector<VexRip> &out);

	bool isPltCall(const VexRip &vr);

	~Oracle() { }
	Oracle(MachineState *_ms, Thread *_thr, const char *tags)
		: ms(_ms), crashedThread(_thr)
	{
		if (tags)
			loadTagTable(tags);
	}

	NAMED_CLASS
};

template <typename a, typename b> unsigned long
hash_pair(const std::pair<a, b> &p)
{
	return __default_hash_function(p.first) + 11 * __default_hash_function(p.second);
}

typedef gc_map<std::pair<VexRip, VexRip>,
	       bool,
	       hash_pair,
	       __default_eq_function<std::pair<VexRip, VexRip> >,
	       __default_visit_function<std::pair<VexRip, VexRip>, bool>,
	       &ir_heap> gc_pair_VexRip_set_t;
//void mergeUlongSets(gc_pair_ulong_set_t *dest, const gc_pair_ulong_set_t *src);

void findInstrSuccessorsAndCallees(AddressSpace *as,
				   const VexRip &rip,
				   std::vector<VexRip> &directExits,
				   gc_pair_VexRip_set_t *callees);

StateMachine *introduceFreeVariables(StateMachine *sm,
				     const Oracle::RegisterAliasingConfiguration *alias,
				     const AllowableOptimisations &opt,
				     Oracle *oracle,
				     bool *done_something);

unsigned getInstructionSize(AddressSpace *as, const VexRip &rip);

#endif /* !ORACLE_H__ */
