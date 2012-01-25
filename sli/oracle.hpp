#ifndef ORACLE_HPP__
#define ORACLE_HPP__

#include <set>
#include "state_machine.hpp"
#include "mapping.hpp"

#include "libvex_guest_offsets.h"

class InstructionSet {
public:
	std::set<unsigned long> rips;
};

class OracleInterface : public GarbageCollected<OracleInterface> {
public:
	virtual ~OracleInterface() {}
	virtual bool storeIsThreadLocal(StateMachineSideEffectStore *) = 0;
	virtual bool loadIsThreadLocal(StateMachineSideEffectLoad *) = 0;
	virtual bool memoryAccessesMightAlias(StateMachineSideEffectLoad *,
					      StateMachineSideEffectStore *) = 0;
	virtual bool memoryAccessesMightAlias(StateMachineSideEffectLoad *,
					      StateMachineSideEffectLoad *) = 0;
	virtual bool memoryAccessesMightAlias(StateMachineSideEffectStore *,
					      StateMachineSideEffectStore *) = 0;
	virtual bool getRbpToRspDelta(unsigned long rip, long *out) = 0;
	NAMED_CLASS
};

/* All of the information from sources other than the main crash dump.
 * Information from the oracle will be true of some executions but not
 * necessarily all of them, so should only really be used where static
 * analysis is insufficient. */
class Oracle : public OracleInterface {
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

	class RegisterAliasingConfiguration;

	class Function : public Named {
		friend class Oracle;

	public:
		unsigned long rip;
	private:
		void *operator new(size_t s); /* DNI */
		char *mkName() const { return my_asprintf("function_%lx", rip); }
		void getInstructionsInFunction(std::vector<unsigned long> &out) const;
		void updateLiveOnEntry(unsigned long rip, AddressSpace *as, bool *changed, Oracle *oracle);
		void updateRbpToRspOffset(unsigned long rip, AddressSpace *as, bool *changed, Oracle *oracle);
		void addPredecessorsNonCall(unsigned long rip, std::vector<unsigned long> &out);
		void addPredecessors(unsigned long rip, std::vector<unsigned long> &out);
		void updateSuccessorInstructionsAliasing(unsigned long rip, AddressSpace *as, std::vector<unsigned long> *changed,
							 Oracle *oracle);
		void getInstructionFallThroughs(unsigned long rip, std::vector<unsigned long> &out);
		void getInstructionCallees(unsigned long rip, std::vector<unsigned long> &out, Oracle *oracle);
		void getSuccessors(unsigned long rip, std::vector<unsigned long> &succ);
		void getFunctionCallers(std::vector<unsigned long> &out, Oracle *oracle);
		bool registerLivenessCorrect() const;
		void setRegisterLivenessCorrect(bool v);
		bool rbpToRspOffsetsCorrect() const;
		void setRbpToRspOffsetsCorrect(bool v);
		bool aliasingConfigCorrect() const;
		void setAliasingConfigCorrect(bool v);
		bool exists() const;
	public:
		Function(unsigned long _rip)
			: rip(_rip)
		{}

		LivenessSet liveOnEntry(unsigned long, bool);
		bool aliasConfigOnEntryToInstruction(unsigned long rip, RegisterAliasingConfiguration *out);
		RegisterAliasingConfiguration aliasConfigOnEntryToInstruction(unsigned long rip);
		RegisterAliasingConfiguration aliasConfigOnEntryToInstruction(unsigned long rip, bool *b);
		void setAliasConfigOnEntryToInstruction(unsigned long rip, const RegisterAliasingConfiguration &config);
		void resolveCallGraph(Oracle *oracle);
		bool addInstruction(unsigned long rip,
				    const std::vector<unsigned long> &callees,
				    const std::vector<unsigned long> &fallThrough,
				    const std::vector<unsigned long> &branch);
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
		friend class RegisterAliasingConfiguration;
		             
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
	class RegisterAliasingConfiguration {
		friend RegisterAliasingConfiguration Function::aliasConfigOnEntryToInstruction(unsigned long rip,
											       bool *b);
		RegisterAliasingConfiguration(float x); /* initialise as function entry configuration */
		RegisterAliasingConfiguration(float x, int y); /* initialise as unknown configuration */
		RegisterAliasingConfiguration() : stackHasLeaked(false) {}
	public:
		bool stackHasLeaked;
		PointerAliasingSet v[NR_REGS];
		
		void operator|=(const RegisterAliasingConfiguration &src) {
			stackHasLeaked |= src.stackHasLeaked;
			for (int i = 0; i < NR_REGS; i++)
				v[i] = v[i] | src.v[i];
		}
		bool operator != (const RegisterAliasingConfiguration &x) const {
			if (stackHasLeaked != x.stackHasLeaked)
				return true;
			for (int i = 0; i < NR_REGS; i++)
				if (v[i] != x.v[i])
					return true;
			return false;
		}
		/* This should be const, but C++ can't quite manage the
		 * initialisation in that case, poor thing. */
		static RegisterAliasingConfiguration functionEntryConfiguration;

		/* Any aliasing pattern possible. */
		static RegisterAliasingConfiguration unknown;

		/* Check whether a and b mght point at the same bit of
		   memory (i.e. have intersecting pointer aliasing
		   sets) given @this's register aliasing
		   configuration.  Note that this assumes that both @a
		   and @b are pointers i.e. it's not just asking
		   whether @a and @b might be equal. */
		bool ptrsMightAlias(IRExpr *a, IRExpr *b, bool) const;

		void prettyPrint(FILE *) const;
	};

	struct tag_entry {
		std::set<unsigned long> loads;
		std::set<unsigned long> stores;
	};
	std::vector<tag_entry> tag_table;
private:
	static const unsigned nr_memory_filter_words = 10267;
	static unsigned long hashRipPair(unsigned long a, unsigned long b) {
		unsigned long h = a + b * 202693;
		while (h >= (nr_memory_filter_words * 64))
			h = (h % (nr_memory_filter_words * 64)) ^ (h / (nr_memory_filter_words * 64));
		assert(h / 64 < nr_memory_filter_words);
		return h;
	}
	unsigned long memoryAliasingFilter[nr_memory_filter_words];
	unsigned long memoryAliasingFilter2[nr_memory_filter_words];
	std::set<std::pair<unsigned long, unsigned long> > *aliasingTable;

	void discoverFunctionHead(unsigned long x, std::vector<unsigned long> &heads);
	static void calculateRegisterLiveness(VexPtr<Oracle> &ths, GarbageCollectionToken token);
	static void calculateRbpToRspOffsets(VexPtr<Oracle> &ths, GarbageCollectionToken token);
	static void calculateAliasing(VexPtr<Oracle> &ths, GarbageCollectionToken token);
	void loadTagTable(const char *path);
	Mapping callGraphMapping;
	void findPossibleJumpTargets(unsigned long from, std::vector<unsigned long> &targets);
	unsigned long functionHeadForInstruction(unsigned long rip);

	enum RbpToRspOffsetState {
		RbpToRspOffsetStateImpossible,
		RbpToRspOffsetStateValid,
		RbpToRspOffsetStateUnknown
	};
	void getRbpToRspOffset(unsigned long rip, RbpToRspOffsetState *state, unsigned long *offset);
	void setRbpToRspOffset(unsigned long rip, RbpToRspOffsetState state, unsigned long offset);

	void visit(HeapVisitor &hv) {
		hv(ms);
		hv(crashedThread);
	}

public:
	static void loadCallGraph(VexPtr<Oracle> &ths, const char *path, GarbageCollectionToken token);
	MachineState *ms;
	Thread *crashedThread;

	static const unsigned STATIC_THREAD = 712;

	void findPreviousInstructions(std::vector<unsigned long> &output);
	void findPreviousInstructions(std::vector<unsigned long> &output, unsigned long rip);
	void findConflictingStores(StateMachineSideEffectLoad *smsel,
				   std::set<unsigned long> &out);
	void clusterRips(const std::set<unsigned long> &inputRips,
			 std::set<InstructionSet> &outputClusters);
	bool storeIsThreadLocal(StateMachineSideEffectStore *s);
	bool loadIsThreadLocal(StateMachineSideEffectLoad *s);
	bool memoryAccessesMightAlias(StateMachineSideEffectLoad *, StateMachineSideEffectLoad *);
	bool memoryAccessesMightAlias(StateMachineSideEffectLoad *, StateMachineSideEffectStore *);
	bool memoryAccessesMightAlias(StateMachineSideEffectStore *, StateMachineSideEffectStore *);
	void findRacingRips(StateMachineSideEffectLoad *, std::set<unsigned long> &);
	void findRacingRips(StateMachineSideEffectStore *, std::set<unsigned long> &);
	bool functionCanReturn(unsigned long rip);

	static void discoverFunctionHeads(VexPtr<Oracle> &ths, std::vector<unsigned long> &heads, GarbageCollectionToken token);

	void getFunctions(std::vector<unsigned long> &out);

	unsigned long dominator(const std::set<unsigned long> &instrs,
				AddressSpace *as,
				unsigned minimum_size);

	void getAllMemoryAccessingInstructions(std::vector<unsigned long> &out) const;

	RegisterAliasingConfiguration getAliasingConfigurationForRip(unsigned long rip);
	LivenessSet liveOnEntryToFunction(unsigned long rip);

	bool getRbpToRspDelta(unsigned long rip, long *out);

	~Oracle() { delete aliasingTable; }
	Oracle(MachineState *_ms, Thread *_thr, const char *tags)
		: ms(_ms), crashedThread(_thr)
	{
		aliasingTable = new std::set<std::pair<unsigned long, unsigned long> >();
		if (tags)
			loadTagTable(tags);
	}
};

extern unsigned long hash_ulong_pair(const std::pair<unsigned long, unsigned long> &p);
typedef gc_map<std::pair<unsigned long, unsigned long>,
	       bool,
	       hash_ulong_pair,
	       __default_eq_function<std::pair<unsigned long, unsigned long> >,
	       __default_visit_function<std::pair<unsigned long, unsigned long>, bool>,
	       &ir_heap> gc_pair_ulong_set_t;
void mergeUlongSets(gc_pair_ulong_set_t *dest, const gc_pair_ulong_set_t *src);

void findInstrSuccessorsAndCallees(AddressSpace *as,
				   unsigned long rip,
				   std::vector<unsigned long> &directExits,
				   gc_pair_ulong_set_t *callees);

StateMachine *introduceFreeVariables(StateMachine *sm,
				     const Oracle::RegisterAliasingConfiguration &alias,
				     const AllowableOptimisations &opt,
				     OracleInterface *oracle,
				     bool *done_something);
unsigned getInstructionSize(AddressSpace *as, unsigned long rip);

#endif /* !ORACLE_H__ */
