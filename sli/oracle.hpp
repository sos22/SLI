#ifndef ORACLE_HPP__
#define ORACLE_HPP__

#include <set>
#include "state_machine.hpp"
#include "mapping.hpp"
#include "library.hpp"
#include "map.h"

#include "libvex_guest_offsets.h"

#include "oracle_rip.hpp"

class TypesDb;
class DynAnalysisRip;

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
	VexRip makeVexRip(const VexRip &useStackOf);

#define mk_operator(op)							\
	bool operator op (const StaticRip &r) const { return rip op r.rip; }
	mk_operator(==)
	mk_operator(<)
#undef mk_operator

	unsigned long rip;
};

class OracleInterface : public GarbageCollected<OracleInterface> {
public:
	virtual bool memoryAccessesMightAlias(const MaiMap &, const IRExprOptimisations &, StateMachineSideEffectLoad *, StateMachineSideEffectLoad *) = 0;
	virtual bool memoryAccessesMightAlias(const MaiMap &, const IRExprOptimisations &, StateMachineSideEffectLoad *, StateMachineSideEffectStore *) = 0;
	virtual bool memoryAccessesMightAlias(const MaiMap &, const IRExprOptimisations &, StateMachineSideEffectStore *, StateMachineSideEffectStore *) = 0;
	bool memoryAccessesMightAlias(const MaiMap &decode, const IRExprOptimisations &opt,
				      StateMachineSideEffectMemoryAccess *a,
				      StateMachineSideEffectMemoryAccess *b);
	virtual bool memoryAccessesMightAliasCrossThread(const DynAnalysisRip &load, const DynAnalysisRip &store) = 0;
	bool memoryAccessesMightAliasCrossThread(const VexRip &load, const VexRip &store){
		return memoryAccessesMightAliasCrossThread(DynAnalysisRip(load), DynAnalysisRip(store));
	}
		
	/* True if any table entry which includes @access as a
	 * non-private entry also includes a non-private store
	 * entry. */
	/* i.e. this is true if there's some possibility that @access
	 * might alias with a store in a remote thread. */
	virtual bool hasConflictingRemoteStores(const MaiMap &, const AllowableOptimisations &opt, StateMachineSideEffectMemoryAccess *access) = 0;

	virtual ~OracleInterface() {}
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
		static LivenessSet argRegisters;
		LivenessSet(unsigned long _m) : mask(_m) {}
	private:
		char *mkName() const;
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
		void updateLiveOnEntry(Oracle *oracle, const StaticRip &rip, AddressSpace *as, bool *changed);
		void updateRbpToRspOffset(const StaticRip &rip, AddressSpace *as, bool *changed, Oracle *oracle);
		void addPredecessorsDirect(const StaticRip &rip, std::vector<StaticRip> &out);
		void addPredecessorsNonCall(const StaticRip &rip, std::vector<StaticRip> &out);
		void addPredecessorsCall(const StaticRip &rip, std::vector<StaticRip> &out);
		void addPredecessorsReturn(const StaticRip &rip, std::vector<StaticRip> &out);
		void updateSuccessorInstructionsAliasing(const StaticRip &rip, AddressSpace *as, std::vector<StaticRip> *changed,
							 Oracle *oracle, bool *done_something);
	public:
		void getInstructionFallThroughs(const StaticRip &rip, std::vector<StaticRip> &out);
	private:
		void getInstructionCallees(const StaticRip &rip, std::vector<StaticRip> &out);
		void getSuccessors(const StaticRip &rip, std::vector<StaticRip> &succ);
		void getFunctionCallers(std::vector<StaticRip> &out);
		bool registerLivenessCorrect() const;
		void setRegisterLivenessCorrect(bool v);
		bool rbpToRspOffsetsCorrect() const;
		void setRbpToRspOffsetsCorrect(bool v);
		bool aliasingConfigCorrect() const;
		void setAliasingConfigCorrect(bool v);
		LivenessSet liveOnEntry(const StaticRip &, bool);
	public:
		Function(const StaticRip &_rip)
			: rip(_rip)
		{}

		ThreadRegisterAliasingConfiguration aliasConfigOnEntryToInstruction(const StaticRip &rip);
		ThreadRegisterAliasingConfiguration aliasConfigOnEntryToInstruction(const StaticRip &rip, bool *b);
		void setAliasConfigOnEntryToInstruction(const StaticRip &rip, const ThreadRegisterAliasingConfiguration &config);
		void resolveCallGraph(Oracle *oracle);
		void calculateRegisterLiveness(Oracle *oracle, AddressSpace *as, bool *done_something);
		void calculateRbpToRspOffsets(AddressSpace *as, Oracle *oracle);
		void calculateAliasing(AddressSpace *as, Oracle *oracle, bool *done_something);

		void visit(HeapVisitor &) { }
		NAMED_CLASS
	};

	class ThreadRegisterAliasingConfiguration {
		friend ThreadRegisterAliasingConfiguration Function::aliasConfigOnEntryToInstruction(const StaticRip &rip,
											       bool *b);
		ThreadRegisterAliasingConfiguration(float x); /* initialise as function entry configuration */
		ThreadRegisterAliasingConfiguration(float x, int y); /* initialise as unknown configuration */
	public:
		ThreadRegisterAliasingConfiguration()
			: stackInStack(false), stackInMemory(false)
		{}
		/* True if the current stack frame contains any pointers to itself. */
		bool stackInStack;
		/* True if memory outside of the current stack frame might contain
		   any pointers to memory in the current stack frame. */
		bool stackInMemory;
		PointerAliasingSet v[NR_REGS];
		
		void operator|=(const ThreadRegisterAliasingConfiguration &src) {
			stackInStack |= src.stackInStack;
			stackInMemory |= src.stackInMemory;
			for (int i = 0; i < NR_REGS; i++)
				v[i] = v[i] | src.v[i];
		}
		bool operator != (const ThreadRegisterAliasingConfiguration &x) const {
			if (stackInStack != x.stackInStack ||
			    stackInMemory != x.stackInMemory)
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

		PointerAliasingSet lookupRegister(const threadAndRegister &r, bool buildingAliasTable) const;
		void set(const threadAndRegister &, const PointerAliasingSet &);
		void addConfig(unsigned tid, const ThreadRegisterAliasingConfiguration &config);

		void prettyPrint(FILE *) const;
	};

	struct callgraph_entry {
		bool is_call;
		std::set<unsigned long> targets;
	};
	typedef std::map<StaticRip, callgraph_entry> callgraph_t;

	TypesDb *type_db;

	static IRSB *getIRSBForRip(AddressSpace *as, const StaticRip &sr, bool singleInstr);
	static IRSB *getIRSBForRip(AddressSpace *as, const VexRip &sr, bool singleInstr);
	IRSB *getIRSBForRip(const VexRip &vr, bool singleInstr);

private:

	void buildReturnAddressTable();
	static void calculateRegisterLiveness(VexPtr<Oracle> &ths, GarbageCollectionToken token);
	static void calculateRbpToRspOffsets(VexPtr<Oracle> &ths, GarbageCollectionToken token);
	static void calculateAliasing(VexPtr<Oracle> &ths, GarbageCollectionToken token);
	void loadTagTable(const char *path);
	void findPossibleJumpTargets(const StaticRip &from, const callgraph_t &callgraph_table, std::vector<StaticRip> &targets);
public:
	StaticRip functionHeadForInstruction(const StaticRip &rip);
private:
	enum RbpToRspOffsetState {
		RbpToRspOffsetStateImpossible,
		RbpToRspOffsetStateValid,
		RbpToRspOffsetStateUnknown
	};
	void getRbpToRspOffset(const StaticRip &rip, RbpToRspOffsetState *state, unsigned long *offset);
	void setRbpToRspOffset(const StaticRip &rip, RbpToRspOffsetState state, unsigned long offset);

	std::vector<StaticRip> terminalFunctions;
	std::vector<StaticRip> crashingFunctions;
	void findNoReturnFunctions();
public:
	bool functionNeverReturns(const StaticRip &rip);
	void findAssertions(std::vector<DynAnalysisRip> &out);
	static void loadCallGraph(VexPtr<Oracle> &ths, const char *cg_path,
				  const char *db_fname, GarbageCollectionToken token);
	void visit(HeapVisitor &hv) {
		hv(ms);
		hv(crashedThread);
		hv(type_db);
	}

	MachineState *ms;
	Thread *crashedThread;

	static const unsigned STATIC_THREAD = 712;

	void findConflictingStores(const MaiMap &mai,
				   StateMachineSideEffectLoad *smsel,
				   std::set<DynAnalysisRip> &out);

	/* True if the access doesn't appear anywhere in the tag
	   table.  This usually indicates that the relevant
	   instruction is accessing the stack. */
private:
	bool hasConflictingRemoteStores(const DynAnalysisRip &dr);
public:
	bool hasConflictingRemoteStores(const MaiMap &, const AllowableOptimisations &opt, StateMachineSideEffectMemoryAccess *access);

private:
	enum mam_result { mam_no_alias, mam_might_alias, mam_private };
	mam_result memoryAccessesMightAliasLL(const DynAnalysisRip &, const DynAnalysisRip &);
	mam_result memoryAccessesMightAliasLS(const DynAnalysisRip &, const DynAnalysisRip &);
	mam_result memoryAccessesMightAliasSS(const DynAnalysisRip &, const DynAnalysisRip &);
	mam_result alias_query(const DynAnalysisRip &dr1,
			       const std::vector<TypesDb::types_entry> &alias1,
			       const DynAnalysisRip &dr2,
			       const std::vector<TypesDb::types_entry> &alias2);
public:
	bool memoryAccessesMightAlias(const MaiMap &,const IRExprOptimisations &, StateMachineSideEffectLoad *, StateMachineSideEffectLoad *);
	bool memoryAccessesMightAlias(const MaiMap &,const IRExprOptimisations &, StateMachineSideEffectLoad *, StateMachineSideEffectStore *);
	bool memoryAccessesMightAlias(const MaiMap &,const IRExprOptimisations &, StateMachineSideEffectStore *, StateMachineSideEffectStore *);
	bool memoryAccessesMightAliasCrossThread(const DynAnalysisRip &load, const DynAnalysisRip &store);

	static void findInstructions(VexPtr<Oracle> &ths, std::vector<StaticRip> &heads,
				     const callgraph_t &callgraph,
				     GarbageCollectionToken token);
	void getFunctions(std::vector<StaticRip> &out);

	ThreadRegisterAliasingConfiguration getAliasingConfigurationForRip(const StaticRip &rip);

private:
	bool getRbpToRspDelta(const StaticRip &rip, long *out);
public:

	ThreadRegisterAliasingConfiguration getAliasingConfigurationForRip(const VexRip &rip);
	bool getRbpToRspDelta(const VexRip &rip, long *out);

	void getInstrCallees(const VexRip &vr, std::vector<VexRip> &out);
	void getInstrFallThroughs(const VexRip &vr, std::vector<VexRip> &out);

	bool isFunctionHead(const VexRip &vr);
	bool isFunctionHead(const StaticRip &vr);
	void getPossibleStackTruncations(const VexRip &vr,
					 std::vector<unsigned long> &callers);
	void findPredecessors(const VexRip &vr, bool includeCallPredecessors,
			      std::vector<VexRip> &out);
	void findPredecessors(unsigned long rip, std::set<unsigned long> &out);

	bool isPltCall(const VexRip &vr);
	LibraryFunctionType identifyLibraryCall(const VexRip &vr);

	bool isCrashingAddr(const VexRip &vr) const;

	~Oracle() { }
	Oracle(MachineState *_ms, Thread *_thr, const char *tags)
		: ms(_ms), crashedThread(_thr)
	{
		if (tags)
			loadTagTable(tags);
		if (ms->elfData)
			findNoReturnFunctions();
	}
};

StateMachine *introduceFreeVariables(StateMachine *sm,
				     const Oracle::RegisterAliasingConfiguration *alias,
				     const AllowableOptimisations &opt,
				     Oracle *oracle,
				     bool *done_something);

unsigned getInstructionSize(AddressSpace *as, const StaticRip &rip);
unsigned stack_offset(Oracle *oracle, unsigned long rip);

#endif /* !ORACLE_H__ */
