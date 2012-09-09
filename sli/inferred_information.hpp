#ifndef INFERRED_INFORMATION_HPP__
#define INFERRED_INFORMATION_HPP__

#include <stdio.h>
#include <vector>

#include "state_machine.hpp"
#include "alloc_mai.hpp"

class Oracle;
class OracleInterface;

class CrashSummary : public GarbageCollected<CrashSummary, &ir_heap> {
	void buildAliasingTable(Oracle *);
public:
	StateMachine *loadMachine;
	StateMachine *storeMachine;
	IRExpr *verificationCondition;
	typedef std::pair<StateMachineSideEffectStore *, StateMachineSideEffectStore *> macroSectionT;
	std::vector<macroSectionT> macroSections;
	typedef std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier> aliasingEntryT;
	std::vector<aliasingEntryT> aliasing;
	MaiMap *mai;
	CrashSummary(StateMachine *_loadMachine, StateMachine *_storeMachine,
		     IRExpr *_verificationCondition, Oracle *oracle,
		     MaiMap *_mai)
		: loadMachine(_loadMachine),
		  storeMachine(_storeMachine),
		  verificationCondition(_verificationCondition),
		  mai(_mai)
	{
		buildAliasingTable(oracle);
	}

	CrashSummary(StateMachine *_loadMachine,
		     StateMachine *_storeMachine,
		     IRExpr *_verificationCondition,
		     const std::vector<macroSectionT> &_macroSections,
		     const std::vector<aliasingEntryT> &_aliasing,
		     MaiMap *_mai)
		: loadMachine(_loadMachine),
		  storeMachine(_storeMachine),
		  verificationCondition(_verificationCondition),
		  macroSections(_macroSections),
		  aliasing(_aliasing),
		  mai(_mai)
	{}

	void visit(HeapVisitor &hv) {
		hv(loadMachine);
		hv(storeMachine);
		hv(verificationCondition);
		for (auto it = macroSections.begin();
		     it != macroSections.end();
		     it++) {
			hv(it->first);
			hv(it->second);
		}
		hv(mai);
	}
	NAMED_CLASS
};

void printCrashSummary(CrashSummary *cs, FILE *f);
CrashSummary *readCrashSummary(int fd);
bool parseCrashSummary(CrashSummary **out, const char *buf, const char **succ);
CrashSummary *readBugReport(const char *name, char **metadata);
class StateMachineTransformer;
CrashSummary *transformCrashSummary(CrashSummary *input, StateMachineTransformer &trans,
				    bool *done_something = NULL);
CrashSummary *internCrashSummary(CrashSummary *cs);

char *buildPatchForCrashSummary(const std::map<const CFGNode *, int> &,
				Oracle *oracle, CrashSummary *summary, const char *ident);

class FixConsumer {
public:
	virtual void operator()(VexPtr<CrashSummary, &ir_heap> &loadMachine,
				GarbageCollectionToken token) = 0;
};

typedef gc_heap_map<VexRip, StateMachineState, &ir_heap>::type InferredInformation;
bool buildProbeMachine(CfgLabelAllocator &allocLabel,
		       const VexPtr<Oracle> &oracle,
		       const DynAnalysisRip &interestingRip,
		       const VexPtr<StateMachineState, &ir_heap> &proximal,
		       ThreadId tid,
		       const AllowableOptimisations &opt,
		       StateMachine ***out,
		       unsigned *nr_out_machines,
		       MaiMap &mai,
		       int *nextFrameId,
		       GarbageCollectionToken token);
bool diagnoseCrash(CfgLabelAllocator &allocLabel,
		   const DynAnalysisRip &,
		   VexPtr<StateMachine, &ir_heap> probeMachine,
		   const VexPtr<Oracle> &oracle,
		   bool needRemoteMacroSections,
		   const AllowableOptimisations &opt,
		   const MaiMap &mai,
		   int nextFrameId,
		   GarbageCollectionToken token);
void considerInstructionSequence(VexPtr<StateMachine, &ir_heap> &probeMachine,
				 VexPtr<Oracle> &oracle,
				 VexPtr<MachineState> &ms,
				 FixConsumer &haveAFix,
				 bool considerEverything,
				 GarbageCollectionToken token);
IRExpr *findHappensBeforeRelations(const VexPtr<CrashSummary, &ir_heap> &summary,
				   const VexPtr<OracleInterface> &oracle,
				   const AllowableOptimisations &opt,
				   GarbageCollectionToken token);

#endif /* !INFERRED_INFORMATION_HPP__ */
