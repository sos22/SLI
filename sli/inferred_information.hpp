#ifndef INFERRED_INFORMATION_HPP__
#define INFERRED_INFORMATION_HPP__

#include <stdio.h>
#include <vector>

#include "state_machine.hpp"

class Oracle;

class CrashSummary : public GarbageCollected<CrashSummary, &ir_heap> {
public:
	StateMachine *loadMachine;
	StateMachine *storeMachine;
	IRExpr *verificationCondition;
	typedef std::pair<StateMachineSideEffectStore *, StateMachineSideEffectStore *> macroSectionT;
	std::vector<macroSectionT> macroSections;

	CrashSummary(StateMachine *_loadMachine, StateMachine *_storeMachine,
		     IRExpr *_verificationCondition)
		: loadMachine(_loadMachine),
		  storeMachine(_storeMachine),
		  verificationCondition(_verificationCondition)
	{}

	CrashSummary(StateMachine *_loadMachine,
		     StateMachine *_storeMachine,
		     IRExpr *_verificationCondition,
		     std::vector<macroSectionT> &_macroSections)
		: loadMachine(_loadMachine),
		  storeMachine(_storeMachine),
		  verificationCondition(_verificationCondition),
		  macroSections(_macroSections)
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
	}
	NAMED_CLASS
};

void printCrashSummary(CrashSummary *cs, FILE *f);
CrashSummary *readCrashSummary(int fd);
bool parseCrashSummary(CrashSummary **out, const char *buf, const char **succ);
CrashSummary *readBugReport(const char *name, char **metadata);

char *buildPatchForCrashSummary(Oracle *oracle, CrashSummary *summary, const char *ident);

class FixConsumer {
public:
	virtual void operator()(VexPtr<CrashSummary, &ir_heap> &loadMachine,
				GarbageCollectionToken token) = 0;
};

typedef gc_heap_map<VexRip, StateMachineState, &ir_heap>::type InferredInformation;
class MemoryAccessIdentifierAllocator;
bool buildProbeMachine(VexPtr<Oracle> &oracle,
		       const DynAnalysisRip &interestingRip,
		       VexPtr<StateMachineState, &ir_heap> &proximal,
		       ThreadId tid,
		       const AllowableOptimisations &opt,
		       StateMachine ***out,
		       unsigned *nr_out_machines,
		       MemoryAccessIdentifierAllocator &mai,
		       GarbageCollectionToken token);
bool diagnoseCrash(const DynAnalysisRip &,
		   VexPtr<StateMachine, &ir_heap> &probeMachine,
		   VexPtr<Oracle> &oracle,
		   bool needRemoteMacroSections,
		   const AllowableOptimisations &opt,
		   const MemoryAccessIdentifierAllocator &mai,
		   GarbageCollectionToken token);
void considerInstructionSequence(VexPtr<StateMachine, &ir_heap> &probeMachine,
				 VexPtr<Oracle> &oracle,
				 VexPtr<MachineState> &ms,
				 FixConsumer &haveAFix,
				 bool considerEverything,
				 GarbageCollectionToken token);
IRExpr *findHappensBeforeRelations(VexPtr<CrashSummary, &ir_heap> &summary,
				   VexPtr<Oracle> &oracle,
				   const AllowableOptimisations &opt,
				   GarbageCollectionToken token);

#endif /* !INFERRED_INFORMATION_HPP__ */
