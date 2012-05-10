#ifndef INFERRED_INFORMATION_HPP__
#define INFERRED_INFORMATION_HPP__

#include <stdio.h>
#include <vector>

#include "state_machine.hpp"

class Oracle;

class CrashSummary : public GarbageCollected<CrashSummary, &ir_heap> {
public:
	class StoreMachineData : public GarbageCollected<StoreMachineData, &ir_heap> {
	public:
		StateMachine *machine;
		typedef std::pair<StateMachineSideEffectStore *, StateMachineSideEffectStore *> macroSectionT;
		std::vector<macroSectionT> macroSections;
		IRExpr *assumption;
		StoreMachineData(StateMachine *_machine, IRExpr *_assumption)
			: machine(_machine), assumption(_assumption)
		{}
		StoreMachineData(StateMachine *_machine, IRExpr *_assumption, std::vector<macroSectionT> &macros)
			: machine(_machine), macroSections(macros), assumption(_assumption)
		{}
		void visit(HeapVisitor &hv) {
			hv(machine);
			hv(assumption);
			for (std::vector<macroSectionT>::iterator it = macroSections.begin();
			     it != macroSections.end();
			     it++) {
				hv(it->first);
				hv(it->second);
			}
		}
		NAMED_CLASS
	};

	CrashSummary(StateMachine *_loadMachine)
		: loadMachine(_loadMachine)
	{}
	CrashSummary(StateMachine *_loadMachine, std::vector<StoreMachineData *> &_storeMachines)
		: loadMachine(_loadMachine), storeMachines(_storeMachines)
	{}

	StateMachine *loadMachine;
	std::vector<StoreMachineData *> storeMachines;
	void visit(HeapVisitor &hv) {
		hv(loadMachine);
		visit_container(storeMachines, hv);
	}
	NAMED_CLASS
};

void printCrashSummary(CrashSummary *cs, FILE *f);
CrashSummary *readCrashSummary(int fd);
bool parseCrashSummary(CrashSummary **out, const char *buf, const char **succ);

char *buildPatchForCrashSummary(Oracle *oracle, CrashSummary *summary, const char *ident);

class FixConsumer {
public:
	virtual void operator()(VexPtr<CrashSummary, &ir_heap> &loadMachine,
				GarbageCollectionToken token) = 0;
};

typedef gc_heap_map<VexRip, StateMachineState, &ir_heap>::type InferredInformation;
StateMachine *buildProbeMachine(VexPtr<Oracle> &oracle,
				const DynAnalysisRip &interestingRip,
				VexPtr<StateMachineState, &ir_heap> &proximal,
				ThreadId tid,
				const AllowableOptimisations &opt,
				GarbageCollectionToken token);
CrashSummary *diagnoseCrash(VexPtr<StateMachine, &ir_heap> &probeMachine,
			    VexPtr<Oracle> &oracle,
			    VexPtr<MachineState> &ms,
			    bool needRemoteMacroSections,
			    const AllowableOptimisations &opt,
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
