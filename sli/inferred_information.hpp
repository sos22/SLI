#ifndef INFERRED_INFORMATION_HPP__
#define INFERRED_INFORMATION_HPP__

#include <stdio.h>
#include <vector>

#include "state_machine.hpp"

class Oracle;

template <typename t>
class CFGNode : public GarbageCollected<CFGNode<t>, &ir_heap>, public PrettyPrintable {
public:
	t fallThroughRip;
	t branchRip;
	CFGNode<t> *fallThrough;
	CFGNode<t> *branch;

	t my_rip;

	bool accepting;

	CFGNode(t rip) : my_rip(rip), accepting(false) {}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%#lx: %#lx(%p), %#lx(%p)",
			wrappedRipToRip(my_rip),
			wrappedRipToRip(fallThroughRip),
			fallThrough,
			wrappedRipToRip(branchRip),
			branch);
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
	VexPtr<gc_heap_map<unsigned long, StateMachine, &ir_heap>::type, &ir_heap> crashReasons;

	InferredInformation(Oracle *_oracle) :
		oracle(_oracle),
		crashReasons(new gc_heap_map<unsigned long, StateMachine, &ir_heap>::type())
	{}
	void addCrashReason(StateMachine *cr) { crashReasons->set(cr->origin, cr); }
	StateMachine *CFGtoCrashReason(unsigned tid, CFGNode<unsigned long> *cfg, bool install);

	void visit(HeapVisitor &hv) {
		hv(oracle);
	}
	void relocate(InferredInformation *to, size_t s) {
		crashReasons.relocate(&to->crashReasons);
	}
	NAMED_CLASS
};

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
bool parseCrashSummary(CrashSummary **out, const char *buf, const char **succ, char **err);

char *buildPatchForCrashSummary(Oracle *oracle, CrashSummary *summary, const char *ident);

class FixConsumer {
public:
	virtual void operator()(VexPtr<CrashSummary, &ir_heap> &loadMachine,
				GarbageCollectionToken token) = 0;
};

StateMachine *buildProbeMachine(std::vector<unsigned long> &previousInstructions,
				VexPtr<InferredInformation> &ii,
				VexPtr<Oracle> &oracle,
				unsigned long interestingRip,
				ThreadId tid,
				GarbageCollectionToken token);
CrashSummary *diagnoseCrash(VexPtr<StateMachine, &ir_heap> &probeMachine,
			    VexPtr<Oracle> &oracle,
			    VexPtr<MachineState> &ms,
			    bool needRemoteMacroSections,
			    GarbageCollectionToken token);
void considerInstructionSequence(VexPtr<StateMachine, &ir_heap> &probeMachine,
				 VexPtr<Oracle> &oracle,
				 VexPtr<MachineState> &ms,
				 FixConsumer &haveAFix,
				 bool considerEverything,
				 GarbageCollectionToken token);
IRExpr *findHappensBeforeRelations(VexPtr<CrashSummary, &ir_heap> &summary,
				   VexPtr<Oracle> &oracle,
				   GarbageCollectionToken token);

#endif /* !INFERRED_INFORMATION_HPP__ */
