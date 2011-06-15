#ifndef INFERRED_INFORMATION_HPP__
#define INFERRED_INFORMATION_HPP__

#include <stdio.h>
#include <vector>

#include "crash_reason.hpp"

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
	VexPtr<gc_heap_map<VexRip, CrashReason, &ir_heap>::type, &ir_heap> crashReasons;

	InferredInformation(Oracle *_oracle) :
		oracle(_oracle),
		crashReasons(new gc_heap_map<VexRip, CrashReason, &ir_heap>::type())
	{}
	void addCrashReason(CrashReason *cr) { crashReasons->set(cr->rip, cr); }
	CFGNode<unsigned long> *CFGFromRip(unsigned long rip, const std::set<unsigned long> &terminalFunctions);
	CrashReason *CFGtoCrashReason(unsigned tid, CFGNode<unsigned long> *cfg);

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
		StoreMachineData(StateMachine *_machine)
			: machine(_machine)
		{}
		StateMachine *machine;
		typedef std::pair<StateMachineSideEffectStore *, StateMachineSideEffectStore *> macroSectionT;
		std::vector<macroSectionT> macroSections;
		void visit(HeapVisitor &hv) {
			hv(machine);
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

	StateMachine *loadMachine;
	std::vector<StoreMachineData *> storeMachines;
	void visit(HeapVisitor &hv) {
		hv(loadMachine);
		visit_container(storeMachines, hv);
	}
	NAMED_CLASS
};

void printCrashSummary(CrashSummary *cs, FILE *f);
char *buildPatchForCrashSummary(Oracle *oracle, CrashSummary *summary);

class FixConsumer {
public:
	virtual void operator()(VexPtr<CrashSummary, &ir_heap> &loadMachine,
				GarbageCollectionToken token) = 0;
};

void considerInstructionSequence(std::vector<unsigned long> &previousInstructions,
				 VexPtr<InferredInformation> &ii,
				 VexPtr<Oracle> &oracle,
				 unsigned long interestingRip,
				 VexPtr<MachineState> &ms,
				 FixConsumer &haveAFix,
				 GarbageCollectionToken token);

#endif /* !INFERRED_INFORMATION_HPP__ */
