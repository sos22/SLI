#ifndef INFERRED_INFORMATION_HPP__
#define INFERRED_INFORMATION_HPP__

#include <stdio.h>
#include <vector>

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

class FixConsumer {
public:
	virtual void operator()(VexPtr<StateMachine, &ir_heap> &probeMachine,
				std::set<std::pair<StateMachineSideEffectStore *,
				                   StateMachineSideEffectStore *> > &remoteMacroSections,
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
