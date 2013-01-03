#ifndef INFERRED_INFORMATION_HPP__
#define INFERRED_INFORMATION_HPP__

#include <stdio.h>
#include <vector>

#include "state_machine.hpp"
#include "alloc_mai.hpp"
#include "visitor.hpp"
#include "map.h"

class Oracle;
class OracleInterface;

class CrashSummary : public GarbageCollected<CrashSummary, &ir_heap> {
	void buildAliasingTable(Oracle *);
public:
	SMScopes *scopes;
	StateMachine *loadMachine;
	StateMachine *storeMachine;
	bbdd *verificationCondition;
	typedef std::pair<MemoryAccessIdentifier, MemoryAccessIdentifier> aliasingEntryT;
	std::vector<aliasingEntryT> aliasing;
	MaiMap *mai;
	CrashSummary(SMScopes *_scopes, StateMachine *_loadMachine,
		     StateMachine *_storeMachine,
		     bbdd *_verificationCondition, Oracle *oracle,
		     MaiMap *_mai)
		: scopes(_scopes),
		  loadMachine(_loadMachine),
		  storeMachine(_storeMachine),
		  verificationCondition(_verificationCondition),
		  mai(_mai)
	{
		buildAliasingTable(oracle);
	}

	CrashSummary(SMScopes *_scopes,
		     StateMachine *_loadMachine,
		     StateMachine *_storeMachine,
		     bbdd *_verificationCondition,
		     const std::vector<aliasingEntryT> &_aliasing,
		     MaiMap *_mai)
		: scopes(_scopes),
		  loadMachine(_loadMachine),
		  storeMachine(_storeMachine),
		  verificationCondition(_verificationCondition),
		  aliasing(_aliasing),
		  mai(_mai)
	{}

	void visit(HeapVisitor &hv) {
		hv(loadMachine);
		hv(storeMachine);
		hv(verificationCondition);
		hv(mai);
	}
	NAMED_CLASS
};

void printCrashSummary(CrashSummary *cs, FILE *f);
CrashSummary *readCrashSummary(SMScopes *scopes, int fd);
bool parseCrashSummary(SMScopes *scopes, CrashSummary **out, const char *buf, const char **succ);
CrashSummary *readBugReport(SMScopes *scopes, const char *name, char **metadata);
class StateMachineTransformer;
CrashSummary *transformCrashSummary(CrashSummary *input,
				    StateMachineTransformer &trans,
				    bool *done_something = NULL);
CrashSummary *internCrashSummary(CrashSummary *cs);

class FixConsumer {
public:
	virtual void operator()(VexPtr<CrashSummary, &ir_heap> &loadMachine,
				GarbageCollectionToken token) = 0;
};

typedef gc_heap_map<VexRip, StateMachineState, &ir_heap>::type InferredInformation;
StateMachine *buildProbeMachine(SMScopes *scopes,
				CfgLabelAllocator &allocLabel,
				const VexPtr<Oracle> &oracle,
				const VexRip &interestingRip,
				ThreadId tid,
				const AllowableOptimisations &opt,
				VexPtr<MaiMap, &ir_heap> &mai,
				GarbageCollectionToken token);
bool diagnoseCrash(SMScopes *scopes,
		   CfgLabelAllocator &allocLabel,
		   const DynAnalysisRip &,
		   VexPtr<StateMachine, &ir_heap> probeMachine,
		   const VexPtr<Oracle> &oracle,
		   FixConsumer &df,
		   const AllowableOptimisations &opt,
		   VexPtr<MaiMap, &ir_heap> &mai,
		   GarbageCollectionToken token);
void considerInstructionSequence(VexPtr<StateMachine, &ir_heap> &probeMachine,
				 VexPtr<Oracle> &oracle,
				 VexPtr<MachineState> &ms,
				 FixConsumer &haveAFix,
				 bool considerEverything,
				 GarbageCollectionToken token);

template <typename ctxtT> static visit_result
visit_crash_summary(ctxtT *ctxt,
		    const state_machine_visitor<ctxtT> *visitor,
		    const CrashSummary *sm)
{
	std::set<const StateMachineState *> memo;
	visit_result res;
	res = visit_const_bdd(ctxt, &visitor->irexpr, sm->verificationCondition);
	if (res == visit_continue)
		res = visit_state_machine(ctxt, visitor, sm->loadMachine, memo);
	if (res == visit_continue)
		res = visit_state_machine(ctxt, visitor, sm->storeMachine, memo);
	return res;
}
template <typename ctxtT> static visit_result
visit_crash_summary(ctxtT *ctxt,
		    const irexpr_visitor<ctxtT> *visitor,
		    const CrashSummary *sm)
{
	std::set<const StateMachineState *> memo;
	visit_result res;
	res = visit_const_bdd(ctxt, visitor, sm->verificationCondition);
	if (res == visit_continue)
		res = visit_state_machine(ctxt, visitor, sm->loadMachine, memo);
	if (res == visit_continue)
		res = visit_state_machine(ctxt, visitor, sm->storeMachine, memo);
	return res;
}

#endif /* !INFERRED_INFORMATION_HPP__ */
