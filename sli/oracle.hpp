#ifndef ORACLE_HPP__
#define ORACLE_HPP__

#include <set>
#include "state_machine.hpp"

class InstructionSet {
public:
	std::set<unsigned long> rips;
};

/* All of the information from sources other than the main crash dump.
 * Information from the oracle will be true of some executions but not
 * necessarily all of them, so should only really be used where static
 * analysis is insufficient. */
class Oracle : public GarbageCollected<Oracle> {
	struct tag_entry {
		std::set<unsigned long> loads;
		std::set<unsigned long> stores;
	};
	std::vector<tag_entry> tag_table;
	void loadTagTable(const char *path);
public:
	MachineState *ms;
	Thread *crashedThread;

	void findPreviousInstructions(std::vector<unsigned long> &output);
	void findConflictingStores(StateMachineSideEffectLoad *smsel,
				   std::set<unsigned long> &out);
	void clusterRips(const std::set<unsigned long> &inputRips,
			 std::set<InstructionSet> &outputClusters);
	bool storeIsThreadLocal(StateMachineSideEffectStore *s);
	bool memoryAccessesMightAlias(StateMachineSideEffectLoad *, StateMachineSideEffectStore *);
	bool functionCanReturn(unsigned long rip);

	Oracle(MachineState *_ms, Thread *_thr, const char *tags)
		: ms(_ms), crashedThread(_thr)
	{
		loadTagTable(tags);
	}
	void visit(HeapVisitor &hv) {
		hv(ms);
		hv(crashedThread);
	}
	NAMED_CLASS
};

extern unsigned long hash_ulong_pair(const std::pair<unsigned long, unsigned long> &p);
typedef gc_map<std::pair<unsigned long, unsigned long>,
	       bool,
	       hash_ulong_pair,
	       __default_eq_function<std::pair<unsigned long, unsigned long> >,
	       __default_visit_function<bool>,
	       &ir_heap> gc_pair_ulong_set_t;
void mergeUlongSets(gc_pair_ulong_set_t *dest, const gc_pair_ulong_set_t *src);

void findInstrSuccessorsAndCallees(AddressSpace *as,
				   unsigned long rip,
				   std::vector<unsigned long> &directExits,
				   gc_pair_ulong_set_t *callees);


#endif /* !ORACLE_H__ */
