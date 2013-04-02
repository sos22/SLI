#ifndef DUMMY_ORACLE_HPP__
#define DUMMY_ORACLE_HPP__

#include "oracle.hpp"

class DummyOracle : public OracleInterface {
	CrashSummary *summary;
	void visit(HeapVisitor &hv) {
		hv(summary);
	}
	bool memoryAccessesMightAlias(const MemoryAccessIdentifier &mai1,
				      const MemoryAccessIdentifier &mai2)
	{
		if (summary->aliasing.empty())
			return true;
		for (auto it = summary->aliasing.begin(); it != summary->aliasing.end(); it++) {
			if ((it->first == mai1 && it->second == mai2) ||
			    (it->first == mai2 && it->second == mai1))
				return true;
		}
		return false;
	}

public:
	DummyOracle(CrashSummary *_summary)
		: summary(_summary)
	{}
	bool memoryAccessesMightAlias(const MaiMap &, const IRExprOptimisations &, StateMachineSideEffectLoad *l1, StateMachineSideEffectLoad *l2) {
		return memoryAccessesMightAlias(l1->rip, l2->rip);
	}
	bool memoryAccessesMightAlias(const MaiMap &, const IRExprOptimisations &, StateMachineSideEffectLoad *l1, StateMachineSideEffectStore *l2) {
		return memoryAccessesMightAlias(l1->rip, l2->rip);
	}
	bool memoryAccessesMightAlias(const MaiMap &, const IRExprOptimisations &, StateMachineSideEffectStore *l1, StateMachineSideEffectStore *l2) {
		return memoryAccessesMightAlias(l1->rip, l2->rip);
	}
	bool memoryAccessesMightAliasCrossThread(const DynAnalysisRip &load, const DynAnalysisRip &store) {
		if (summary->aliasing.empty())
			return true;
		for (auto it = summary->aliasing.begin();
		     it != summary->aliasing.end();
		     it++) {
			for (auto it1 = summary->mai->begin(it->first); !it1.finished(); it1.advance()) {
				if (load != it1.dr() && store != it1.dr())
					continue;
				for (auto it2 = summary->mai->begin(it->second); !it2.finished(); it2.advance()) {
					if ((load == it1.dr() && store == it2.dr()) ||
					    (load == it2.dr() && store == it1.dr()))
						return true;
				}
			}
		}
		return false;
	}
	bool memoryAccessesMightAliasCrossThreadSym(const DynAnalysisRip &load, const DynAnalysisRip &store) {
		return memoryAccessesMightAliasCrossThread(load, store) ||
			memoryAccessesMightAliasCrossThread(store, load);
	}
        bool memoryAccessesMightAliasCrossThread(const VexRip &load, const VexRip &store) {
		return memoryAccessesMightAliasCrossThread(DynAnalysisRip(load),
							   DynAnalysisRip(store));
	}
	bool hasConflictingRemoteStores(const MaiMap &, const AllowableOptimisations &, StateMachineSideEffectMemoryAccess *access) {
		if (summary->aliasing.empty())
			return true;
		for (auto it = summary->aliasing.begin(); it != summary->aliasing.end(); it++) {
			if (it->first != access->rip && it->second != access->rip)
				continue;
			if (it->first.tid == it->second.tid )
				continue;
			return true;
		}
		return false;
	}
};

#endif /* !DUMMY_ORACLE_HPP__ */
