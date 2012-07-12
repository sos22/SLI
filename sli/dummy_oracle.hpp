#ifndef DUMMY_ORACLE_HPP__
#define DUMMY_ORACLE_HPP__

class DummyOracle : public OracleInterface {
	CrashSummary *summary;
	CfgDecode *decode;
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
	DummyOracle(CrashSummary *_summary, CfgDecode *_decode)
		: summary(_summary), decode(_decode)
	{}
	bool memoryAccessesMightAlias(CfgDecode &, const AllowableOptimisations &, StateMachineSideEffectLoad *l1, StateMachineSideEffectLoad *l2) {
		return memoryAccessesMightAlias(l1->rip, l2->rip);
	}
	bool memoryAccessesMightAlias(CfgDecode &, const AllowableOptimisations &, StateMachineSideEffectLoad *l1, StateMachineSideEffectStore *l2) {
		return memoryAccessesMightAlias(l1->rip, l2->rip);
	}
	bool memoryAccessesMightAlias(CfgDecode &, const AllowableOptimisations &, StateMachineSideEffectStore *l1, StateMachineSideEffectStore *l2) {
		return memoryAccessesMightAlias(l1->rip, l2->rip);
	}
	bool memoryAccessesMightAliasCrossThread(const DynAnalysisRip &load, const DynAnalysisRip &store) {
		if (summary->aliasing.empty())
			return true;
		for (auto it = summary->aliasing.begin();
		     it != summary->aliasing.end();
		     it++) {
			if ((load == decode->dr(it->first.where) && store == decode->dr(it->second.where)) ||
			    (store == decode->dr(it->first.where) && load == decode->dr(it->second.where)))
				return true;
		}
		return false;
	}
        bool memoryAccessesMightAliasCrossThread(const VexRip &load, const VexRip &store) {
		return memoryAccessesMightAliasCrossThread(DynAnalysisRip(load),
							   DynAnalysisRip(store));
	}
	bool hasConflictingRemoteStores(CfgDecode &, const AllowableOptimisations &, StateMachineSideEffectMemoryAccess *) {
		return true;
	}
};

#endif /* !DUMMY_ORACLE_HPP__ */
