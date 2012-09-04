#ifndef EVAL_STATE_MACHINE_HPP__
#define EVAL_STATE_MACHINE_HPP__

class AllowableOptimisations;
class OracleInterface;
class StateMachine;
class StateMachineSideEffectStore;
class CrashSummary;
class MaiMap;

class remoteMacroSectionsT : public GarbageCollected<remoteMacroSectionsT, &ir_heap> {
	typedef std::vector<std::pair<StateMachineSideEffectStore *,
				      StateMachineSideEffectStore *> > contentT;
	contentT content;

public:
	class iterator {
		friend class remoteMacroSectionsT;
		unsigned idx;
		const remoteMacroSectionsT *owner;
		iterator(const remoteMacroSectionsT *, unsigned);
	public:
		class __content {
		public:
			StateMachineSideEffectStore *start;
			StateMachineSideEffectStore *end;
		};
	private:
		mutable __content content;
	public:
		bool operator!=(const iterator &other) const;
		void operator++(int);
		const __content *operator->() const;
	};

	iterator begin() const;
	iterator end() const;

	void insert(StateMachineSideEffectStore *start,
		    StateMachineSideEffectStore *end);

	void visit(HeapVisitor &hv);
	NAMED_CLASS

	friend class iterator;
};

IRExpr *survivalConstraintIfExecutedAtomically(const VexPtr<MaiMap, &ir_heap> &mai,
					       const VexPtr<StateMachine, &ir_heap> &sm,
					       const VexPtr<IRExpr, &ir_heap> &assumption,
					       const VexPtr<OracleInterface> &oracle,
					       bool escapingStateSurvive,
					       const AllowableOptimisations &opt,
					       GarbageCollectionToken token);
IRExpr *crashingConstraintIfExecutedAtomically(const VexPtr<MaiMap, &ir_heap> &mai,
					       const VexPtr<StateMachine, &ir_heap> &sm,
					       const VexPtr<IRExpr, &ir_heap> &assumption,
					       const VexPtr<OracleInterface> &oracle,
					       bool escapingStateSurvive,
					       const AllowableOptimisations &opt,
					       GarbageCollectionToken token);
bool evalMachineUnderAssumption(const VexPtr<StateMachine, &ir_heap> &sm,
				const VexPtr<OracleInterface> &oracle,
				const VexPtr<IRExpr, &ir_heap> &assumption,
				const AllowableOptimisations &opt,
				bool *mightSurvive, bool *mightCrash,
				GarbageCollectionToken token);
IRExpr *crossProductSurvivalConstraint(const VexPtr<StateMachine, &ir_heap> &probeMachine,
				       const VexPtr<StateMachine, &ir_heap> &storeMachine,
				       const VexPtr<OracleInterface> &oracle,
				       const VexPtr<IRExpr, &ir_heap> &initialStateCondition,
				       const AllowableOptimisations &opt,
				       const VexPtr<MaiMap, &ir_heap> &mai,
				       GarbageCollectionToken token);
bool findRemoteMacroSections(const VexPtr<MaiMap, &ir_heap> &mai,
			     const VexPtr<StateMachine, &ir_heap> &readMachine,
			     const VexPtr<StateMachine, &ir_heap> &writeMachine,
			     const VexPtr<IRExpr, &ir_heap> &assumption,
			     const VexPtr<OracleInterface> &oracle,
			     const AllowableOptimisations &opt,
			     VexPtr<remoteMacroSectionsT, &ir_heap> &output,
			     GarbageCollectionToken token);
bool fixSufficient(const VexPtr<MaiMap, &ir_heap> &mai,
		   const VexPtr<StateMachine, &ir_heap> &writeMachine,
		   const VexPtr<StateMachine, &ir_heap> &probeMachine,
		   const VexPtr<IRExpr, &ir_heap> &assumption,
		   const VexPtr<OracleInterface> &oracle,
		   const AllowableOptimisations &opt,
		   const VexPtr<remoteMacroSectionsT, &ir_heap> &sections,
		   GarbageCollectionToken token);
IRExpr *writeMachineSuitabilityConstraint(const VexPtr<MaiMap, &ir_heap> &mai,
					  const VexPtr<StateMachine, &ir_heap> &writeMachine,
					  const VexPtr<StateMachine, &ir_heap> &readMachine,
					  const VexPtr<OracleInterface> &oracle,
					  const VexPtr<IRExpr, &ir_heap> &assumption,
					  const AllowableOptimisations &opt,
					  GarbageCollectionToken token);
IRExpr *getCrossMachineCrashRequirement(
	const VexPtr<StateMachine, &ir_heap> &readMachine,
	const VexPtr<StateMachine, &ir_heap> &writeMachine,
	const VexPtr<OracleInterface> &oracle,
	const VexPtr<IRExpr, &ir_heap> &assumption,
	const AllowableOptimisations &opt,
	const VexPtr<MaiMap, &ir_heap> &mai,
	GarbageCollectionToken token);

#endif /* !EVAL_STATE_MACHINE_HPP__ */
