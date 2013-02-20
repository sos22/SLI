#ifndef EVAL_STATE_MACHINE_HPP__
#define EVAL_STATE_MACHINE_HPP__

class AllowableOptimisations;
class IRExprOptimisations;
class OracleInterface;
class StateMachine;
class StateMachineSideEffectStore;
class CrashSummary;
class MaiMap;
class SMScopes;
class bbdd;

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

bbdd *survivalConstraintIfExecutedAtomically(SMScopes *scopes,
					     const VexPtr<MaiMap, &ir_heap> &mai,
					     const VexPtr<StateMachine, &ir_heap> &sm,
					     const VexPtr<bbdd, &ir_heap> &assumption,
					     const VexPtr<OracleInterface> &oracle,
					     bool escapingStateSurvive,
					     const IRExprOptimisations &opt,
					     GarbageCollectionToken token);
bbdd *crashingConstraintIfExecutedAtomically(SMScopes *scopes,
					     const VexPtr<MaiMap, &ir_heap> &mai,
					     const VexPtr<StateMachine, &ir_heap> &sm,
					     const VexPtr<bbdd, &ir_heap> &assumption,
					     const VexPtr<OracleInterface> &oracle,
					     bool escapingStateSurvive,
					     const IRExprOptimisations &opt,
					     GarbageCollectionToken token);
bbdd *crossProductSurvivalConstraint(SMScopes *scopes,
				     const VexPtr<StateMachine, &ir_heap> &probeMachine,
				     const VexPtr<StateMachine, &ir_heap> &storeMachine,
				     const VexPtr<OracleInterface> &oracle,
				     const VexPtr<bbdd, &ir_heap> &initialStateCondition,
				     const AllowableOptimisations &opt,
				     const VexPtr<MaiMap, &ir_heap> &mai,
				     GarbageCollectionToken token);
bbdd *writeMachineSuitabilityConstraint(SMScopes *scopes,
					VexPtr<MaiMap, &ir_heap> &mai,
					const VexPtr<StateMachine, &ir_heap> &writeMachine,
					const VexPtr<StateMachine, &ir_heap> &readMachine,
					const VexPtr<OracleInterface> &oracle,
					const VexPtr<bbdd, &ir_heap> &assumption,
					const AllowableOptimisations &opt,
					GarbageCollectionToken token);
void collectConstraints(SMScopes *scopes,
			const VexPtr<MaiMap, &ir_heap> &mai,
			const VexPtr<StateMachine, &ir_heap> &sm,
			VexPtr<OracleInterface> &oracle,
			const IRExprOptimisations &opt,
			GcSet<IRExpr, &ir_heap> &out,
			GarbageCollectionToken token);

smrbdd *compileMachineToBdd(SMScopes *scopes,
			    const VexPtr<MaiMap, &ir_heap> &mai,
			    const VexPtr<StateMachine, &ir_heap> &sm,
			    VexPtr<OracleInterface> &oracle,
			    const IRExprOptimisations &opt,
			    GarbageCollectionToken token);

#endif /* !EVAL_STATE_MACHINE_HPP__ */
