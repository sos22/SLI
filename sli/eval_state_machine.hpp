#ifndef EVAL_STATE_MACHINE_HPP__
#define EVAL_STATE_MACHINE_HPP__

class AllowableOptimisations;

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

IRExpr *survivalConstraintIfExecutedAtomically(VexPtr<StateMachine, &ir_heap> &sm,
					       VexPtr<IRExpr, &ir_heap> &assumption,
					       VexPtr<Oracle> &oracle,
					       const AllowableOptimisations &opt,
					       GarbageCollectionToken token);
bool evalMachineUnderAssumption(VexPtr<StateMachine, &ir_heap> &sm, VexPtr<Oracle> &oracle,
				VexPtr<IRExpr, &ir_heap> assumption,
				const AllowableOptimisations &opt,
				bool *mightSurvive, bool *mightCrash,
				GarbageCollectionToken token);
bool evalCrossProductMachine(VexPtr<StateMachine, &ir_heap> &probeMachine,
			     VexPtr<StateMachine, &ir_heap> &storeMachine,
			     VexPtr<Oracle> &oracle,
			     VexPtr<IRExpr, &ir_heap> &initialStateCondition,
			     const AllowableOptimisations &opt,
			     bool *mightSurvive,
			     bool *mightCrash,
			     GarbageCollectionToken token);
bool findRemoteMacroSections(VexPtr<StateMachine, &ir_heap> &readMachine,
			     VexPtr<StateMachine, &ir_heap> &writeMachine,
			     VexPtr<IRExpr, &ir_heap> &assumption,
			     VexPtr<Oracle> &oracle,
			     const AllowableOptimisations &opt,
			     VexPtr<remoteMacroSectionsT, &ir_heap> &output,
			     GarbageCollectionToken token);
bool fixSufficient(VexPtr<StateMachine, &ir_heap> &writeMachine,
		   VexPtr<StateMachine, &ir_heap> &probeMachine,
		   VexPtr<IRExpr, &ir_heap> &assumption,
		   VexPtr<Oracle> &oracle,
		   const AllowableOptimisations &opt,
		   VexPtr<remoteMacroSectionsT, &ir_heap> &sections,
		   GarbageCollectionToken token);
IRExpr *writeMachineCrashConstraint(StateMachine *sm,
				    IRExpr *surviveExpression,
				    IRExpr *crashExpression,
				    IRExpr *escapeExpression,
				    const AllowableOptimisations &opt);
IRExpr *writeMachineSuitabilityConstraint(VexPtr<StateMachine, &ir_heap> &writeMachine,
					  VexPtr<StateMachine, &ir_heap> &readMachine,
					  VexPtr<Oracle> &oracle,
					  VexPtr<IRExpr, &ir_heap> &assumption,
					  const AllowableOptimisations &opt,
					  GarbageCollectionToken token);

#endif /* !EVAL_STATE_MACHINE_HPP__ */
