#ifndef EVAL_STATE_MACHINE_HPP__
#define EVAL_STATE_MACHINE_HPP__

typedef std::set<std::pair<StateMachineSideEffectStore *,
			   StateMachineSideEffectStore *> > remoteMacroSectionsT;

IRExpr *survivalConstraintIfExecutedAtomically(VexPtr<StateMachine, &ir_heap> &sm,
					       VexPtr<Oracle> &oracle,
					       GarbageCollectionToken token);
void evalMachineUnderAssumption(VexPtr<StateMachine, &ir_heap> &sm, VexPtr<Oracle> &oracle,
				VexPtr<IRExpr, &ir_heap> assumption,
				bool *mightSurvive, bool *mightCrash,
				GarbageCollectionToken token);
IRExpr *writeMachineSuitabilityConstraint(StateMachine *readMachine,
					  StateMachine *writeMachine,
					  IRExpr *assumption,
					  Oracle *oracle);
void evalCrossProductMachine(VexPtr<StateMachine, &ir_heap> &sm1,
			     VexPtr<StateMachine, &ir_heap> &sm2,
			     VexPtr<Oracle> &oracle,
			     VexPtr<IRExpr, &ir_heap> &initialStateCondition,
			     bool *mightSurvive,
			     bool *mightCrash,
			     GarbageCollectionToken token);
bool findRemoteMacroSections(StateMachine *readMachine,
			     StateMachine *writeMachine,
			     IRExpr *assumption,
			     Oracle *oracle,
			     remoteMacroSectionsT &output);
bool fixSufficient(StateMachine *writeMachine,
		   StateMachine *probeMachine,
		   IRExpr *assumption,
		   Oracle *oracle,
		   const remoteMacroSectionsT &sections);

#endif /* !EVAL_STATE_MACHINE_HPP__ */
