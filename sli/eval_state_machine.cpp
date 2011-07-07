#include "sli.h"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "nd_chooser.h"
#include "eval_state_machine.hpp"
#include "offline_analysis.hpp"

class StateMachineEvalContext {
public:
	StateMachineEvalContext()
		: justPathConstraint(NULL)
	{}
	std::vector<StateMachineSideEffectStore *> stores;
	std::map<Int, IRExpr *> binders;
	/* justPathConstraint contains all of the assumptions we've
	   made using the ND chooser.  pathConstraint is that plus the
	   initial assumption. */
	IRExpr *pathConstraint;
	IRExpr *justPathConstraint;
};

class SpecialiseIRExpr : public IRExprTransformer {
	std::map<Int,IRExpr *> &binders;
	IRExpr *transformIexBinder(IRExpr *e, bool *done_something) {
		if (binders.count(e->Iex.Binder.binder)) {
			*done_something = true;
			return binders[e->Iex.Binder.binder];
		}
		return IRExprTransformer::transformIexBinder(e, done_something);
	}
public:
	SpecialiseIRExpr(std::map<Int, IRExpr *> &_binders)
		: binders(_binders)
	{}
};

static IRExpr *
specialiseIRExpr(IRExpr *iex, std::map<Int,IRExpr *> &binders)
{
	SpecialiseIRExpr s(binders);
	return s.transformIRExpr(iex);
}

static bool
expressionIsTrue(IRExpr *exp, NdChooser &chooser, std::map<Int, IRExpr *> &binders, IRExpr **assumption,
		 IRExpr **accumulatedAssumptions)
{
	exp = simplifyIRExpr(
		specialiseIRExpr(exp, binders),
		AllowableOptimisations::defaultOptimisations);

	/* Combine the path constraint with the new expression and see
	   if that produces a contradiction.  If it does then we know
	   for sure that the new expression is false. */
	IRExpr *e =
		simplifyIRExpr(
			IRExpr_Binop(
				Iop_And1,
				*assumption,
				exp),
			AllowableOptimisations::defaultOptimisations);
	if (e->tag == Iex_Const) {
		/* That shouldn't produce the constant 1 very often.
		   If it does, it indicates that the path constraint
		   is definitely true, and the new expression is
		   definitely true, but for some reason we weren't
		   able to simplify the path constraint down to 1
		   earlier.  Consider that a lucky break and simplify
		   it now. */
		if (e->Iex.Const.con->Ico.U1) {
			*assumption = e;
			return true;
		} else {
			return false;
		}
	}

	/* Now try it the other way around, by combining the path
	   constraint with ¬exp.  If we had a perfect theorem prover
	   this would be redundant with the previous version, but we
	   don't, so it isn't. */
	IRExpr *e2 =
		simplifyIRExpr(
			IRExpr_Binop(
				Iop_And1,
				*assumption,
				IRExpr_Unop(
					Iop_Not1,
					exp)),
			AllowableOptimisations::defaultOptimisations);
	if (e2->tag == Iex_Const) {
		/* If X & ¬Y is definitely true, Y is definitely
		 * false and X is definitely true. */
		if (e2->Iex.Const.con->Ico.U1) {
			*assumption = IRExpr_Const(IRConst_U1(1));
			return false;
		}

		/* So now we know that X & ¬Y is definitely false, and
		 * we assume that X is true.  Therefore ¬Y is false
		 * and Y is true. */
		return true;
	}

	/* Can't prove it one way or another.  Use the
	   non-deterministic chooser to guess. */
	int res;
	bool isNewChoice;
	res = chooser.nd_choice(2, &isNewChoice);

#if 0
	if (isNewChoice) {
		printf("Having to use state split to check whether ");
		ppIRExpr(exp, stdout);
		printf(" is true under assumption ");
		ppIRExpr(*assumption, stdout);
		printf("\n");
	}
#endif

	if (res == 0) {
		*assumption = e;
		if (accumulatedAssumptions && *accumulatedAssumptions)
			*accumulatedAssumptions =
				simplifyIRExpr(
					IRExpr_Binop(
						Iop_And1,
						*accumulatedAssumptions,
						exp),
					AllowableOptimisations::defaultOptimisations);
		return true;
	} else {
		*assumption = e2;
		if (accumulatedAssumptions && *accumulatedAssumptions)
			*accumulatedAssumptions =
				simplifyIRExpr(
					IRExpr_Binop(
						Iop_And1,
						*accumulatedAssumptions,
						IRExpr_Unop(
							Iop_Not1,
							exp)),
					AllowableOptimisations::defaultOptimisations);
		return false;
	}
}

static bool
evalExpressionsEqual(IRExpr *exp1, IRExpr *exp2, NdChooser &chooser, std::map<Int, IRExpr *> &binders,
		     IRExpr **assumption, IRExpr **accAssumptions)
{
	return expressionIsTrue(IRExpr_Binop(
					Iop_CmpEQ64,
					exp1,
					exp2),
				chooser,
				binders,
				assumption,
				accAssumptions);
}

static void evalStateMachine(StateMachine *sm,
			     bool *crashes,
			     NdChooser &chooser,
			     Oracle *oracle,
			     StateMachineEvalContext &ctxt);

static void
evalStateMachineSideEffect(StateMachineSideEffect *smse,
			   NdChooser &chooser,
			   Oracle *oracle,
			   std::map<Int, IRExpr *> &binders,
			   std::vector<StateMachineSideEffectStore *> &stores,
			   IRExpr **assumption,
			   IRExpr **accumulatedAssumptions)
{
	if (StateMachineSideEffectStore *smses =
	    dynamic_cast<StateMachineSideEffectStore *>(smse)) {
		IRExpr *v = IRExpr_Unop(Iop_Not1,
					IRExpr_Unop(Iop_BadPtr, smses->addr));
		*assumption = simplifyIRExpr(
			IRExpr_Binop(Iop_And1, *assumption, v),
			AllowableOptimisations::defaultOptimisations);
		if (accumulatedAssumptions && *accumulatedAssumptions)
			*accumulatedAssumptions =
				simplifyIRExpr(
					IRExpr_Binop(Iop_And1, *accumulatedAssumptions, v),
					AllowableOptimisations::defaultOptimisations);
		stores.push_back(
			new StateMachineSideEffectStore(
				specialiseIRExpr(smses->addr, binders),
				specialiseIRExpr(smses->data, binders),
				smses->rip
				)
				);
	} else if (StateMachineSideEffectLoad *smsel =
		   dynamic_cast<StateMachineSideEffectLoad *>(smse)) {
		IRExpr *v = IRExpr_Unop(Iop_Not1,
					IRExpr_Unop(Iop_BadPtr, smsel->smsel_addr));
		*assumption = simplifyIRExpr(
			IRExpr_Binop(Iop_And1, *assumption, v),
			AllowableOptimisations::defaultOptimisations);
		if (accumulatedAssumptions && *accumulatedAssumptions)
			*accumulatedAssumptions =
				simplifyIRExpr(
					IRExpr_Binop(Iop_And1, *accumulatedAssumptions, v),
					AllowableOptimisations::defaultOptimisations);
		IRExpr *val;
		val = NULL;
		for (std::vector<StateMachineSideEffectStore *>::reverse_iterator it = stores.rbegin();
		     !val && it != stores.rend();
		     it++) {
			StateMachineSideEffectStore *smses = *it;
			if (!oracle->memoryAccessesMightAlias(smsel, smses))
				continue;
			if (evalExpressionsEqual(smses->addr, smsel->smsel_addr, chooser, binders, assumption, accumulatedAssumptions))
				val = smses->data;
		}
		if (!val)
			val = IRExpr_Load(False, Iend_LE, Ity_I64, smsel->smsel_addr);
		binders[smsel->key] = val;
	} else if (StateMachineSideEffectCopy *smsec =
		   dynamic_cast<StateMachineSideEffectCopy *>(smse)) {
		binders[smsec->key] =
			specialiseIRExpr(smsec->value, binders);
	} else {
		abort();
	}
}

static void
evalStateMachineEdge(StateMachineEdge *sme,
		     bool *crashes,
		     NdChooser &chooser,
		     Oracle *oracle,
		     StateMachineEvalContext &ctxt)
{
	for (std::vector<StateMachineSideEffect *>::iterator it = sme->sideEffects.begin();
	     it != sme->sideEffects.end();
	     it++)
		evalStateMachineSideEffect(*it, chooser, oracle, ctxt.binders,
					   ctxt.stores, &ctxt.pathConstraint,
					   &ctxt.justPathConstraint);
	if (ctxt.pathConstraint->tag == Iex_Const &&
	    ctxt.pathConstraint->Iex.Const.con->Ico.U1 == 0) {
		/* We've found a contradiction.  That means that the
		   original program would have crashed, *but* in a way
		   other than the one which we're investigating.  We
		   therefore treat that as no-crash and abort the
		   run. */
		*crashes = false;
		return;
	}
	evalStateMachine(sme->target, crashes, chooser, oracle, ctxt);
}

/* Walk the state machine and figure out whether it's going to crash.
   If we hit something which we can't solve statically or via the
   oracle, ask the chooser which way we should go, and then emit a
   path constraint saying which way we went.  Stubs are assumed to
   never crash. */
static void
evalStateMachine(StateMachine *sm,
		 bool *crashes,
		 NdChooser &chooser,
		 Oracle *oracle,
		 StateMachineEvalContext &ctxt)
{
	if (TIMEOUT) {
		*crashes = false; /* Lacking any better ideas */
		return;
	}

	if (dynamic_cast<StateMachineCrash *>(sm)) {
		*crashes = true;
		return;
	}
	if (dynamic_cast<StateMachineNoCrash *>(sm) ||
	    dynamic_cast<StateMachineStub *>(sm)) {
		*crashes = false;
		return;
	}
	if (StateMachineProxy *smp =
	    dynamic_cast<StateMachineProxy *>(sm)) {
		evalStateMachineEdge(smp->target, crashes, chooser, oracle, ctxt);
		return;
	}
	if (StateMachineBifurcate *smb =
	    dynamic_cast<StateMachineBifurcate *>(sm)) {
		if (expressionIsTrue(smb->condition, chooser, ctxt.binders, &ctxt.pathConstraint, &ctxt.justPathConstraint)) {
			evalStateMachineEdge(smb->trueTarget, crashes, chooser, oracle, ctxt);
		} else {
			evalStateMachineEdge(smb->falseTarget, crashes, chooser, oracle, ctxt);
		}
		return;
	}
	if (dynamic_cast<StateMachineUnreached *>(sm)) {
		/* Whoops... */
		fprintf(_logfile, "Evaluating an unreachable state machine?\n");
		*crashes = false;
		return;
	}

	abort();
}

/* Assume that @sm executes atomically.  Figure out a constraint on
   the initial state which will lead to it not crashing. */
IRExpr *
survivalConstraintIfExecutedAtomically(VexPtr<StateMachine, &ir_heap> &sm,
				       VexPtr<Oracle> &oracle,
				       GarbageCollectionToken token)
{
	NdChooser chooser;
	VexPtr<IRExpr, &ir_heap> currentConstraint(IRExpr_Const(IRConst_U1(1)));
	bool crashes;

	do {
		if (TIMEOUT)
			return NULL;

		LibVEX_maybe_gc(token);
		StateMachineEvalContext ctxt;
		ctxt.pathConstraint = IRExpr_Const(IRConst_U1(1));
		evalStateMachine(sm, &crashes, chooser, oracle, ctxt);
		if (crashes) {
			/* This path leads to a crash, so the
			   constraint should include something to make
			   sure that we don't go down here. */
			IRExpr *newConstraint =
				IRExpr_Binop(
					Iop_And1,
					currentConstraint,
					IRExpr_Unop(
						Iop_Not1,
						ctxt.pathConstraint));
			ctxt.pathConstraint =
				simplifyIRExpr(
					IRExpr_Unop(Iop_Not1, ctxt.pathConstraint),
					AllowableOptimisations::defaultOptimisations);
			newConstraint = simplifyIRExpr(newConstraint,
						       AllowableOptimisations::defaultOptimisations);
			currentConstraint = newConstraint;
		}
	} while (chooser.advance());

	return currentConstraint;
}

/* Augment @assumption so that it's sufficient to prove that @sm will
 * definitely crash. */
IRExpr *
writeMachineCrashConstraint(VexPtr<StateMachine, &ir_heap> &sm,
			       VexPtr<IRExpr, &ir_heap> &assumption,
			       VexPtr<Oracle> &oracle,
			       GarbageCollectionToken token)
{
	NdChooser chooser;
	VexPtr<IRExpr, &ir_heap> conjunctConstraint(assumption);
	VexPtr<IRExpr, &ir_heap> disjunctConstraint(IRExpr_Const(IRConst_U1(0)));
	bool crashes;

	do {
		if (TIMEOUT)
			return NULL;

		LibVEX_maybe_gc(token);
		StateMachineEvalContext ctxt;

		/* You might think that we should use the
		   currentConstraint here, rather than the assumption.
		   Not so: changing the path constraint would mean
		   that evalStateMachine will make a different pattern
		   of ND choices on each iteration, which would
		   confuse the ND chooser. */
		ctxt.pathConstraint = assumption;
		ctxt.justPathConstraint = IRExpr_Const(IRConst_U1(1));
		evalStateMachine(sm, &crashes, chooser, oracle, ctxt);

		if (!crashes) {
			/* Survival should be pretty rare here, and
			   pretty much only happen if the constraints
			   on the machine contradict themselves
			   (i.e. X must be simultaneously BadPtr and
			   !BadPtr).  It doesn't really matter much
			   what we do in that case (the rest of the
			   machinery will discard those paths later
			   on), but as an optimisation extend the
			   assumption so that we don't even have to
			   think abou them again. */
			fprintf(_logfile, "\t\tStore machine survived during writeMachineSurvivalConstraint?\n");
			conjunctConstraint =
				IRExpr_Binop(
					Iop_And1,
					conjunctConstraint,
					IRExpr_Unop(
						Iop_Not1,
						ctxt.justPathConstraint));
			conjunctConstraint =
				simplifyIRExpr(conjunctConstraint,
					       AllowableOptimisations::defaultOptimisations);
		} else {
			/* The machine crashed this time, and
			 * justPathConstraint is the assumption which
			 * we had to make to make it go down this
			 * path.  Collect together every such set of
			 * assumptions, across every possible path,
			 * and require that we will always go down one
			 * of them.  Most of the time, there is only
			 * one such path, and so this is very easy. */
			disjunctConstraint =
				IRExpr_Binop(
					Iop_Or1,
					disjunctConstraint,
					ctxt.justPathConstraint);
			disjunctConstraint =
				simplifyIRExpr(disjunctConstraint,
					       AllowableOptimisations::defaultOptimisations);
		}
	} while (chooser.advance());

	IRExpr *finalConstraint = IRExpr_Binop(Iop_And1,
					       conjunctConstraint,
					       disjunctConstraint);
	finalConstraint = simplifyIRExpr(finalConstraint,
					 AllowableOptimisations::defaultOptimisations);
	return finalConstraint;
}

bool
evalMachineUnderAssumption(VexPtr<StateMachine, &ir_heap> &sm, VexPtr<Oracle> &oracle,
			   VexPtr<IRExpr, &ir_heap> assumption,
			   bool *mightSurvive, bool *mightCrash,
			   GarbageCollectionToken token)
{
	NdChooser chooser;
	bool crashes;

	*mightSurvive = false;
	*mightCrash = false;
	while (!*mightCrash || !*mightSurvive) {
		if (TIMEOUT)
			return false;
		LibVEX_maybe_gc(token);
		StateMachineEvalContext ctxt;
		ctxt.pathConstraint = assumption;
		evalStateMachine(sm, &crashes, chooser, oracle, ctxt);
		if (crashes)
			*mightCrash = true;
		else
			*mightSurvive = true;
		if (!chooser.advance())
			break;
	}
	return true;
}

class CrossEvalState {
public:
	StateMachineEdge *currentEdge;
	unsigned nextEdgeSideEffectIdx;
	bool finished;
	bool crashed;
	std::map<Int, IRExpr *> binders;
	CrossEvalState(StateMachineEdge *_e, int _i)
		: currentEdge(_e), nextEdgeSideEffectIdx(_i), finished(false),
		  crashed(false)
	{}
};

class CrossMachineEvalContext {
public:
	IRExpr *pathConstraint;
	std::vector<StateMachineSideEffectStore *> stores;
	CrossEvalState *states[2];
	std::vector<StateMachineSideEffect *> history;
	void advanceMachine(unsigned tid, NdChooser &chooser, Oracle *oracle);
	void advanceToSideEffect(unsigned tid, NdChooser &chooser, Oracle *oracle);
	void dumpHistory(FILE *f) const;
};

void
CrossMachineEvalContext::dumpHistory(FILE *f) const
{
	for (std::vector<StateMachineSideEffect *>::const_iterator it = history.begin();
	     it != history.end();
	     it++) {
		fprintf(f, "\t");
		(*it)->prettyPrint(f);
		fprintf(f, "\n");
	}
}

void
CrossMachineEvalContext::advanceToSideEffect(unsigned tid,
					     NdChooser &chooser,
					     Oracle *oracle)
{
	CrossEvalState *machine = states[tid];
	StateMachine *s;

top:
	while (machine->nextEdgeSideEffectIdx == machine->currentEdge->sideEffects.size()) {
		/* We've hit the end of the edge.  Move to the next
		 * state. */
		s = machine->currentEdge->target;
		assert(!dynamic_cast<StateMachineUnreached *>(s));
		if (dynamic_cast<StateMachineCrash *>(s)) {
			machine->finished = true;
			machine->crashed = true;
			return;
		}
		if (dynamic_cast<StateMachineNoCrash *>(s) ||
		    dynamic_cast<StateMachineStub *>(s)) {
			machine->finished = true;
			return;
		}
		if (StateMachineProxy *smp =
		    dynamic_cast<StateMachineProxy *>(s)) {
			machine->currentEdge = smp->target;
			machine->nextEdgeSideEffectIdx = 0;
			continue;
		}
		if (StateMachineBifurcate *smb =
		    dynamic_cast<StateMachineBifurcate *>(s)) {
			if (expressionIsTrue(smb->condition, chooser, machine->binders, &pathConstraint, NULL))
				machine->currentEdge = smb->trueTarget;
			else
				machine->currentEdge = smb->falseTarget;
			machine->nextEdgeSideEffectIdx = 0;
			continue;
		}
		abort();
	}

	/* You don't need to context switch after a copy, because
	   they're purely local. */
	StateMachineSideEffect *se;
	se = machine->currentEdge->sideEffects[machine->nextEdgeSideEffectIdx];
	if (dynamic_cast<StateMachineSideEffectCopy *>(se)) {
		evalStateMachineSideEffect(se, chooser, oracle, machine->binders, stores, &pathConstraint, NULL);
		history.push_back(se);
		machine->nextEdgeSideEffectIdx++;
		goto top;
	}
}

void
CrossMachineEvalContext::advanceMachine(unsigned tid,
					NdChooser &chooser,
					Oracle *oracle)
{
	CrossEvalState *machine = states[tid];

top:
	advanceToSideEffect(tid, chooser, oracle);
	if (machine->finished || machine->crashed)
		return;

	StateMachineSideEffect *se;
	se = machine->currentEdge->sideEffects[machine->nextEdgeSideEffectIdx];	
	assert(!dynamic_cast<StateMachineSideEffectCopy *>(se));
	assert(!dynamic_cast<StateMachineSideEffectUnreached *>(se));
	evalStateMachineSideEffect(se, chooser, oracle, machine->binders, stores, &pathConstraint, NULL);
	history.push_back(se);
	machine->nextEdgeSideEffectIdx++;

	advanceToSideEffect(tid, chooser, oracle);

	/* Now look at what the other machine is doing, and decide
	   whether the side effect we just issued might conceivably
	   race with the other machine's current side effect. */
	CrossEvalState *other = states[1-tid];
	if (other->finished) {
		/* If the other machine has finished then there really
		   is no point in continuing to explore alternative
		   interleavings. */
		goto top;
	}

	assert(other->nextEdgeSideEffectIdx < other->currentEdge->sideEffects.size());
	StateMachineSideEffect *otherSe = other->currentEdge->sideEffects[other->nextEdgeSideEffectIdx];
	if (StateMachineSideEffectLoad *otherLoad =
	    dynamic_cast<StateMachineSideEffectLoad *>(otherSe)) {
		if (StateMachineSideEffectStore *localStore =
		    dynamic_cast<StateMachineSideEffectStore *>(se)) {
			if (!oracle->memoryAccessesMightAlias(otherLoad, localStore) ||
			    definitelyNotEqual(otherLoad->smsel_addr, localStore->addr, 
					       AllowableOptimisations::defaultOptimisations)) {
				goto top;
			}
		} else {
			assert(dynamic_cast<StateMachineSideEffectLoad *>(se));
			/* Two loads can never alias */
			goto top;
		}
	} else {
		StateMachineSideEffectStore *otherStore =
			dynamic_cast<StateMachineSideEffectStore *>(otherSe);
		assert(otherStore);

		if (StateMachineSideEffectStore *localStore =
		    dynamic_cast<StateMachineSideEffectStore *>(se)) {
			if (!oracle->memoryAccessesMightAlias(otherStore, localStore) ||
			    definitelyNotEqual(otherStore->addr, localStore->addr, 
					       AllowableOptimisations::defaultOptimisations))
				goto top;
		} else {
			StateMachineSideEffectLoad *localLoad =
				dynamic_cast<StateMachineSideEffectLoad *>(se);
			if (!oracle->memoryAccessesMightAlias(localLoad, otherStore) ||
			    definitelyNotEqual(otherStore->addr, localLoad->smsel_addr, 
					       AllowableOptimisations::defaultOptimisations))
				goto top;
		}
	}			
}

/* Run sm1 and sm2 in parallel, ***stopping as soon as sm1
 * terminates***.  Consider every possible interleaving of the
 * machines, and every possible aliasing pattern.  Set *mightSurvive
 * to true if any run caused sm1 to reach a NoCrash state, otherwise
 * set it to false; likewise *mightCrash for Crash states. */
bool
evalCrossProductMachine(VexPtr<StateMachine, &ir_heap> &sm1,
			VexPtr<StateMachine, &ir_heap> &sm2,
			VexPtr<Oracle> &oracle,
			VexPtr<IRExpr, &ir_heap> &initialStateCondition,
			bool *mightSurvive,
			bool *mightCrash,
			GarbageCollectionToken token)
{
	NdChooser chooser;

	*mightSurvive = false;
	*mightCrash = false;

	VexPtr<StateMachineEdge, &ir_heap> sme1(new StateMachineEdge(sm1));
	VexPtr<StateMachineEdge, &ir_heap> sme2(new StateMachineEdge(sm2));
	while (!*mightCrash || !*mightSurvive) {
		if (TIMEOUT)
			return false;

		LibVEX_maybe_gc(token);

		CrossMachineEvalContext ctxt;
		assert(ctxt.stores.size() == 0);
		ctxt.pathConstraint = initialStateCondition;
		CrossEvalState s1(sme1, 0);
		CrossEvalState s2(sme2, 0);
		ctxt.states[0] = &s1;
		ctxt.states[1] = &s2;
		ctxt.advanceToSideEffect(0, chooser, oracle);
		ctxt.advanceToSideEffect(1, chooser, oracle);
		while (!s1.finished && !s2.finished)
			ctxt.advanceMachine(chooser.nd_choice(2),
					    chooser,
					    oracle);
		while (!s1.finished)
			ctxt.advanceMachine(0, chooser, oracle);
		if (s1.crashed) {
#if 0
			if (!*mightCrash) {
				printf("First crashing history:\n");
				ctxt.dumpHistory();
			}
#endif
			*mightCrash = true;
		} else {
#if 0
			if (!*mightSurvive) {
				printf("First surviving history:\n");
				ctxt.dumpHistory();
			}
#endif
			*mightSurvive = true;
		}
		if (!chooser.advance())
			break;
	}

	return true;
}

/* Running the store machine atomically and then runing the probe
   machine atomically shouldn't ever crash.  Tweak the initial
   assumption so that it doesn't.  Returns NULL if that's not
   possible. */
IRExpr *
writeMachineSuitabilityConstraint(
	VexPtr<StateMachine, &ir_heap> &readMachine,
	VexPtr<StateMachine, &ir_heap> &writeMachine,
	VexPtr<IRExpr, &ir_heap> &assumption,
	VexPtr<Oracle> &oracle,
	GarbageCollectionToken token)
{
	fprintf(_logfile, "\t\tBuilding write machine suitability constraint.\n");
	VexPtr<IRExpr, &ir_heap> rewrittenAssumption(assumption);
	NdChooser chooser;
	VexPtr<StateMachineEdge, &ir_heap> writeStartEdge(new StateMachineEdge(writeMachine));
	do {
		if (TIMEOUT)
			return NULL;

		LibVEX_maybe_gc(token);

		std::vector<StateMachineSideEffectStore *> storesIssuedByWriter;
		std::map<Int, IRExpr *> writerBinders;
		StateMachineEdge *writerEdge;
		IRExpr *pathConstraint;
		IRExpr *thisTimeConstraint;

		pathConstraint = assumption;
		writerEdge = writeStartEdge;
		thisTimeConstraint = IRExpr_Const(IRConst_U1(1));
		while (1) {
			for (unsigned i = 0; i < writerEdge->sideEffects.size(); i++) {
				evalStateMachineSideEffect(writerEdge->sideEffects[i],
							   chooser,
							   oracle,
							   writerBinders,
							   storesIssuedByWriter,
							   &pathConstraint,
							   &thisTimeConstraint);
			}

			StateMachine *s = writerEdge->target;
			if (dynamic_cast<StateMachineCrash *>(s) ||
			    dynamic_cast<StateMachineNoCrash *>(s) ||
			    dynamic_cast<StateMachineStub *>(s)) {
				/* Hit end of writer */
				break;
			} else if (StateMachineProxy *smp = dynamic_cast<StateMachineProxy *>(s)) {
				writerEdge = smp->target;
			} else {
				StateMachineBifurcate *smb =
					dynamic_cast<StateMachineBifurcate *>(s);
				assert(smb);
				if (expressionIsTrue(smb->condition, chooser, writerBinders, &pathConstraint, &thisTimeConstraint))
					writerEdge = smb->trueTarget;
				else
					writerEdge = smb->falseTarget;
			}
		}

		StateMachineEvalContext readEvalCtxt;
		readEvalCtxt.pathConstraint = pathConstraint;
		readEvalCtxt.stores = storesIssuedByWriter;
		readEvalCtxt.justPathConstraint = thisTimeConstraint;
		bool crashes;
		evalStateMachine(readMachine, &crashes, chooser, oracle, readEvalCtxt);
		if (crashes) {
			/* We get a crash if we evaluate the read
			   machine after running the store machine to
			   completion -> this is a poor choice of
			   store machines. */

			/* If we evaluate the read machine to
			   completion after running the write
			   machine to completion under these
			   assumptions then we get a crash ->
			   these assumptions must be false. */
			rewrittenAssumption = simplifyIRExpr(
				IRExpr_Binop(
					Iop_And1,
					rewrittenAssumption,
					IRExpr_Unop(
						Iop_Not1,
						readEvalCtxt.justPathConstraint)),
				AllowableOptimisations::defaultOptimisations);
		}
	} while (chooser.advance());
	
	if (rewrittenAssumption->tag == Iex_Const &&
	    rewrittenAssumption->Iex.Const.con->Ico.U64 == 0) {
		fprintf(_logfile, "\t\tBad choice of machines\n");
		return NULL;
	}
	return rewrittenAssumption;
}

/* Run the write machine, covering every possible schedule and
 * aliasing pattern.  After every store, run the read machine
 * atomically.  Find ranges of the store machine where the read
 * machine predicts a crash; these ranges are the remote macro
 * sections (as opposed to remote micro sections, which are just the
 * individual stores).  We assume that @assumption holds before
 * either machine starts running. */
/* Returns false if we discover something which suggests that this is
 * a bad choice of write machine, or true otherwise. */
bool
findRemoteMacroSections(VexPtr<StateMachine, &ir_heap> &readMachine,
			VexPtr<StateMachine, &ir_heap> &writeMachine,
			VexPtr<IRExpr, &ir_heap> &assumption,
			VexPtr<Oracle> &oracle,
			VexPtr<remoteMacroSectionsT, &ir_heap> &output,
			GarbageCollectionToken token)
{
	NdChooser chooser;

	VexPtr<StateMachineEdge, &ir_heap> writeStartEdge(new StateMachineEdge(writeMachine));
	do {
		if (TIMEOUT)
			return false;

		LibVEX_maybe_gc(token);

		std::vector<StateMachineSideEffectStore *> storesIssuedByWriter;
		std::map<Int, IRExpr *> writerBinders;
		StateMachineEdge *writerEdge;
		unsigned writeEdgeIdx;
		IRExpr *pathConstraint;
		StateMachineSideEffectStore *sectionStart;
		bool finished;
		StateMachineSideEffectStore *smses;

		writeEdgeIdx = 0;
		pathConstraint = assumption;
		writerEdge = writeStartEdge;
		sectionStart = NULL;
		finished = false;
		smses = NULL;
		while (!finished) {
			/* Have we hit the end of the current writer edge? */

			if (writeEdgeIdx == writerEdge->sideEffects.size()) {
				/* Yes, move to the next state. */
				StateMachine *s = writerEdge->target;
				assert(!dynamic_cast<StateMachineUnreached *>(s));
				if (dynamic_cast<StateMachineTerminal *>(s)) {
					/* Hit the end of the writer
					 * -> we're done. */
					/* Note that we need to
					   evaluate the read machine
					   one last time, so that we
					   can take account of any
					   assumptions made due to any
					   branches after the last
					   side-effect. */
					/* i.e. a store machine branch
					   will change the path
					   constraint, which could
					   cause the read machien to
					   go from crash to non-crash,
					   and we need to make sure
					   that we pick that up as the
					   end of a critical
					   section. */
					/* Example of code where this is
					   important:

					   acquire_lock();
					   x = foo->flag;
					   foo->bar = 5;
					   if (x) {
					       release_lock();
					       return;
					   }
					   foo->flag = 0;
					   release_lock();

					   but with the locking taken
					   out.
					*/
					finished = true;
					goto eval_read_machine;
				}
				if (StateMachineProxy *smp =
				    dynamic_cast<StateMachineProxy *>(s)) {
					writerEdge = smp->target;
					writeEdgeIdx = 0;
					continue;
				}
				StateMachineBifurcate *smb =
					dynamic_cast<StateMachineBifurcate *>(s);
				assert(smb);
				if (expressionIsTrue(smb->condition, chooser, writerBinders, &pathConstraint, NULL))
					writerEdge = smb->trueTarget;
				else
					writerEdge = smb->falseTarget;
				writeEdgeIdx = 0;
				continue;				
			}

			/* Advance the writer by one state.  Note that
			   we *don't* consider running the read before
			   any write states, as that's already been
			   handled and is known to lead to
			   no-crash. */
			StateMachineSideEffect *se;
			se = writerEdge->sideEffects[writeEdgeIdx];
			evalStateMachineSideEffect(se, chooser, oracle, writerBinders, storesIssuedByWriter, &pathConstraint, NULL);
			writeEdgeIdx++;

			/* Advance to a store */
			smses = dynamic_cast<StateMachineSideEffectStore *>(se);
			if (!smses)
				continue;

		eval_read_machine:
			/* The writer just issued a store, so we
			   should now try running the reader
			   atomically.  We discard any stores issued
			   by the reader once it's finished, but we
			   need to track them while it's running, so
			   need a fresh eval ctxt and a fresh copy of
			   the stores list every time around the
			   loop. */
			StateMachineEvalContext readEvalCtxt;
			readEvalCtxt.pathConstraint = pathConstraint;
			readEvalCtxt.stores = storesIssuedByWriter;
			bool crashes;
			evalStateMachine(readMachine, &crashes, chooser, oracle, readEvalCtxt);
			if (crashes) {
				if (!sectionStart) {
					/* The previous attempt at
					   evaluating the read machine
					   didn't lead to a crash, so
					   this is the start of a
					   critical section. */
					sectionStart = smses;
				} else {
					/* Critical section
					 * continues. */
				}
			} else {
				if (sectionStart) {
					/* Previous attempt did crash
					   -> this is the end of the
					   section. */
					output->insert(sectionStart, smses);
					sectionStart = NULL;
				}
			}
		}

		/* This is enforced by the suitability check at the
		 * top of this function. */
		if (sectionStart) {
			fprintf(_logfile, "Whoops... running store machine and then running load machine doesn't lead to goodness.\n");
			/* Give up, shouldn't ever happen. */
			return false;
		}
	} while (chooser.advance());
	return true;
}

bool
fixSufficient(StateMachine *writeMachine,
	      StateMachine *probeMachine,
	      IRExpr *assumption,
	      Oracle *oracle,
	      remoteMacroSectionsT *sections)
{
	NdChooser chooser;
	StateMachineEdge *writeStartEdge = new StateMachineEdge(writeMachine);

	do {
		if (TIMEOUT)
			return false;

		std::vector<StateMachineSideEffectStore *> storesIssuedByWriter;
		std::map<Int, IRExpr *> writerBinders;
		StateMachineEdge *writerEdge;
		unsigned writeEdgeIdx;
		IRExpr *pathConstraint;
		std::set<StateMachineSideEffectStore *> incompleteSections;

		writeEdgeIdx = 0;
		pathConstraint = assumption;
		writerEdge = writeStartEdge;
		while (1) {
			/* Have we hit the end of the current writer edge? */
			if (writeEdgeIdx == writerEdge->sideEffects.size()) {
				/* Yes, move to the next state. */
				StateMachine *s = writerEdge->target;
				assert(!dynamic_cast<StateMachineUnreached *>(s));
				if (dynamic_cast<StateMachineCrash *>(s) ||
				    dynamic_cast<StateMachineNoCrash *>(s) ||
				    dynamic_cast<StateMachineStub *>(s)) {
					/* Hit the end of the writer
					 * -> we're done. */
					break;
				}
				if (StateMachineProxy *smp =
				    dynamic_cast<StateMachineProxy *>(s)) {
					writerEdge = smp->target;
					writeEdgeIdx = 0;
					continue;
				}
				StateMachineBifurcate *smb =
					dynamic_cast<StateMachineBifurcate *>(s);
				assert(smb);
				if (expressionIsTrue(smb->condition, chooser, writerBinders, &pathConstraint, NULL))
					writerEdge = smb->trueTarget;
				else
					writerEdge = smb->falseTarget;
				writeEdgeIdx = 0;
				continue;				
			}

			/* Advance the writer by one state.  Note that
			   we *don't* consider running the read before
			   any write states, as that's already been
			   handled and is known to lead to
			   no-crash. */
			StateMachineSideEffect *se;
			se = writerEdge->sideEffects[writeEdgeIdx];
			evalStateMachineSideEffect(se, chooser, oracle, writerBinders, storesIssuedByWriter, &pathConstraint, NULL);
			writeEdgeIdx++;

			/* Only consider running the probe machine if
			 * we just executed a store. */
			StateMachineSideEffectStore *smses =
				dynamic_cast<StateMachineSideEffectStore *>(se);
			if (!smses)
				continue;

			/* Did we just leave a critical section? */
			if (incompleteSections.count(smses))
				incompleteSections.erase(smses);
			/* Did we just enter a critical section? */
			for (remoteMacroSectionsT::iterator it = sections->begin();
			     it != sections->end();
			     it++) {
				if (it->start == smses)
					incompleteSections.insert(it->end);
			}
			/* If we have incomplete critical sections, we
			 * can't run the probe machine. */
			if (incompleteSections.size() != 0)
				continue;

			/* The writer just issued a store and is not
			   in a critical section, so we should now try
			   running the reader atomically.  */
			StateMachineEvalContext readEvalCtxt;
			readEvalCtxt.pathConstraint = pathConstraint;
			readEvalCtxt.stores = storesIssuedByWriter;
			bool crashes;
			evalStateMachine(probeMachine, &crashes, chooser, oracle, readEvalCtxt);
			if (crashes) {
				fprintf(_logfile, "Fix is insufficient, witness: ");
				ppIRExpr(readEvalCtxt.pathConstraint, _logfile);
				fprintf(_logfile, "\n");
				return false; 
			}
		}
	} while (chooser.advance());

	/* If we get here then there's no way of crashing the probe
	   machine by running it in parallel with the store machine,
	   provided the proposed fix is applied.  That means that the
	   proposed fix is good. */

	return true;
}

