#include "sli.h"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "nd_chooser.h"
#include "eval_state_machine.hpp"
#include "offline_analysis.hpp"
#include "inferred_information.hpp"
#include "cnf.hpp"
#include "libvex_prof.hpp"

/* All of the state needed to evaluate a single pure IRExpr. */
class threadState {
public:
	std::map<threadAndRegister, IRExpr *, threadAndRegister::partialCompare> registers;
};

typedef std::vector<std::pair<StateMachine *, StateMachineSideEffectMemoryAccess *> > memLogT;
class StateMachineEvalContext {
public:
	StateMachineEvalContext()
		: collectOrderingConstraints(false),
		  justPathConstraint(NULL)
	{}
	memLogT memLog;
	threadState state;
	bool collectOrderingConstraints;
	/* justPathConstraint contains all of the assumptions we've
	   made using the ND chooser.  pathConstraint is that plus the
	   initial assumption. */
	IRExpr *pathConstraint;
	IRExpr *justPathConstraint;
};

class SpecialiseIRExpr : public IRExprTransformer {
	threadState &state;
	IRExpr *transformIex(IRExprGet *e) {
		auto it = state.registers.find(e->reg);
		if (it != state.registers.end())
			return it->second;
		return IRExprTransformer::transformIex(e);
	}
public:
	SpecialiseIRExpr(threadState &_state)
		: state(_state)
	{}
};

static IRExpr *
specialiseIRExpr(IRExpr *iex, threadState &state)
{
	SpecialiseIRExpr s(state);
	return s.transformIRExpr(iex);
}

static bool
expressionIsTrue(IRExpr *exp, NdChooser &chooser, threadState &state, const AllowableOptimisations &opt, 
		 IRExpr **assumption, IRExpr **accumulatedAssumptions)
{
	if (TIMEOUT)
		return true;

	exp = simplifyIRExpr(internIRExpr(specialiseIRExpr(exp, state)), opt);

	/* Combine the path constraint with the new expression and see
	   if that produces a contradiction.  If it does then we know
	   for sure that the new expression is false. */
	IRExpr *e =
		simplifyIRExpr(
			IRExpr_Binop(
				Iop_And1,
				*assumption,
				exp),
			opt);
	if (e->tag == Iex_Const) {
		/* That shouldn't produce the constant 1 very often.
		   If it does, it indicates that the path constraint
		   is definitely true, and the new expression is
		   definitely true, but for some reason we weren't
		   able to simplify the path constraint down to 1
		   earlier.  Consider that a lucky break and simplify
		   it now. */
		if (((IRExprConst *)e)->con->Ico.U1) {
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
			opt);
	if (e2->tag == Iex_Const) {
		/* If X & ¬Y is definitely true, Y is definitely
		 * false and X is definitely true. */
		if (((IRExprConst *)e2)->con->Ico.U1) {
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
	} else {
		printf("Retread old choice\n");
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
					opt);
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
					opt);
		return false;
	}
}

static bool
evalExpressionsEqual(IRExpr *exp1, IRExpr *exp2, NdChooser &chooser, threadState &state,
		     const AllowableOptimisations &opt, IRExpr **assumption, IRExpr **accAssumptions)
{
	return expressionIsTrue(IRExpr_Binop(
					Iop_CmpEQ64,
					exp1,
					exp2),
				chooser,
				state,
				opt,
				assumption,
				accAssumptions);
}

static void
addOrderingConstraint(ThreadVexRip before,
		      ThreadVexRip after,
		      const AllowableOptimisations &opt,
		      IRExpr **assumption,
		      IRExpr **accumulatedAssumptions)
{
	IRExpr *edge;
	if (before <= after)
		edge = IRExpr_HappensBefore(before, after);
	else
		edge = IRExpr_Unop(Iop_Not1,
				   IRExpr_HappensBefore(after, before));
	*assumption =
		simplifyIRExpr(IRExpr_Binop(Iop_And1,
					    edge,
					    *assumption),
			       opt);
	if (accumulatedAssumptions && *accumulatedAssumptions)
		*accumulatedAssumptions =
			simplifyIRExpr(IRExpr_Binop(Iop_And1,
						    edge,
						    *accumulatedAssumptions),
				       opt);
}

static void evalStateMachine(StateMachine *rootMachine,
			     StateMachineState *sm,
			     bool *crashes,
			     NdChooser &chooser,
			     Oracle *oracle,
			     const AllowableOptimisations &opt,
			     StateMachineEvalContext &ctxt);

static bool
evalStateMachineSideEffect(StateMachine *thisMachine,
			   StateMachineSideEffect *smse,
			   NdChooser &chooser,
			   Oracle *oracle,
			   threadState &state,
			   memLogT &memLog,
			   bool collectOrderingConstraints,
			   const AllowableOptimisations &opt,
			   IRExpr **assumption,
			   IRExpr **accumulatedAssumptions)
{
	IRExpr *addr = NULL;
	if (smse->type == StateMachineSideEffect::Load ||
	    smse->type == StateMachineSideEffect::Store) {
		StateMachineSideEffectMemoryAccess *smsema =
			dynamic_cast<StateMachineSideEffectMemoryAccess *>(smse);
		assert(smsema);
		addr = specialiseIRExpr(smsema->addr, state);
		IRExpr *v = IRExpr_Unop(Iop_Not1,
					IRExpr_Unop(Iop_BadPtr, addr));
		*assumption = simplifyIRExpr(
			IRExpr_Binop(Iop_And1, *assumption, v),
			opt);
		if (!collectOrderingConstraints && accumulatedAssumptions && *accumulatedAssumptions)
			*accumulatedAssumptions =
				simplifyIRExpr(
					IRExpr_Binop(Iop_And1, *accumulatedAssumptions, v),
					opt);
	}

	switch (smse->type) {
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectStore *smses =
			dynamic_cast<StateMachineSideEffectStore *>(smse);
		assert(smses);
		assert(addr);
		if (collectOrderingConstraints) {
			for (memLogT::reverse_iterator it = memLog.rbegin();
			     it != memLog.rend();
			     it++) {
				if (it->first == thisMachine)
					continue;
				if (it->second->type != StateMachineSideEffect::Load)
					continue;
				StateMachineSideEffectLoad *smsel =
					dynamic_cast<StateMachineSideEffectLoad *>(it->second);
				assert(smsel);
				if (!oracle->memoryAccessesMightAlias(opt, smsel, smses))
					continue;
				if (evalExpressionsEqual(addr, smsel->addr, chooser, state, opt, assumption, accumulatedAssumptions))
					addOrderingConstraint(
						smsel->rip,
						smses->rip,
						opt,
						assumption,
						accumulatedAssumptions);
			}
		}
		IRExpr *data = specialiseIRExpr(smses->data, state);
		memLog.push_back(
			std::pair<StateMachine *, StateMachineSideEffectMemoryAccess *>
			(thisMachine,
			 new StateMachineSideEffectStore(
				 specialiseIRExpr(addr, state),
				 specialiseIRExpr(data, state),
				 smses->rip
				 )
				));
		break;
	}
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel =
			dynamic_cast<StateMachineSideEffectLoad *>(smse);
		assert(smsel);
		assert(addr);
		StateMachineSideEffectStore *satisfier;
		StateMachine *satisfierMachine;
		satisfier = NULL;
		satisfierMachine = NULL;
		for (memLogT::reverse_iterator it = memLog.rbegin();
		     it != memLog.rend();
		     it++) {
			StateMachineSideEffectStore *smses = dynamic_cast<StateMachineSideEffectStore *>(it->second);
			if (!smses || !oracle->memoryAccessesMightAlias(opt, smsel, smses))
				continue;
			if (evalExpressionsEqual(smses->addr, addr, chooser, state, opt, assumption, accumulatedAssumptions)) {
				if (!collectOrderingConstraints) {
					satisfier = smses;
					satisfierMachine = it->first;
					break;
				} else {
					if (satisfier) {
						if (it->first != satisfierMachine)
							addOrderingConstraint(
								smses->rip,
								satisfier->rip,
								opt,
								assumption,
								accumulatedAssumptions);
					} else {
						if (it->first != thisMachine)
							addOrderingConstraint(
								smses->rip,
								smsel->rip,
								opt,
								assumption,
								accumulatedAssumptions);
						satisfier = smses;
						satisfierMachine = it->first;
					}
				}
			}
		}
		IRExpr *val;
		if (satisfier)
			val = satisfier->data;
		else
			val = IRExpr_Load(Ity_I64, addr, smsel->rip);
		if (collectOrderingConstraints)
			memLog.push_back(
				std::pair<StateMachine *, StateMachineSideEffectMemoryAccess *>(
					thisMachine,
					new StateMachineSideEffectLoad(
						smsel->target,
						specialiseIRExpr(addr, state),
						smsel->rip)));
		state.registers[smsel->target] = val;
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec =
			dynamic_cast<StateMachineSideEffectCopy *>(smse);
		assert(smsec);
		state.registers[smsec->target] =
			specialiseIRExpr(smsec->value, state);
		break;
	}
	case StateMachineSideEffect::Unreached:
		abort();
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(smse);
		if (expressionIsTrue(smseaf->value, chooser, state, opt,
				     assumption, accumulatedAssumptions))
			return false;
		break;
	}
	case StateMachineSideEffect::Phi:
		/* These don't do anything at the semantic level.  We
		   interpret ignoring generation numbers, so assigning
		   x_n = x_{last n} is a no-op. */
		break;
	}
	return true;
}

static void
evalStateMachineEdge(StateMachine *thisMachine,
		     StateMachineEdge *sme,
		     bool *crashes,
		     NdChooser &chooser,
		     Oracle *oracle,
		     const AllowableOptimisations &opt,
		     StateMachineEvalContext &ctxt)
{
	bool valid = true;
	for (std::vector<StateMachineSideEffect *>::iterator it = sme->sideEffects.begin();
	     valid && !TIMEOUT && it != sme->sideEffects.end();
	     it++)
		valid &=
			evalStateMachineSideEffect(thisMachine, *it, chooser, oracle, ctxt.state,
						   ctxt.memLog, ctxt.collectOrderingConstraints,
						   opt,
						   &ctxt.pathConstraint,
						   &ctxt.justPathConstraint);
	if (!valid ||
	    (ctxt.pathConstraint->tag == Iex_Const &&
	     ((IRExprConst *)ctxt.pathConstraint)->con->Ico.U1 == 0)) {
		/* We've found a contradiction.  That means that the
		   original program would have crashed, *but* in a way
		   other than the one which we're investigating.  We
		   therefore treat that as no-crash and abort the
		   run. */
		*crashes = false;
		return;
	}
	evalStateMachine(thisMachine, sme->target, crashes, chooser, oracle, opt, ctxt);
}

/* Walk the state machine and figure out whether it's going to crash.
   If we hit something which we can't solve statically or via the
   oracle, ask the chooser which way we should go, and then emit a
   path constraint saying which way we went.  Stubs are assumed to
   never crash. */
static void
evalStateMachine(StateMachine *rootMachine,
		 StateMachineState *sm,
		 bool *crashes,
		 NdChooser &chooser,
		 Oracle *oracle,
		 const AllowableOptimisations &opt,
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
		evalStateMachineEdge(rootMachine, smp->target, crashes, chooser, oracle, opt, ctxt);
		return;
	}
	if (StateMachineBifurcate *smb =
	    dynamic_cast<StateMachineBifurcate *>(sm)) {
		if (expressionIsTrue(smb->condition, chooser, ctxt.state, opt, &ctxt.pathConstraint, &ctxt.justPathConstraint)) {
			evalStateMachineEdge(rootMachine, smb->trueTarget, crashes, chooser, oracle, opt, ctxt);
		} else {
			evalStateMachineEdge(rootMachine, smb->falseTarget, crashes, chooser, oracle, opt, ctxt);
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
				       const AllowableOptimisations &opt,
				       GarbageCollectionToken token)
{
	__set_profiling(survivalConstraintIfExecutedAtomically);
	NdChooser chooser;
	VexPtr<IRExpr, &ir_heap> currentConstraint(IRExpr_Const(IRConst_U1(1)));
	bool crashes;

	do {
		if (TIMEOUT)
			return NULL;

		LibVEX_maybe_gc(token);
		StateMachineEvalContext ctxt;
		ctxt.pathConstraint = IRExpr_Const(IRConst_U1(1));
		evalStateMachine(sm, sm->root, &crashes, chooser, oracle, opt, ctxt);
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
			newConstraint = simplifyIRExpr(newConstraint, opt);
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
			    const AllowableOptimisations &opt, 
			    GarbageCollectionToken token)
{
	__set_profiling(writeMachineCrashConstraint);
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
		evalStateMachine(sm, sm->root, &crashes, chooser, oracle, opt, ctxt);

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
				simplifyIRExpr(conjunctConstraint, opt);
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
				simplifyIRExpr(disjunctConstraint, opt);
		}
	} while (chooser.advance());

	IRExpr *finalConstraint = IRExpr_Binop(Iop_And1,
					       conjunctConstraint,
					       disjunctConstraint);
	finalConstraint = simplifyIRExpr(finalConstraint, opt);
	return finalConstraint;
}

bool
evalMachineUnderAssumption(VexPtr<StateMachine, &ir_heap> &sm, VexPtr<Oracle> &oracle,
			   VexPtr<IRExpr, &ir_heap> assumption,
			   const AllowableOptimisations &opt,
			   bool *mightSurvive, bool *mightCrash,
			   GarbageCollectionToken token)
{
	__set_profiling(evalMachineUnderAssumption);
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
		evalStateMachine(sm, sm->root, &crashes, chooser, oracle, opt, ctxt);
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
	StateMachine *rootMachine;
	StateMachineEdge *currentEdge;
	unsigned nextEdgeSideEffectIdx;
	bool finished;
	bool crashed;
	threadState state;
	CrossEvalState(StateMachine *_rootMachine, StateMachineEdge *_e, int _i)
		: rootMachine(_rootMachine),
		  currentEdge(_e),
		  nextEdgeSideEffectIdx(_i),
		  finished(false),
		  crashed(false)
	{}
};

class CrossMachineEvalContext {
	void advanceToSideEffect(CrossEvalState *machine, NdChooser &chooser, Oracle *oracle,
				 const AllowableOptimisations &opt,
				 std::set<VexRip> &usefulRips, bool wantLoad);
public:
	bool collectOrderingConstraints;
	IRExpr *pathConstraint;
	IRExpr *justPathConstraint;
	memLogT memLog;
	CrossEvalState *loadMachine;
	CrossEvalState *storeMachine;
	std::vector<StateMachineSideEffect *> history;
	std::set<VexRip> &probeMachineRacingInstructions;
	std::set<VexRip> &storeMachineRacingInstructions;
	void advanceMachine(NdChooser &chooser, Oracle *oracle, const AllowableOptimisations &opt, bool doLoad);
	void dumpHistory(FILE *f) const;
	void advanceToLoad(NdChooser &chooser, Oracle *oracle, const AllowableOptimisations &opt) {
		advanceToSideEffect(loadMachine, chooser, oracle, opt, probeMachineRacingInstructions, true);
	}
	void advanceToStore(NdChooser &chooser, Oracle *oracle, const AllowableOptimisations &opt) {
		advanceToSideEffect(storeMachine, chooser, oracle, opt, storeMachineRacingInstructions, false);
	}
	CrossMachineEvalContext(std::set<VexRip> &_probeMachineRacingInstructions,
				std::set<VexRip> &_storeMachineRacingInstructions)
		: collectOrderingConstraints(false),
		  pathConstraint(NULL),
		  justPathConstraint(NULL),
		  probeMachineRacingInstructions(_probeMachineRacingInstructions),
		  storeMachineRacingInstructions(_storeMachineRacingInstructions)
	{}
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
CrossMachineEvalContext::advanceToSideEffect(CrossEvalState *machine,
					     NdChooser &chooser,
					     Oracle *oracle,
					     const AllowableOptimisations &opt,
					     std::set<VexRip> &interestingRips,
					     bool wantLoad)
{
	StateMachineState *s;

top:
	if (TIMEOUT)
		return;

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
			if (expressionIsTrue(smb->condition, chooser, machine->state, opt, &pathConstraint, &justPathConstraint))
				machine->currentEdge = smb->trueTarget;
			else
				machine->currentEdge = smb->falseTarget;
			machine->nextEdgeSideEffectIdx = 0;
			continue;
		}
		abort();
	}

	StateMachineSideEffect *se;
	bool acceptable;
	se = machine->currentEdge->sideEffects[machine->nextEdgeSideEffectIdx];

	acceptable = se->type == StateMachineSideEffect::Store;
	if (wantLoad)
		acceptable |= se->type == StateMachineSideEffect::Load;
	if (acceptable) {
		StateMachineSideEffectMemoryAccess *smea = dynamic_cast<StateMachineSideEffectMemoryAccess *>(se);
		if (smea)
			acceptable &= interestingRips.count(smea->rip.rip);
	}
	if (!acceptable) {
		if (!evalStateMachineSideEffect(machine->rootMachine, se, chooser, oracle, machine->state, memLog,
						collectOrderingConstraints, opt, &pathConstraint, &justPathConstraint)) {
			/* Found a contradiction -> get out */
			machine->finished = true;
			return;
		}
		history.push_back(se);
		machine->nextEdgeSideEffectIdx++;
		goto top;
	}
}

void
CrossMachineEvalContext::advanceMachine(NdChooser &chooser,
					Oracle *oracle,
					const AllowableOptimisations &opt,
					bool doLoad)
{
	CrossEvalState *machine = doLoad ? loadMachine : storeMachine;

	if (doLoad)
		advanceToLoad(chooser, oracle, opt);
	else
		advanceToStore(chooser, oracle, opt);
	if (machine->finished || machine->crashed || TIMEOUT)
		return;

	StateMachineSideEffect *se;
	assert(machine->nextEdgeSideEffectIdx < machine->currentEdge->sideEffects.size());
	se = machine->currentEdge->sideEffects[machine->nextEdgeSideEffectIdx];	
	if (!evalStateMachineSideEffect(machine->rootMachine, se, chooser, oracle, machine->state, memLog,
					collectOrderingConstraints, opt, &pathConstraint, &justPathConstraint)) {
		machine->finished = true;
	} else {
		history.push_back(se);
		machine->nextEdgeSideEffectIdx++;
	}
}

static void
findCrossMachineRacingInstructions(StateMachine *probeMachine,
				   StateMachine *storeMachine,
				   Oracle *oracle,
				   const AllowableOptimisations &opt,
				   std::set<VexRip> &probeMachineRacingInstructions,
				   std::set<VexRip> &storeMachineRacingInstructions)
{
	std::set<StateMachineSideEffectStore *> storeMachineStores;
	findAllStores(storeMachine, storeMachineStores);
	for (auto it = storeMachineStores.begin(); it != storeMachineStores.end(); it++)
		oracle->findRacingRips(*it, probeMachineRacingInstructions);

	std::set<StateMachineSideEffectLoad *> probeMachineLoads;
	findAllLoads(probeMachine, probeMachineLoads);
	for (auto it = probeMachineLoads.begin(); it != probeMachineLoads.end(); it++)
		oracle->findRacingRips(opt, *it, storeMachineRacingInstructions);
}

bool
evalCrossProductMachine(VexPtr<StateMachine, &ir_heap> &probeMachine,
			VexPtr<StateMachine, &ir_heap> &storeMachine,
			VexPtr<Oracle> &oracle,
			VexPtr<IRExpr, &ir_heap> &initialStateCondition,
			const AllowableOptimisations &opt,
			bool *mightSurvive,
			bool *mightCrash,
			GarbageCollectionToken token)
{
	__set_profiling(evalCrossProductMachine);
	NdChooser chooser;

	*mightSurvive = false;
	*mightCrash = false;

	std::set<VexRip> probeMachineRacingInstructions;
	std::set<VexRip> storeMachineRacingInstructions;
	findCrossMachineRacingInstructions(probeMachine, storeMachine, oracle,
					   opt,
					   probeMachineRacingInstructions,
					   storeMachineRacingInstructions);

	AllowableOptimisations loadMachineOpt = opt;
	loadMachineOpt.nonLocalLoads = &probeMachineRacingInstructions;
	probeMachine = optimiseStateMachine(probeMachine, loadMachineOpt, oracle,
					    true, token);

	VexPtr<StateMachineEdge, &ir_heap> probeEdge(new StateMachineEdge(probeMachine->root));
	VexPtr<StateMachineEdge, &ir_heap> storeEdge(new StateMachineEdge(storeMachine->root));
	while (!*mightCrash || !*mightSurvive) {
		if (TIMEOUT)
			return false;

		LibVEX_maybe_gc(token);

		CrossMachineEvalContext ctxt(probeMachineRacingInstructions, storeMachineRacingInstructions);
		ctxt.pathConstraint = initialStateCondition;
		CrossEvalState s1(probeMachine, probeEdge, 0);
		CrossEvalState s2(storeMachine, storeEdge, 0);
		ctxt.loadMachine = &s1;
		ctxt.storeMachine = &s2;
		while (!TIMEOUT && !s1.finished && !s2.finished)
			ctxt.advanceMachine(chooser,
					    oracle,
					    opt,
					    chooser.nd_choice(2));
		while (!TIMEOUT && !s1.finished)
			ctxt.advanceMachine(chooser, oracle, opt, true);
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
	const AllowableOptimisations &opt,
	GarbageCollectionToken token)
{
	__set_profiling(writeMachineSuitabilityConstraint);
	fprintf(_logfile, "\t\tBuilding write machine suitability constraint.\n");
	VexPtr<IRExpr, &ir_heap> rewrittenAssumption(assumption);
	NdChooser chooser;
	VexPtr<StateMachineEdge, &ir_heap> writeStartEdge(new StateMachineEdge(writeMachine->root));
	do {
		if (TIMEOUT)
			return NULL;

		LibVEX_maybe_gc(token);

		memLogT memLog;
		threadState writerState;
		StateMachineEdge *writerEdge;
		IRExpr *pathConstraint;
		IRExpr *thisTimeConstraint;
		bool writer_failed = false;

		pathConstraint = assumption;
		writerEdge = writeStartEdge;
		thisTimeConstraint = IRExpr_Const(IRConst_U1(1));
		while (!writer_failed) {
			for (unsigned i = 0; !writer_failed && !TIMEOUT && i < writerEdge->sideEffects.size(); i++) {
				if (!evalStateMachineSideEffect(writeMachine,
								writerEdge->sideEffects[i],
								chooser,
								oracle,
								writerState,
								memLog,
								false,
								opt,
								&pathConstraint,
								&thisTimeConstraint)) {
					/* There's no way the writer
					 * could actually get here.
					 * Get out */
					writer_failed = true;
				}
			}

			StateMachineState *s = writerEdge->target;
			if (writer_failed ||
			    dynamic_cast<StateMachineCrash *>(s) ||
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
				if (expressionIsTrue(smb->condition, chooser, writerState, opt, &pathConstraint, &thisTimeConstraint))
					writerEdge = smb->trueTarget;
				else
					writerEdge = smb->falseTarget;
			}
		}

		if (!writer_failed) {
			StateMachineEvalContext readEvalCtxt;
			readEvalCtxt.pathConstraint = pathConstraint;
			readEvalCtxt.memLog = memLog;
			readEvalCtxt.justPathConstraint = thisTimeConstraint;
			bool crashes;
			evalStateMachine(readMachine, readMachine->root, &crashes, chooser, oracle, opt, readEvalCtxt);
			if (crashes) {
				/* We get a crash if we evaluate the
				   read machine after running the
				   store machine to completion -> this
				   is a poor choice of store
				   machines. */

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
					opt);
			}
		}
	} while (chooser.advance());
	
	if (rewrittenAssumption->tag == Iex_Const &&
	    ((IRExprConst *)rewrittenAssumption.get())->con->Ico.U64 == 0) {
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
			const AllowableOptimisations &opt,
			VexPtr<remoteMacroSectionsT, &ir_heap> &output,
			GarbageCollectionToken token)
{
	__set_profiling(findRemoteMacroSections);
	NdChooser chooser;

	VexPtr<StateMachineEdge, &ir_heap> writeStartEdge(new StateMachineEdge(writeMachine->root));
	do {
		if (TIMEOUT)
			return false;

		LibVEX_maybe_gc(token);

		memLogT storesIssuedByWriter;
		threadState writerState;
		StateMachineEdge *writerEdge;
		unsigned writeEdgeIdx;
		IRExpr *pathConstraint;
		StateMachineSideEffectStore *sectionStart;
		bool finished;
		StateMachineSideEffectStore *smses;
		bool writer_failed;

		writeEdgeIdx = 0;
		pathConstraint = assumption;
		writerEdge = writeStartEdge;
		sectionStart = NULL;
		finished = false;
		smses = NULL;
		writer_failed = false;

		while (!writer_failed && !TIMEOUT && !finished) {
			/* Have we hit the end of the current writer edge? */

			if (writeEdgeIdx == writerEdge->sideEffects.size()) {
				/* Yes, move to the next state. */
				StateMachineState *s = writerEdge->target;
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
				if (expressionIsTrue(smb->condition, chooser, writerState, opt, &pathConstraint, NULL))
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
			if (!evalStateMachineSideEffect(writeMachine, se, chooser, oracle, writerState, storesIssuedByWriter, false, opt, &pathConstraint, NULL)) {
				writer_failed = true;
				break;
			}
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
			readEvalCtxt.memLog = storesIssuedByWriter;
			bool crashes;
			evalStateMachine(readMachine, readMachine->root, &crashes, chooser, oracle, opt, readEvalCtxt);
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
		if (!writer_failed && sectionStart) {
			fprintf(_logfile, "Whoops... running store machine and then running load machine doesn't lead to goodness.\n");
			/* Give up, shouldn't ever happen. */
			return false;
		}
	} while (chooser.advance());
	return true;
}

bool
fixSufficient(VexPtr<StateMachine, &ir_heap> &writeMachine,
	      VexPtr<StateMachine, &ir_heap> &probeMachine,
	      VexPtr<IRExpr, &ir_heap> &assumption,
	      VexPtr<Oracle> &oracle,
	      const AllowableOptimisations &opt,
	      VexPtr<remoteMacroSectionsT, &ir_heap> &sections,
	      GarbageCollectionToken token)
{
	__set_profiling(fixSufficient);
	NdChooser chooser;
	VexPtr<StateMachineEdge, &ir_heap> writeStartEdge(new StateMachineEdge(writeMachine->root));

	do {
		if (TIMEOUT)
			return false;

		LibVEX_maybe_gc(token);

		memLogT storesIssuedByWriter;
		threadState writerState;
		StateMachineEdge *writerEdge;
		unsigned writeEdgeIdx;
		IRExpr *pathConstraint;
		std::set<StateMachineSideEffectStore *> incompleteSections;

		writeEdgeIdx = 0;
		pathConstraint = assumption;
		writerEdge = writeStartEdge;
		while (!TIMEOUT) {
			/* Have we hit the end of the current writer edge? */
			if (writeEdgeIdx == writerEdge->sideEffects.size()) {
				/* Yes, move to the next state. */
				StateMachineState *s = writerEdge->target;
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
				if (expressionIsTrue(smb->condition, chooser, writerState, opt, &pathConstraint, NULL))
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
			if (!evalStateMachineSideEffect(writeMachine, se, chooser, oracle, writerState, storesIssuedByWriter, false, opt, &pathConstraint, NULL)) {
				/* Contradiction in the writer -> give
				 * up. */
				break;
			}
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
			readEvalCtxt.memLog = storesIssuedByWriter;
			bool crashes;
			evalStateMachine(probeMachine, probeMachine->root, &crashes, chooser, oracle, opt, readEvalCtxt);
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

static void
findHappensBeforeRelations(VexPtr<StateMachine, &ir_heap> &probeMachine,
			   VexPtr<StateMachine, &ir_heap> &storeMachine,
			   VexPtr<IRExpr, &ir_heap> &result,
			   VexPtr<Oracle> &oracle,
			   VexPtr<IRExpr, &ir_heap> &initialStateCondition,
			   const AllowableOptimisations &opt,
			   GarbageCollectionToken token)
{
	NdChooser chooser;
	VexPtr<IRExpr, &ir_heap> newCondition(IRExpr_Const(IRConst_U1(0)));

	std::set<VexRip> probeMachineRacingInstructions;
	std::set<VexRip> storeMachineRacingInstructions;
	findCrossMachineRacingInstructions(probeMachine, storeMachine, oracle,
					   opt,
					   probeMachineRacingInstructions,
					   storeMachineRacingInstructions);

	VexPtr<StateMachineEdge, &ir_heap> probeEdge(new StateMachineEdge(probeMachine->root));
	VexPtr<StateMachineEdge, &ir_heap> storeEdge(new StateMachineEdge(storeMachine->root));
	while (1) {
		if (TIMEOUT)
			return;

		LibVEX_maybe_gc(token);

		CrossMachineEvalContext ctxt(probeMachineRacingInstructions,
					     storeMachineRacingInstructions);
		ctxt.collectOrderingConstraints = true;
		ctxt.pathConstraint = initialStateCondition;
		ctxt.justPathConstraint = IRExpr_Const(IRConst_U1(1));
		CrossEvalState s1(probeMachine, probeEdge, 0);
		CrossEvalState s2(storeMachine, storeEdge, 0);
		ctxt.loadMachine = &s1;
		ctxt.storeMachine = &s2;
		while (!TIMEOUT && !s1.finished && !s2.finished)
			ctxt.advanceMachine(chooser,
					    oracle,
					    opt,
					    chooser.nd_choice(2));
		while (!TIMEOUT && !s1.finished)
			ctxt.advanceMachine(chooser, oracle, opt, true);
		while (!TIMEOUT && !s2.finished)
			ctxt.advanceMachine(chooser, oracle, opt, false);
		if (s1.crashed) {
			newCondition =
				IRExpr_Binop(
					Iop_Or1,
					newCondition,
					ctxt.justPathConstraint);
			newCondition = simplifyIRExpr(newCondition,
						      opt);
		}
		if (!chooser.advance())
			break;
	}	

	result = simplifyIRExpr(
		IRExpr_Binop(
			Iop_Or1,
			result,
			newCondition),
		opt);
}

IRExpr *
findHappensBeforeRelations(VexPtr<CrashSummary, &ir_heap> &summary,
			   VexPtr<Oracle> &oracle,
			   const AllowableOptimisations &opt,
			   GarbageCollectionToken token)
{
	__set_profiling(findHappensBeforeRelations);
	VexPtr<IRExpr, &ir_heap> res(IRExpr_Const(IRConst_U1(0)));
	VexPtr<StateMachine, &ir_heap> probeMachine(summary->loadMachine);
	for (unsigned x = 0; x < summary->storeMachines.size(); x++) {
		LibVEX_maybe_gc(token);
		VexPtr<StateMachine, &ir_heap> storeMachine(summary->storeMachines[x]->machine);
		VexPtr<IRExpr, &ir_heap> assumption(summary->storeMachines[x]->assumption);
		findHappensBeforeRelations(probeMachine, storeMachine, res, oracle, assumption, opt, token);
	}
	return res;
}

