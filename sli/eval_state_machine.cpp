#include "sli.h"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "nd_chooser.h"
#include "eval_state_machine.hpp"
#include "offline_analysis.hpp"
#include "inferred_information.hpp"
#include "intern.hpp"
#include "libvex_prof.hpp"
#include "typesdb.hpp"

/* All of the state needed to evaluate a single pure IRExpr. */
class threadState {
	/* This is a little bit tricky, because we need to support
	   sub-word writes to registers, but in the vast majority of
	   cases we'll only read back at the written type.  The fix is
	   just to keep track of writes to each individual type.
	   When all of the writes are present, the value of the register
	   is given by:

	   val8 |
	   (val16 & ~0xff) |
	   (val32 & ~0xffff) |
	   (val64 & ~0xffffffff)

	   If val16 were missing (NULL), say, the value would be

	   val8 |
	   (val32 & ~0xffffff) |
	   (val64 & ~0xffffffff)

	   As another example, if val8 and val32 were missing, the value
	   would be

	   val16 |
	   (val64 & 0xffffffffffff0000)

	   If val64 is missing then it's replaced by the initial value
	   of the register.

	   Updates are fairly simple: you just assign to the relevant
	   valX field and then clear all of the smaller ones (so if
	   you e.g. write to val32 you clear val16 and val8).
	*/
	struct register_val {
		IRExpr *val8;
		IRExpr *val16;
		IRExpr *val32;
		IRExpr *val64;
		register_val()
			: val8(NULL), val16(NULL), val32(NULL), val64(NULL)
		{}
	};

	/* The values of all of the registers */
	std::map<threadAndRegister, register_val, threadAndRegister::fullCompare> registers;
	/* The order in which registers have been assigned to.  This
	   makes implementing Phi nodes much easier.  Each register
	   appears at most once in here. */
	std::vector<threadAndRegister> assignmentOrder;

	void bump_register_in_assignment_order(const threadAndRegister &reg) {
		for (auto it = assignmentOrder.begin();
		     it != assignmentOrder.end();
		     it++) {
			if (threadAndRegister::fullEq(*it, reg)) {
				assignmentOrder.erase(it);
				break;
			}
		}
		assignmentOrder.push_back(reg);
	}

	IRExpr *setTemporary(const threadAndRegister &reg, IRExpr *inp);
public:
	IRExpr *register_value(const threadAndRegister &reg,
			       IRType type) {
		auto it = registers.find(reg);
		if (it == registers.end())
			return NULL;
		register_val &rv(it->second);
		switch (type) {
		case Ity_I8:
			if (rv.val8)
				return rv.val8;
			else if (rv.val16)
				return IRExpr_Unop(Iop_16to8, rv.val16);
			else if (rv.val32)
				return IRExpr_Unop(Iop_32to8, rv.val32);
			else if (rv.val64)
				return IRExpr_Unop(Iop_64to8, rv.val64);
			else
				return NULL;
		case Ity_I16:
			if (rv.val8) {
				IRExpr *acc = IRExpr_Unop(Iop_8Uto16, rv.val8);
				IRExpr *mask = IRExpr_Const(IRConst_U16(0xff00));
				IRExpr *hi;
				if (rv.val16) {
					hi = rv.val16;
				} else if (rv.val32) {
					hi = IRExpr_Unop(Iop_32to16, rv.val32);
				} else if (rv.val64) {
					hi = IRExpr_Unop(Iop_64to16, rv.val64);
				} else {
					hi = IRExpr_Get(reg, type);
				}
				acc = IRExpr_Binop(Iop_Or16,
						   acc,
						   IRExpr_Binop(
							   Iop_And16,
							   hi,
							   mask));
				rv.val8 = NULL;
				rv.val16 = acc;
				return acc;
			} else if (rv.val16) {
				return rv.val16;
			} else if (rv.val32) {
				return IRExpr_Unop(Iop_32to16, rv.val32);
			} else if (rv.val64) {
				return IRExpr_Unop(Iop_64to16, rv.val64);
			} else
				return NULL;
		case Ity_I32: {
			IRExpr *res = NULL;
			unsigned mask = ~0;
			if (rv.val8) {
				res = IRExpr_Unop(Iop_8Uto32, rv.val8);
				mask = ~0xff;
			}
			if (rv.val16) {
				IRExpr *a = IRExpr_Unop(Iop_16Uto32, rv.val16);
				if (res)
					res = IRExpr_Binop(
						Iop_Or32,
						res,
						IRExpr_Binop(
							Iop_And32,
							a,
							IRExpr_Const(IRConst_U32(mask))));
				else
					res = a;
				mask = ~0xffff;
			}
			IRExpr *parent;
			if (rv.val32) {
				parent = rv.val32;
			} else if (rv.val64) {
				parent = IRExpr_Unop(Iop_64to32, rv.val64);
			} else if (res) {
				parent = IRExpr_Get(reg, Ity_I32);
			} else {
				parent = NULL;
			}

			if (res)
				res = IRExpr_Binop(
					Iop_Or32,
					res,
					IRExpr_Binop(
						Iop_And32,
						parent,
						IRExpr_Const(IRConst_U32(mask))));
			else
				res = parent;
			rv.val8 = NULL;
			rv.val16 = NULL;
			rv.val32 = res;
			return res;
		}

		case Ity_I64: {
			IRExpr *res = NULL;
			unsigned long mask = ~0ul;
			if (rv.val8) {
				res = IRExpr_Unop(Iop_8Uto64, rv.val8);
				mask = ~0xfful;
			}
			if (rv.val16) {
				IRExpr *a = IRExpr_Unop(Iop_16Uto64, rv.val16);
				if (res)
					res = IRExpr_Binop(
						Iop_Or64,
						res,
						IRExpr_Binop(
							Iop_And64,
							a,
							IRExpr_Const(IRConst_U64(mask))));
				else
					res = a;
				mask = ~0xfffful;
			}
			if (rv.val32) {
				IRExpr *a = IRExpr_Unop(Iop_32Uto64, rv.val32);
				if (res)
					res = IRExpr_Binop(
						Iop_Or64,
						res,
						IRExpr_Binop(
							Iop_And64,
							a,
							IRExpr_Const(IRConst_U64(mask))));
				else
					res = a;
				mask = ~0xfffffffful;
			}
			if (rv.val64) {
				if (res)
					res = IRExpr_Binop(
						Iop_Or64,
						res,
						IRExpr_Binop(
							Iop_And64,
							rv.val64,
							IRExpr_Const(IRConst_U64(mask))));
				else
					res = rv.val64;
			} else {
				if (res)
					res = IRExpr_Binop(
						Iop_Or64,
						res,
						IRExpr_Binop(
							Iop_And64,
							IRExpr_Get(reg, Ity_I64),
							IRExpr_Const(IRConst_U64(mask))));
				
			}
			/* res might still be NULL.  That's okay; it
			   just means that we want to pick up the
			   initial value of the register. */
			rv.val8 = NULL;
			rv.val16 = NULL;
			rv.val32 = NULL;
			rv.val64 = res;
			return res;
		}
		default:
			abort();
		}
	}
	void set_register(const threadAndRegister &reg, IRExpr *e, IRExpr **assumption) {
		register_val &rv(registers[reg]);
		switch (e->type()) {
		case Ity_I8:
			rv.val8 = e;
			break;
		case Ity_I16:
			rv.val8 = NULL;
			rv.val16 = e;
			break;
		case Ity_I32:
			rv.val8 = NULL;
			rv.val16 = NULL;
			rv.val32 = e;
			break;
		case Ity_I64:
			rv.val8 = NULL;
			rv.val16 = NULL;
			rv.val32 = NULL;
			rv.val64 = e;
			break;
		default:
			abort();
		}

		if (reg.isTemp())
			*assumption = setTemporary(reg, *assumption);

		bump_register_in_assignment_order(reg);
	}
	void eval_phi(StateMachineSideEffectPhi *phi, IRExpr **assumption) {
		for (auto it = assignmentOrder.rbegin();
		     it != assignmentOrder.rend();
		     it++) {
			if (threadAndRegister::partialEq(*it, phi->reg)) {
				for (auto it2 = phi->generations.begin();
				     it2 != phi->generations.end();
				     it2++) {
					if (it2->first == it->gen()) {
						registers[phi->reg] = registers[*it];
						if (phi->reg.isTemp())
							*assumption = setTemporary(phi->reg, *assumption);
						bump_register_in_assignment_order(phi->reg);
						return;
					}
				}
			}
		}
		/* We haven't yet assigned to any registers in the
		   input set of the Phi, so we're going to pick up the
		   initial value of the super-register. */
		/* The initial value must be an allowable one. */
#ifndef NDEBUG
		bool found_it;
		found_it = false;
		for (auto it = phi->generations.begin();
		     !found_it && it != phi->generations.end();
		     it++)
			if (it->first == (unsigned)-1)
				found_it = true;
		assert(found_it);
#endif
		/* Pick up initial value */
		register_val &rv(registers[phi->reg]);
		rv.val8 = NULL;
		rv.val16 = NULL;
		rv.val32 = NULL;
		rv.val64 = NULL;
		if (phi->reg.isTemp())
			*assumption = setTemporary(phi->reg, *assumption);
		bump_register_in_assignment_order(phi->reg);
	}
};

/* Rewrite @e now that we know the value of @reg */
IRExpr *
threadState::setTemporary(const threadAndRegister &reg, IRExpr *e)
{
	struct _ : public IRExprTransformer {
		const threadAndRegister &reg;
		threadState *_this;
		_(const threadAndRegister &_reg, threadState *__this)
			: reg(_reg), _this(__this)
		{}
		IRExpr *transformIex(IRExprGet *ieg) {
			if (threadAndRegister::fullEq(ieg->reg, reg))
				return _this->register_value(reg, ieg->ty);
			else
				return IRExprTransformer::transformIex(ieg);
		}
	} doit(reg, this);
	return doit.doit(e);
}

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
		IRExpr *e2 = state.register_value(e->reg, e->type());
		if (e2)
			return coerceTypes(e->type(), e2);
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
	return s.doit(iex);
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
addOrderingConstraint(const MemoryAccessIdentifier &before,
		      const MemoryAccessIdentifier &after,
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
			if (!smses)
				continue;
			/* We only accept stores which define the
			 * entire thing which we're looking for.  If
			 * something's stored as 64 bits then we'll
			 * take a load of 32 bits, but if it's stored
			 * as 32 bits then we won't take a load of 64
			 * bits. */
			if (smses->data->type() < smsel->type) {
#warning This is unsound
				continue;
			}

			if (!oracle->memoryAccessesMightAlias(opt, smsel, smses))
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
		if (satisfier) {
			val = coerceTypes(smsel->type, satisfier->data);
		} else {
			val = IRExpr_Load(smsel->type, addr, smsel->rip);
		}
		if (collectOrderingConstraints)
			memLog.push_back(
				std::pair<StateMachine *, StateMachineSideEffectMemoryAccess *>(
					thisMachine,
					new StateMachineSideEffectLoad(
						smsel->target,
						specialiseIRExpr(addr, state),
						smsel->rip,
						smsel->type)));
		state.set_register(smsel->target, val, assumption);
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec =
			dynamic_cast<StateMachineSideEffectCopy *>(smse);
		assert(smsec);
		state.set_register(smsec->target,
				   specialiseIRExpr(smsec->value, state),
				   assumption);
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
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *smsep =
			(StateMachineSideEffectPhi *)(smse);
		state.eval_phi(smsep, assumption);
		break;
	}
	}
	return true;
}

static bool
smallStepEvalStateMachineEdge(StateMachine *thisMachine,
			      StateMachineEdge *sme,
			      bool *crashes,
			      NdChooser &chooser,
			      Oracle *oracle,
			      const AllowableOptimisations &opt,
			      StateMachineEvalContext &ctxt)
{
	bool valid = true;
	if (sme->sideEffect)
		valid &=
			evalStateMachineSideEffect(thisMachine,
						   sme->sideEffect,
						   chooser,
						   oracle,
						   ctxt.state,
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
		return true;
	}
	return false;
}

/* Walk the state machine and figure out whether it's going to crash.
   If we hit something which we can't solve statically or via the
   oracle, ask the chooser which way we should go, and then emit a
   path constraint saying which way we went.  Stubs are assumed to
   never crash. */
static StateMachineEdge *
smallStepEvalStateMachine(StateMachine *rootMachine,
			  StateMachineState *sm,
			  bool *crashes,
			  NdChooser &chooser,
			  Oracle *oracle,
			  const AllowableOptimisations &opt,
			  StateMachineEvalContext &ctxt)
{
	if (TIMEOUT) {
		*crashes = false; /* Lacking any better ideas */
		return NULL;
	}

	switch (sm->type) {
	case StateMachineState::Crash:
		*crashes = true;
		return NULL;
	case StateMachineState::NoCrash:
	case StateMachineState::Stub:
		*crashes = false;
		return NULL;
	case StateMachineState::Proxy:
		return ((StateMachineProxy *)sm)->target;
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)sm;
		if (expressionIsTrue(smb->condition, chooser, ctxt.state, opt, &ctxt.pathConstraint, &ctxt.justPathConstraint))
			return smb->trueTarget;
		else
			return smb->falseTarget;
	}
	case StateMachineState::Unreached:
		/* Whoops... */
		fprintf(_logfile, "Evaluating an unreachable state machine?\n");
		*crashes = false;
		return NULL;
	}

	abort();
}

static void
bigStepEvalStateMachine(StateMachine *rootMachine,
			StateMachineState *sm,
			bool *crashes,
			NdChooser &chooser,
			Oracle *oracle,
			const AllowableOptimisations &opt,
			StateMachineEvalContext &ctxt)
{
	while (1) {
		StateMachineEdge *e = smallStepEvalStateMachine(rootMachine,
								sm,
								crashes,
								chooser,
								oracle,
								opt,
								ctxt);
		if (!e)
			return;
		if (smallStepEvalStateMachineEdge(rootMachine,
						  e,
						  crashes,
						  chooser,
						  oracle,
						  opt,
						  ctxt))
			return;
		sm = e->target;
	}
}

/* Assume that @sm executes atomically.  Figure out a constraint on
   the initial state which will lead to it not crashing. */
IRExpr *
survivalConstraintIfExecutedAtomically(VexPtr<StateMachine, &ir_heap> &sm,
				       VexPtr<Oracle> &oracle,
				       const AllowableOptimisations &opt,
				       GarbageCollectionToken token)
{
	return writeMachineCrashConstraint(sm,
					   IRExpr_Const(IRConst_U1(1)),
					   IRExpr_Const(IRConst_U1(0)),
					   IRExpr_Const(IRConst_U1(1)),
					   opt);
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
		bigStepEvalStateMachine(sm, sm->root, &crashes, chooser, oracle, opt, ctxt);
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
	bool finished;
	bool crashed;
	threadState state;
	bool skipThisSideEffect;
	CrossEvalState(StateMachine *_rootMachine, StateMachineEdge *_e)
		: rootMachine(_rootMachine),
		  currentEdge(_e),
		  finished(false),
		  crashed(false),
		  skipThisSideEffect(false)
	{}
};

class CrossMachineEvalContext {
	StateMachineSideEffect *advanceToSideEffect(CrossEvalState *machine, NdChooser &chooser, Oracle *oracle,
						    const AllowableOptimisations &opt,
						    std::set<DynAnalysisRip> &usefulRips, bool wantLoad);
public:
	bool collectOrderingConstraints;
	IRExpr *pathConstraint;
	IRExpr *justPathConstraint;
	memLogT memLog;
	CrossEvalState *loadMachine;
	CrossEvalState *storeMachine;
	std::vector<StateMachineSideEffect *> history;
	std::set<DynAnalysisRip> &probeMachineRacingInstructions;
	std::set<DynAnalysisRip> &storeMachineRacingInstructions;
	void advanceMachine(NdChooser &chooser, Oracle *oracle, const AllowableOptimisations &opt, bool doLoad);
	void dumpHistory(FILE *f) const;
	StateMachineSideEffect *advanceToLoad(NdChooser &chooser, Oracle *oracle, const AllowableOptimisations &opt) {
		return advanceToSideEffect(loadMachine, chooser, oracle, opt, probeMachineRacingInstructions, true);
	}
	StateMachineSideEffect *advanceToStore(NdChooser &chooser, Oracle *oracle, const AllowableOptimisations &opt) {
		return advanceToSideEffect(storeMachine, chooser, oracle, opt, storeMachineRacingInstructions, false);
	}
	CrossMachineEvalContext(std::set<DynAnalysisRip> &_probeMachineRacingInstructions,
				std::set<DynAnalysisRip> &_storeMachineRacingInstructions)
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

StateMachineSideEffect *
CrossMachineEvalContext::advanceToSideEffect(CrossEvalState *machine,
					     NdChooser &chooser,
					     Oracle *oracle,
					     const AllowableOptimisations &opt,
					     std::set<DynAnalysisRip> &interestingRips,
					     bool wantLoad)
{
	while (!TIMEOUT) {
		StateMachineSideEffect *se = machine->currentEdge->sideEffect;
		if (se && !machine->skipThisSideEffect) {
			bool acceptable = se->type == StateMachineSideEffect::Store;
			if (wantLoad)
				acceptable |= se->type == StateMachineSideEffect::Load;
			if (acceptable) {
				StateMachineSideEffectMemoryAccess *smea = dynamic_cast<StateMachineSideEffectMemoryAccess *>(se);
				if (smea)
					acceptable &= interestingRips.count(DynAnalysisRip(smea->rip.rip.rip));
			}
			if (acceptable) {
				machine->skipThisSideEffect = true;
				return se;
			}
			if (!evalStateMachineSideEffect(machine->rootMachine, se, chooser, oracle, machine->state, memLog,
							collectOrderingConstraints, opt, &pathConstraint, &justPathConstraint)) {
				/* Found a contradiction -> get out */
				machine->finished = true;
				return NULL;
			}
			history.push_back(se);
		}

		machine->skipThisSideEffect = false;

		StateMachineState *s = machine->currentEdge->target;
		switch (s->type) {
		case StateMachineState::Unreached:
			abort();
		case StateMachineState::Crash:
			machine->finished = true;
			machine->crashed = true;
			return NULL;
		case StateMachineState::NoCrash:
		case StateMachineState::Stub:
			machine->finished = true;
			return NULL;
		case StateMachineState::Proxy: {
			StateMachineProxy *smp = (StateMachineProxy *)s;
			machine->currentEdge = smp->target;
			break;
		}
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
			if (expressionIsTrue(smb->condition, chooser, machine->state, opt, &pathConstraint, &justPathConstraint))
				machine->currentEdge = smb->trueTarget;
			else
				machine->currentEdge = smb->falseTarget;
			break;
		}
		}
	}
	return NULL;
}

void
CrossMachineEvalContext::advanceMachine(NdChooser &chooser,
					Oracle *oracle,
					const AllowableOptimisations &opt,
					bool doLoad)
{
	CrossEvalState *machine = doLoad ? loadMachine : storeMachine;
	StateMachineSideEffect *se;

	if (doLoad)
		se = advanceToLoad(chooser, oracle, opt);
	else
		se = advanceToStore(chooser, oracle, opt);
	if (!se)
		return;

	if (!evalStateMachineSideEffect(machine->rootMachine, se, chooser, oracle, machine->state, memLog,
					collectOrderingConstraints, opt, &pathConstraint, &justPathConstraint)) {
		machine->finished = true;
	} else {
		history.push_back(se);
	}
}

static void
findCrossMachineRacingInstructions(StateMachine *probeMachine,
				   StateMachine *storeMachine,
				   Oracle *oracle,
				   const AllowableOptimisations &opt,
				   std::set<DynAnalysisRip> &probeMachineRacingInstructions,
				   std::set<DynAnalysisRip> &storeMachineRacingInstructions)
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

	std::set<DynAnalysisRip> probeMachineRacingInstructions;
	std::set<DynAnalysisRip> storeMachineRacingInstructions;
	findCrossMachineRacingInstructions(probeMachine, storeMachine, oracle,
					   opt,
					   probeMachineRacingInstructions,
					   storeMachineRacingInstructions);

	AllowableOptimisations loadMachineOpt = opt.setnonLocalLoads(&probeMachineRacingInstructions);
	probeMachine = optimiseStateMachine(probeMachine, loadMachineOpt, oracle,
					    true, true, token);

	VexPtr<StateMachineEdge, &ir_heap> probeEdge(new StateMachineEdge(probeMachine->root));
	VexPtr<StateMachineEdge, &ir_heap> storeEdge(new StateMachineEdge(storeMachine->root));
	while (!*mightCrash || !*mightSurvive) {
		if (TIMEOUT)
			return false;

		LibVEX_maybe_gc(token);

		CrossMachineEvalContext ctxt(probeMachineRacingInstructions, storeMachineRacingInstructions);
		ctxt.pathConstraint = initialStateCondition;
		CrossEvalState s1(probeMachine, probeEdge);
		CrossEvalState s2(storeMachine, storeEdge);
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

struct findRemoteMacroSectionsState {
	int writeEdgeIdx;
	StateMachineEdge *writerEdge;
	StateMachineEvalContext writerContext;
	bool finished;
	bool writer_failed;

	StateMachineSideEffectStore *advanceWriteMachine(StateMachine *writeMachine,
							 NdChooser &chooser,
							 Oracle *oracle,
							 const AllowableOptimisations &opt);
};

StateMachineSideEffectStore *
findRemoteMacroSectionsState::advanceWriteMachine(StateMachine *writeMachine,
						  NdChooser &chooser,
						  Oracle *oracle,
						  const AllowableOptimisations &opt)
{
	/* Have we hit the end of the current writer edge? */
top:
	if (writeEdgeIdx == 1 || !writerEdge->sideEffect) {
		/* Yes, move to the next state. */
		StateMachineState *s = writerEdge->target;
		assert(s->type != StateMachineState::Unreached);
		bool c;
		writerEdge = smallStepEvalStateMachine(writeMachine,
						       s,
						       &c,
						       chooser,
						       oracle,
						       opt,
						       writerContext);
		if (!writerEdge) {
			/* Hit the end of the writer -> we're done. */
			/* Note that we need to evaluate the read
			   machine one last time, so that we can take
			   account of any assumptions made due to any
			   branches after the last side-effect. */
			/* i.e. a store machine branch will change the
			   path constraint, which could cause the read
			   machien to go from crash to non-crash, and
			   we need to make sure that we pick that up
			   as the end of a critical section. */
			/* Example of code where this is important:

			   acquire_lock();
			   x = foo->flag;
			   foo->bar = 5;
			   if (x) {
			        release_lock();
				return;
			   }
			   foo->flag = 0;
			   release_lock();

			   but with the locking taken out.
			*/
			finished = true;
			return NULL;
		}
		writeEdgeIdx = 0;
		goto top;
	}

	/* Advance the writer by one state.  Note that we *don't*
	   consider running the read before any write states, as
	   that's already been handled and is known to lead to
	   no-crash. */
	StateMachineSideEffect *se;
	se = writerEdge->sideEffect;
	assert(se);
	if (!evalStateMachineSideEffect(writeMachine, se, chooser, oracle,
					writerContext.state,
					writerContext.memLog,
					false, opt,
					&writerContext.pathConstraint,
					NULL)) {
		writer_failed = true;
		return NULL;
	}
	writeEdgeIdx++;

	/* Advance to a store */
	StateMachineSideEffectStore *smses = dynamic_cast<StateMachineSideEffectStore *>(se);
	if (!smses)
		goto top;

	return smses;
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

		findRemoteMacroSectionsState state;
		StateMachineSideEffectStore *sectionStart;

		state.writerContext.pathConstraint = assumption;
		state.writerEdge = writeStartEdge;
		state.writeEdgeIdx = 0;
		sectionStart = NULL;
		state.finished = false;
		state.writer_failed = false;

		while (!state.writer_failed && !TIMEOUT && !state.finished) {
			StateMachineSideEffectStore *smses = state.advanceWriteMachine(writeMachine, chooser, oracle, opt);

			/* The writer just issued a store, so we
			   should now try running the reader
			   atomically.  We discard any stores issued
			   by the reader once it's finished, but we
			   need to track them while it's running, so
			   need a fresh eval ctxt and a fresh copy of
			   the stores list every time around the
			   loop. */
			StateMachineEvalContext readEvalCtxt = state.writerContext;
			bool crashes;
			bigStepEvalStateMachine(readMachine, readMachine->root, &crashes, chooser,
						oracle, opt, readEvalCtxt);
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
		if (!state.writer_failed && sectionStart) {
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

		std::set<StateMachineSideEffectStore *> incompleteSections;

		findRemoteMacroSectionsState state;

		state.writerContext.pathConstraint = assumption;
		state.writerEdge = writeStartEdge;
		state.writeEdgeIdx = 0;
		while (!TIMEOUT) {
			StateMachineSideEffectStore *smses = state.advanceWriteMachine(writeMachine, chooser, oracle, opt);

			if (state.writer_failed) {
				/* Contradiction in the writer -> give
				 * up. */
				break;
			}

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
			StateMachineEvalContext readEvalCtxt = state.writerContext;
			bool crashes;
			bigStepEvalStateMachine(probeMachine, probeMachine->root, &crashes, chooser, oracle, opt, readEvalCtxt);
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

	std::set<DynAnalysisRip> probeMachineRacingInstructions;
	std::set<DynAnalysisRip> storeMachineRacingInstructions;
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
		CrossEvalState s1(probeMachine, probeEdge);
		CrossEvalState s2(storeMachine, storeEdge);
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

