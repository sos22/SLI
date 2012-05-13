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

	IRExpr *setTemporary(const threadAndRegister &reg, IRExpr *inp, const AllowableOptimisations &opt);
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
	void set_register(const threadAndRegister &reg, IRExpr *e,
			  IRExpr **assumption,
			  const AllowableOptimisations &opt) {
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
			*assumption = setTemporary(reg, *assumption, opt);

		bump_register_in_assignment_order(reg);
	}
	void eval_phi(StateMachineSideEffectPhi *phi, IRExpr **assumption,
		      const AllowableOptimisations &opt) {
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
							*assumption = setTemporary(phi->reg, *assumption, opt);
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
			*assumption = setTemporary(phi->reg, *assumption, opt);
		bump_register_in_assignment_order(phi->reg);
	}
};

/* Rewrite @e now that we know the value of @reg */
IRExpr *
threadState::setTemporary(const threadAndRegister &reg, IRExpr *e, const AllowableOptimisations &opt)
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
	return simplifyIRExpr(doit.doit(e), opt);
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
	StateMachineState *currentState;

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
		state.set_register(smsel->target, val, assumption, opt);
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec =
			dynamic_cast<StateMachineSideEffectCopy *>(smse);
		assert(smsec);
		state.set_register(smsec->target,
				   specialiseIRExpr(smsec->value, state),
				   assumption,
				   opt);
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
		state.eval_phi(smsep, assumption, opt);
		break;
	}
	}
	return true;
}

/* Walk the state machine and figure out whether it's going to crash.
   If we hit something which we can't solve statically or via the
   oracle, ask the chooser which way we should go, and then emit a
   path constraint saying which way we went.  Stubs are assumed to
   never crash. */
static StateMachineState *
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
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)sm;
		if (!evalStateMachineSideEffect(rootMachine,
						sme->sideEffect,
						chooser,
						oracle,
						ctxt.state,
						ctxt.memLog,
						ctxt.collectOrderingConstraints,
						opt,
						&ctxt.pathConstraint,
						&ctxt.justPathConstraint)) {
			*crashes = false;
			return NULL;
		}
		return sme->target;
	}
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)sm;
		if (expressionIsTrue(smb->condition, chooser, ctxt.state, opt, &ctxt.pathConstraint, &ctxt.justPathConstraint))
			return smb->trueTarget;
		else
			return smb->falseTarget;
	}
	case StateMachineState::NdChoice: {
		StateMachineNdChoice *smnd = (StateMachineNdChoice *)sm;
		if (smnd->successors.size() != 0)
			return chooser.nd_choice(smnd->successors);
		/* Fall through to the Unreached case if we have no
		 * available successors. */
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
			bool *crashes,
			NdChooser &chooser,
			Oracle *oracle,
			const AllowableOptimisations &opt,
			StateMachineEvalContext &ctxt)
{
	while (1) {
		ctxt.currentState =
			smallStepEvalStateMachine(rootMachine,
						  ctxt.currentState,
						  crashes,
						  chooser,
						  oracle,
						  opt,
						  ctxt);
		if (!ctxt.currentState)
			return;
	}
}

struct EvalPathConsumer {
	virtual bool crash(IRExpr *assumption, IRExpr *accAssumption) __attribute__((warn_unused_result)) = 0;
	virtual bool survive(IRExpr *assumption, IRExpr *accAssumption) __attribute__((warn_unused_result)) = 0;
	virtual bool escape(IRExpr *assumption, IRExpr *accAssumption) __attribute__((warn_unused_result)) = 0;
	virtual bool badMachine() __attribute__((warn_unused_result)) {
		abort();
	}
	bool collectOrderingConstraints;
	bool needsAccAssumptions;
	EvalPathConsumer()
		: collectOrderingConstraints(false),
		  needsAccAssumptions(false)
	{}
};

/* Note that this is stack-allocated but live across GCes! */
class EvalContext {
	enum trool {tr_true, tr_false, tr_unknown};
	trool evalBooleanExpression(IRExpr *what, const AllowableOptimisations &opt);
	void evalSideEffect(StateMachine *sm, Oracle *oracle, bool collectOrderingConstraints,
			    std::vector<EvalContext> &pendingStates, StateMachineSideEffect *smse,
			    const AllowableOptimisations &opt);

	VexPtr<IRExpr, &ir_heap> assumption;
	VexPtr<IRExpr, &ir_heap> accumulatedAssumption;
	threadState state;
	memLogT memlog;

	EvalContext(const EvalContext &o, StateMachineState *sms)
		: assumption(o.assumption),
		  accumulatedAssumption(o.accumulatedAssumption),
		  state(o.state),
		  memlog(o.memlog),
		  currentState(sms)
	{}
	/* Create a new context which is like this one, but with an
	   extra assumption. */
	EvalContext(const EvalContext &o, StateMachineState *sms, IRExpr *assume)
		: assumption(o.assumption ? IRExpr_Binop(Iop_And1, o.assumption, assume) : NULL),
		  accumulatedAssumption(o.accumulatedAssumption
					? IRExpr_Binop(Iop_And1, o.accumulatedAssumption, assume)
					: NULL),
		  state(o.state),
		  memlog(o.memlog),
		  currentState(sms)
	{}
	EvalContext(const EvalContext &o, const threadState &_state,
		    const memLogT &_memlog, IRExpr *_assumption,
		    IRExpr *_accAssumption)
		: assumption(_assumption),
		  accumulatedAssumption(_accAssumption),
		  state(_state),
		  memlog(_memlog),
		  currentState(o.currentState)
	{}
public:
	VexPtr<StateMachineState, &ir_heap> currentState;
	bool advance(Oracle *oracle, const AllowableOptimisations &opt,
		     std::vector<EvalContext> &pendingStates,
		     StateMachine *sm,
		     EvalPathConsumer &consumer) __attribute__((warn_unused_result));
	EvalContext(StateMachine *sm, IRExpr *initialAssumption, bool useAccAssumptions)
		: assumption(initialAssumption),
		  accumulatedAssumption(useAccAssumptions ? IRExpr_Const(IRConst_U1(1)) : NULL),
		  currentState(sm->root)
	{}
	EvalContext(const EvalContext &o)
		: assumption(o.assumption),
		  accumulatedAssumption(o.accumulatedAssumption),
		  state(o.state),
		  memlog(o.memlog),
		  currentState(o.currentState)
	{}
};

EvalContext::trool
EvalContext::evalBooleanExpression(IRExpr *what, const AllowableOptimisations &opt)
{
	assert(what->type() == Ity_I1);
	what = simplifyIRExpr(internIRExpr(specialiseIRExpr(what, state)), opt);
	IRExpr *e;
	if (what->tag == Iex_Const) {
		IRExprConst *iec = (IRExprConst *)what;
		if (iec->con->Ico.U1)
			return tr_true;
		else
			return tr_false;
	}

	e = simplifyIRExpr(
		IRExpr_Binop(
			Iop_And1,
			assumption,
			what),
		opt);
	if (e->tag == Iex_Const) {
		IRExprConst *iec = (IRExprConst *)e;
		if (iec->con->Ico.U1) {
			/* We just proved that the assumption is
			 * definitely true. */
			printf("Path assumption reduces to true?\n");
			dbg_break("Path assumption reduces to true?\n");
			assumption = e;
			return tr_true;
		} else {
			return tr_false;
		}
	}

	e = simplifyIRExpr(
		IRExpr_Binop(
			Iop_And1,
			assumption,
			IRExpr_Unop(
				Iop_Not1,
				what)),
		opt);
	if (e->tag == Iex_Const) {
		IRExprConst *iec = (IRExprConst *)e;
		if (iec->con->Ico.U1) {
			/* So X & ~Y is definitely true, where X is
			   our assumption and Y is the thing which
			   we're after.  That tells us that the
			   assumption is definitely true, and
			   therefore useless, and that @what is
			   definitely false. */
			printf("Path assumption is definitely true in way 2?\n");
			dbg_break("Path assumption is definitely true in way 2?\n");
			assumption = e;
			return tr_false;
		} else {
			return tr_true;
		}
	}

	/* Give up on this one and just accept that we don't know. */
	return tr_unknown;
}

void
EvalContext::evalSideEffect(StateMachine *sm, Oracle *oracle, bool collectOrderingConstraints,
			    std::vector<EvalContext> &pendingStates, StateMachineSideEffect *smse,
			    const AllowableOptimisations &opt)
{
	NdChooser chooser;

	do {
		IRExpr *assumption = this->assumption;
		IRExpr *accAssumption = this->accumulatedAssumption;
		threadState state(this->state);
		memLogT memlog(this->memlog);
		if (!evalStateMachineSideEffect(sm, smse, chooser, oracle,
						state, memlog,
						collectOrderingConstraints,
						opt,
						&assumption, &accAssumption)) {
			pendingStates.push_back(
				EvalContext(*this, StateMachineNoCrash::get()));
		} else {
			pendingStates.push_back(
				EvalContext(*this, state, memlog, assumption, accAssumption));
		}
	} while (chooser.advance());
}

/* You might that we could stash things like @oracle, @opt, and @sm in
   the EvalContext itself and not have to pass them around all the
   time.  That'd work, but it'd mean duplicating those pointers in
   every item in the pending state queue, which would make that queue
   much bigger, which'd be kind of annoying. */
bool
EvalContext::advance(Oracle *oracle, const AllowableOptimisations &opt,
		     std::vector<EvalContext> &pendingStates,
		     StateMachine *sm,
		     EvalPathConsumer &consumer)
{
	switch (currentState->type) {
	case StateMachineState::Crash:
		return consumer.crash(assumption, accumulatedAssumption);
	case StateMachineState::NoCrash:
		return consumer.survive(assumption, accumulatedAssumption);
	case StateMachineState::Stub:
		return consumer.escape(assumption, accumulatedAssumption);
	case StateMachineState::Unreached:
		return consumer.badMachine();
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)currentState.get();
		currentState = sme->target;
		if (sme->sideEffect)
			evalSideEffect(sm, oracle, consumer.collectOrderingConstraints,
				       pendingStates, sme->sideEffect, opt);
		return true;
	}
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)currentState.get();
		trool res = evalBooleanExpression(smb->condition, opt);
		switch (res) {
		case tr_true:
			pendingStates.push_back(EvalContext(
							*this,
							smb->trueTarget));
			break;
		case tr_false:
			pendingStates.push_back(EvalContext(
							*this,
							smb->falseTarget));
			break;
		case tr_unknown:
			pendingStates.push_back(EvalContext(
							*this,
							smb->falseTarget,
							IRExpr_Unop(
								Iop_Not1,
								smb->condition)));
			pendingStates.push_back(EvalContext(
							*this,
							smb->trueTarget,
							smb->condition));
			break;
		}
		return true;
	}
	case StateMachineState::NdChoice: {
		StateMachineNdChoice *smnd = (StateMachineNdChoice *)currentState.get();
		if (smnd->successors.size() == 0) {
			return consumer.badMachine();
		} else {
			pendingStates.reserve(pendingStates.size() + smnd->successors.size() - 1);
			for (auto it = smnd->successors.begin();
			     it != smnd->successors.end();
			     it++)
				pendingStates.push_back(EvalContext(*this, *it));
		}
		return true;
	}
	}
	abort();
}

static bool
enumEvalPaths(VexPtr<StateMachine, &ir_heap> &sm,
	      VexPtr<IRExpr, &ir_heap> &assumption,
	      VexPtr<Oracle> &oracle,
	      const AllowableOptimisations &opt,
	      struct EvalPathConsumer &consumer,
	      GarbageCollectionToken &token)
{
	std::vector<EvalContext> pendingStates;

	pendingStates.push_back(EvalContext(sm, assumption, consumer.needsAccAssumptions));

	while (!pendingStates.empty()) {
		if (TIMEOUT)
			return true;

		LibVEX_maybe_gc(token);

		EvalContext ctxt(pendingStates.back());
		pendingStates.pop_back();
		if (!ctxt.advance(oracle, opt, pendingStates, sm, consumer))
			return false;
	}
	return true;
}

/* Assume that @sm executes atomically.  Figure out a constraint on
   the initial state which will lead to it not crashing. */
IRExpr *
survivalConstraintIfExecutedAtomically(VexPtr<StateMachine, &ir_heap> &sm,
				       VexPtr<IRExpr, &ir_heap> &assumption,
				       VexPtr<Oracle> &oracle,
				       const AllowableOptimisations &opt,
				       GarbageCollectionToken token)
{
	__set_profiling(survivalConstraintIfExecutedAtomically);

	struct _ : public EvalPathConsumer {
		VexPtr<IRExpr, &ir_heap> res;
		VexPtr<IRExpr, &ir_heap> &assumption;
		const AllowableOptimisations &opt;
		bool crash(IRExpr *pathConstraint, IRExpr *justPathConstraint) {
			IRExpr *component =
				IRExpr_Unop(
					Iop_Not1,
					justPathConstraint ? justPathConstraint : pathConstraint);
			if (res)
				res = IRExpr_Binop(
					Iop_And1,
					res,
					component);
			else
				res = component;
			res = simplifyIRExpr(res, opt);
			return true;
		}
		bool survive(IRExpr *, IRExpr *) { return true; }
		bool escape(IRExpr *, IRExpr *) { return true; }
		_(VexPtr<IRExpr, &ir_heap> &_assumption,
		  const AllowableOptimisations &_opt)
			: res(NULL), assumption(_assumption), opt(_opt)
		{}
	} consumeEvalPath(assumption, opt);
	if (assumption)
		consumeEvalPath.needsAccAssumptions = true;
	else
		assumption = IRExpr_Const(IRConst_U1(1));
	enumEvalPaths(sm, assumption, oracle, opt, consumeEvalPath, token);

	if (TIMEOUT)
		return NULL;
	else if (consumeEvalPath.res)
		return consumeEvalPath.res;
	else
		return IRExpr_Const(IRConst_U1(1));
}

bool
evalMachineUnderAssumption(VexPtr<StateMachine, &ir_heap> &sm, VexPtr<Oracle> &oracle,
			   VexPtr<IRExpr, &ir_heap> assumption,
			   const AllowableOptimisations &opt,
			   bool *mightSurvive, bool *mightCrash,
			   GarbageCollectionToken token)
{
	__set_profiling(evalMachineUnderAssumption);

	struct : public EvalPathConsumer {
		bool *mightSurvive, *mightCrash;

		bool crash(IRExpr *, IRExpr *) {
			*mightCrash = true;
			if (*mightSurvive)
				return false;
			return true;
		}
		bool survive(IRExpr *, IRExpr *) {
			*mightSurvive = true;
			if (*mightCrash)
				return false;
			return true;
		}
		bool escape(IRExpr *, IRExpr *) {
			return survive(NULL, NULL);
		}
	} consumer;
	consumer.mightSurvive = mightSurvive;
	consumer.mightCrash = mightCrash;

	enumEvalPaths(sm, assumption, oracle, opt, consumer, token);

	if (TIMEOUT)
		return false;

	return true;
}

class CrossEvalState {
public:
	StateMachine *rootMachine;
	StateMachineState *currentState;
	bool finished;
	bool crashed;
	threadState state;
	CrossEvalState(StateMachine *_rootMachine)
		: rootMachine(_rootMachine),
		  currentState(_rootMachine->root),
		  finished(false),
		  crashed(false)
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
		StateMachineState *s = machine->currentState;
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
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
			if (expressionIsTrue(smb->condition, chooser, machine->state, opt, &pathConstraint, &justPathConstraint))
				machine->currentState = smb->trueTarget;
			else
				machine->currentState = smb->falseTarget;
			break;
		}
		case StateMachineState::NdChoice: {
			StateMachineNdChoice *smnd = (StateMachineNdChoice *)s;
			machine->currentState = chooser.nd_choice(smnd->successors);
			break;
		}
		case StateMachineState::SideEffecting: {
			StateMachineSideEffecting *smse = (StateMachineSideEffecting *)s;
			if (smse->sideEffect) {
				StateMachineSideEffect *se = smse->sideEffect;
				bool acceptable = se->type == StateMachineSideEffect::Store;
				if (wantLoad)
					acceptable |= se->type == StateMachineSideEffect::Load;
				if (acceptable) {
					StateMachineSideEffectMemoryAccess *smea = dynamic_cast<StateMachineSideEffectMemoryAccess *>(se);
					if (smea)
						acceptable &= interestingRips.count(DynAnalysisRip(smea->rip.rip.rip));
				}
				if (acceptable) {
					machine->currentState = smse->target;
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
			machine->currentState = smse->target;
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
	probeMachine = duplicateStateMachine(probeMachine);
	probeMachine = optimiseStateMachine(probeMachine, loadMachineOpt, oracle,
					    true, true, token);

	while (!*mightCrash || !*mightSurvive) {
		if (TIMEOUT)
			return false;

		LibVEX_maybe_gc(token);

		CrossMachineEvalContext ctxt(probeMachineRacingInstructions, storeMachineRacingInstructions);
		ctxt.pathConstraint = initialStateCondition;
		CrossEvalState s1(probeMachine);
		CrossEvalState s2(storeMachine);
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
	bool skipFirstSideEffect;
	StateMachineState *writerState;
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
	StateMachineSideEffectStore *smses = NULL;

	while (!TIMEOUT && !smses) {
		StateMachineState *s = writerState;
		switch (s->type) {
		case StateMachineState::Unreached:
			abort();
		case StateMachineState::Crash:
			writer_failed = true;
			return NULL;
		case StateMachineState::NoCrash:
		case StateMachineState::Stub:
			finished = true;
			return NULL;
		case StateMachineState::Bifurcate: {
			StateMachineBifurcate *smb = (StateMachineBifurcate *)s;
			if (expressionIsTrue(smb->condition, chooser, writerContext.state, opt,
					     &writerContext.pathConstraint, &writerContext.justPathConstraint))
				writerState = smb->trueTarget;
			else
				writerState = smb->falseTarget;
			break;
		}
		case StateMachineState::NdChoice: {
			StateMachineNdChoice *smnd = (StateMachineNdChoice *)s;
			writerState = chooser.nd_choice(smnd->successors);
			break;
		}
		case StateMachineState::SideEffecting: {
			StateMachineSideEffecting *smse = (StateMachineSideEffecting *)s;
			StateMachineSideEffect *se = smse->sideEffect;
			if (se) {
				if (se->type == StateMachineSideEffect::Store)
					smses = (StateMachineSideEffectStore *)se;
				if (!evalStateMachineSideEffect(writeMachine, se, chooser, oracle, writerContext.state,
								writerContext.memLog,
								writerContext.collectOrderingConstraints, opt,
								&writerContext.pathConstraint,
								&writerContext.justPathConstraint)) {
					/* Found a contradiction -> get out */
					writer_failed = true;
					return NULL;
				}
			}
			writerState = smse->target;
		}
		}
	}
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

	do {
		if (TIMEOUT)
			return false;

		LibVEX_maybe_gc(token);

		findRemoteMacroSectionsState state;
		StateMachineSideEffectStore *sectionStart;

		state.writerContext.pathConstraint = assumption;
		state.writerState = writeMachine->root;
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
			readEvalCtxt.currentState = readMachine->root;
			bool crashes;
			bigStepEvalStateMachine(readMachine, &crashes, chooser,
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

	do {
		if (TIMEOUT)
			return false;

		LibVEX_maybe_gc(token);

		std::set<StateMachineSideEffectStore *> incompleteSections;

		findRemoteMacroSectionsState state;

		state.writerContext.pathConstraint = assumption;
		state.writerState = writeMachine->root;
		state.skipFirstSideEffect = false;
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
			readEvalCtxt.currentState = probeMachine->root;
			bool crashes;
			bigStepEvalStateMachine(probeMachine, &crashes, chooser, oracle, opt, readEvalCtxt);
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

	while (1) {
		if (TIMEOUT)
			return;

		LibVEX_maybe_gc(token);

		CrossMachineEvalContext ctxt(probeMachineRacingInstructions,
					     storeMachineRacingInstructions);
		ctxt.collectOrderingConstraints = true;
		ctxt.pathConstraint = initialStateCondition;
		ctxt.justPathConstraint = IRExpr_Const(IRConst_U1(1));
		CrossEvalState s1(probeMachine);
		CrossEvalState s2(storeMachine);
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

/* Transform @machine so that wherever it would previously branch to
   StateMachineCrash it will now branch to the root of @to.  If @from
   is a store state then this effectively concatenates the two
   machines together.  We duplicate both machines in the process. */
static StateMachine *
concatenateStateMachines(const StateMachine *machine, const StateMachine *to)
{
	std::map<const StateMachineState *, StateMachineState *> rewriteRules;

	to = duplicateStateMachine(to);

	/* This is moderately tricky: setting rules for all of the
	   terminal states, even no-op rules, forces rewriteMachine()
	   to duplicate every state, because it duplicates any state
	   which can ultimately reach a state which it has a rule for. */
	rewriteRules[StateMachineCrash::get()] = to->root;
	rewriteRules[StateMachineNoCrash::get()] = StateMachineNoCrash::get();
	rewriteRules[StateMachineUnreached::get()] = StateMachineUnreached::get();

	StateMachineTransformer::rewriteMachine(machine, rewriteRules);
	assert(rewriteRules.count(machine->root));
#ifndef NDEBUG
	std::map<unsigned, VexRip> newOrigin;
	for (auto it = machine->origin.begin();
	     it != machine->origin.end();
	     it++) {
		assert(!newOrigin.count(it->first));
		newOrigin.insert(*it);
	}
	for (auto it = to->origin.begin();
	     it != to->origin.end();
	     it++) {
		assert(!newOrigin.count(it->first));
		newOrigin.insert(*it);
	}
	std::vector<std::pair<unsigned, VexRip> > neworigin(newOrigin.begin(), newOrigin.end());
#else
#error write me
#endif
	return new StateMachine(rewriteRules[machine->root],
				neworigin,
				machine->freeVariables);
}

IRExpr *
writeMachineSuitabilityConstraint(VexPtr<StateMachine, &ir_heap> &writeMachine,
				  VexPtr<StateMachine, &ir_heap> &readMachine,
				  VexPtr<Oracle> &oracle,
				  VexPtr<IRExpr, &ir_heap> &assumption,
				  const AllowableOptimisations &opt,
				  GarbageCollectionToken token)
{
	__set_profiling(writeMachineSuitabilityConstraint);

	VexPtr<StateMachine, &ir_heap> combinedMachine;

	combinedMachine = concatenateStateMachines(
		writeMachine,
		readMachine);
	combinedMachine = optimiseStateMachine(combinedMachine,
					       opt
					          .enableassumeExecutesAtomically()
					          .enableignoreSideEffects()
					          .enableassumeNoInterferingStores()
					          .enablenoExtend(),
					       oracle,
					       true,
					       true,
					       token);
	return survivalConstraintIfExecutedAtomically(
		combinedMachine,
		assumption,
		oracle,
		opt,
		token);
}
