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
#include "allowable_optimisations.hpp"
#include "sat_checker.hpp"
#include "alloc_mai.hpp"

#ifdef NDEBUG
#define debug_dump_state_traces false
#define debug_dump_crash_reasons false
#define debug_survival_constraint false
#else
static bool debug_dump_state_traces = false;
static bool debug_dump_crash_reasons = false;
static bool debug_survival_constraint = false;
#endif

/* All of the state needed to evaluate a single pure IRExpr. */
/* Note that this is not GCed, but contains bare pointers to GCed
   objects, so needs to be manually visited if live across GC
   points. */
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
		void visit(HeapVisitor &hv) {
			hv(val8);
			hv(val16);
			hv(val32);
			hv(val64);
		}
	};

	/* The values of all of the registers */
	std::map<threadAndRegister, register_val> registers;
	/* The order in which registers have been assigned to.  This
	   makes implementing Phi nodes much easier.  Each register
	   appears at most once in here. */
	std::vector<threadAndRegister> assignmentOrder;

	void bump_register_in_assignment_order(const threadAndRegister &reg) {
		for (auto it = assignmentOrder.begin();
		     it != assignmentOrder.end();
		     it++) {
			if (*it == reg) {
				assignmentOrder.erase(it);
				break;
			}
		}
		assignmentOrder.push_back(reg);
	}

	IRExpr *setTemporary(const threadAndRegister &reg, IRExpr *inp, const IRExprOptimisations &opt);
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
				IRExpr *mask = IRExpr_Const_U16(0xff00);
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
							IRExpr_Const_U32(mask)));
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
						IRExpr_Const_U32(mask)));
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
							IRExpr_Const_U64(mask)));
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
							IRExpr_Const_U64(mask)));
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
							IRExpr_Const_U64(mask)));
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
							IRExpr_Const_U64(mask)));
				
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
			  const IRExprOptimisations &opt) {
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
		case Ity_I128:
			/* Bit of a hack.  We only have 64 bit
			   registers, so if we have to store a 128 bit
			   value we just truncate it down. */
			set_register(reg, IRExpr_Unop(Iop_128to64, e), assumption, opt);
			return;
		default:
			abort();
		}

		if (reg.isTemp())
			*assumption = setTemporary(reg, *assumption, opt);

		bump_register_in_assignment_order(reg);
	}
	void eval_phi(StateMachineSideEffectPhi *phi, IRExpr **assumption,
		      const IRExprOptimisations &opt) {
		for (auto it = assignmentOrder.rbegin();
		     it != assignmentOrder.rend();
		     it++) {
			for (auto it2 = phi->generations.begin();
			     it2 != phi->generations.end();
			     it2++) {
				if (it2->reg == *it) {
					registers[phi->reg] = registers[*it];
					if (phi->reg.isTemp())
						*assumption = setTemporary(phi->reg, *assumption, opt);
					bump_register_in_assignment_order(phi->reg);
					return;
				}
			}
		}
		/* We haven't yet assigned to any registers in the
		   input set of the Phi, so we're going to pick up the
		   initial value of the super-register. */
		threadAndRegister genM1(threadAndRegister::invalid());
		for (auto it = phi->generations.begin();
		     genM1.isInvalid() && it != phi->generations.end();
		     it++)
			if (it->reg.gen() == (unsigned)-1)
				genM1 = it->reg;
		assert(genM1.isValid());

		/* Pick up initial value */
		set_register(phi->reg, IRExpr_Get(genM1, Ity_I64), assumption, opt);
	}

	IRExpr *specialiseIRExpr(IRExpr *iex);
	void visit(HeapVisitor &hv) {
		for (auto it = registers.begin();
		     it != registers.end();
		     it++) {
			it->second.visit(hv);
		}
	}
};

/* Rewrite @e now that we know the value of @reg */
IRExpr *
threadState::setTemporary(const threadAndRegister &reg, IRExpr *e, const IRExprOptimisations &opt)
{
	struct _ : public IRExprTransformer {
		const threadAndRegister &reg;
		threadState *_this;
		_(const threadAndRegister &_reg, threadState *__this)
			: reg(_reg), _this(__this)
		{}
		IRExpr *transformIex(IRExprGet *ieg) {
			if (ieg->reg == reg)
				return _this->register_value(reg, ieg->ty);
			else
				return IRExprTransformer::transformIex(ieg);
		}
	} doit(reg, this);
	return simplifyIRExpr(doit.doit(e), opt);
}

IRExpr *
threadState::specialiseIRExpr(IRExpr *iex)
{
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
	SpecialiseIRExpr s(*this);
	return s.doit(iex);
}

class memLogT : public std::vector<std::pair<StateMachine *, StateMachineSideEffectStore *> > {
public:
	void visit(HeapVisitor &hv) {
		for (auto it = begin(); it != end(); it++) {
			hv(it->first);
			hv(it->second);
		}
	}
};

struct EvalPathConsumer {
	virtual void crash(IRExpr *assumption, IRExpr *accAssumption) = 0;
	virtual void survive(IRExpr *assumption, IRExpr *accAssumption) = 0;
	virtual void escape(IRExpr *assumption, IRExpr *accAssumption) = 0;
	virtual void badMachine() {
		abort();
	}
	bool needsAccAssumptions;
	bool noImplicitBadPtrs;
	bool aborted;
	EvalPathConsumer()
		: needsAccAssumptions(false),
		  noImplicitBadPtrs(false),
		  aborted(false)
	{}
};

class EvalContext : public GcCallback<&ir_heap> {
	enum trool { tr_true, tr_false, tr_unknown };
	IRExpr *assumption;
public:
	IRExpr *accumulatedAssumption;
private:
	threadState state;
	memLogT memlog;
public:
	bool atomic;
	StateMachineState *currentState;
private:
#ifndef NDEBUG
	std::vector<int> statePath;
	std::map<const StateMachineState *, int> stateLabels;
#endif

	void runGc(HeapVisitor &hv) {
		hv(assumption);
		hv(accumulatedAssumption);
		state.visit(hv);
		memlog.visit(hv);
		hv(currentState);
#ifndef NDEBUG
		std::vector<std::pair<const StateMachineState *, int> > vectStateLabels(stateLabels.begin(), stateLabels.end());
		for (auto it = vectStateLabels.begin();
		     it != vectStateLabels.end();
		     it++)
			hv(it->first);
		stateLabels.clear();
		stateLabels.insert(vectStateLabels.begin(), vectStateLabels.end());
#endif
	}

	trool evalBooleanExpression(IRExpr *what, const IRExprOptimisations &opt);
	void evalSideEffect(const MaiMap &decode, StateMachine *sm, OracleInterface *oracle,
			    EvalPathConsumer &consumer, std::vector<EvalContext> &pendingStates,
			    StateMachineSideEffect *smse, const IRExprOptimisations &opt);

	void advance_state_trace()
	{
#ifndef NDEBUG
		if (!debug_dump_state_traces)
			return;
		assert(stateLabels.count(currentState));
		assert(stateLabels[currentState] != 0);
		statePath.push_back(stateLabels[currentState]);
#endif
	}
	EvalContext(const EvalContext &o, StateMachineState *sms)
		: assumption(o.assumption),
		  accumulatedAssumption(o.accumulatedAssumption),
		  state(o.state),
		  memlog(o.memlog),
		  atomic(o.atomic),
		  currentState(sms)
#ifndef NDEBUG
		, statePath(o.statePath)
		, stateLabels(o.stateLabels)
#endif
	{
		advance_state_trace();
	}
	/* Create a new context which is like this one, but with an
	   extra assumption. */
	EvalContext(const EvalContext &o, StateMachineState *sms, IRExpr *assume,
		    const IRExprOptimisations &opt)
		: assumption(o.assumption ? IRExpr_Binop(Iop_And1, o.assumption, assume) : assume),
		  accumulatedAssumption(o.accumulatedAssumption
					? IRExpr_Binop(Iop_And1, o.accumulatedAssumption, assume)
					: NULL),
		  state(o.state),
		  memlog(o.memlog),
		  atomic(o.atomic),
		  currentState(sms)
#ifndef NDEBUG
		, statePath(o.statePath)
		, stateLabels(o.stateLabels)
#endif
	{
		if (assumption)
			assumption = simplifyIRExpr(assumption, opt);
		if (accumulatedAssumption)
			accumulatedAssumption = simplifyIRExpr(accumulatedAssumption, opt);
		advance_state_trace();
	}
	enum evalStateMachineSideEffectRes {
		esme_normal,
		esme_escape,
		esme_ignore_path
	};
	evalStateMachineSideEffectRes evalStateMachineSideEffect(
		const MaiMap &decode,
		StateMachine *thisMachine,
		StateMachineSideEffect *smse,
		bool noImplicitBadPtrs,
		NdChooser &chooser,
		OracleInterface *oracle,
		const IRExprOptimisations &opt);
	bool expressionIsTrue(IRExpr *exp, bool addToAccConstraint, NdChooser &chooser, const IRExprOptimisations &opt);
	bool evalExpressionsEqual(IRExpr *exp1, IRExpr *exp2, bool addToAccConstraint, NdChooser &chooser, const IRExprOptimisations &opt);
public:
	void advance(const MaiMap &decode,
		     OracleInterface *oracle,
		     const IRExprOptimisations &opt,
		     std::vector<EvalContext> &pendingStates,
		     StateMachine *sm,
		     EvalPathConsumer &consumer);
	EvalContext(StateMachine *sm, IRExpr *initialAssumption, bool useAccAssumptions,
		    std::map<const StateMachineState*, int> &
#ifndef NDEBUG
		    _stateLabels
#endif
		)
		: assumption(initialAssumption),
		  accumulatedAssumption(useAccAssumptions ? IRExpr_Const_U1(true) : NULL),
		  atomic(false),
		  currentState(sm->root)
#ifndef NDEBUG
		, stateLabels(_stateLabels)
#endif
	{
		advance_state_trace();
	}
};

bool
EvalContext::expressionIsTrue(IRExpr *exp, bool addToAccConstraint, NdChooser &chooser, const IRExprOptimisations &opt)
{
	if (TIMEOUT)
		return true;

	exp = simplifyIRExpr(internIRExpr(state.specialiseIRExpr(exp)), opt);

	/* Combine the path constraint with the new expression and see
	   if that produces a contradiction.  If it does then we know
	   for sure that the new expression is false. */
	IRExpr *e =
		simplifyIRExpr(
			IRExpr_Binop(
				Iop_And1,
				assumption,
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
		if (((IRExprConst *)e)->Ico.U1) {
			assumption = e;
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
				assumption,
				IRExpr_Unop(
					Iop_Not1,
					exp)),
			opt);
	if (e2->tag == Iex_Const) {
		/* If X & ¬Y is definitely true, Y is definitely
		 * false and X is definitely true. */
		if (((IRExprConst *)e2)->Ico.U1) {
			assumption = IRExpr_Const_U1(true);
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
		assumption = e;
		if (addToAccConstraint && accumulatedAssumption)
			accumulatedAssumption =
				simplifyIRExpr(
					IRExpr_Binop(
						Iop_And1,
						accumulatedAssumption,
						exp),
					opt);
		return true;
	} else {
		assumption = e2;
		if (addToAccConstraint && accumulatedAssumption)
			accumulatedAssumption =
				simplifyIRExpr(
					IRExpr_Binop(
						Iop_And1,
						accumulatedAssumption,
						IRExpr_Unop(
							Iop_Not1,
							exp)),
					opt);
		return false;
	}
}

bool
EvalContext::evalExpressionsEqual(IRExpr *exp1, IRExpr *exp2, bool addToAccConstraint, NdChooser &chooser, const IRExprOptimisations &opt)
{
	return expressionIsTrue(IRExpr_Binop(
					Iop_CmpEQ64,
					exp1,
					exp2),
				addToAccConstraint,
				chooser,
				opt);
}

EvalContext::evalStateMachineSideEffectRes
EvalContext::evalStateMachineSideEffect(const MaiMap &decode,
					StateMachine *thisMachine,
					StateMachineSideEffect *smse,
					bool noImplicitBadPtrs,
					NdChooser &chooser,
					OracleInterface *oracle,
					const IRExprOptimisations &opt)
{
	IRExpr *addr = NULL;
	if (smse->type == StateMachineSideEffect::Load ||
	    smse->type == StateMachineSideEffect::Store) {
		StateMachineSideEffectMemoryAccess *smsema =
			dynamic_cast<StateMachineSideEffectMemoryAccess *>(smse);
		assert(smsema);
		addr = state.specialiseIRExpr(smsema->addr);
		if (expressionIsTrue(IRExpr_Unop(Iop_BadPtr, addr), !noImplicitBadPtrs, chooser, opt))
			return esme_escape;
	}

	switch (smse->type) {
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectStore *smses =
			dynamic_cast<StateMachineSideEffectStore *>(smse);
		assert(smses);
		assert(addr);
		memlog.push_back(
			std::pair<StateMachine *, StateMachineSideEffectStore *>
			(thisMachine,
			 new StateMachineSideEffectStore(
				 smses,
				 state.specialiseIRExpr(addr),
				 state.specialiseIRExpr(smses->data))));
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
		for (memLogT::reverse_iterator it = memlog.rbegin();
		     it != memlog.rend();
		     it++) {
			StateMachineSideEffectStore *smses = it->second;
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

			if (!oracle->memoryAccessesMightAlias(decode, opt, smsel, smses))
				continue;
			if (evalExpressionsEqual(smses->addr, addr, true, chooser, opt)) {
				satisfier = smses;
				satisfierMachine = it->first;
				break;
			}
		}
		IRExpr *val;
		if (satisfier) {
			val = coerceTypes(smsel->type, satisfier->data);
		} else {
			val = IRExpr_Load(smsel->type, addr);
		}
		state.set_register(smsel->target, val, &assumption, opt);
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec =
			dynamic_cast<StateMachineSideEffectCopy *>(smse);
		assert(smsec);
		state.set_register(smsec->target,
				   state.specialiseIRExpr(smsec->value),
				   &assumption,
				   opt);
		break;
	}
	case StateMachineSideEffect::Unreached:
		abort();
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(smse);
		if (expressionIsTrue(
			    smseaf->value,
			    true,
			    chooser, opt)) {
			if (smseaf->reflectsActualProgram)
				return esme_escape;
			else
				return esme_ignore_path;
		}
		break;
	}
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *smsep =
			(StateMachineSideEffectPhi *)(smse);
		state.eval_phi(smsep, &assumption, opt);
		break;
	}
	case StateMachineSideEffect::StartAtomic:
		assert(!atomic);
		atomic = true;
		break;
	case StateMachineSideEffect::EndAtomic:
		assert(atomic);
		atomic = false;
		break;
	case StateMachineSideEffect::StartFunction:
	case StateMachineSideEffect::EndFunction:

	case StateMachineSideEffect::PointerAliasing: {
		StateMachineSideEffectPointerAliasing *p =
			(StateMachineSideEffectPointerAliasing *)smse;
		/* The only use we make of a PointerAliasing side
		   effect is to say that things which aliasing says
		   are definitely valid pointers really are definitely
		   valid pointers.  Todo: could do much better
		   here. */
		if (!p->set.mightBeNonPointer() &&
		    expressionIsTrue(
			    IRExpr_Unop(
				    Iop_BadPtr,
				    IRExpr_Get(p->reg, Ity_I64)),
			    true,
			    chooser,
			    opt)) {
			return esme_escape;
		}
		break;
	}

		/* Todo: could maybe use this to improve aliasing. */
	case StateMachineSideEffect::StackLayout:
		break;
	}
	return esme_normal;
}

EvalContext::trool
EvalContext::evalBooleanExpression(IRExpr *what, const IRExprOptimisations &opt)
{
	assert(what->type() == Ity_I1);
	IRExpr *e;
	if (what->tag == Iex_Const) {
		IRExprConst *iec = (IRExprConst *)what;
		if (iec->Ico.U1)
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
		if (iec->Ico.U1) {
			/* We just proved that the assumption is
			 * definitely true. */
			warning("Path assumption reduces to true?\n");
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
		if (iec->Ico.U1) {
			/* So X & ~Y is definitely true, where X is
			   our assumption and Y is the thing which
			   we're after.  That tells us that the
			   assumption is definitely true, and
			   therefore useless, and that @what is
			   definitely false. */
			warning("Path assumption is definitely true in way 2?\n");
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
EvalContext::evalSideEffect(const MaiMap &decode, StateMachine *sm, OracleInterface *oracle,
			    EvalPathConsumer &consumer, std::vector<EvalContext> &pendingStates,
			    StateMachineSideEffect *smse, const IRExprOptimisations &opt)
{
	NdChooser chooser;

	do {
		EvalContext newContext(*this);
		evalStateMachineSideEffectRes res =
			newContext.evalStateMachineSideEffect(decode,
							      sm,
							      smse,
							      consumer.noImplicitBadPtrs,
							      chooser,
							      oracle,
							      opt);
		switch (res) {
		case esme_normal:
			pendingStates.push_back(newContext);
			break;
		case esme_ignore_path:
			break;
		case esme_escape:
			consumer.escape(newContext.assumption, newContext.accumulatedAssumption);
			break;
		}
	} while (chooser.advance());
}

/* You might that we could stash things like @oracle, @opt, and @sm in
   the EvalContext itself and not have to pass them around all the
   time.  That'd work, but it'd mean duplicating those pointers in
   every item in the pending state queue, which would make that queue
   much bigger, which'd be kind of annoying. */
void
EvalContext::advance(const MaiMap &decode,
		     OracleInterface *oracle,
		     const IRExprOptimisations &opt,
		     std::vector<EvalContext> &pendingStates,
		     StateMachine *sm,
		     EvalPathConsumer &consumer)
{
	if (debug_dump_state_traces && currentState->type == StateMachineState::Terminal) {
#ifndef NDEBUG
		assert(stateLabels.count(currentState));
		printf("Reached state %d, trace: ", stateLabels[currentState]);
		for (auto it = statePath.begin(); it != statePath.end(); it++) {
			if (it != statePath.begin())
				printf(", ");
			printf("%d", *it);
		}
		printf("; assumption ");
		ppIRExpr(assumption, stdout);
		printf("\n");
#endif
	}
	switch (currentState->type) {
	case StateMachineState::Terminal: {
		auto smt = (StateMachineTerminal *)currentState;
		switch (smt->res) {
		case smr_crash:
			if (debug_dump_crash_reasons) {
				printf("Found a crash, assumption ");
				ppIRExpr(assumption, stdout);
				if (accumulatedAssumption) {
					printf(", accumulated assumption ");
					ppIRExpr(accumulatedAssumption, stdout);
				}
				printf("\n");
			}
			consumer.crash(assumption, accumulatedAssumption);
			return;
		case smr_survive:
			consumer.survive(assumption, accumulatedAssumption);
			return;
		case smr_unreached:
			consumer.badMachine();
			return;
		}
		abort();
	}
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)currentState;
		currentState = sme->target;
		advance_state_trace();
		if (sme->sideEffect) {
			evalSideEffect(decode, sm, oracle, consumer, pendingStates,
				       sme->sideEffect, opt);
		} else {
			pendingStates.push_back(*this);
		}
		return;
	}
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)currentState;
		IRExpr *cond =
			simplifyIRExpr(
				internIRExpr(
					state.specialiseIRExpr(smb->condition)),
				opt);
		trool res = evalBooleanExpression(cond, opt);
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
								cond),
							opt));
			pendingStates.push_back(EvalContext(
							*this,
							smb->trueTarget,
							cond,
							opt));
			break;
		}
		return;
	}
	}
	abort();
}

static void
enumEvalPaths(const VexPtr<MaiMap, &ir_heap> &decode,
	      const VexPtr<StateMachine, &ir_heap> &sm,
	      const VexPtr<IRExpr, &ir_heap> &assumption,
	      const VexPtr<OracleInterface> &oracle,
	      const IRExprOptimisations &opt,
	      struct EvalPathConsumer &consumer,
	      GarbageCollectionToken &token,
	      bool loud = false)
{
	std::vector<EvalContext> pendingStates;
	std::map<const StateMachineState *, int> stateLabels;
	int cntr = 0;

	if (debug_dump_state_traces) {
		printf("Eval machine:\n");
		printStateMachine(sm, stdout, stateLabels);
		printf("Under assumption ");
		ppIRExpr(assumption, stdout);
		printf("\n");
	}

	pendingStates.push_back(EvalContext(sm, assumption, consumer.needsAccAssumptions, stateLabels));

	while (!TIMEOUT && !consumer.aborted && !pendingStates.empty()) {
		LibVEX_maybe_gc(token);

		EvalContext ctxt(pendingStates.back());
		pendingStates.pop_back();
		ctxt.advance(*decode, oracle, opt, pendingStates, sm, consumer);
		if (loud && cntr++ % 100 == 0)
			printf("Processed %d states; %zd in queue\n", cntr, pendingStates.size());
	}
}

static IRExpr *
_survivalConstraintIfExecutedAtomically(const VexPtr<MaiMap, &ir_heap> &mai,
					const VexPtr<StateMachine, &ir_heap> &sm,
					VexPtr<IRExpr, &ir_heap> assumption,
					const VexPtr<OracleInterface> &oracle,
					bool escapingStatesSurvive,
					bool wantCrash,
					const IRExprOptimisations &opt,
					GarbageCollectionToken token)
{
	__set_profiling(survivalConstraintIfExecutedAtomically);

	if (debug_survival_constraint) {
		printf("%s(sm = ..., assumption = %s, escapingStatesSurvive = %s, wantCrash = %s, opt = %s)\n",
		       __func__,
		       assumption ? nameIRExpr(assumption) : "<null>",
		       escapingStatesSurvive ? "true" : "false",
		       wantCrash ? "true" : "false",
		       opt.name());
		printStateMachine(sm, stdout);
	}

	struct _ : public EvalPathConsumer {
		VexPtr<IRExpr, &ir_heap> res;
		const IRExprOptimisations &opt;
		bool escapingStatesSurvive;
		bool wantCrash;
		void addComponent(const char *label, IRExpr *pathConstraint, IRExpr *justPathConstraint) {
#warning Think hard about what we're doing here.  Should we constraint it to never reach a crashing node, or merely to always reach a surviving one?'
#warning Makes a difference due to incompleteness of simplifier and also presence of ND choice states.
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
			if (debug_survival_constraint)
				printf("%s: add %s, got %s\n",
				       label,
				       nameIRExpr(component),
				       nameIRExpr(res));
		}
		void crash(IRExpr *pathConstraint, IRExpr *justPathConstraint) {
			if (!wantCrash)
				addComponent("crash", pathConstraint, justPathConstraint);
		}
		void survive(IRExpr *pathConstraint, IRExpr *justPathConstraint) {
			if (wantCrash)
				addComponent("survive", pathConstraint, justPathConstraint);
		}
		void escape(IRExpr *pathConstraint, IRExpr *justPathConstraint) {
			if (escapingStatesSurvive && wantCrash)
				addComponent("escape", pathConstraint, justPathConstraint);
			else if (!escapingStatesSurvive && !wantCrash)
				addComponent("escape", pathConstraint, justPathConstraint);
		}
		_(const VexPtr<IRExpr, &ir_heap> &_assumption,
		  const IRExprOptimisations &_opt,
		  bool _escapingStatesSurvive,
		  bool _wantCrash)
			: res(_assumption), opt(_opt), escapingStatesSurvive(_escapingStatesSurvive),
			  wantCrash(_wantCrash)
		{}
	} consumeEvalPath(assumption, opt, escapingStatesSurvive, wantCrash);
	if (assumption)
		consumeEvalPath.needsAccAssumptions = true;
	else
		assumption = IRExpr_Const_U1(true);
	enumEvalPaths(mai, sm, assumption, oracle, opt, consumeEvalPath, token);

	if (debug_survival_constraint)
		printf("%s: result %s\n", __func__,
		       consumeEvalPath.res ? nameIRExpr(consumeEvalPath.res) : "const(1)");
	
	if (TIMEOUT)
		return NULL;
	else if (consumeEvalPath.res) {
		IRExpr *res = simplifyIRExpr(simplify_via_anf(consumeEvalPath.res), opt);
		if (debug_survival_constraint)
			printf("%s: after optimisation, result %s\n",
			       __func__, nameIRExpr(res));
		return res;
	} else
		return IRExpr_Const_U1(true);
}

/* Assume that @sm executes atomically.  Figure out a constraint on
   the initial state which will lead to it not crashing. */
IRExpr *
survivalConstraintIfExecutedAtomically(const VexPtr<MaiMap, &ir_heap> &mai,
				       const VexPtr<StateMachine, &ir_heap> &sm,
				       const VexPtr<IRExpr, &ir_heap> &assumption,
				       const VexPtr<OracleInterface> &oracle,
				       bool escapingStatesSurvive,
				       const IRExprOptimisations &opt,
				       GarbageCollectionToken token)
{
	return _survivalConstraintIfExecutedAtomically(
		mai,
		sm,
		assumption,
		oracle,
		escapingStatesSurvive,
		false,
		opt,
		token);
}

/* Assume that @sm executes atomically.  Figure out a constraint on
   the initial state which will lead to it not surviving. */
IRExpr *
crashingConstraintIfExecutedAtomically(const VexPtr<MaiMap, &ir_heap> &mai,
				       const VexPtr<StateMachine, &ir_heap> &sm,
				       const VexPtr<IRExpr, &ir_heap> &assumption,
				       const VexPtr<OracleInterface> &oracle,
				       bool escapingStatesSurvive,
				       const IRExprOptimisations &opt,
				       GarbageCollectionToken token)
{
	return _survivalConstraintIfExecutedAtomically(
		mai,
		sm,
		assumption,
		oracle,
		escapingStatesSurvive,
		true,
		opt,
		token);
}

static StateMachineState *
shallowCloneState(StateMachineState *s)
{
	switch (s->type) {
	case StateMachineState::Terminal:
		return s;
	case StateMachineState::Bifurcate:
		return new StateMachineBifurcate(*(StateMachineBifurcate *)s);
	case StateMachineState::SideEffecting:
		return new StateMachineSideEffecting(*(StateMachineSideEffecting *)s);
	}
	abort();
}

/* A state in a cross machine.  p is the state of the probe
   machine and s the state of the store machine.  We also
   track whether the probe machine has issued a load and the
   store machine a store, because that allows us to optimise
   when we consider context switches slightly. */
struct crossStateT {
	StateMachineState *p;
	StateMachineState *s;
	bool store_issued_store;
	bool probe_issued_access;
	bool probe_is_atomic;
	bool store_is_atomic;
	crossStateT(StateMachineState *_p,
		    StateMachineState *_s,
		    bool _sis,
		    bool _pi_acc,
		    bool _pia,
		    bool _sia)
		: p(_p),
		  s(_s),
		  store_issued_store(_sis),
		  probe_issued_access(_pi_acc),
		  probe_is_atomic(_pia),
		  store_is_atomic(_sia)
	{}
	bool operator<(const crossStateT &o) const {
#define do_field(n)				\
		if (n < o.n)			\
			return true;		\
		if (n > o.n)			\
			return false
		do_field(p);
		do_field(s);
		do_field(store_issued_store);
		do_field(probe_issued_access);
		do_field(probe_is_atomic);
		do_field(store_is_atomic);
#undef do_field
		return false;
	}
};

static bool
definitelyDoesntRace(const MaiMap &decode,
		     StateMachineSideEffect *probeEffect,
		     StateMachineState *storeMachine,
		     const IRExprOptimisations &opt,
		     bool allowStoreLoadRaces,
		     OracleInterface *oracle,
		     std::set<StateMachineState *> &memo)
{
	if (!memo.insert(storeMachine).second)
		return true;
	StateMachineSideEffect *otherEffect = storeMachine->getSideEffect();
	if (otherEffect) {
		switch (probeEffect->type) {
		case StateMachineSideEffect::StartAtomic:
			if (otherEffect->type == StateMachineSideEffect::StartAtomic)
				return false;
			break;
		case StateMachineSideEffect::Load:
			if (otherEffect->type == StateMachineSideEffect::Store &&
			    oracle->memoryAccessesMightAlias(
				    decode,
				    opt,
				    (StateMachineSideEffectLoad *)probeEffect,
				    (StateMachineSideEffectStore *)otherEffect))
				return false;
			break;
		case StateMachineSideEffect::Store:
			if (otherEffect->type == StateMachineSideEffect::Load &&
			    allowStoreLoadRaces) {
				if (oracle->memoryAccessesMightAlias(
					    decode,
					    opt,
					    (StateMachineSideEffectLoad *)otherEffect,
					    (StateMachineSideEffectStore *)probeEffect))
					return false;
			} else if (otherEffect->type == StateMachineSideEffect::Store) {
				if (oracle->memoryAccessesMightAlias(
					    decode,
					    opt,
					    (StateMachineSideEffectStore *)otherEffect,
					    (StateMachineSideEffectStore *)probeEffect))
					return false;
			}
			break;

			/* Purely local side-effects never race.
			   These should arguably be filtered out
			   before we get here; nevermind. */
		case StateMachineSideEffect::AssertFalse:
		case StateMachineSideEffect::EndAtomic:
		case StateMachineSideEffect::Copy:
		case StateMachineSideEffect::Phi:
		case StateMachineSideEffect::Unreached:
		case StateMachineSideEffect::StartFunction:
		case StateMachineSideEffect::EndFunction:
		case StateMachineSideEffect::PointerAliasing:
		case StateMachineSideEffect::StackLayout:
			return true;
		}
	}
	std::vector<StateMachineState *> targets;
	storeMachine->targets(targets);
	for (auto it = targets.begin(); it != targets.end(); it++)
		if (!definitelyDoesntRace(decode, probeEffect, *it, opt, allowStoreLoadRaces, oracle, memo))
			return false;
	return true;
}

/* Returns true if there are any stores in @machine which might
   conceivably race with @probeEffect. */
static bool
probeDefinitelyDoesntRace(const MaiMap &decode, StateMachineSideEffect *probeEffect,
			  StateMachineState *storeMachine,
			  const IRExprOptimisations &opt, OracleInterface *oracle)
{
	std::set<StateMachineState *> memo;
	return definitelyDoesntRace(decode, probeEffect, storeMachine, opt, false, oracle, memo);
}
static bool
storeDefinitelyDoesntRace(const MaiMap &decode, StateMachineSideEffect *storeEffect,
			  StateMachineState *probeMachine,
			  const IRExprOptimisations &opt, OracleInterface *oracle)
{
	std::set<StateMachineState *> memo;
	return definitelyDoesntRace(decode, storeEffect, probeMachine, opt, true, oracle, memo);
}

static StateMachine *
buildCrossProductMachine(const MaiMap &maiIn,
			 StateMachine *probeMachine,
			 StateMachine *storeMachine,
			 OracleInterface *oracle,
			 MaiMap *&maiOut,
			 int *next_fake_free_variable,
			 const IRExprOptimisations &opt)
{
	maiOut = maiIn.dupe();

	std::map<crossStateT, StateMachineState *> results;
	typedef std::pair<StateMachineState **, crossStateT> relocT;
	std::vector<relocT> pendingRelocs;

	StateMachineState *crossMachineRoot;
	crossMachineRoot = NULL;
	pendingRelocs.push_back(
		relocT(&crossMachineRoot, crossStateT(probeMachine->root, storeMachine->root, false, false, false, false)));
	while (!pendingRelocs.empty()) {
		relocT r(pendingRelocs.back());
		pendingRelocs.pop_back();

		assert(!*r.first);
		if (results.count(r.second)) {
			*r.first = results[r.second];
			continue;
		}

		crossStateT crossState(r.second);

		struct {
			StateMachineState *operator()(const crossStateT &crossState,
						      std::vector<relocT> &pendingRelocs) {
				assert(!crossState.store_is_atomic);
				StateMachineState *res = shallowCloneState(crossState.p);
				bool lockState =
					(crossState.probe_is_atomic ||
					 (crossState.p->getSideEffect() &&
					  crossState.p->getSideEffect()->type == StateMachineSideEffect::StartAtomic)) &&
					!(crossState.p->getSideEffect() &&
					  crossState.p->getSideEffect()->type == StateMachineSideEffect::EndAtomic);
				std::vector<StateMachineState **> targets;
				res->targets(targets);
				for (auto it = targets.begin(); it != targets.end(); it++) {
					pendingRelocs.push_back(
						relocT(*it,
						       crossStateT(
							       **it,
							       crossState.s,
							       crossState.store_issued_store,
							       true,
							       lockState,
							       crossState.store_is_atomic
							       )));
					**it = NULL;
				}
				return res;
			}
		} advanceProbeMachine;
		struct {
			StateMachineState *operator()(const crossStateT &crossState,
						      std::vector<relocT> &pendingRelocs) {
				assert(!crossState.probe_is_atomic);
				StateMachineState *res = shallowCloneState(crossState.s);

				bool lockState =
					(crossState.store_is_atomic ||
					 (crossState.s->getSideEffect() &&
					  crossState.s->getSideEffect()->type == StateMachineSideEffect::StartAtomic)) &&
					!(crossState.s->getSideEffect() &&
					  crossState.s->getSideEffect()->type == StateMachineSideEffect::EndAtomic);

				std::vector<StateMachineState **> targets;
				res->targets(targets);
				for (auto it = targets.begin(); it != targets.end(); it++) {
					pendingRelocs.push_back(
						relocT(*it,
						       crossStateT(
							       crossState.p,
							       **it,
							       true,
							       crossState.probe_issued_access,
							       crossState.probe_is_atomic,
							       lockState)));
					**it = NULL;
				}
				return res;
			}
		} advanceStoreMachine;
		StateMachineState *newState;
		if (crossState.probe_is_atomic) {
			/* We have to issue probe effects until we get
			 * to an EndAtomic side effect. */
			assert(!crossState.store_is_atomic);
			newState = advanceProbeMachine(crossState, pendingRelocs);
		} else if (crossState.store_is_atomic) {
			/* Likewise, if the store machine is currently
			   atomic then we need to advance it. */
			newState = advanceStoreMachine(crossState, pendingRelocs);
		} else {
			/* Neither machine is in an atomic block, need
			 * to race them. */
			StateMachineSideEffect *probe_effect = crossState.p->getSideEffect();
			StateMachineSideEffect *store_effect = crossState.s->getSideEffect();

			if (crossState.p->type == StateMachineState::Terminal) {
				/* The probe machine has reached its
				   end.  The result is the result of
				   the whole machine. */
				/* Exception: we don't consider the
				   case where the probe machine
				   crashes before the store machine
				   has issued any stores, so that just
				   turns into Unreached. */
				if (crossState.p == StateMachineTerminal::survive() ||
				    crossState.store_issued_store)
					newState = crossState.p;
				else
					newState = StateMachineTerminal::unreached();
			} else if (crossState.s->type == StateMachineState::Terminal) {
				/* If the store machine terminates at
				   <survive> or <unreached> then we
				   should ignore this path.  If it
				   terminates at <crash> then we need
				   to run the probe machine to
				   completion to see what's what. */
				/* Another exception: we don't want to
				   consider the case where the store
				   machine completes before the load
				   machine has issued any loads, so
				   turn that into <unreached> as
				   well. */
				if (crossState.probe_issued_access &&
				    crossState.s == StateMachineTerminal::crash())
					newState = advanceProbeMachine(crossState, pendingRelocs);
				else
					newState = StateMachineTerminal::unreached();
			} else if (!probe_effect ||
				   probeDefinitelyDoesntRace(*maiOut, probe_effect, crossState.s, opt, oracle)) {
				/* If the probe effect definitely
				   cannot race with anything left in
				   the store machine then we should
				   issue it unconditionally. */
				newState = advanceProbeMachine(crossState, pendingRelocs);
			} else if (!store_effect ||
				   storeDefinitelyDoesntRace(*maiOut, store_effect, crossState.p, opt, oracle)) {
				/* Likewise, if a store effect isn't a
				 * memory access then it's definitely
				 * not going to race, so we can issue
				 * it unconditionally. */
				newState = advanceStoreMachine(crossState, pendingRelocs);
			} else {
				StateMachineSideEffectMemoryAccess *probe_access =
					dynamic_cast<StateMachineSideEffectMemoryAccess *>(probe_effect);
				StateMachineSideEffectMemoryAccess *store_access =
					dynamic_cast<StateMachineSideEffectMemoryAccess *>(store_effect);
				/* Both machines want to issue side
				   effects, and there's some
				   possibility of an interesting race.
				   Pick a non-deterministic
				   interleaving. */

				/* First possibility: let the probe
				 * machine go first */
				StateMachineState *nextProbe =
					advanceProbeMachine(crossState, pendingRelocs);

				/* Second possibility: let the store
				   machine go first. */
				StateMachineState *nextStore = advanceStoreMachine(crossState, pendingRelocs);
				if (probe_access && store_access) {
					/* If we're racing memory
					   accesses against each
					   other, then when the two
					   addresses are different
					   then it doesn't matter
					   which we decide to issue
					   first.  We therefore only
					   need to consider issuing
					   the store first when they
					   do match.  Equivalent, we
					   can have the
					   store-goes-first case
					   assert that they're equal,
					   and that's what we do. */
					nextStore = new StateMachineSideEffecting(
						nextStore->dbg_origin,
						new StateMachineSideEffectAssertFalse(
							IRExpr_Unop(
								Iop_Not1, /* Remember, it's assertfalse,
									     so need to invert the condition. */
								IRExpr_Binop(
									Iop_CmpEQ64,
									probe_access->addr,
									store_access->addr)),
							false),
						nextStore);
				} else {
					/* Other case is that we race
					   a START_ATOMIC against
					   something, for which
					   there's nothing to assert,
					   which makes things a bit
					   easier. */
				}
				IRExpr *fv;
				if (probe_access && store_access) {
					fv = IRExpr_HappensBefore(
						probe_access->rip,
						store_access->rip);
				} else {
					ThreadRip tr(-1, VexRip::invent_vex_rip((*next_fake_free_variable)++));
					fv = maiOut->freeVariable(
						Ity_I1,
						-1,
						NULL,
						false);
				}
				newState = new StateMachineBifurcate(
					VexRip(),
					fv,
					nextProbe,
					nextStore);
			}
		}
		results[r.second] = newState;
		*r.first = newState;
	}

	std::vector<std::pair<unsigned, const CFGNode *> > cfg_roots(probeMachine->cfg_roots);
	for (auto it = storeMachine->cfg_roots.begin(); it != storeMachine->cfg_roots.end(); it++) {
		bool already_present = false;
		for (auto it2 = cfg_roots.begin(); !already_present && it2 != cfg_roots.end(); it2++)
			if (*it2 == *it)
				already_present = true;
		if (!already_present)
			cfg_roots.push_back(*it);
	}
        return new StateMachine(crossMachineRoot, cfg_roots);
}

static StateMachine *
stripUninterpretableAnnotations(StateMachine *inp)
{
	std::map<StateMachineState *, StateMachineState *> rewrites;
	typedef std::pair<StateMachineState *, StateMachineState **> relocT;
	std::vector<relocT> relocs;
	StateMachineState *newRoot;
	relocs.push_back(relocT(inp->root, &newRoot));
	while (!relocs.empty()) {
		relocT reloc(relocs.back());
		relocs.pop_back();
		auto it_did_insert = rewrites.insert(
			std::pair<StateMachineState *, StateMachineState *>
			(reloc.first, (StateMachineState *)NULL));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert) {
			switch (reloc.first->type) {
			case StateMachineState::Bifurcate: {
				StateMachineBifurcate *old =
					(StateMachineBifurcate *)reloc.first;
				StateMachineBifurcate *nw =
					new StateMachineBifurcate(
						old->dbg_origin,
						old->condition,
						NULL,
						NULL);
				relocs.push_back(relocT(old->trueTarget, &nw->trueTarget));
				relocs.push_back(relocT(old->falseTarget, &nw->falseTarget));
				it->second = nw;
				break;
			}
			case StateMachineState::Terminal:
				it->second = it->first;
				break;
			case StateMachineState::SideEffecting: {
				StateMachineSideEffecting *old =
					(StateMachineSideEffecting *)reloc.first;
				StateMachineSideEffecting *nw =
					new StateMachineSideEffecting(
						old->dbg_origin,
						old->sideEffect,
						NULL);
				if (old->sideEffect->type == StateMachineSideEffect::StackLayout ||
				    old->sideEffect->type == StateMachineSideEffect::StartFunction ||
				    old->sideEffect->type == StateMachineSideEffect::EndFunction)
					nw->sideEffect = NULL;
				relocs.push_back(relocT(old->target, &nw->target));
				it->second = nw;
				break;
			}
			}
		}
		assert(it->second != NULL);
		*reloc.second = it->second;
	}
	return new StateMachine(inp, newRoot);
}

IRExpr *
crossProductSurvivalConstraint(const VexPtr<StateMachine, &ir_heap> &probeMachine,
			       const VexPtr<StateMachine, &ir_heap> &storeMachine,
			       const VexPtr<OracleInterface> &oracle,
			       const VexPtr<IRExpr, &ir_heap> &initialStateCondition,
			       const AllowableOptimisations &optIn,
			       const VexPtr<MaiMap, &ir_heap> &mai,
			       GarbageCollectionToken token)
{
	int fake_cntr = 0; /* a counter of fakes, not a fake counter */
	__set_profiling(evalCrossProductMachine);

	AllowableOptimisations opt =
		optIn
		    .enableassumeExecutesAtomically()
		    .enableignoreSideEffects()
		    .enableassumeNoInterferingStores()
		    .enablenoExtend();
	VexPtr<MaiMap, &ir_heap> decode;
	VexPtr<StateMachine, &ir_heap> crossProductMachine(
		buildCrossProductMachine(
			*mai,
			stripUninterpretableAnnotations(probeMachine),
			stripUninterpretableAnnotations(storeMachine),
			oracle,
			decode.get(),
			&fake_cntr,
			opt));
	crossProductMachine =
		optimiseStateMachine(
			decode,
			crossProductMachine,
			opt,
			oracle,
			false,
			token);
	if (crossProductMachine->root == StateMachineTerminal::unreached()) {
		/* This indicates that the store machine and probe
		   machine assert incompatible things.  e.g. suppose
		   the probe machine amounts to saying we'll crash if
		   some global variable is a bad pointer, but the
		   store machine unconditionally dereferences it.
		   Easy to deal with: just return the constant 1, so
		   that we don't report a bug. */
		return IRExpr_Const_U1(true);
	}

	return survivalConstraintIfExecutedAtomically(
		decode,
		crossProductMachine,
		initialStateCondition,
		oracle,
		true,
		opt,
		token);
}

/* Transform @machine so that wherever it would previously branch to
   StateMachineCrash it will now branch to the root of @to.  If @from
   is a store state then this effectively concatenates the two
   machines together.  We duplicate both machines in the process. */
/* Slightly non-obvious: we make the composite machine branch to
   <crash> if the first machine branches to <survive>.  The idea is
   that the composite machine runs the first machine to completion and
   then, if that predicts a crash, runs the second machine to
   completion. */
static StateMachine *
concatenateStateMachinesCrashing(const StateMachine *machine, const StateMachine *to)
{
	std::map<const StateMachineState *, StateMachineState *> rewriteRules;

	to = duplicateStateMachine(to);

	/* This is moderately tricky: setting rules for all of the
	   terminal states, even no-op rules, forces rewriteMachine()
	   to duplicate every state, because it duplicates any state
	   which can ultimately reach a state which it has a rule for. */
	rewriteRules[StateMachineTerminal::crash()] = to->root;
	rewriteRules[StateMachineTerminal::survive()] = StateMachineTerminal::crash();
	rewriteRules[StateMachineTerminal::unreached()] = StateMachineTerminal::unreached();

	StateMachineTransformer::rewriteMachine(machine, rewriteRules, false);
	assert(rewriteRules.count(machine->root));
	std::vector<std::pair<unsigned, const CFGNode *> > cfg_roots(machine->cfg_roots);
	for (auto it = to->cfg_roots.begin(); it != to->cfg_roots.end(); it++) {
		bool already_present = false;
		for (auto it2 = cfg_roots.begin(); !already_present && it2 != cfg_roots.end(); it2++)
			if (*it2 == *it)
				already_present = true;
		if (!already_present)
			cfg_roots.push_back(*it);
	}
	return new StateMachine(rewriteRules[machine->root],
				cfg_roots);
}

IRExpr *
writeMachineSuitabilityConstraint(VexPtr<MaiMap, &ir_heap> &mai,
				  const VexPtr<StateMachine, &ir_heap> &writeMachine,
				  const VexPtr<StateMachine, &ir_heap> &readMachine,
				  const VexPtr<OracleInterface> &oracle,
				  const VexPtr<IRExpr, &ir_heap> &assumption,
				  const AllowableOptimisations &opt,
				  GarbageCollectionToken token)
{
	__set_profiling(writeMachineSuitabilityConstraint);

	VexPtr<StateMachine, &ir_heap> combinedMachine;

	writeMachine->assertAcyclic();
	readMachine->assertAcyclic();
	combinedMachine = concatenateStateMachinesCrashing(
		writeMachine,
		readMachine);
	combinedMachine->assertAcyclic();
	combinedMachine = optimiseStateMachine(mai,
					       combinedMachine,
					       opt
					          .enableassumeExecutesAtomically()
					          .enableignoreSideEffects()
					          .enableassumeNoInterferingStores()
					          .enablenoExtend(),
					       oracle,
					       true,
					       token);
	if (combinedMachine->root == StateMachineTerminal::unreached()) {
		/* This means that running the store machine and then
		   running the load machine is guaranteed to never
		   survive.  That tells us that the store machine is
		   never suitable, so the suitability constraint is
		   just 0. */
		return IRExpr_Const_U1(false);
	}
	return survivalConstraintIfExecutedAtomically(
		mai,
		combinedMachine,
		assumption,
		oracle,
		false,
		opt,
		token);
}

/* Just collect all of the constraints which the symbolic execution
 * engine spits out.  The idea is that if you generate a set of input
 * states X such that, for every condition Y which this emits some
 * member of X makes Y false and some member makes it true then that
 * should get you reasonably close to exploring all of the interesting
 * behaviour in the machine. */
/* The number of constraints you get from a single machine is
   arbitrarily limited to 1000, just because the only consumer of this
   data can't handle any more than that without exploding due to
   super-linear scaling behaviour. */
void
collectConstraints(const VexPtr<MaiMap, &ir_heap> &mai,
		   const VexPtr<StateMachine, &ir_heap> &sm,
		   VexPtr<OracleInterface> &oracle,
		   const IRExprOptimisations &opt,
		   std::vector<IRExpr *> &out,
		   GarbageCollectionToken token)
{
	struct : public EvalPathConsumer, public GcCallback<&ir_heap> {
		std::vector<IRExpr *> *out;
		void runGc(HeapVisitor &hv) {
			for (auto it = out->begin(); it != out->end(); it++)
				hv(*it);
		}
		void addConstraint(IRExpr *a) {
			out->push_back(a);
			if (out->size() > 1000)
				aborted = true;
		}
		void crash(IRExpr *assumption, IRExpr *) {
			addConstraint(assumption);
		}
		void survive(IRExpr *assumption, IRExpr *) {
			addConstraint(assumption);
		}
		void escape(IRExpr *assumption, IRExpr *) {
			addConstraint(assumption);
		}
		void badMachine(void) {
		}
	} consumer;
	consumer.out = &out;
	enumEvalPaths(mai, sm, IRExpr_Const_U1(true), oracle, opt, consumer, token, true);
}
