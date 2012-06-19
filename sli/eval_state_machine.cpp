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

#ifdef NDEBUG
#define debug_dump_state_traces 0
#define debug_dump_crash_reasons 0
#else
static bool debug_dump_state_traces = false;
static bool debug_dump_crash_reasons = false;
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

class memLogT : public std::vector<std::pair<StateMachine *, StateMachineSideEffectMemoryAccess *> > {
public:
	void visit(HeapVisitor &hv) {
		for (auto it = begin(); it != end(); it++) {
			hv(it->first);
			hv(it->second);
		}
	}
};

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

	trool evalBooleanExpression(IRExpr *what, const AllowableOptimisations &opt);
	bool evalSideEffect(StateMachine *sm, OracleInterface *oracle, EvalPathConsumer &consumer,
			    std::vector<EvalContext> &pendingStates, StateMachineSideEffect *smse,
			    const AllowableOptimisations &opt) __attribute__((warn_unused_result));


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
		    const AllowableOptimisations &opt)
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
		StateMachine *thisMachine,
		StateMachineSideEffect *smse,
		NdChooser &chooser,
		OracleInterface *oracle,
		bool collectOrderingConstraints,
		const AllowableOptimisations &opt);
	bool expressionIsTrue(IRExpr *exp, NdChooser &chooser, const AllowableOptimisations &opt);
	bool evalExpressionsEqual(IRExpr *exp1, IRExpr *exp2, NdChooser &chooser, const AllowableOptimisations &opt);

public:
	bool advance(OracleInterface *oracle, const AllowableOptimisations &opt,
		     std::vector<EvalContext> &pendingStates,
		     StateMachine *sm,
		     EvalPathConsumer &consumer) __attribute__((warn_unused_result));
	enum smallStepResult { ssr_crash, ssr_survive, ssr_escape,
			       ssr_ignore_path, ssr_failed, ssr_continue };
	smallStepResult smallStepEvalStateMachine(StateMachine *rootMachine,
						  NdChooser &chooser,
						  OracleInterface *oracle,
						  bool collectOrderingConstraints,
						  const AllowableOptimisations &opt);
	enum bigStepResult { bsr_crash, bsr_survive, bsr_failed };
	bigStepResult bigStepEvalStateMachine(StateMachine *rootMachine,
					      bigStepResult preferred_result,
					      NdChooser &chooser,
					      OracleInterface *oracle,
					      bool collectOrderingConstraints,
					      const AllowableOptimisations &opt);
	EvalContext(StateMachine *sm, IRExpr *initialAssumption, bool useAccAssumptions,
		    std::map<const StateMachineState*, int> &_stateLabels)
		: assumption(initialAssumption),
		  accumulatedAssumption(useAccAssumptions ? IRExpr_Const(IRConst_U1(1)) : NULL),
		  atomic(false),
		  currentState(sm->root)
#ifndef NDEBUG
		, stateLabels(_stateLabels)
#endif
	{
		advance_state_trace();
	}
	EvalContext(const EvalContext &o)
		: assumption(o.assumption),
		  accumulatedAssumption(o.accumulatedAssumption),
		  state(o.state),
		  memlog(o.memlog),
		  atomic(o.atomic),
		  currentState(o.currentState)
#ifndef NDEBUG
		, statePath(o.statePath),
		  stateLabels(o.stateLabels)
#endif
	{
	}	
};

bool
EvalContext::expressionIsTrue(IRExpr *exp, NdChooser &chooser, const AllowableOptimisations &opt)
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
		if (((IRExprConst *)e)->con->Ico.U1) {
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
		if (((IRExprConst *)e2)->con->Ico.U1) {
			assumption = IRExpr_Const(IRConst_U1(1));
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
		if (accumulatedAssumption)
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
		if (accumulatedAssumption)
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
EvalContext::evalExpressionsEqual(IRExpr *exp1, IRExpr *exp2, NdChooser &chooser, const AllowableOptimisations &opt)
{
	return expressionIsTrue(IRExpr_Binop(
					Iop_CmpEQ64,
					exp1,
					exp2),
				chooser,
				opt);
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

/* Build an expression which evaluates to true precisely when
   dereferencing @e requires us to dereference a bad pointer in an LD
   expression. */
static IRExpr *
dereferencesBadPointerIf(IRExpr *e)
{
	struct : public IRExprTransformer {
		std::set<IRExpr *> addrs;
		IRExpr *transformIex(IRExprLoad *iel) {
			addrs.insert(iel->addr);
			return IRExprTransformer::transformIex(iel);
		}
	} collectAddresses;
	collectAddresses.doit(e);
	IRExprAssociative *derefsBadPointer = IRExpr_Associative(collectAddresses.addrs.size(), Iop_Or1);
	for (auto it = collectAddresses.addrs.begin(); it != collectAddresses.addrs.end(); it++) {
		derefsBadPointer->contents[derefsBadPointer->nr_arguments++] =
			IRExpr_Unop(
				Iop_BadPtr,
				*it);
	}
	return derefsBadPointer;
}

EvalContext::evalStateMachineSideEffectRes
EvalContext::evalStateMachineSideEffect(StateMachine *thisMachine,
					StateMachineSideEffect *smse,
					NdChooser &chooser,
					OracleInterface *oracle,
					bool collectOrderingConstraints,
					const AllowableOptimisations &opt)
{
	IRExpr *addr = NULL;
	if (smse->type == StateMachineSideEffect::Load ||
	    smse->type == StateMachineSideEffect::Store) {
		StateMachineSideEffectMemoryAccess *smsema =
			dynamic_cast<StateMachineSideEffectMemoryAccess *>(smse);
		assert(smsema);
		addr = state.specialiseIRExpr(smsema->addr);
		IRExpr *v = IRExpr_Binop(
			Iop_Or1,
			IRExpr_Unop(Iop_BadPtr, addr),
			dereferencesBadPointerIf(addr));
		if (expressionIsTrue(v, chooser, opt))
			return esme_escape;
	}

	switch (smse->type) {
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectStore *smses =
			dynamic_cast<StateMachineSideEffectStore *>(smse);
		assert(smses);
		assert(addr);
		if (collectOrderingConstraints) {
			for (memLogT::reverse_iterator it = memlog.rbegin();
			     it != memlog.rend();
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
				if (evalExpressionsEqual(addr, smsel->addr, chooser, opt))
					addOrderingConstraint(
						smsel->rip,
						smses->rip,
						opt,
						&assumption,
						&accumulatedAssumption);
			}
		}
		memlog.push_back(
			std::pair<StateMachine *, StateMachineSideEffectMemoryAccess *>
			(thisMachine,
			 new StateMachineSideEffectStore(
				 state.specialiseIRExpr(addr),
				 state.specialiseIRExpr(smses->data),
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
		for (memLogT::reverse_iterator it = memlog.rbegin();
		     it != memlog.rend();
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
			if (evalExpressionsEqual(smses->addr, addr, chooser, opt)) {
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
								&assumption,
								&accumulatedAssumption);
					} else {
						if (it->first != thisMachine)
							addOrderingConstraint(
								smses->rip,
								smsel->rip,
								opt,
								&assumption,
								&accumulatedAssumption);
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
			val = IRExpr_Load(smsel->type, addr, MemoryAccessIdentifier::initial_value());
		}
		if (collectOrderingConstraints)
			memlog.push_back(
				std::pair<StateMachine *, StateMachineSideEffectMemoryAccess *>(
					thisMachine,
					new StateMachineSideEffectLoad(
						smsel->target,
						state.specialiseIRExpr(addr),
						smsel->rip,
						smsel->type)));
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
			    IRExpr_Binop(
				    Iop_Or1,
				    smseaf->value,
				    dereferencesBadPointerIf(smseaf->value)),
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
		break;
	}
	return esme_normal;
}

/* Walk the state machine and figure out whether it's going to crash.
   If we hit something which we can't solve statically or via the
   oracle, ask the chooser which way we should go, and then emit a
   path constraint saying which way we went.  Stubs are assumed to
   never crash. */
/* Returns tr_true if we crash, tr_false if we survive, and tr_unknown
   if the machine isn't finished yet. */
EvalContext::smallStepResult
EvalContext::smallStepEvalStateMachine(StateMachine *rootMachine,
				       NdChooser &chooser,
				       OracleInterface *oracle,
				       bool collectOrderingConstraints,
				       const AllowableOptimisations &opt)
{
	if (TIMEOUT)
		return ssr_failed;

	switch (currentState->type) {
	case StateMachineState::Crash:
		return ssr_crash;
	case StateMachineState::NoCrash:
		return ssr_survive;
	case StateMachineState::Stub:
		return ssr_escape;
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)currentState;
		evalStateMachineSideEffectRes res =
			evalStateMachineSideEffect(rootMachine,
						   sme->sideEffect,
						   chooser,
						   oracle,
						   collectOrderingConstraints,
						   opt);
		switch (res) {
		case esme_escape:
			return ssr_escape;
		case esme_ignore_path:
			return ssr_ignore_path;
		case esme_normal:
			currentState = sme->target;
			return ssr_continue;
		}
		abort();
	}
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)currentState;
		if (expressionIsTrue(smb->condition, chooser, opt))
			currentState = smb->trueTarget;
		else
			currentState = smb->falseTarget;
		return ssr_continue;
	}
	case StateMachineState::NdChoice: {
		StateMachineNdChoice *smnd = (StateMachineNdChoice *)currentState;
		if (smnd->successors.size() != 0) {
			currentState = chooser.nd_choice(smnd->successors);
			return ssr_continue;
		}
		/* Fall through to the Unreached case if we have no
		 * available successors. */
	}
	case StateMachineState::Unreached:
		/* Whoops... */
		fprintf(_logfile, "Evaluating an unreachable state machine?\n");
		return ssr_failed;
	}

	abort();
}

EvalContext::bigStepResult
EvalContext::bigStepEvalStateMachine(StateMachine *rootMachine,
				     bigStepResult preferred_result,
				     NdChooser &chooser,
				     OracleInterface *oracle,
				     bool collectOrderingConstraints,
				     const AllowableOptimisations &opt)
{
	while (1) {
		smallStepResult res =
			smallStepEvalStateMachine(rootMachine,
						  chooser,
						  oracle,
						  collectOrderingConstraints,
						  opt);
		switch (res) {
		case EvalContext::ssr_crash:
			return bsr_crash;
		case ssr_survive:
			return bsr_survive;
		case ssr_escape:
			return preferred_result;
		case ssr_ignore_path:
			return preferred_result;
		case ssr_failed:
			return bsr_failed;
		case ssr_continue:
			continue;
		}
		abort();
	}
}

EvalContext::trool
EvalContext::evalBooleanExpression(IRExpr *what, const AllowableOptimisations &opt)
{
	assert(what->type() == Ity_I1);
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

bool
EvalContext::evalSideEffect(StateMachine *sm, OracleInterface *oracle, EvalPathConsumer &consumer,
			    std::vector<EvalContext> &pendingStates, StateMachineSideEffect *smse,
			    const AllowableOptimisations &opt)
{
	NdChooser chooser;

	do {
		EvalContext newContext(*this);
		evalStateMachineSideEffectRes res =
			newContext.evalStateMachineSideEffect(sm, smse, chooser, oracle,
							      consumer.collectOrderingConstraints,
							      opt);
		switch (res) {
		case esme_normal:
			pendingStates.push_back(newContext);
			break;
		case esme_ignore_path:
			break;
		case esme_escape:
			if (!consumer.escape(newContext.assumption, newContext.accumulatedAssumption))
				return false;
			break;
		}
	} while (chooser.advance());
	return true;
}

/* You might that we could stash things like @oracle, @opt, and @sm in
   the EvalContext itself and not have to pass them around all the
   time.  That'd work, but it'd mean duplicating those pointers in
   every item in the pending state queue, which would make that queue
   much bigger, which'd be kind of annoying. */
bool
EvalContext::advance(OracleInterface *oracle, const AllowableOptimisations &opt,
		     std::vector<EvalContext> &pendingStates,
		     StateMachine *sm,
		     EvalPathConsumer &consumer)
{
	if (debug_dump_state_traces && currentState->isTerminal()) {
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
	case StateMachineState::Crash:
		if (debug_dump_crash_reasons) {
			printf("Found a crash, assumption ");
			ppIRExpr(assumption, stdout);
			if (accumulatedAssumption) {
				printf(", accumulated assumption ");
				ppIRExpr(accumulatedAssumption, stdout);
			}
			printf("\n");
		}
		return consumer.crash(assumption, accumulatedAssumption);
	case StateMachineState::NoCrash:
		return consumer.survive(assumption, accumulatedAssumption);
	case StateMachineState::Stub:
		return consumer.escape(assumption, accumulatedAssumption);
	case StateMachineState::Unreached:
		return consumer.badMachine();
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)currentState;
		currentState = sme->target;
		if (sme->sideEffect &&
		    !evalSideEffect(sm, oracle, consumer, pendingStates,
				    sme->sideEffect, opt))
			return false;
		advance_state_trace();
		return true;
	}
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)currentState;
		IRExpr *cond =
			simplifyIRExpr(
				internIRExpr(
					state.specialiseIRExpr(smb->condition)),
				opt);
		IRExpr *derefBad = dereferencesBadPointerIf(cond);
		trool res = evalBooleanExpression(derefBad, opt);
		switch (res) {
		case tr_true:
			return consumer.escape(assumption, accumulatedAssumption);
		case tr_unknown: {
			IRExpr *a = simplifyIRExpr(internIRExpr(IRExpr_Binop(Iop_And1, assumption, derefBad)), opt);
			IRExpr *a2;
			assert(a->tag != Iex_Const);
			if (accumulatedAssumption)
				a2 = simplifyIRExpr(
					internIRExpr(
						IRExpr_Binop(
							Iop_And1,
							accumulatedAssumption,
							derefBad)),
					opt);
			else
				a2 = NULL;
			if (!consumer.escape(a, a2))
				return false;
			assumption = IRExpr_Binop(Iop_And1, assumption,
						  IRExpr_Unop(Iop_Not1, derefBad));
			if (accumulatedAssumption)
				accumulatedAssumption =
					IRExpr_Binop(Iop_And1, accumulatedAssumption,
						     IRExpr_Unop(Iop_Not1, derefBad));
			assumption = simplifyIRExpr(internIRExpr(assumption), opt);
			if (accumulatedAssumption)
				accumulatedAssumption = simplifyIRExpr(internIRExpr(accumulatedAssumption), opt);
			break;
		}
		case tr_false:
			break;
		}
		res = evalBooleanExpression(cond, opt);
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
		return true;
	}
	case StateMachineState::NdChoice: {
		StateMachineNdChoice *smnd = (StateMachineNdChoice *)currentState;
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
enumEvalPaths(const VexPtr<StateMachine, &ir_heap> &sm,
	      const VexPtr<IRExpr, &ir_heap> &assumption,
	      const VexPtr<OracleInterface> &oracle,
	      const AllowableOptimisations &opt,
	      struct EvalPathConsumer &consumer,
	      GarbageCollectionToken &token)
{
	std::vector<EvalContext> pendingStates;
	std::map<const StateMachineState *, int> stateLabels;

	if (debug_dump_state_traces) {
		printf("Eval machine:\n");
		printStateMachine(sm, stdout, stateLabels);
		printf("Under assumption ");
		ppIRExpr(assumption, stdout);
		printf("\n");
	}

	pendingStates.push_back(EvalContext(sm, assumption, consumer.needsAccAssumptions, stateLabels));

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
survivalConstraintIfExecutedAtomically(const VexPtr<StateMachine, &ir_heap> &sm,
				       VexPtr<IRExpr, &ir_heap> assumption,
				       const VexPtr<OracleInterface> &oracle,
				       bool escapingStatesSurvive,
				       const AllowableOptimisations &opt,
				       GarbageCollectionToken token)
{
	__set_profiling(survivalConstraintIfExecutedAtomically);

	struct _ : public EvalPathConsumer {
		VexPtr<IRExpr, &ir_heap> res;
		const AllowableOptimisations &opt;
		bool escapingStatesSurvive;
		bool crash(IRExpr *pathConstraint, IRExpr *justPathConstraint) {
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
			return true;
		}
		bool survive(IRExpr *, IRExpr *) { return true; }
		bool escape(IRExpr *pathConstraint, IRExpr *justPathConstraint) {
			if (escapingStatesSurvive)
				return survive(pathConstraint, justPathConstraint);
			else
				return crash(pathConstraint, justPathConstraint);
		}
		_(const VexPtr<IRExpr, &ir_heap> &_assumption,
		  const AllowableOptimisations &_opt,
		  bool _escapingStatesSurvive)
			: res(_assumption), opt(_opt), escapingStatesSurvive(_escapingStatesSurvive)
		{}
	} consumeEvalPath(assumption, opt, escapingStatesSurvive);
	if (assumption)
		consumeEvalPath.needsAccAssumptions = true;
	else
		assumption = IRExpr_Const(IRConst_U1(1));
	enumEvalPaths(sm, assumption, oracle, opt, consumeEvalPath, token);

	if (TIMEOUT)
		return NULL;
	else if (consumeEvalPath.res)
		return simplifyIRExpr(simplify_via_anf(consumeEvalPath.res), opt);
	else
		return IRExpr_Const(IRConst_U1(1));
}

bool
evalMachineUnderAssumption(const VexPtr<StateMachine, &ir_heap> &sm,
			   const VexPtr<OracleInterface> &oracle,
			   const VexPtr<IRExpr, &ir_heap> &assumption,
			   const AllowableOptimisations &opt,
			   bool *mightSurvive, bool *mightCrash,
			   GarbageCollectionToken token)
{
	__set_profiling(evalMachineUnderAssumption);

	*mightSurvive = false;
	*mightCrash = false;

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
	consumer.needsAccAssumptions = true;

	enumEvalPaths(sm, assumption, oracle, opt, consumer, token);

	if (TIMEOUT)
		return false;

	return true;
}

static StateMachineState *
shallowCloneState(StateMachineState *s)
{
	switch (s->type) {
#define do_case(name)					\
	case StateMachineState:: name :			\
		return StateMachine ## name ::get()
		do_case(Unreached);
		do_case(Crash);
		do_case(NoCrash);
#undef do_case
#define do_case(name)							\
		case StateMachineState:: name :				\
			return new StateMachine ## name			\
				(*(StateMachine ## name *)s)
		do_case(Stub);
		do_case(Bifurcate);
		do_case(SideEffecting);
		do_case(NdChoice);
#undef do_case
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
	bool probe_is_atomic;
	bool store_is_atomic;
	crossStateT(StateMachineState *_p,
		    StateMachineState *_s,
		    bool _sis,
		    bool _pia,
		    bool _sia)
		: p(_p),
		  s(_s),
		  store_issued_store(_sis),
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
		do_field(probe_is_atomic);
		do_field(store_is_atomic);
#undef do_field
		return false;
	}
};

static bool
definitelyDoesntRace(StateMachineSideEffect *probeEffect,
		     StateMachineState *storeMachine,
		     const AllowableOptimisations &opt,
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
				    opt,
				    (StateMachineSideEffectLoad *)probeEffect,
				    (StateMachineSideEffectStore *)otherEffect))
				return false;
			break;
		case StateMachineSideEffect::Store:
			if (otherEffect->type == StateMachineSideEffect::Load &&
			    allowStoreLoadRaces) {
				if (oracle->memoryAccessesMightAlias(
					    opt,
					    (StateMachineSideEffectLoad *)otherEffect,
					    (StateMachineSideEffectStore *)probeEffect))
					return false;
			} else if (otherEffect->type == StateMachineSideEffect::Store) {
				if (oracle->memoryAccessesMightAlias(
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
			return true;
		}
	}
	std::vector<StateMachineState *> targets;
	storeMachine->targets(targets);
	for (auto it = targets.begin(); it != targets.end(); it++)
		if (!definitelyDoesntRace(probeEffect, *it, opt, allowStoreLoadRaces, oracle, memo))
			return false;
	return true;
}

/* Returns true if there are any stores in @machine which might
   conceivably race with @probeEffect. */
static bool
probeDefinitelyDoesntRace(StateMachineSideEffect *probeEffect, StateMachineState *storeMachine,
			  const AllowableOptimisations &opt, OracleInterface *oracle)
{
	std::set<StateMachineState *> memo;
	return definitelyDoesntRace(probeEffect, storeMachine, opt, false, oracle, memo);
}
static bool
storeDefinitelyDoesntRace(StateMachineSideEffect *storeEffect, StateMachineState *probeMachine,
			  const AllowableOptimisations &opt, OracleInterface *oracle)
{
	std::set<StateMachineState *> memo;
	return definitelyDoesntRace(storeEffect, probeMachine, opt, true, oracle, memo);
}

static StateMachine *
buildCrossProductMachine(StateMachine *probeMachine, StateMachine *storeMachine,
			 OracleInterface *oracle, const AllowableOptimisations &opt)
{
	std::map<crossStateT, StateMachineState *> results;

	typedef std::pair<StateMachineState **, crossStateT> relocT;
	std::vector<relocT> pendingRelocs;

	StateMachineState *crossMachineRoot;
	crossMachineRoot = NULL;
	pendingRelocs.push_back(
		relocT(&crossMachineRoot, crossStateT(probeMachine->root, storeMachine->root, false, false, false)));
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
			assert(!crossState.p->isTerminal());
			newState = advanceProbeMachine(crossState, pendingRelocs);
		} else if (crossState.store_is_atomic) {
			/* Likewise, if the store machine is currently
			   atomic then we need to advance it. */
			assert(!crossState.s->isTerminal());
			newState = advanceStoreMachine(crossState, pendingRelocs);
		} else {
			/* Neither machine is in an atomic block, need
			 * to race them. */
			StateMachineSideEffect *probe_effect = crossState.p->getSideEffect();
			StateMachineSideEffect *store_effect = crossState.s->getSideEffect();

			if (crossState.p->isTerminal()) {
				/* The probe machine has reached its
				   end.  The result is the result of
				   the whole machine. */
				/* Exception: we don't consider the
				   case where the probe machine
				   crashes before the store machine
				   has issued any stores, so that just
				   turns into Unreached. */
				if (crossState.p->type == StateMachineState::NoCrash ||
				    crossState.store_issued_store)
					newState = crossState.p;
				else
					newState = StateMachineUnreached::get();
			} else if (crossState.s->isTerminal()) {
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
				if (crossState.s->type == StateMachineState::Crash)
					newState = advanceProbeMachine(crossState, pendingRelocs);
				else
					newState = StateMachineUnreached::get();
			} else if (!probe_effect ||
				   probeDefinitelyDoesntRace(probe_effect, crossState.s, opt, oracle)) {
				/* If the probe effect definitely
				   cannot race with anything left in
				   the store machine then we should
				   issue it unconditionally. */
				newState = advanceProbeMachine(crossState, pendingRelocs);
			} else if (!store_effect ||
				   storeDefinitelyDoesntRace(store_effect, crossState.p, opt, oracle)) {
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
				std::vector<StateMachineState *> possible;
				/* First possibility: let the probe
				 * machine go first */
				StateMachineState *nextProbe =
					advanceProbeMachine(crossState, pendingRelocs);
				possible.push_back(nextProbe);

				/* Second possibility: let the store
				   machine go first. */
				StateMachineState *s = advanceStoreMachine(crossState, pendingRelocs);
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
					s = new StateMachineSideEffecting(
						s->origin,
						new StateMachineSideEffectAssertFalse(
							IRExpr_Unop(
								Iop_Not1, /* Remember, it's assertfalse,
									     so need to invert the condition. */
								IRExpr_Binop(
									Iop_CmpEQ64,
									probe_access->addr,
									store_access->addr)),
							false),
						s);
				} else {
					/* Other case is that we race
					   a START_ATOMIC against
					   something, for which
					   there's nothing to assert,
					   which makes things a bit
					   easier. */
				}
				possible.push_back(s);
				newState = new StateMachineNdChoice(VexRip(), possible);
			}
		}
		results[r.second] = newState;
		*r.first = newState;
	}

	std::vector<std::pair<unsigned, VexRip> > origin(probeMachine->origin);
        origin.insert(origin.end(), storeMachine->origin.begin(), storeMachine->origin.end());
        return new StateMachine(crossMachineRoot, origin);
}

IRExpr *
crossProductSurvivalConstraint(const VexPtr<StateMachine, &ir_heap> &probeMachine,
			       const VexPtr<StateMachine, &ir_heap> &storeMachine,
			       const VexPtr<OracleInterface> &oracle,
			       const VexPtr<IRExpr, &ir_heap> &initialStateCondition,
			       const AllowableOptimisations &optIn,
			       GarbageCollectionToken token)
{
	__set_profiling(evalCrossProductMachine);

	AllowableOptimisations opt =
		optIn
		    .enableassumeExecutesAtomically()
		    .enableignoreSideEffects()
		    .enableassumeNoInterferingStores()
		    .enablenoExtend();
	VexPtr<StateMachine, &ir_heap> crossProductMachine(
		buildCrossProductMachine(
			probeMachine,
			storeMachine,
			oracle,
			opt));
	crossProductMachine =
		optimiseStateMachine(
			crossProductMachine,
			opt,
			oracle,
			false,
			token);
	if (crossProductMachine->root->type == StateMachineState::Unreached) {
		/* This indicates that the store machine and probe
		   machine assert incompatible things.  e.g. suppose
		   the probe machine amounts to saying we'll crash if
		   some global variable is a bad pointer, but the
		   store machine unconditionally dereferences it.
		   Easy to deal with: just return the constant 1, so
		   that we don't report a bug. */
		return IRExpr_Const(IRConst_U1(1));
	}

	return survivalConstraintIfExecutedAtomically(
		crossProductMachine,
		initialStateCondition,
		oracle,
		true,
		opt,
		token);
}

struct findRemoteMacroSectionsState {
	EvalContext writerContext;
	bool finished;
	bool writer_failed;

	StateMachineSideEffectStore *advanceWriteMachine(StateMachine *writeMachine,
							 NdChooser &chooser,
							 OracleInterface *oracle,
							 const AllowableOptimisations &opt);
	findRemoteMacroSectionsState(StateMachine *sm,
				     IRExpr *initialAssumption,
				     bool accumulateAssumptions,
				     std::map<const StateMachineState *, int> &stateLabels)
		: writerContext(sm, initialAssumption, accumulateAssumptions,
				stateLabels)
	{}
};

StateMachineSideEffectStore *
findRemoteMacroSectionsState::advanceWriteMachine(StateMachine *writeMachine,
						  NdChooser &chooser,
						  OracleInterface *oracle,
						  const AllowableOptimisations &opt)
{
	StateMachineSideEffectStore *smses = NULL;

	while (!TIMEOUT && (!smses || writerContext.atomic)) {
		StateMachineSideEffect *sideEffect = writerContext.currentState->getSideEffect();
		if (sideEffect && sideEffect->type == StateMachineSideEffect::Store)
			smses = (StateMachineSideEffectStore *)sideEffect;
		switch (writerContext.smallStepEvalStateMachine(
				writeMachine,
				chooser,
				oracle,
				false,
				opt)) {
		case EvalContext::ssr_crash:
		case EvalContext::ssr_escape:
		case EvalContext::ssr_failed:
			writer_failed = true;
			return NULL;
		case EvalContext::ssr_survive:
		case EvalContext::ssr_ignore_path:
			finished = true;
			return NULL;
		case EvalContext::ssr_continue:
			break;
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
findRemoteMacroSections(const VexPtr<StateMachine, &ir_heap> &readMachine,
			const VexPtr<StateMachine, &ir_heap> &writeMachine,
			const VexPtr<IRExpr, &ir_heap> &assumption,
			const VexPtr<OracleInterface> &oracle,
			const AllowableOptimisations &opt,
			VexPtr<remoteMacroSectionsT, &ir_heap> &output,
			GarbageCollectionToken token)
{
	__set_profiling(findRemoteMacroSections);
	NdChooser chooser;

	std::map<const StateMachineState *, int> stateLabels;

	do {
		if (TIMEOUT)
			return false;

		LibVEX_maybe_gc(token);

		findRemoteMacroSectionsState state(writeMachine, assumption, false, stateLabels);
		StateMachineSideEffectStore *sectionStart;

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
			EvalContext readEvalCtxt = state.writerContext;
			readEvalCtxt.currentState = readMachine->root;
			switch (readEvalCtxt.bigStepEvalStateMachine(
					readMachine,
					sectionStart ? EvalContext::bsr_crash : EvalContext::bsr_survive,
					chooser,
					oracle,
					false,
					opt)) {
			case EvalContext::bsr_crash:
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
				break;
			case EvalContext::bsr_survive:
				if (sectionStart) {
					/* Previous attempt did crash
					   -> this is the end of the
					   section. */
					output->insert(sectionStart, smses);
					sectionStart = NULL;
				}
				break;
			case EvalContext::bsr_failed:
				return false;
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
fixSufficient(const VexPtr<StateMachine, &ir_heap> &writeMachine,
	      const VexPtr<StateMachine, &ir_heap> &probeMachine,
	      const VexPtr<IRExpr, &ir_heap> &assumption,
	      const VexPtr<OracleInterface> &oracle,
	      const AllowableOptimisations &opt,
	      const VexPtr<remoteMacroSectionsT, &ir_heap> &sections,
	      GarbageCollectionToken token)
{
	__set_profiling(fixSufficient);
	NdChooser chooser;

	std::map<const StateMachineState *, int> stateLabels;

	do {
		if (TIMEOUT)
			return false;

		LibVEX_maybe_gc(token);

		std::set<StateMachineSideEffectStore *> incompleteSections;

		findRemoteMacroSectionsState state(writeMachine, assumption, false, stateLabels);
		state.writerContext.accumulatedAssumption = IRExpr_Const(IRConst_U1(1));
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
			EvalContext readEvalCtxt = state.writerContext;
			readEvalCtxt.currentState = probeMachine->root;
			switch (readEvalCtxt.bigStepEvalStateMachine(
					probeMachine,
					EvalContext::bsr_survive,
					chooser,
					oracle,
					false,
					opt)) {
			case EvalContext::bsr_crash:
				fprintf(_logfile, "Fix is insufficient, witness: ");
				ppIRExpr(readEvalCtxt.accumulatedAssumption, _logfile);
				fprintf(_logfile, "\n");
				return false; 
			case EvalContext::bsr_survive:
				break;
			case EvalContext::bsr_failed:
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
findHappensBeforeRelations(
	const VexPtr<StateMachine, &ir_heap> &probeMachine,
	const VexPtr<StateMachine, &ir_heap> &storeMachine,
	VexPtr<IRExpr, &ir_heap> &result,
	const VexPtr<OracleInterface> &oracle,
	const VexPtr<IRExpr, &ir_heap> &initialStateCondition,
	const AllowableOptimisations &opt,
	GarbageCollectionToken token)
{
	struct : public EvalPathConsumer {
		VexPtr<IRExpr, &ir_heap> newCondition;
		const AllowableOptimisations *opt;
		bool crash(IRExpr *, IRExpr *justPathConstraint) {
			newCondition =
				IRExpr_Binop(
					Iop_Or1,
					newCondition,
					justPathConstraint);
			newCondition = simplifyIRExpr(newCondition,
						      *opt);
			return true;
		}
		bool survive(IRExpr *, IRExpr *) { return true; }
		bool escape(IRExpr *, IRExpr *) { return true; }
	} consumer;
	consumer.needsAccAssumptions = true;
	consumer.collectOrderingConstraints = true;
	consumer.newCondition = IRExpr_Const(IRConst_U1(0));
	consumer.opt = &opt;

	VexPtr<StateMachine, &ir_heap> combinedMachine;
	combinedMachine = buildCrossProductMachine(probeMachine, storeMachine,
						   oracle, opt);
	combinedMachine =
		optimiseStateMachine(
			combinedMachine,
			opt,
			oracle,
			false,
			token);
	if (!enumEvalPaths(combinedMachine, initialStateCondition, oracle, opt, consumer, token))
		return;

	result = simplifyIRExpr(
		IRExpr_Binop(
			Iop_Or1,
			result,
			consumer.newCondition),
		opt);
}

IRExpr *
findHappensBeforeRelations(const VexPtr<CrashSummary, &ir_heap> &summary,
			   const VexPtr<OracleInterface> &oracle,
			   const AllowableOptimisations &opt,
			   GarbageCollectionToken token)
{
	__set_profiling(findHappensBeforeRelations);
	VexPtr<IRExpr, &ir_heap> res(IRExpr_Const(IRConst_U1(0)));
	VexPtr<StateMachine, &ir_heap> probeMachine(summary->loadMachine);
	VexPtr<StateMachine, &ir_heap> storeMachine(summary->storeMachine);
	VexPtr<IRExpr, &ir_heap> assumption(summary->verificationCondition);
	findHappensBeforeRelations(probeMachine, storeMachine, res, oracle, assumption, opt, token);

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

	StateMachineTransformer::rewriteMachine(machine, rewriteRules, false);
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
				neworigin);
}

IRExpr *
writeMachineSuitabilityConstraint(const VexPtr<StateMachine, &ir_heap> &writeMachine,
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
	combinedMachine = concatenateStateMachines(
		writeMachine,
		readMachine);
	combinedMachine->assertAcyclic();
	combinedMachine = optimiseStateMachine(combinedMachine,
					       opt
					          .enableassumeExecutesAtomically()
					          .enableignoreSideEffects()
					          .enableassumeNoInterferingStores()
					          .enablenoExtend(),
					       oracle,
					       true,
					       token);
	if (combinedMachine->root == StateMachineUnreached::get()) {
		/* This means that running the store machine and then
		   running the load machine is guaranteed to never
		   survive.  That tells us that the store machine is
		   never suitable, so the suitability constraint is
		   just 0. */
		return IRExpr_Const(IRConst_U1(0));
	}
	return survivalConstraintIfExecutedAtomically(
		combinedMachine,
		assumption,
		oracle,
		false,
		opt,
		token);
}

/* Build an expression P such that if P is true then running
   @readMachine and @writeMachine in parallel might crash, for some
   possible interleaving.  P itself does not include any
   happens-before constraints, so it's not sufficient to prove that
   the machine will definitely crash.  It's just sufficient to prove
   that there is some interleaving which leads to a crash. */
IRExpr *
getCrossMachineCrashRequirement(
	const VexPtr<StateMachine, &ir_heap> &readMachine,
	const VexPtr<StateMachine, &ir_heap> &writeMachine,
	const VexPtr<OracleInterface> &oracle,
	const VexPtr<IRExpr, &ir_heap> &assumption,
	const AllowableOptimisations &optIn,
	GarbageCollectionToken token)
{
	__set_profiling(getCrossMachineCrashRequirement);

	AllowableOptimisations opt =
		optIn
		    .enableassumeExecutesAtomically()
		    .enableignoreSideEffects()
		    .enableassumeNoInterferingStores()
		    .enablenoExtend();
	VexPtr<StateMachine, &ir_heap> crossProductMachine(
		buildCrossProductMachine(
			readMachine,
			writeMachine,
			oracle,
			opt));
	crossProductMachine =
		optimiseStateMachine(
			crossProductMachine,
			opt,
			oracle,
			false,
			token);

	struct : public EvalPathConsumer {
		VexPtr<IRExpr, &ir_heap> accumulator;
		const AllowableOptimisations *opt;

		bool crash(IRExpr *, IRExpr *accAssumption) {
			if (accumulator) {
				accumulator =
					IRExpr_Binop(
						Iop_Or1,
						accumulator,
						accAssumption);
				accumulator = simplifyIRExpr(
					accumulator,
					*opt);
			} else {
				accumulator = accAssumption;
			}
			return true;
		}
		bool survive(IRExpr *, IRExpr *) {
			return true;
		}
		bool escape(IRExpr *, IRExpr *) {
			return true;
		}
	} consumer;
	consumer.opt = &opt;
	consumer.needsAccAssumptions = true;

	enumEvalPaths(crossProductMachine, assumption, oracle, opt, consumer, token);

	if (TIMEOUT)
		return NULL;

	return consumer.accumulator;
}
