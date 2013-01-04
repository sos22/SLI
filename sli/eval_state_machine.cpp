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
#include "bdd.hpp"
#include "ssa.hpp"

#ifdef NDEBUG
#define debug_survival_constraint false
#else
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
		exprbdd *val8;
		exprbdd *val16;
		exprbdd *val32;
		exprbdd *val64;
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

	IRExpr *setTemporary(SMScopes *scopes, const threadAndRegister &reg, IRExpr *inp, const IRExprOptimisations &opt);
	bbdd *setTemporary(SMScopes *scopes, const threadAndRegister &reg, bbdd *inp,
			   const IRExprOptimisations &opt,
			   std::map<bbdd *, bbdd *> &memo);
	exprbdd *setTemporary(SMScopes *scopes, const threadAndRegister &reg, exprbdd *inp,
			      const IRExprOptimisations &opt,
			      std::map<exprbdd *, exprbdd *> &memo);
	bbdd *setTemporary(SMScopes *scopes, const threadAndRegister &reg, bbdd *inp,
			   const IRExprOptimisations &opt) {
		std::map<bbdd *, bbdd *> memo;
		return setTemporary(scopes, reg, inp, opt, memo);
	}
	exprbdd *setTemporary(SMScopes *scopes, const threadAndRegister &reg, exprbdd *inp, const IRExprOptimisations &opt) {
		std::map<exprbdd *, exprbdd *> memo;
		return setTemporary(scopes, reg, inp, opt, memo);
	}
public:
	exprbdd *register_value(SMScopes *scopes,
				const threadAndRegister &reg,
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
				return exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_16to8, rv.val16);
			else if (rv.val32)
				return exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_32to8, rv.val32);
			else if (rv.val64)
				return exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_64to8, rv.val64);
			else
				return NULL;
		case Ity_I16:
			if (rv.val8) {
				exprbdd *acc = exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_8Uto16, rv.val8);
				exprbdd *mask = exprbdd::var(&scopes->exprs, &scopes->bools, IRExpr_Const_U16(0xff00));
				exprbdd *hi;
				if (rv.val16) {
					hi = rv.val16;
				} else if (rv.val32) {
					hi = exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_32to16, rv.val32);
				} else if (rv.val64) {
					hi = exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_64to16, rv.val64);
				} else {
					hi = exprbdd::var(&scopes->exprs, &scopes->bools, IRExpr_Get(reg, type));
				}
				acc = exprbdd::binop(
					&scopes->exprs,
					&scopes->bools,
					Iop_Or16,
					acc,
					exprbdd::binop(
						&scopes->exprs,
						&scopes->bools,
						Iop_And16,
						hi,
						mask));
				rv.val8 = NULL;
				rv.val16 = acc;
				return acc;
			} else if (rv.val16) {
				return rv.val16;
			} else if (rv.val32) {
				return exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_32to16, rv.val32);
			} else if (rv.val64) {
				return exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_64to16, rv.val64);
			} else {
				return NULL;
			}
		case Ity_I32: {
			exprbdd *res = NULL;
			unsigned mask = ~0;
			if (rv.val8) {
				res = exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_8Uto32, rv.val8);
				mask = ~0xff;
			}
			if (rv.val16) {
				exprbdd *a = exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_16Uto32, rv.val16);
				if (res)
					res = exprbdd::binop(
						&scopes->exprs,
						&scopes->bools,
						Iop_Or32,
						res,
						exprbdd::binop(
							&scopes->exprs,
							&scopes->bools,
							Iop_And32,
							a,
							exprbdd::var(
								&scopes->exprs,
								&scopes->bools,
								IRExpr_Const_U32(mask))));
				else
					res = a;
				mask = ~0xffff;
			}
			exprbdd *parent;
			if (rv.val32) {
				parent = rv.val32;
			} else if (rv.val64) {
				parent = exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_64to32, rv.val64);
			} else if (res) {
				parent = exprbdd::var(&scopes->exprs, &scopes->bools, IRExpr_Get(reg, Ity_I32));
			} else {
				parent = NULL;
			}

			if (res)
				res = exprbdd::binop(
					&scopes->exprs,
					&scopes->bools,
					Iop_Or32,
					res,
					exprbdd::binop(
						&scopes->exprs,
						&scopes->bools,
						Iop_And32,
						parent,
						exprbdd::var(&scopes->exprs, &scopes->bools, IRExpr_Const_U32(mask))));
			else
				res = parent;
			rv.val8 = NULL;
			rv.val16 = NULL;
			rv.val32 = res;
			return res;
		}

		case Ity_I64: {
			exprbdd *res = NULL;
			unsigned long mask = ~0ul;
			if (rv.val8) {
				res = exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_8Uto64, rv.val8);
				mask = ~0xfful;
			}
			if (rv.val16) {
				exprbdd *a = exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_16Uto64, rv.val16);
				if (res)
					res = exprbdd::binop(
						&scopes->exprs,
						&scopes->bools,
						Iop_Or64,
						res,
						exprbdd::binop(
							&scopes->exprs,
							&scopes->bools,
							Iop_And64,
							a,
							exprbdd::var(&scopes->exprs, &scopes->bools, IRExpr_Const_U64(mask))));
				else
					res = a;
				mask = ~0xfffful;
			}
			if (rv.val32) {
				exprbdd *a = exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_32Uto64, rv.val32);
				if (res)
					res = exprbdd::binop(
						&scopes->exprs,
						&scopes->bools,
						Iop_Or64,
						res,
						exprbdd::binop(
							&scopes->exprs,
							&scopes->bools,
							Iop_And64,
							a,
							exprbdd::var(&scopes->exprs, &scopes->bools, IRExpr_Const_U64(mask))));
				else
					res = a;
				mask = ~0xfffffffful;
			}
			if (rv.val64) {
				if (res)
					res = exprbdd::binop(
						&scopes->exprs,
						&scopes->bools,
						Iop_Or64,
						res,
						exprbdd::binop(
							&scopes->exprs,
							&scopes->bools,
							Iop_And64,
							rv.val64,
							exprbdd::var(&scopes->exprs, &scopes->bools, IRExpr_Const_U64(mask))));
				else
					res = rv.val64;
			} else {
				if (res)
					res = exprbdd::binop(
						&scopes->exprs,
						&scopes->bools,
						Iop_Or64,
						res,
						exprbdd::binop(
							&scopes->exprs,
							&scopes->bools,
							Iop_And64,
							exprbdd::var(&scopes->exprs, &scopes->bools, IRExpr_Get(reg, Ity_I64)),
							exprbdd::var(&scopes->exprs, &scopes->bools, IRExpr_Const_U64(mask))));
				
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
	void set_register(SMScopes *scopes,
			  const threadAndRegister &reg,
			  exprbdd *e,
			  bbdd **assumption,
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
			set_register(scopes, reg, exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_128to64, e), assumption, opt);
			return;
		default:
			abort();
		}

		if (reg.isTemp())
			*assumption = setTemporary(scopes, reg, *assumption, opt);

		bump_register_in_assignment_order(reg);
	}
	void eval_phi(SMScopes *scopes,
		      StateMachineSideEffectPhi *phi,
		      bbdd **assumption,
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
						*assumption = setTemporary(scopes, phi->reg, *assumption, opt);
					bump_register_in_assignment_order(phi->reg);
					return;
				}
			}
		}
		/* If none of the phi inputs have been assigned to
		   then the phi doesn't matter, so just pick some
		   arbitrary constants. */
		IRExpr *c;

		/* shut compiler up */
		c = (IRExpr *)0xf001;

		switch (phi->ty) {
#define do_ty(n)						\
			case Ity_I ## n :			\
				c = IRExpr_Const_U ## n(0);	\
				break
			do_ty(1);
			do_ty(8);
			do_ty(16);
			do_ty(32);
			do_ty(64);
#undef do_ty
		case Ity_I128:
			c = IRExpr_Const_U128(0, 0);
			break;
		case Ity_INVALID:
			abort();
			break;
		}
		set_register(scopes, phi->reg,
			     exprbdd::var(&scopes->exprs, &scopes->bools, c),
			     assumption, opt);
		return;
	}

	bbdd *specialiseIRExpr(SMScopes *, bbdd *iex);
	smrbdd *specialiseIRExpr(SMScopes *, smrbdd *iex);
	exprbdd *specialiseIRExpr(SMScopes *, exprbdd *iex);
	void visit(HeapVisitor &hv) {
		for (auto it = registers.begin();
		     it != registers.end();
		     it++) {
			it->second.visit(hv);
		}
	}
};

/* Rewrite @e now that we know the value of @reg */
bbdd *
threadState::setTemporary(SMScopes *scopes, const threadAndRegister &reg, bbdd *e, const IRExprOptimisations &opt,
			  std::map<bbdd *, bbdd *> &memo)
{
	if (e->isLeaf)
		return e;
	auto it_did_insert = memo.insert(std::pair<bbdd *, bbdd *>(e, NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;
	IRExpr *cond = setTemporary(scopes, reg, e->internal().condition, opt);
	bbdd *trueB = setTemporary(scopes, reg, e->internal().trueBranch, opt, memo);
	bbdd *falseB = setTemporary(scopes, reg, e->internal().falseBranch, opt, memo);
	bbdd *res;
	if (cond == e->internal().condition && trueB == e->internal().trueBranch && falseB == e->internal().falseBranch)
		res = e;
	else
		res = bbdd::ifelse(&scopes->bools,
				   bbdd::var(&scopes->bools, cond),
				   trueB,
				   falseB);
	it->second = res;
	return res;
}
exprbdd *
threadState::setTemporary(SMScopes *scopes, const threadAndRegister &reg, exprbdd *e, const IRExprOptimisations &opt,
			  std::map<exprbdd *, exprbdd *> &memo)
{
	if (e->isLeaf)
		return exprbdd::var(&scopes->exprs, &scopes->bools,
				    setTemporary(scopes, reg, e->leaf(), opt));
	auto it_did_insert = memo.insert(std::pair<exprbdd *, exprbdd *>(e, NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;
	IRExpr *cond = setTemporary(scopes, reg, e->internal().condition, opt);
	exprbdd *trueB = setTemporary(scopes, reg, e->internal().trueBranch, opt, memo);
	exprbdd *falseB = setTemporary(scopes, reg, e->internal().falseBranch, opt, memo);
	exprbdd *res;
	if (cond == e->internal().condition && trueB == e->internal().trueBranch && falseB == e->internal().falseBranch)
		res = e;
	else
		res = exprbdd::ifelse(&scopes->exprs,
				      bbdd::var(&scopes->bools, cond),
				      trueB,
				      falseB);
	it->second = res;
	return res;
}
IRExpr *
threadState::setTemporary(SMScopes *scopes, const threadAndRegister &reg, IRExpr *e, const IRExprOptimisations &opt)
{
	struct _ : public IRExprTransformer {
		const threadAndRegister &reg;
		threadState *_this;
		SMScopes *_scopes;
		_(const threadAndRegister &_reg, threadState *__this, SMScopes *__scopes)
			: reg(_reg), _this(__this), _scopes(__scopes)
		{}
		IRExpr *transformIex(IRExprGet *ieg) {
			if (ieg->reg == reg)
				return exprbdd::to_irexpr(_this->register_value(_scopes, reg, ieg->ty));
			else
				return IRExprTransformer::transformIex(ieg);
		}
	} doit(reg, this, scopes);
	return simplifyIRExpr(doit.doit(e), opt);
}

class SpecialiseIRExpr : public IRExprTransformer {
	threadState &state;
	SMScopes *scopes;
	IRExpr *transformIex(IRExprGet *e) {
		exprbdd *e2 = state.register_value(scopes, e->reg, e->type());
		if (e2)
			return coerceTypes(e->type(), exprbdd::to_irexpr(e2));
		return IRExprTransformer::transformIex(e);
	}
public:
	SpecialiseIRExpr(threadState &_state, SMScopes *_scopes)
		: state(_state), scopes(_scopes)
	{}
};
bbdd *
threadState::specialiseIRExpr(SMScopes *scopes, bbdd *bbdd)
{
	SpecialiseIRExpr s(*this, scopes);
	return s.transform_bbdd(&scopes->bools, bbdd);
}
smrbdd *
threadState::specialiseIRExpr(SMScopes *scopes, smrbdd *smrbdd)
{
	SpecialiseIRExpr s(*this, scopes);
	return s.transform_smrbdd(&scopes->bools, &scopes->smrs, smrbdd);
}
exprbdd *
threadState::specialiseIRExpr(SMScopes *scopes, exprbdd *smrbdd)
{
	SpecialiseIRExpr s(*this, scopes);
	return s.transform_exprbdd(&scopes->bools, &scopes->exprs, smrbdd);
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

class EvalContext : public GcCallback<&ir_heap> {
	enum trool { tr_true, tr_false, tr_unknown };
public:
	bbdd *pathConstraint;
private:
	threadState state;
	memLogT memlog;
public:
	bool atomic;
	StateMachineState *currentState;
private:
	void runGc(HeapVisitor &hv) {
		state.visit(hv);
		memlog.visit(hv);
		hv(currentState);
		hv(pathConstraint);
	}

	trool evalBooleanExpression(SMScopes *scopes, bbdd *what, bbdd **simplified, const IRExprOptimisations &opt);
	void evalSideEffect(SMScopes *scopes, const MaiMap &decode, StateMachine *sm, OracleInterface *oracle,
			    smrbdd *&result, StateMachineRes unreachedIs, std::vector<EvalContext> &pendingStates,
			    StateMachineSideEffect *smse, const IRExprOptimisations &opt);

	EvalContext(const EvalContext &o, StateMachineState *sms)
		: pathConstraint(o.pathConstraint),
		  state(o.state),
		  memlog(o.memlog),
		  atomic(o.atomic),
		  currentState(sms)
	{
	}
	/* Create a new context which is like this one, but with an
	   extra assumption. */
	EvalContext(SMScopes *scopes,
		    const EvalContext &o,
		    StateMachineState *sms,
		    bbdd *assume)
		: pathConstraint(bbdd::And(&scopes->bools, o.pathConstraint, assume)),
		  state(o.state),
		  memlog(o.memlog),
		  atomic(o.atomic),
		  currentState(sms)
	{
	}
	enum evalStateMachineSideEffectRes {
		esme_normal,
		esme_escape,
		esme_ignore_path
	};
	evalStateMachineSideEffectRes evalStateMachineSideEffect(
		SMScopes *scopes,
		const MaiMap &decode,
		StateMachine *thisMachine,
		StateMachineSideEffect *smse,
		NdChooser &chooser,
		OracleInterface *oracle,
		const IRExprOptimisations &opt);
	bool expressionIsTrue(SMScopes *scopes, bbdd *exp, NdChooser &chooser, const IRExprOptimisations &opt);
	bool expressionIsTrue(SMScopes *scopes, exprbdd *exp, NdChooser &chooser, const IRExprOptimisations &opt);
	bool evalExpressionsEqual(SMScopes *scopes, exprbdd *exp1, exprbdd *exp2, NdChooser &chooser, const IRExprOptimisations &opt);
public:
	void advance(SMScopes *scopes,
		     const MaiMap &decode,
		     OracleInterface *oracle,
		     const IRExprOptimisations &opt,
		     std::vector<EvalContext> &pendingStates,
		     StateMachineRes unreachedIs,
		     StateMachine *sm,
		     smrbdd *&result);
	EvalContext(StateMachine *sm, bbdd *_pathConstraint)
		: pathConstraint(_pathConstraint),
		  atomic(false),
		  currentState(sm->root)
	{
		assert(pathConstraint);
	}
};

bool
EvalContext::expressionIsTrue(SMScopes *scopes, bbdd *exp, NdChooser &chooser, const IRExprOptimisations &opt)
{
	if (TIMEOUT)
		return true;
	bbdd *simplified;
	switch (evalBooleanExpression(scopes, exp, &simplified, opt)) {
	case tr_true:
		return true;
	case tr_false:
		return false;
	case tr_unknown:
		/* Can't prove it one way or another.  Use the
		   non-deterministic chooser to guess. */
		if (chooser.nd_choice(2) == 0) {
			pathConstraint =
				bbdd::And(
					&scopes->bools,
					simplified,
					pathConstraint);
			return true;
		} else {
			pathConstraint =
				bbdd::And(
					&scopes->bools,
					bbdd::invert(&scopes->bools, simplified),
					pathConstraint);
			return false;
		}
	}
	abort();
}

bool
EvalContext::expressionIsTrue(SMScopes *scopes, exprbdd *exp, NdChooser &chooser, const IRExprOptimisations &opt)
{
	return expressionIsTrue(scopes, exprbdd::to_bbdd(&scopes->bools, exp), chooser, opt);
}

bool
EvalContext::evalExpressionsEqual(SMScopes *scopes, exprbdd *exp1, exprbdd *exp2, NdChooser &chooser, const IRExprOptimisations &opt)
{
	return expressionIsTrue(
		scopes,
		exprbdd::binop(
			&scopes->exprs,
			&scopes->bools,
			Iop_CmpEQ64,
			exp1,
			exp2),
		chooser,
		opt);
}

EvalContext::evalStateMachineSideEffectRes
EvalContext::evalStateMachineSideEffect(SMScopes *scopes,
					const MaiMap &decode,
					StateMachine *thisMachine,
					StateMachineSideEffect *smse,
					NdChooser &chooser,
					OracleInterface *oracle,
					const IRExprOptimisations &opt)
{
	exprbdd *addr = NULL;
	if (smse->type == StateMachineSideEffect::Load ||
	    smse->type == StateMachineSideEffect::Store) {
		StateMachineSideEffectMemoryAccess *smsema =
			dynamic_cast<StateMachineSideEffectMemoryAccess *>(smse);
		assert(smsema);
		addr = state.specialiseIRExpr(scopes, smsema->addr);
		exprbdd *a = exprbdd::unop(
				    &scopes->exprs,
				    &scopes->bools,
				    Iop_BadPtr,
				    addr);
		if (TIMEOUT)
			return esme_escape;
		assert(a);
		if (expressionIsTrue(scopes, a, chooser, opt))
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
				 state.specialiseIRExpr(scopes, addr),
				 state.specialiseIRExpr(scopes, smses->data))));
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
			if (evalExpressionsEqual(scopes, smses->addr, addr, chooser, opt)) {
				satisfier = smses;
				satisfierMachine = it->first;
				break;
			}
		}
		exprbdd *val;
		if (satisfier) {
			val = exprbdd::coerceTypes(
				&scopes->exprs,
				&scopes->bools,
				smsel->type,
				satisfier->data);
		} else {
			val = exprbdd::load(&scopes->exprs, &scopes->bools, smsel->type, addr);
		}
		if (!TIMEOUT)
			state.set_register(scopes, smsel->target, val, &pathConstraint, opt);
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec =
			dynamic_cast<StateMachineSideEffectCopy *>(smse);
		assert(smsec);
		state.set_register(scopes,
				   smsec->target,
				   state.specialiseIRExpr(scopes, smsec->value),
				   &pathConstraint,
				   opt);
		break;
	}
	case StateMachineSideEffect::Unreached:
		abort();
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(smse);
		if (expressionIsTrue(
			    scopes,
			    smseaf->value,
			    chooser,
			    opt)) {
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
		state.eval_phi(scopes, smsep, &pathConstraint, opt);
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

	case StateMachineSideEffect::ImportRegister: {
		StateMachineSideEffectImportRegister *p =
			(StateMachineSideEffectImportRegister *)smse;
		state.set_register(scopes,
				   p->reg,
				   exprbdd::var(
					   &scopes->exprs,
					   &scopes->bools,
					   IRExpr_Get(threadAndRegister::reg(p->tid, p->vex_offset, -1), Ity_I64)),
				   &pathConstraint,
				   opt);
		/* The only use we make of a PointerAliasing side
		   effect is to say that things which aliasing says
		   are definitely valid pointers really are definitely
		   valid pointers.  Todo: could do much better
		   here. */
		if (!p->set.mightBeNonPointer() &&
		    expressionIsTrue(
			    scopes,
			    bbdd::var(&scopes->bools, IRExpr_Unop(
					      Iop_BadPtr,
					      IRExpr_Get(p->reg, Ity_I64))),
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
EvalContext::evalBooleanExpression(SMScopes *scopes, bbdd *what, bbdd **simplified, const IRExprOptimisations &opt)
{
	bbdd *simplifiedCondition =
		bbdd::assume(
			&scopes->bools,
			what,
			pathConstraint);
	if (!simplifiedCondition) {
		/* @what is a contradiction when combined with
		 * @pathConstraint.  That means we can say whatever we
		 * like and it won't actually matter. */
		return tr_true;
	}
	simplifiedCondition = simplifyBDD(&scopes->bools, simplifiedCondition, opt);
	if (TIMEOUT) {
		/* Guess; we'll ignore the result, anyway. */
		return tr_true;
	}
	if (simplifiedCondition->isLeaf) {
		if (simplifiedCondition->leaf())
			return tr_true;
		else
			return tr_false;
	}

	/* Give up on this one and just accept that we don't know. */
	*simplified = simplifiedCondition;
	return tr_unknown;
}

void
EvalContext::evalSideEffect(SMScopes *scopes, const MaiMap &decode, StateMachine *sm, OracleInterface *oracle,
			    smrbdd *&result, StateMachineRes unreached, std::vector<EvalContext> &pendingStates,
			    StateMachineSideEffect *smse, const IRExprOptimisations &opt)
{
	NdChooser chooser;

	do {
		EvalContext newContext(*this);
		evalStateMachineSideEffectRes res =
			newContext.evalStateMachineSideEffect(scopes,
							      decode,
							      sm,
							      smse,
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
			result = smrbdd::ifelse(&scopes->smrs,
						newContext.pathConstraint,
						scopes->smrs.cnst(unreached),
						result);
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
EvalContext::advance(SMScopes *scopes,
		     const MaiMap &decode,
		     OracleInterface *oracle,
		     const IRExprOptimisations &opt,
		     std::vector<EvalContext> &pendingStates,
		     StateMachineRes unreachedIs,
		     StateMachine *sm,
		     smrbdd *&result)
{
	switch (currentState->type) {
	case StateMachineState::Terminal: {
		auto smt = (StateMachineTerminal *)currentState;
		result = smrbdd::ifelse(
			&scopes->smrs,
			pathConstraint,
			state.specialiseIRExpr(
				scopes,
				smrbdd::replaceTerminal(
					&scopes->smrs,
					smr_unreached,
					unreachedIs,
					smt->res)),
			result);
		return;
	}
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)currentState;
		currentState = sme->target;
		if (sme->sideEffect) {
			evalSideEffect(scopes, decode, sm, oracle, result,
				       unreachedIs, pendingStates,
				       sme->sideEffect, opt);
		} else {
			pendingStates.push_back(*this);
		}
		return;
	}
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)currentState;
		bbdd *cond = state.specialiseIRExpr(scopes, smb->condition);
		bbdd *scond;
		trool res = evalBooleanExpression(scopes, cond, &scond, opt);
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
							scopes,
							*this,
							smb->falseTarget,
							bbdd::invert(
								&scopes->bools,
								scond)));
			pendingStates.push_back(EvalContext(
							scopes,
							*this,
							smb->trueTarget,
							scond));
			break;
		}
		return;
	}
	}
	abort();
}

static smrbdd *
enumEvalPaths(SMScopes *scopes,
	      const VexPtr<MaiMap, &ir_heap> &decode,
	      const VexPtr<StateMachine, &ir_heap> &sm,
	      const VexPtr<bbdd, &ir_heap> &assumption,
	      const VexPtr<OracleInterface> &oracle,
	      const IRExprOptimisations &opt,
	      StateMachineRes unreachedIs,
	      GarbageCollectionToken &token,
	      bool loud = false)
{
	int cntr = 0;
	std::vector<EvalContext> pendingStates;
	VexPtr<smrbdd, &ir_heap> result;

	result = scopes->smrs.cnst(unreachedIs);

	pendingStates.push_back(EvalContext(sm, assumption ? assumption.get() : scopes->bools.cnst(true)));

	while (!TIMEOUT && !pendingStates.empty()) {
		LibVEX_maybe_gc(token);

		EvalContext ctxt(pendingStates.back());
		pendingStates.pop_back();
		ctxt.advance(scopes, *decode, oracle, opt, pendingStates, unreachedIs, sm, result);
		if (loud && cntr++ % 100 == 0)
			printf("Processed %d states; %zd in queue\n", cntr, pendingStates.size());
	}
	return result;
}

static bbdd *
_survivalConstraintIfExecutedAtomically(SMScopes *scopes,
					const VexPtr<MaiMap, &ir_heap> &mai,
					const VexPtr<StateMachine, &ir_heap> &sm,
					VexPtr<bbdd, &ir_heap> assumption,
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
		       assumption ? "..." : "<null>",
		       escapingStatesSurvive ? "true" : "false",
		       wantCrash ? "true" : "false",
		       opt.name());
		if (assumption)
			assumption->prettyPrint(stdout);
		printStateMachine(sm, stdout);
	}

	smrbdd *smr = enumEvalPaths(scopes, mai, sm, assumption, oracle, opt,
				    escapingStatesSurvive ? smr_survive : smr_crash,
				    token);
	if (!smr)
		return NULL;
	std::map<StateMachineRes, bbdd *> selectors(smrbdd::to_selectors(&scopes->bools, smr));
	bbdd *crashIf, *surviveIf, *unreachedIf;
	if (selectors.count(smr_crash))
		crashIf = selectors[smr_crash];
	else
		crashIf = scopes->bools.cnst(false);
	if (selectors.count(smr_survive))
		surviveIf = selectors[smr_survive];
	else
		surviveIf = scopes->bools.cnst(false);
	if (selectors.count(smr_unreached))
		unreachedIf = selectors[smr_unreached];
	else
		unreachedIf = scopes->bools.cnst(false);
	if (escapingStatesSurvive)
		surviveIf = bbdd::Or(&scopes->bools, surviveIf, unreachedIf);
	else
		crashIf = bbdd::Or(&scopes->bools, crashIf, unreachedIf);
	bbdd *resBdd;
	if (wantCrash)
		resBdd = crashIf;
	else
		resBdd = surviveIf;

	if (debug_survival_constraint) {
		printf("%s: result:", __func__);
		resBdd->prettyPrint(stdout);
	}
	
	if (TIMEOUT)
		return NULL;
	return resBdd;
}

/* Assume that @sm executes atomically.  Figure out a constraint on
   the initial state which will lead to it not crashing. */
bbdd *
survivalConstraintIfExecutedAtomically(SMScopes *scopes,
				       const VexPtr<MaiMap, &ir_heap> &mai,
				       const VexPtr<StateMachine, &ir_heap> &sm,
				       const VexPtr<bbdd, &ir_heap> &assumption,
				       const VexPtr<OracleInterface> &oracle,
				       bool escapingStatesSurvive,
				       const IRExprOptimisations &opt,
				       GarbageCollectionToken token)
{
	return _survivalConstraintIfExecutedAtomically(
		scopes,
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
bbdd *
crashingConstraintIfExecutedAtomically(SMScopes *scopes,
				       const VexPtr<MaiMap, &ir_heap> &mai,
				       const VexPtr<StateMachine, &ir_heap> &sm,
				       const VexPtr<bbdd, &ir_heap> &assumption,
				       const VexPtr<OracleInterface> &oracle,
				       bool escapingStatesSurvive,
				       const IRExprOptimisations &opt,
				       GarbageCollectionToken token)
{
	return _survivalConstraintIfExecutedAtomically(
		scopes,
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
		case StateMachineSideEffect::ImportRegister:
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
buildCrossProductMachine(SMScopes *scopes,
			 const MaiMap &maiIn,
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
				bool pia =
					crossState.probe_issued_access ||
					(crossState.p->getSideEffect() &&
					 (crossState.p->getSideEffect()->type == StateMachineSideEffect::Store ||
					  crossState.p->getSideEffect()->type == StateMachineSideEffect::Load));
				std::vector<StateMachineState **> targets;
				res->targets(targets);
				for (auto it = targets.begin(); it != targets.end(); it++) {
					pendingRelocs.push_back(
						relocT(*it,
						       crossStateT(
							       **it,
							       crossState.s,
							       crossState.store_issued_store,
							       pia,
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
				bool sis =
					crossState.store_issued_store ||
					(crossState.s->getSideEffect() &&
					 crossState.s->getSideEffect()->type == StateMachineSideEffect::Store);
				std::vector<StateMachineState **> targets;
				res->targets(targets);
				for (auto it = targets.begin(); it != targets.end(); it++) {
					pendingRelocs.push_back(
						relocT(*it,
						       crossStateT(
							       crossState.p,
							       **it,
							       sis,
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
				newState = new StateMachineTerminal(
					crossState.p->dbg_origin,
					crossState.store_issued_store ?
						((StateMachineTerminal *)crossState.p)->res :
						scopes->smrs.cnst(smr_unreached));
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
				newState = new StateMachineTerminal(
					crossState.s->dbg_origin,
					scopes->smrs.cnst(smr_unreached));
				if (crossState.probe_issued_access) {
					std::map<StateMachineRes, bbdd *> selectors(
						smrbdd::to_selectors(
							&scopes->bools,
							((StateMachineTerminal *)crossState.s)->res));
					if (selectors.count(smr_crash))
						newState =
							new StateMachineBifurcate(
								crossState.s->dbg_origin,
								selectors[smr_crash],
								advanceProbeMachine(crossState, pendingRelocs),
								newState);
				}
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
							bbdd::invert(
								&scopes->bools,
								exprbdd::to_bbdd(
									&scopes->bools,
									exprbdd::binop(
										&scopes->exprs,
										&scopes->bools,
										Iop_CmpEQ64,
										probe_access->addr,
										store_access->addr))),
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
					bbdd::var(&scopes->bools, fv),
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
        return convertToSSA(scopes, new StateMachine(crossMachineRoot, cfg_roots));
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

bbdd *
crossProductSurvivalConstraint(SMScopes *scopes,
			       const VexPtr<StateMachine, &ir_heap> &probeMachine,
			       const VexPtr<StateMachine, &ir_heap> &storeMachine,
			       const VexPtr<OracleInterface> &oracle,
			       const VexPtr<bbdd, &ir_heap> &initialStateCondition,
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
			scopes,
			*mai,
			stripUninterpretableAnnotations(probeMachine),
			stripUninterpretableAnnotations(storeMachine),
			oracle,
			decode.get(),
			&fake_cntr,
			opt));
	if (!crossProductMachine)
		return NULL;
	crossProductMachine =
		optimiseStateMachine(
			scopes,
			decode,
			crossProductMachine,
			opt,
			oracle,
			true,
			token);

	return survivalConstraintIfExecutedAtomically(
		scopes,
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
   <unreached> if the first machine branches to <survive>.  The idea
   is that the composite machine runs the first machine to completion
   and then, if that predicts a crash, runs the second machine to
   completion. */
struct concat_machines_state {
	bool in_first_machine;
	StateMachineState *state;
	bool operator<(const concat_machines_state &o) const {
		if (in_first_machine < o.in_first_machine)
			return true;
		if (in_first_machine > o.in_first_machine)
			return false;
		return state < o.state;
	}
	concat_machines_state(bool ifm, StateMachineState *s)
		: in_first_machine(ifm), state(s)
	{}
};
static StateMachine *
concatenateStateMachinesCrashing(SMScopes *scopes, const StateMachine *machine, const StateMachine *to)
{
	typedef std::pair<StateMachineState **, concat_machines_state> relocT;
	std::map<concat_machines_state, StateMachineState *> newStates;
	std::vector<relocT> relocs;
	StateMachineState *newRoot = NULL;
	relocs.push_back(relocT(&newRoot, concat_machines_state(true, machine->root)));
	while (!relocs.empty()) {
		relocT reloc(relocs.back());
		relocs.pop_back();
		auto it_did_insert = newStates.insert(
			std::pair<concat_machines_state, StateMachineState *>
			(reloc.second, (StateMachineState *)NULL));
		auto it = it_did_insert.first;
		auto did_insert = it_did_insert.second;
		if (did_insert) {
			StateMachineState *inpState = reloc.second.state;
			switch (inpState->type) {
			case StateMachineState::Terminal: {
				StateMachineTerminal *inp_smt =
					(StateMachineTerminal *)inpState;
				if (reloc.second.in_first_machine) {
					std::map<StateMachineRes, bbdd *> sel(smrbdd::to_selectors(&scopes->bools, inp_smt->res));
					StateMachineState *unreached =
						new StateMachineTerminal(
							inp_smt->dbg_origin,
							scopes->smrs.cnst(smr_unreached));
					if (sel.count(smr_crash)) {
						StateMachineBifurcate *smb =
							new StateMachineBifurcate(
								inp_smt->dbg_origin,
								sel[smr_crash],
								NULL,
								unreached);
						relocs.push_back(
							relocT(&smb->trueTarget,
							       concat_machines_state(
								       false,
								       to->root)));
						it->second = smb;
					} else {
						it->second = unreached;
					}
				} else {
					it->second = new StateMachineTerminal(
						inp_smt->dbg_origin,
						inp_smt->res);
				}
				break;
			}
			case StateMachineState::Bifurcate: {
				StateMachineBifurcate *inp_smb =
					(StateMachineBifurcate *)inpState;
				StateMachineBifurcate *out_smb =
					new StateMachineBifurcate(
						inp_smb->dbg_origin,
						inp_smb->condition,
						NULL,
						NULL);
				relocs.push_back(
					relocT(&out_smb->trueTarget,
					       concat_machines_state(
						       reloc.second.in_first_machine,
						       inp_smb->trueTarget)));
				relocs.push_back(
					relocT(&out_smb->falseTarget,
					       concat_machines_state(
						       reloc.second.in_first_machine,
						       inp_smb->falseTarget)));
				it->second = out_smb;
				break;
			}
			case StateMachineState::SideEffecting: {
				StateMachineSideEffecting *inp_sme =
					(StateMachineSideEffecting *)inpState;
				StateMachineSideEffecting *out_sme =
					new StateMachineSideEffecting(
						inp_sme->dbg_origin,
						inp_sme->sideEffect,
						NULL);
				relocs.push_back(
					relocT(&out_sme->target,
					       concat_machines_state(
						       reloc.second.in_first_machine,
						       inp_sme->target)));
				it->second = out_sme;
				break;
			}
			}
		}
		*reloc.first = it->second;
	}

	std::vector<std::pair<unsigned, const CFGNode *> > cfg_roots(machine->cfg_roots);
	for (auto it = to->cfg_roots.begin(); it != to->cfg_roots.end(); it++) {
		bool already_present = false;
		for (auto it2 = cfg_roots.begin(); !already_present && it2 != cfg_roots.end(); it2++)
			if (*it2 == *it)
				already_present = true;
		if (!already_present)
			cfg_roots.push_back(*it);
	}
	return new StateMachine(newRoot, cfg_roots);
}

bbdd *
writeMachineSuitabilityConstraint(SMScopes *scopes,
				  VexPtr<MaiMap, &ir_heap> &mai,
				  const VexPtr<StateMachine, &ir_heap> &writeMachine,
				  const VexPtr<StateMachine, &ir_heap> &readMachine,
				  const VexPtr<OracleInterface> &oracle,
				  const VexPtr<bbdd, &ir_heap> &assumption,
				  const AllowableOptimisations &opt,
				  GarbageCollectionToken token)
{
	__set_profiling(writeMachineSuitabilityConstraint);

	VexPtr<StateMachine, &ir_heap> combinedMachine;

	writeMachine->assertAcyclic();
	readMachine->assertAcyclic();
	combinedMachine = concatenateStateMachinesCrashing(
		scopes,
		writeMachine,
		readMachine);
	combinedMachine->assertAcyclic();
	combinedMachine = optimiseStateMachine(scopes,
					       mai,
					       combinedMachine,
					       opt
					          .enableassumeExecutesAtomically()
					          .enableignoreSideEffects()
					          .enableassumeNoInterferingStores()
					          .enablenoExtend(),
					       oracle,
					       true,
					       token);
	return survivalConstraintIfExecutedAtomically(
		scopes,
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
void
collectConstraints(SMScopes *scopes,
		   const VexPtr<MaiMap, &ir_heap> &mai,
		   const VexPtr<StateMachine, &ir_heap> &sm,
		   VexPtr<OracleInterface> &oracle,
		   const IRExprOptimisations &opt,
		   std::vector<IRExpr *> &out,
		   GarbageCollectionToken token)
{
	enumEvalPaths(scopes, mai, sm, scopes->bools.cnst(true), oracle, opt, smr_unreached, token, true);
	scopes->ordering.enumVariables(out);
}
