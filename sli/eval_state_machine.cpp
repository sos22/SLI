#include "sli.h"
#include "state_machine.hpp"
#include "oracle.hpp"
#include "eval_state_machine.hpp"
#include "offline_analysis.hpp"
#include "inferred_information.hpp"
#include "intern.hpp"
#include "libvex_prof.hpp"
#include "typesdb.hpp"
#include "allowable_optimisations.hpp"
#include "alloc_mai.hpp"
#include "bdd.hpp"
#include "ssa.hpp"
#include "stacked_cdf.hpp"

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

	void bump_register_in_assignment_order(const threadAndRegister &reg,
					       bool havePhis) {
		if (!havePhis) {
			return;
		}
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
		case Ity_I128:
			/* Cheat and just zero-extend the low 64 bits. */
			return exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_64UtoV128, register_value(scopes, reg, Ity_I64));
		default:
			abort();
		}
	}
	void set_register(SMScopes *scopes,
			  const threadAndRegister &reg,
			  exprbdd *e,
			  bbdd **assumption,
			  bool havePhis,
			  const IRExprOptimisations &opt) {
		if (TIMEOUT)
			return;
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
			set_register(scopes, reg, exprbdd::unop(&scopes->exprs, &scopes->bools, Iop_128to64, e), assumption,
				     havePhis, opt);
			return;
		default:
			abort();
		}

		*assumption = setTemporary(scopes, reg, *assumption, opt);

		bump_register_in_assignment_order(reg, havePhis);
	}
	void eval_phi(SMScopes *scopes,
		      StateMachineSideEffectPhi *phi,
		      bbdd **assumption,
		      bool havePhis,
		      const IRExprOptimisations &opt) {
		if (!havePhis) {
			abort();
		}
		for (auto it = assignmentOrder.rbegin();
		     it != assignmentOrder.rend();
		     it++) {
			for (auto it2 = phi->generations.begin();
			     it2 != phi->generations.end();
			     it2++) {
				if (it2->reg == *it) {
					registers[phi->reg] = registers[*it];
					*assumption = setTemporary(scopes, phi->reg, *assumption, opt);
					bump_register_in_assignment_order(phi->reg, havePhis);
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
			     assumption, havePhis, opt);
		return;
	}

private:
	IRExpr *specialiseIRExpr(SMScopes *scopes, IRExpr *, std::map<IRExpr *, IRExpr *> &memo);
	bbdd *specialiseIRExpr(SMScopes *, bbdd *iex,
			       std::map<bbdd *, bbdd *> &,
			       std::map<IRExpr *, IRExpr *> &);
	smrbdd *specialiseIRExpr(SMScopes *, smrbdd *iex,
				 std::map<smrbdd *, smrbdd *> &,
				 std::map<IRExpr *, IRExpr *> &);
	exprbdd *specialiseIRExpr(SMScopes *, exprbdd *iex,
				  std::map<exprbdd *, exprbdd *> &,
				  std::map<IRExpr *, IRExpr *> &);
public:
	bbdd *specialiseIRExpr(SMScopes *scopes, bbdd *iex) {
		std::map<bbdd *, bbdd *> memo1;
		std::map<IRExpr *, IRExpr *> memo2;
		return specialiseIRExpr(scopes, iex, memo1, memo2);
	}
	smrbdd *specialiseIRExpr(SMScopes *scopes, smrbdd *iex) {
		std::map<smrbdd *, smrbdd *> memo1;
		std::map<IRExpr *, IRExpr *> memo2;
		return specialiseIRExpr(scopes, iex, memo1, memo2);
	}
	exprbdd *specialiseIRExpr(SMScopes *scopes, exprbdd *iex) {
		std::map<exprbdd *, exprbdd *> memo1;
		std::map<IRExpr *, IRExpr *> memo2;
		return specialiseIRExpr(scopes, iex, memo1, memo2);
	}
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
	if (e->isLeaf())
		return e;
	auto it_did_insert = memo.insert(std::pair<bbdd *, bbdd *>(e, (bbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;
	IRExpr *cond = setTemporary(scopes, reg, e->internal().condition, opt);
	bbdd *trueB = setTemporary(scopes, reg, e->internal().trueBranch, opt, memo);
	bbdd *falseB = setTemporary(scopes, reg, e->internal().falseBranch, opt, memo);
	bbdd *res;
	if (cond == e->internal().condition && trueB == e->internal().trueBranch && falseB == e->internal().falseBranch) {
		res = e;
	} else if (cond == e->internal().condition) {
		res = scopes->bools.node(e->internal().condition,
					 e->internal().rank,
					 trueB,
					 falseB);
	} else {
		res = bbdd::ifelse(&scopes->bools,
				   bbdd::var(&scopes->bools, cond),
				   trueB,
				   falseB);
	}
	it->second = res;
	return res;
}
exprbdd *
threadState::setTemporary(SMScopes *scopes, const threadAndRegister &reg, exprbdd *e, const IRExprOptimisations &opt,
			  std::map<exprbdd *, exprbdd *> &memo)
{
	if (e->isLeaf())
		return exprbdd::var(&scopes->exprs, &scopes->bools,
				    setTemporary(scopes, reg, e->leaf(), opt));
	auto it_did_insert = memo.insert(std::pair<exprbdd *, exprbdd *>(e, (exprbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;
	IRExpr *cond = setTemporary(scopes, reg, e->internal().condition, opt);
	exprbdd *trueB = setTemporary(scopes, reg, e->internal().trueBranch, opt, memo);
	exprbdd *falseB = setTemporary(scopes, reg, e->internal().falseBranch, opt, memo);
	exprbdd *res;
	if (cond == e->internal().condition && trueB == e->internal().trueBranch && falseB == e->internal().falseBranch) {
		res = e;
	} else if (cond == e->internal().condition) {
		res = scopes->exprs.node(e->internal().condition,
					 e->internal().rank,
					 trueB,
					 falseB);
	} else {
		res = exprbdd::ifelse(&scopes->exprs,
				      bbdd::var(&scopes->bools, cond),
				      trueB,
				      falseB);
	}
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

IRExpr *
threadState::specialiseIRExpr(SMScopes *scopes, IRExpr *what, std::map<IRExpr *, IRExpr *> &memo)
{
	if (what->tag == Iex_Const ||
	    what->tag == Iex_HappensBefore ||
	    what->tag == Iex_FreeVariable ||
	    what->tag == Iex_EntryPoint ||
	    what->tag == Iex_ControlFlow) {
		return what;
	}

	auto it_did_insert = memo.insert(std::pair<IRExpr *, IRExpr *>(what, (IRExpr *)0xf001));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	switch (what->tag) {
	case Iex_Get: {
		auto g = (IRExprGet *)what;
		exprbdd *r = register_value(scopes, g->reg, g->ty);
		if (r) {
			it->second = exprbdd::to_irexpr(r);
		} else {
			it->second = what;
		}
		break;
	}
	case Iex_GetI: {
		auto g = (IRExprGetI *)what;
		auto ix = specialiseIRExpr(scopes, g->ix, memo);
		if (ix == g->ix) {
			it->second = what;
		} else {
			it->second = IRExprGetI::mk(g, ix);
		}
		break;
	}
	case Iex_Qop: {
		auto g = (IRExprQop *)what;
		auto a = specialiseIRExpr(scopes, g->arg1, memo);
		auto b = specialiseIRExpr(scopes, g->arg2, memo);
		auto c = specialiseIRExpr(scopes, g->arg3, memo);
		auto d = specialiseIRExpr(scopes, g->arg4, memo);
		if (a == g->arg1 && b == g->arg2 &&
		    c == g->arg3 && d == g->arg4) {
			it->second = g;
		} else {
			it->second = IRExprQop::mk(g->op, a, b, c, d);
		}
		break;
	}
	case Iex_Triop: {
		auto g = (IRExprTriop *)what;
		auto a = specialiseIRExpr(scopes, g->arg1, memo);
		auto b = specialiseIRExpr(scopes, g->arg2, memo);
		auto c = specialiseIRExpr(scopes, g->arg3, memo);
		if (a == g->arg1 && b == g->arg2 && c == g->arg3) {
			it->second = g;
		} else {
			it->second = IRExprTriop::mk(g->op, a, b, c);
		}
		break;
	}
	case Iex_Binop: {
		auto g = (IRExprBinop *)what;
		auto a = specialiseIRExpr(scopes, g->arg1, memo);
		auto b = specialiseIRExpr(scopes, g->arg2, memo);
		if (a == g->arg1 && b == g->arg2) {
			it->second = g;
		} else {
			it->second = IRExprBinop::mk(g->op, a, b);
		}
		break;
	}
	case Iex_Unop: {
		auto g = (IRExprUnop *)what;
		auto a = specialiseIRExpr(scopes, g->arg, memo);
		if (a == g->arg) {
			it->second = g;
		} else {
			it->second = IRExprUnop::mk(g->op, a);
		}
		break;
	}

	case Iex_Mux0X:
		/* Shouldn't be present once we've converted to
		 * BDDs */
		abort();

		/* Already handled above */
	case Iex_HappensBefore:
	case Iex_FreeVariable:
	case Iex_EntryPoint:
	case Iex_ControlFlow:
	case Iex_Const:
		abort();

	case Iex_CCall: {
		auto g = (IRExprCCall *)what;
		int nr_args;
		for (nr_args = 0; g->args[nr_args]; nr_args++) {
			/* nop */
		}
		IRExpr *c[nr_args];
		bool realloc = false;
		for (int i = 0; i < nr_args; i++) {
			c[i] = specialiseIRExpr(scopes, g->args[i], memo);
			if (c[i] != g->args[i]) {
				realloc = true;
			}
		}
		if (!realloc) {
			it->second = g;
		} else {
			IRExpr **newArgs = alloc_irexpr_array(nr_args + 1);
			memcpy(newArgs, c, nr_args * sizeof(IRExpr *));
			newArgs[nr_args] = NULL;
			it->second = IRExprCCall::mk(g->cee, g->retty, newArgs);
		}
		break;
	}
	case Iex_Associative: {
		auto g = (IRExprAssociative *)what;
		IRExpr *newArgs[g->nr_arguments];
		bool realloc = false;
		for (int i = 0; i < g->nr_arguments; i++) {
			newArgs[i] = specialiseIRExpr(scopes, g->contents[i], memo);
			if (newArgs[i] != g->contents[i]) {
				realloc = true;
			}
		}
		if (!realloc) {
			it->second = g;
		} else {
			it->second = IRExpr_Associative_Copy(g->op, g->nr_arguments, newArgs);
		}
		break;
	}
	case Iex_Load: {
		auto g = (IRExprLoad *)what;
		auto addr = specialiseIRExpr(scopes, g->addr, memo);
		if (addr == g->addr) {
			it->second = g;
		} else {
			it->second = IRExprLoad::mk(g->ty, addr);
		}
		break;
	}
	}
	return it->second;
}

bbdd *
threadState::specialiseIRExpr(SMScopes *scopes, bbdd *what, std::map<bbdd *, bbdd *> &memo,
			      std::map<IRExpr *, IRExpr *> &exprMemo)
{
	if (what->isLeaf()) {
		return what;
	}
	auto it_did_insert = memo.insert(std::pair<bbdd *, bbdd *>(what, (bbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		IRExpr *cond = specialiseIRExpr(scopes, what->internal().condition, exprMemo);
		bbdd *t = specialiseIRExpr(scopes, what->internal().trueBranch, memo, exprMemo);
		bbdd *f = specialiseIRExpr(scopes, what->internal().falseBranch, memo, exprMemo);
		if (TIMEOUT) {
			it->second = what;
		} else if (t == f) {
			it->second = t;
		} else if (cond == what->internal().condition &&
			   t == what->internal().trueBranch &&
			   f == what->internal().falseBranch) {
			it->second = what;
		} else if (cond == what->internal().condition) {
			it->second = scopes->bools.node(what->internal().condition,
							what->internal().rank,
							t,
							f);
		} else {
			it->second = bbdd::ifelse(&scopes->bools,
						  bbdd::var(&scopes->bools, cond),
						  t,
						  f);
		}
	}
	return it->second;
}
smrbdd *
threadState::specialiseIRExpr(SMScopes *scopes, smrbdd *what, std::map<smrbdd *, smrbdd *> &memo,
			      std::map<IRExpr *, IRExpr *> &exprMemo)
{
	if (what->isLeaf()) {
		return what;
	}
	auto it_did_insert = memo.insert(std::pair<smrbdd *, smrbdd *>(what, (smrbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		IRExpr *cond = specialiseIRExpr(scopes, what->internal().condition, exprMemo);
		smrbdd *t = specialiseIRExpr(scopes, what->internal().trueBranch, memo, exprMemo);
		smrbdd *f = specialiseIRExpr(scopes, what->internal().falseBranch, memo, exprMemo);
		if (TIMEOUT) {
			it->second = what;
		} else if (t == f) {
			it->second = t;
		} else if (cond == what->internal().condition &&
			   t == what->internal().trueBranch &&
			   f == what->internal().falseBranch) {
			it->second = what;
		} else if (cond == what->internal().condition) {
			it->second = scopes->smrs.node(what->internal().condition,
						       what->internal().rank,
						       t,
						       f);
		} else {
			it->second = smrbdd::ifelse(&scopes->smrs,
						    bbdd::var(&scopes->bools, cond),
						    t,
						    f);
		}
	}
	return it->second;
}
exprbdd *
threadState::specialiseIRExpr(SMScopes *scopes, exprbdd *what, std::map<exprbdd *, exprbdd *> &memo,
			      std::map<IRExpr *, IRExpr *> &exprMemo)
{
	auto it_did_insert = memo.insert(std::pair<exprbdd *, exprbdd *>(what, (exprbdd *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (what->isLeaf()) {
			IRExpr *l = specialiseIRExpr(scopes, what->leaf(), exprMemo);
			if (l == what->leaf()) {
				it->second = what;
			} else {
				it->second = exprbdd::var(
					&scopes->exprs,
					&scopes->bools,
					l);
			}
		} else {
			IRExpr *cond = specialiseIRExpr(scopes, what->internal().condition, exprMemo);
			exprbdd *t = specialiseIRExpr(scopes, what->internal().trueBranch, memo, exprMemo);
			exprbdd *f = specialiseIRExpr(scopes, what->internal().falseBranch, memo, exprMemo);
			if (TIMEOUT) {
				it->second = what;
			} else if (t == f) {
				it->second = t;
			} else if (cond == what->internal().condition &&
				   t == what->internal().trueBranch &&
				   f == what->internal().falseBranch) {
				it->second = what;
			} else if (cond == what->internal().condition) {
				it->second = scopes->exprs.node(what->internal().condition,
								what->internal().rank,
								t,
								f);
			} else {
				it->second = exprbdd::ifelse(&scopes->exprs,
							     bbdd::var(&scopes->bools, cond),
							     t,
							     f);
			}
		}
	}
	return it->second;
}

class memLogT : public std::vector<StateMachineSideEffectStore *> {
public:
	void visit(HeapVisitor &hv) {
		for (auto it = begin(); it != end(); it++) {
			hv(*it);
		}
	}
};

class EvalContext : public GcCallback<&ir_heap> {
	enum trool { tr_true, tr_false, tr_unknown };
public:
	bbdd *justPathConstraint;
private:
	threadState state;
	memLogT memlog;
	StateMachineState *_currentState;
public:
#ifndef NDEBUG
	std::vector<StateMachineState *> history;
#endif

	bool isMagicState(std::map<const StateMachineState *, int> &) {
#if 0
		static const int desired[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 12, 0};
		unsigned idx = 0;
		while (1) {
			if (desired[idx] == 0) {
				return true;
			}
			if (idx == history.size() || labels[history[idx]] != desired[idx]) {
				return false;
			}
			idx++;
		}
#else
		return false;
#endif
	}
	void setState(StateMachineState *s) {
#ifndef NDEBUG
		if (debug_survival_constraint) {
			history.push_back(s);
		}
#endif
		_currentState = s;
	}

private:
	void runGc(HeapVisitor &hv) {
		state.visit(hv);
		memlog.visit(hv);
		hv(_currentState);
		hv(justPathConstraint);
#ifndef NDEBUG
		for (auto it = history.begin(); it != history.end(); it++) {
			hv(*it);
		}
#endif
	}

	trool evalBooleanExpression(SMScopes *scopes, bbdd *assumption, bbdd *what, bbdd **simplified, const IRExprOptimisations &opt);

	EvalContext(const EvalContext &o, StateMachineState *sms)
		: justPathConstraint(o.justPathConstraint)
		, state(o.state)
		, memlog(o.memlog)
#ifndef NDEBUG
		, history(o.history)
#endif
	{
		setState(sms);
	}
	/* Create a new context which is like this one, but with an
	   extra constraint. */
	EvalContext(SMScopes *scopes,
		    const EvalContext &o,
		    StateMachineState *sms,
		    bbdd *constraint)
		: justPathConstraint(bbdd::And(&scopes->bools, o.justPathConstraint, constraint))
		, state(o.state)
		, memlog(o.memlog)
#ifndef NDEBUG
		, history(o.history)
#endif
	{
		setState(sms);
	}
	template <typename paramT>
	void evalStateMachineSideEffect(
		SMScopes *scopes,
		bbdd *assumption,
		const MaiMap &decode,
		StateMachineSideEffect *smse,
		OracleInterface *oracle,
		bool havePhis,
		typename paramT::resultT &result,
		const IRExprOptimisations &opt);
	template <typename paramT>
	void assertFalse(bbdd::scope *scope,
			 bbdd *what,
			 const IRExprOptimisations &opt,
			 typename paramT::resultT &result);
public:
	template <typename paramT>
	void advance(SMScopes *scopes,
		     bbdd *assumption,
		     const MaiMap &decode,
		     OracleInterface *oracle,
		     const IRExprOptimisations &opt,
		     std::vector<EvalContext> &pendingStates,
		     bool havePhis,
		     typename paramT::resultT &result);
	EvalContext(StateMachine *sm, bbdd *_pathConstraint)
		: justPathConstraint(_pathConstraint)
	{
		assert(justPathConstraint);
		setState(sm->root);
	}

	void prettyPrint(FILE *f, std::map<const StateMachineState *, int> &labels)
	{
		fprintf(f, "EvalContext(current = l%d)\n",
			labels[_currentState]);
		justPathConstraint->prettyPrint(f);
		printHistory(f,labels);
	}
#ifndef NDEBUG
	void printHistory(FILE *f, std::map<const StateMachineState *, int> &labels)
	{
		if (debug_survival_constraint) {
			fprintf(f, "History: ");
			for (auto it = history.begin();
			     it != history.end();
			     it++) {
				if (it != history.begin()) {
					fprintf(f, ", ");
				}
				fprintf(f, "l%d", labels[*it]);
			}
			fprintf(f, "\n");
		}
	}
#else
	void printHistory(FILE *, std::map<const StateMachineState *, int> &) {
	}
#endif

};

template <typename paramT> void
EvalContext::assertFalse(bbdd::scope *scope, bbdd *what, const IRExprOptimisations &opt,
			 typename paramT::resultT &result)
{
	what = simplifyBDD(scope, what, opt);
	if (what) {
		paramT::addPathToUnreached(scope, result, justPathConstraint, what);
		auto isGood = bbdd::invert(scope, what);
		if (isGood) {
			bbdd *newConstraint =
				bbdd::And(scope,
					  justPathConstraint,
					  isGood);
			if (newConstraint) {
				justPathConstraint = newConstraint;
			}
		}
	}
}

template <typename paramT> void
EvalContext::evalStateMachineSideEffect(SMScopes *scopes,
					bbdd *assumption,
					const MaiMap &decode,
					StateMachineSideEffect *smse,
					OracleInterface *oracle,
					bool havePhis,
					typename paramT::resultT &result,
					const IRExprOptimisations &opt)
{
	exprbdd *addr = NULL;
	if (smse->type == StateMachineSideEffect::Load ||
	    smse->type == StateMachineSideEffect::Store) {
		StateMachineSideEffectMemoryAccess *smsema =
			dynamic_cast<StateMachineSideEffectMemoryAccess *>(smse);
		assert(smsema);
		addr = state.specialiseIRExpr(scopes, smsema->addr);
		if (TIMEOUT) {
			return;
		}
		if (!smsema->tag.neverBadPtr()) {
			exprbdd *a = exprbdd::unop(
				&scopes->exprs,
				&scopes->bools,
				Iop_BadPtr,
				addr);
			if (TIMEOUT) {
				return;
			}
			assert(a);
			bbdd *isBad = exprbdd::to_bbdd(&scopes->bools, a);
			if (TIMEOUT) {
				return;
			}
			assertFalse<paramT>(&scopes->bools, isBad, opt, result);
			if ((justPathConstraint->isLeaf() && !justPathConstraint->leaf()) || TIMEOUT) {
				return;
			}
		}
	}

	switch (smse->type) {
	case StateMachineSideEffect::Store: {
		StateMachineSideEffectStore *smses =
			dynamic_cast<StateMachineSideEffectStore *>(smse);
		assert(smses);
		assert(addr);
		auto data = state.specialiseIRExpr(scopes, smses->data);
		if (TIMEOUT) {
			return;
		}
		memlog.push_back(
			new StateMachineSideEffectStore(
				smses,
				addr,
				data));
		break;
	}
	case StateMachineSideEffect::Load: {
		StateMachineSideEffectLoad *smsel =
			dynamic_cast<StateMachineSideEffectLoad *>(smse);
		assert(smsel);
		assert(addr);
		exprbdd *acc = exprbdd::load(&scopes->exprs, &scopes->bools, smsel->type, addr);
		for (auto it = memlog.begin();
		     it != memlog.end();
		     it++) {
			StateMachineSideEffectStore *store = *it;
			/* We only accept stores which define the
			 * entire thing which we're looking for.  If
			 * something's stored as 64 bits then we'll
			 * take a load of 32 bits, but if it's stored
			 * as 32 bits then we won't take a load of 64
			 * bits. */
			if (store->data->type() < smsel->type) {
#warning This is unsound
				continue;
			}

			if (!oracle->memoryAccessesMightAlias(decode, opt, smsel, store))
				continue;
			exprbdd *addressesEq =
				exprbdd::binop(
					&scopes->exprs,
					&scopes->bools,
					Iop_CmpEQ64,
					addr,
					store->addr);
			if (TIMEOUT) {
				return;
			}
			/* The order of the next few operations
			   (convert to BBDD, apply assumption, apply
			   justPathConstraint) only matters for
			   performance, and not for correctness. */
			addressesEq = exprbdd::assume(
				&scopes->exprs,
				addressesEq,
				assumption);
			if (TIMEOUT) {
				return;
			}
			bbdd *addressEqBool =
				exprbdd::to_bbdd(&scopes->bools, addressesEq);
			if (TIMEOUT) {
				return;
			}
			addressEqBool = bbdd::assume(
				&scopes->bools,
				addressEqBool,
				justPathConstraint);
			if (TIMEOUT) {
				return;
			}
			addressEqBool = simplifyBDD(&scopes->bools, addressEqBool, opt);
			if (TIMEOUT) {
				return;
			}
			/* End of block where ordering doesn't matter */

			exprbdd *val =
				exprbdd::coerceTypes(
					&scopes->exprs,
					&scopes->bools,
					smsel->type,
					store->data);
			if (TIMEOUT) {
				return;
			}
			acc = exprbdd::ifelse(
				&scopes->exprs,
				addressEqBool,
				val,
				acc);
			if (TIMEOUT) {
				return;
			}
		}
		state.set_register(scopes, smsel->target, acc, &justPathConstraint, havePhis, opt);
		break;
	}
	case StateMachineSideEffect::Copy: {
		StateMachineSideEffectCopy *smsec =
			dynamic_cast<StateMachineSideEffectCopy *>(smse);
		assert(smsec);
		auto val = state.specialiseIRExpr(scopes, smsec->value);
		if (TIMEOUT) {
			return;
		}
		state.set_register(scopes,
				   smsec->target,
				   val,
				   &justPathConstraint,
				   havePhis,
				   opt);
		break;
	}
	case StateMachineSideEffect::Unreached:
		abort();
	case StateMachineSideEffect::AssertFalse: {
		StateMachineSideEffectAssertFalse *smseaf =
			dynamic_cast<StateMachineSideEffectAssertFalse *>(smse);
		auto v = state.specialiseIRExpr(
			scopes,
			smseaf->value);
		if (TIMEOUT) {
			return;
		}
		assertFalse<paramT>(&scopes->bools, v, opt, result);
		break;
	}
	case StateMachineSideEffect::Phi: {
		StateMachineSideEffectPhi *smsep =
			(StateMachineSideEffectPhi *)(smse);
		assert(havePhis);
		state.eval_phi(scopes, smsep, &justPathConstraint, havePhis, opt);
		break;
	}
	case StateMachineSideEffect::StartAtomic:
		break;
	case StateMachineSideEffect::EndAtomic:
		break;
	case StateMachineSideEffect::ImportRegister: {
		StateMachineSideEffectImportRegister *p =
			(StateMachineSideEffectImportRegister *)smse;
		threadAndRegister tr(threadAndRegister::reg(p->tid, p->vex_offset, -1));
		IRExpr *g = IRExpr_Get(tr, Ity_I64);
		state.set_register(scopes,
				   p->reg,
				   exprbdd::var(
					   &scopes->exprs,
					   &scopes->bools,
					   g),
				   &justPathConstraint,
				   havePhis,
				   opt);
#if !CONFIG_NO_STATIC_ALIASING
		/* The only use we make of a PointerAliasing side
		   effect is to say that things which aliasing says
		   are definitely valid pointers really are definitely
		   valid pointers.  Todo: could do much better
		   here. */
		if (!p->set.mightBeNonPointer()) {
			auto b = bbdd::var(&scopes->bools,
					   IRExpr_Unop(
						   Iop_BadPtr,
						   g));
			if (b) {
				assertFalse<paramT>(&scopes->bools, b, opt, result);
			}
		}
#endif
		break;
	}

		/* Todo: could maybe use this to improve aliasing. */
#if TRACK_FRAMES
	case StateMachineSideEffect::StartFunction:
	case StateMachineSideEffect::EndFunction:
	case StateMachineSideEffect::StackLayout:
		break;
#endif
	}
}

EvalContext::trool
EvalContext::evalBooleanExpression(SMScopes *scopes, bbdd *assumption, bbdd *what, bbdd **simplified, const IRExprOptimisations &opt)
{
	bbdd *simplifiedCondition =
		bbdd::assume(
			&scopes->bools,
			what,
			justPathConstraint);
	if (!simplifiedCondition) {
		/* @what is a contradiction when combined with
		 * @pathConstraint.  That means we can say whatever we
		 * like and it won't actually matter. */
		return tr_true;
	}
	simplifiedCondition =
		bbdd::assume(
			&scopes->bools,
			what,
			assumption);
	if (!simplifiedCondition) {
		return tr_true;
	}
	simplifiedCondition = simplifyBDD(&scopes->bools, simplifiedCondition, opt);
	if (TIMEOUT) {
		/* Guess; we'll ignore the result, anyway. */
		return tr_true;
	}
	if (simplifiedCondition->isLeaf()) {
		if (simplifiedCondition->leaf())
			return tr_true;
		else
			return tr_false;
	}

	/* Give up on this one and just accept that we don't know. */
	*simplified = simplifiedCondition;
	return tr_unknown;
}

static bool
usesUninit(const IRExpr *what)
{
	struct v {
		static visit_result Get(void *, const IRExprGet *ieg) {
			if (ieg->reg.isReg() &&
			    ieg->reg.gen() == (unsigned)-1) {
				return visit_continue;
			} else {
				return visit_abort;
			}
		}
	};
	static irexpr_visitor<void> visitor;
	visitor.Get = v::Get;
	return visit_irexpr((void *)NULL, &visitor, what) == visit_abort;
}

static smrbdd *
suppressUninit(smrbdd::scope *scope, smrbdd *input, bool kill_smr_unreached,
	       std::map<smrbdd *, smrbdd *> &memo)
{
	auto it_did_insert = memo.insert(std::pair<smrbdd *, smrbdd *>(input, (smrbdd *)0xf001));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;

	if (!did_insert) {
		/* it->second is already correct */
	} else if (input->isLeaf()) {
		it->second = input;
	} else {
		auto t = suppressUninit(scope, input->internal().trueBranch, kill_smr_unreached, memo);
		auto f = suppressUninit(scope, input->internal().falseBranch, kill_smr_unreached, memo);
		if (t == f ||
		    !t ||
		    (kill_smr_unreached && t->isLeaf() && t->leaf() == smr_unreached)) {
			it->second = f;
		} else if (!f || (kill_smr_unreached && f->isLeaf() && f->leaf() == smr_unreached)) {
			it->second = t;
		} else if (usesUninit(input->internal().condition)) {
			it->second = NULL;
		} else if (t == input->internal().trueBranch &&
			   f == input->internal().falseBranch) {
			it->second = input;
		} else {
			it->second = scope->node(
				input->internal().condition,
				input->internal().rank,
				t,
				f);
		}
	}
	return it->second;
}

static smrbdd *
suppressUninit(smrbdd::scope *scope, bool kill_smr_unreached, smrbdd *input)
{
	std::map<smrbdd *, smrbdd *> memo;
	return suppressUninit(scope, input, kill_smr_unreached, memo);
}

#ifndef NDEBUG
static void
assertClosed(smrbdd *what)
{
	std::set<smrbdd *> visited;
	std::vector<smrbdd *> pending;
	pending.push_back(what);
	while (!pending.empty()) {
		what = pending.back();
		pending.pop_back();
		if (!visited.insert(what).second) {
			continue;
		}
		if (!what->isLeaf()) {
			pending.push_back(what->internal().trueBranch);
			pending.push_back(what->internal().falseBranch);
			assert(!usesUninit(what->internal().condition));
		}
	}
}
#else
static void
assertClosed(smrbdd *)
{
}
#endif

/* You might that we could stash things like @oracle, @opt, and @sm in
   the EvalContext itself and not have to pass them around all the
   time.  That'd work, but it'd mean duplicating those pointers in
   every item in the pending state queue, which would make that queue
   much bigger, which'd be kind of annoying. */
template <typename paramT> void
EvalContext::advance(SMScopes *scopes,
		     bbdd *assumption,
		     const MaiMap &decode,
		     OracleInterface *oracle,
		     const IRExprOptimisations &opt,
		     std::vector<EvalContext> &pendingStates,
		     bool havePhis,
		     typename paramT::resultT &result)
{
	if (justPathConstraint->isLeaf() && !justPathConstraint->leaf()) {
		/* This path is dead. */
		if (debug_survival_constraint) {
			printf("Path is dead\n");
		}
		pendingStates.pop_back();
		return;
	}

	assert(this == &pendingStates.back());
	switch (_currentState->type) {
	case StateMachineState::Terminal: {
		auto smt = (StateMachineTerminal *)_currentState;
		auto res = state.specialiseIRExpr(scopes, smt->res);
		if (TIMEOUT) {
			return;
		}
		paramT::addPathToTerminal(scopes, result, res, justPathConstraint);

		/* Caution: this will de-initialise *this, and might
		   deallocate it, so once you've done this you can't
		   access any member variables any more. */
		pendingStates.pop_back();
		return;
	}
	case StateMachineState::SideEffecting: {
		StateMachineSideEffecting *sme = (StateMachineSideEffecting *)_currentState;
		setState(sme->target);
		if (sme->sideEffect) {
			evalStateMachineSideEffect<paramT>(scopes,
							   assumption,
							   decode,
							   sme->sideEffect,
							   oracle,
							   havePhis,
							   result,
							   opt);
		}
		return;
	}
	case StateMachineState::Bifurcate: {
		StateMachineBifurcate *smb = (StateMachineBifurcate *)_currentState;
		bbdd *cond = state.specialiseIRExpr(scopes, smb->condition);
		if (TIMEOUT) {
			return;
		}
		bbdd *scond;
		trool res = evalBooleanExpression(scopes, assumption, cond, &scond, opt);
		switch (res) {
		case tr_true:
			setState(smb->trueTarget);
			break;
		case tr_false:
			setState(smb->falseTarget);
			break;
		case tr_unknown:
			/* We rely on the caller to have reserved
			   enough space in @pendingStates that this
			   doesn't cause a realloc (which would
			   invalidate the @this pointer, which would
			   be bad). */
			pendingStates.push_back(EvalContext(
							scopes,
							*this,
							smb->falseTarget,
							bbdd::invert(
								&scopes->bools,
								scond)));
			setState(smb->trueTarget);
			justPathConstraint = bbdd::And(&scopes->bools, justPathConstraint, scond);
			break;
		}
		return;
	}
	}
	abort();
}

static bool
hasPhis(StateMachine *sm)
{
	struct {
		static visit_result Phi(void *, const StateMachineSideEffectPhi *) {
			return visit_abort;
		}
	} foo;
	static struct state_machine_visitor<void> visitor;
	visitor.Phi = foo.Phi;
	return visit_state_machine((void *)NULL, &visitor, sm) == visit_abort;
}

template <typename paramT> static typename paramT::resultT
enumEvalPaths(SMScopes *scopes,
	      const VexPtr<MaiMap, &ir_heap> &decode,
	      const VexPtr<StateMachine, &ir_heap> &sm,
	      VexPtr<bbdd, &ir_heap> assumption,
	      const VexPtr<OracleInterface> &oracle,
	      const IRExprOptimisations &opt,
	      StateMachineRes unreachedIs,
	      GarbageCollectionToken token)
{
	std::vector<EvalContext> pendingStates;
	typename paramT::resultT result;
	std::map<const StateMachineState *, int> labels;

	if (debug_survival_constraint) {
		printf("%s(sm = ..., assumption = %s, unreachedIs = %s)\n",
		       __func__,
		       assumption ? "..." : "<null>",
		       nameSmr(unreachedIs));
		if (assumption)
			assumption->prettyPrint(stdout);
		printStateMachine(sm->root, stdout, labels);
	}

	bool havePhis = hasPhis(sm);

	result = paramT::initialResult(scopes, unreachedIs);

	pendingStates.push_back(EvalContext(sm, scopes->bools.cnst(true)));
	if (!assumption) {
		assumption = scopes->bools.cnst(true);
	}
	while (!pendingStates.empty()) {
		if (TIMEOUT) {
			return NULL;
		}
		LibVEX_maybe_gc(token);

		/* Make sure we don't need to realloc pendingStates at
		 * a bad place. */
		pendingStates.reserve(pendingStates.size() + 1);

		EvalContext &ctxt(pendingStates.back());
		if (debug_survival_constraint) {
			ctxt.printHistory(stdout, labels);
			if (ctxt.isMagicState(labels)) {
				dbg_break("Here");
			}
		}

		ctxt.advance<paramT>(scopes, assumption, *decode, oracle, opt, pendingStates, havePhis,
				     result);
	}

	if (debug_survival_constraint) {
		printf("Result of symbolic execution:\n");
		result->prettyPrint(stdout);
	}

	if (!TIMEOUT) {
		paramT::suppressUnreached(scopes, unreachedIs, result);
	}

	if (debug_survival_constraint && result) {
		printf("Unreached suppressed:\n");
		result->prettyPrint(stdout);
	}

	return result;
}

struct normalEvalParams {
	typedef VexPtr<smrbdd, &ir_heap> resultT;
	static smrbdd *initialResult(SMScopes *scopes, StateMachineRes unreachedIs) {
		return scopes->smrs.cnst(unreachedIs);
	}
	static void addPathToTerminal(SMScopes *scopes,
				      resultT &result,
				      smrbdd *termRes,
				      bbdd *justPathConstraint) {
		if (TIMEOUT) {
			return;
		}
		termRes = suppressUninit(&scopes->smrs, true, termRes);
		if (!termRes) {
			if (debug_survival_constraint) {
				printf("Reached terminal is unreachable?\n");
			}
		} else {
			if (debug_survival_constraint) {
				printf("Terminal, result:\n");
				termRes->prettyPrint(stdout);
			}
			result = smrbdd::ifelse(
				&scopes->smrs,
				justPathConstraint,
				termRes,
				result);
			if (TIMEOUT) {
				return;
			}
			result = suppressUninit(&scopes->smrs, true, result);
			assert(result != NULL);
			if (debug_survival_constraint) {
				printf("New overall result:\n");
				result->prettyPrint(stdout);
			}
		}

		assertClosed(result);
	}
	static void addPathToUnreached(bbdd::scope *,
				       resultT &,
				       bbdd *,
				       bbdd *) {
		/* Does nothing: for normal interpretation, paths to
		   unreached need to be suppressed. */
	}
	static void suppressUnreached(SMScopes *scopes,
				      StateMachineRes unreachedIs,
				      resultT &result) {
		result = smrbdd::replaceTerminal(&scopes->smrs, smr_unreached, unreachedIs, result);
	}
};

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

	smrbdd *smr = enumEvalPaths<normalEvalParams>(
		scopes, mai, sm, assumption, oracle, opt,
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
	case StateMachineState::SideEffecting: {
		auto sme = (StateMachineSideEffecting *)s;
		if (!sme->sideEffect ||
		    sme->sideEffect->type == StateMachineSideEffect::StartAtomic ||
		    sme->sideEffect->type == StateMachineSideEffect::EndAtomic) {
			return new StateMachineSideEffecting(s->dbg_origin, NULL, sme->target);
		} else {
			return new StateMachineSideEffecting(sme);
		}
	}
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
#if TRACK_FRAMES
		case StateMachineSideEffect::StartFunction:
		case StateMachineSideEffect::EndFunction:
		case StateMachineSideEffect::StackLayout:
#endif
		case StateMachineSideEffect::ImportRegister:
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
			 const IRExprOptimisations &opt,
			 StateMachineRes unreachedIs,
			 std::map<threadAndRegister, threadAndRegister> &ssaCorrespondence)
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
						scopes->smrs.cnst(unreachedIs));
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
					scopes->smrs.cnst(unreachedIs));
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
			} else if (crossState.p->type == StateMachineState::Bifurcate &&
				   crossState.s->type != StateMachineState::Bifurcate &&
				   (!store_effect ||
				    storeDefinitelyDoesntRace(*maiOut, store_effect, crossState.p, opt, oracle))) {
				/* If it's a choice between a
				   bifurcate and a non-bifurcate then
				   always issue the non-bifurcate
				   first, because that tends to lead
				   to fewer states in total.  */
				/* (The symmetrical case, where the
				   store is a bifurcate and the probe
				   isn't, is subsumed by the next
				   case) */
				newState = advanceStoreMachine(crossState, pendingRelocs);
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
				assert(probe_access || probe_effect->type == StateMachineSideEffect::StartAtomic);
				assert(store_access || store_effect->type == StateMachineSideEffect::StartAtomic);
				const MemoryAccessIdentifier &probeMai(probe_access ? probe_access->rip : ((StateMachineSideEffectStartAtomic *)probe_effect)->mai);
				const MemoryAccessIdentifier &storeMai(store_access ? store_access->rip : ((StateMachineSideEffectStartAtomic *)store_effect)->mai);
				newState = new StateMachineBifurcate(
					VexRip(),
					bbdd::var(&scopes->bools, IRExpr_HappensBefore(probeMai, storeMai)),
					nextProbe,
					nextStore);
			}
		}
		results[r.second] = newState;
		*r.first = newState;
	}

	std::vector<std::pair<StateMachine::entry_point, StateMachine::entry_point_ctxt> > cfg_roots(probeMachine->cfg_roots);
	for (auto it = storeMachine->cfg_roots.begin(); it != storeMachine->cfg_roots.end(); it++) {
		bool already_present = false;
		for (auto it2 = cfg_roots.begin(); !already_present && it2 != cfg_roots.end(); it2++) {
			if (it2->first == it->first) {
				already_present = true;
			}
		}
		if (!already_present) {
			cfg_roots.push_back(*it);
		}
	}
	if (TIMEOUT) {
		return NULL;
	}
        return convertToSSA(scopes, new StateMachine(crossMachineRoot, cfg_roots), ssaCorrespondence);
}

#if TRACK_FRAMES
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
				if (old->sideEffect &&
				    (old->sideEffect->type == StateMachineSideEffect::StackLayout ||
				     old->sideEffect->type == StateMachineSideEffect::StartFunction ||
				     old->sideEffect->type == StateMachineSideEffect::EndFunction)) {
					nw->sideEffect = NULL;
				}
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
#endif

static bbdd *
deSsa(bbdd::scope *scope, bbdd *what, const std::map<threadAndRegister, threadAndRegister> &correspondence)
{
	struct : public IRExprTransformer {
		const std::map<threadAndRegister, threadAndRegister> *correspondence;
		IRExpr *transformIex(IRExprGet *ieg) {
			auto it = correspondence->find(ieg->reg);
			if (it == correspondence->end()) {
				return ieg;
			} else {
				return IRExpr_Get(it->second, ieg->ty);
			}
		}
	} doit;
	doit.correspondence = &correspondence;
	return doit.transform_bbdd(scope, what);
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
	stackedCdf::startCrashConstraint();
	__set_profiling(evalCrossProductMachine);

	AllowableOptimisations opt =
		optIn
		    .enableassumeExecutesAtomically()
		    .enableignoreSideEffects()
		    .enableassumeNoInterferingStores()
		    .enablenoExtend();
	VexPtr<MaiMap, &ir_heap> decode;
	std::map<threadAndRegister, threadAndRegister> ssaCorrespondence;
	StateMachine *strippedProbe = probeMachine;
	StateMachine *strippedStore = storeMachine;
	stackedCdf::startCrashConstraintResimplify();
#if TRACK_FRAMES
	strippedProbe = stripUninterpretableAnnotations(probeMachine);
	strippedStore = stripUninterpretableAnnotations(storeMachine);
#endif
	strippedProbe = mapUnreached(&scopes->smrs, strippedProbe, smr_survive);
	strippedStore = mapUnreached(&scopes->smrs, strippedStore, smr_survive);
	stackedCdf::stopCrashConstraintResimplify();
	stackedCdf::startCrashConstraintBuildCross();
	VexPtr<StateMachine, &ir_heap> crossProductMachine(
		buildCrossProductMachine(
			scopes,
			*mai,
			strippedProbe,
			strippedStore,
			oracle,
			decode.get(),
			opt,
			smr_survive,
			ssaCorrespondence));
	stackedCdf::stopCrashConstraintBuildCross();
	if (!crossProductMachine) {
		stackedCdf::stopCrashConstraint();
		return NULL;
	}
	bool ignore;
	stackedCdf::startCrashConstraintResimplify();
	optimiseAssuming(scopes, crossProductMachine, initialStateCondition, &ignore);
	crossProductMachine =
		optimiseStateMachine(
			scopes,
			decode,
			crossProductMachine,
			opt,
			oracle,
			true,
			token);
	crossProductMachine = mapUnreached(&scopes->smrs, crossProductMachine, smr_survive);
	stackedCdf::stopCrashConstraintResimplify();

	if (TIMEOUT) {
		return NULL;
	}
	stackedCdf::startCrashConstraintSymbolicExecute();
	bbdd *res_ssa = survivalConstraintIfExecutedAtomically(
		scopes,
		decode,
		crossProductMachine,
		initialStateCondition,
		oracle,
		true,
		opt,
		token);
	stackedCdf::stopCrashConstraintSymbolicExecute();
	if (!res_ssa) {
		stackedCdf::stopCrashConstraint();
		return NULL;
	}
	auto res = deSsa(&scopes->bools, res_ssa, ssaCorrespondence);
	stackedCdf::stopCrashConstraint();
	return res;
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
concatenateStateMachinesCrashing(SMScopes *scopes, const StateMachine *machine, const StateMachine *to,
				 StateMachineRes unreachedIs)
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
							scopes->smrs.cnst(unreachedIs));
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

	std::vector<std::pair<StateMachine::entry_point, StateMachine::entry_point_ctxt> > cfg_roots(machine->cfg_roots);
	for (auto it = to->cfg_roots.begin(); it != to->cfg_roots.end(); it++) {
		bool already_present = false;
		for (auto it2 = cfg_roots.begin(); !already_present && it2 != cfg_roots.end(); it2++) {
			if (it2->first == it->first) {
				already_present = true;
			}
		}
		if (!already_present) {
			cfg_roots.push_back(*it);
		}
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
	stackedCdf::startBuildWAtomic();
	__set_profiling(writeMachineSuitabilityConstraint);

	VexPtr<StateMachine, &ir_heap> combinedMachine;

	writeMachine->assertAcyclic();
	readMachine->assertAcyclic();
	stackedCdf::startBuildWAtomicMachine();
	combinedMachine = concatenateStateMachinesCrashing(
		scopes,
		writeMachine,
		readMachine,
		smr_crash);
	stackedCdf::stopBuildWAtomicMachine();
	if (TIMEOUT) {
		stackedCdf::stopBuildWAtomic();
		return NULL;
	}
	combinedMachine->assertAcyclic();
	stackedCdf::startBuildWAtomicResimplify();
	combinedMachine = mapUnreached(&scopes->smrs, combinedMachine, smr_crash);
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
	stackedCdf::stopBuildWAtomicResimplify();
	if (TIMEOUT) {
		return NULL;
	}
	stackedCdf::startBuildWAtomicSymbolicExecute();
	auto res = survivalConstraintIfExecutedAtomically(
		scopes,
		mai,
		combinedMachine,
		assumption,
		oracle,
		false,
		opt,
		token);
	stackedCdf::stopBuildWAtomicSymbolicExecute();
	if (res) {
		res = bbdd::And(&scopes->bools, res, assumption);
	}
	stackedCdf::stopBuildWAtomic();
	return res;
}

template <typename bddT> static void
enumVariables(bddT *src, std::set<IRExpr *> &out, std::set<bddT *> &memo)
{
	if (src->isLeaf() || !memo.insert(src).second) {
		return;
	}
	out.insert(src->internal().condition);
	enumVariables(src->internal().trueBranch, out, memo);
	enumVariables(src->internal().falseBranch, out, memo);
}

struct collectConstraintsParams {
	struct resultT {
		std::set<IRExpr *> &exprs;
		GcSet<bbdd, &ir_heap> memo1;
		GcSet<smrbdd, &ir_heap> memo2;
		resultT(std::set<IRExpr *> &_exprs)
			: exprs(_exprs)
		{}
	};

	static void addPathToTerminal(SMScopes *scopes, resultT &result,
				      smrbdd *res, bbdd *pathConstraint) {
		enumVariables(pathConstraint, result.exprs, result.memo1);
		res = suppressUninit(&scopes->smrs, false, res);
		if (!res) {
			if (debug_survival_constraint) {
				printf("Reached terminal is unreachable?\n");
			}
		} else {
			if (debug_survival_constraint) {
				printf("Terminal, result:\n");
				res->prettyPrint(stdout);
			}
			enumVariables(res, result.exprs, result.memo2);
               }
	}
	static void addPathToUnreached(bbdd::scope *,
				       resultT &result,
				       bbdd *pathConstraint,
				       bbdd *unreachedIf)
	{
		enumVariables(pathConstraint, result.exprs, result.memo1);
		enumVariables(unreachedIf, result.exprs, result.memo1);
	}
};

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
		   GcSet<IRExpr, &ir_heap> &out,
		   GarbageCollectionToken token)
{
	bool havePhis = hasPhis(sm);
	std::vector<EvalContext> pendingStates;

	collectConstraintsParams::resultT results(out);

	WeakSet<bbdd, &ir_heap> memo;

	pendingStates.push_back(EvalContext(sm, scopes->bools.cnst(true)));
	while (!pendingStates.empty()) {
		LibVEX_maybe_gc(token);

		pendingStates.reserve(pendingStates.size() + 1);

		EvalContext &ctxt(pendingStates.back());
		enumVariables(ctxt.justPathConstraint, out, memo);
		ctxt.advance<collectConstraintsParams>(scopes, scopes->bools.cnst(true), *mai, oracle, opt, pendingStates, havePhis, results);
	}
}

#include "bdd_tmpl.cpp"

typedef Maybe<StateMachineRes> msmr;

class msmrbdd : public const_bdd<msmr, msmrbdd> {
	friend class const_bdd_scope<msmrbdd>;
	friend class bdd_scope<msmrbdd>;
	friend class _bdd<msmr, msmrbdd>;
#ifdef NDEBUG
	void _sanity_check(msmr) const {}
#else
	void _sanity_check(msmr r) const {
		if (r.valid) {
			sanity_check_smr(r.content);
		}
	}
#endif
	void _prettyPrint(FILE *f, msmr r) const {
		if (r.valid) {
			fprintf(f, "<%s>", nameSmr(r.content));
		} else {
			fprintf(f, "<missing>");
		}
	}

	msmrbdd(bdd_rank rank, IRExpr *cond, msmrbdd *trueB, msmrbdd *falseB)
		: const_bdd<msmr, msmrbdd>(rank, cond, trueB, falseB)
	{}
	msmrbdd(const msmr &b)
		: const_bdd<msmr, msmrbdd>(b)
	{}
	static smrbdd *ignore_invalid(smrbdd::scope *scp, msmrbdd *what, sane_map<msmrbdd *, smrbdd *> &memo);
	static msmrbdd *from_smrbdd(scope *scp, smrbdd *what, sane_map<smrbdd *, msmrbdd *> &memo);
public:
	smrbdd *ignore_invalid(smrbdd::scope *scp);
	static msmrbdd *from_smrbdd(scope *scp, smrbdd *what);
};

msmrbdd *
msmrbdd::from_smrbdd(scope *scp, smrbdd *what, sane_map<smrbdd *, msmrbdd *> &memo)
{
	if (what->isLeaf()) {
		return scp->cnst(what->leaf());
	}
	auto it_did_insert = memo.insert(what, (msmrbdd *)0xf001);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	auto t = from_smrbdd(scp, what->internal().trueBranch, memo);
	auto f = from_smrbdd(scp, what->internal().falseBranch, memo);
	it->second = scp->node(
		what->internal().condition,
		what->internal().rank,
		t,
		f);
	return it->second;
}

msmrbdd *
msmrbdd::from_smrbdd(scope *scp, smrbdd *what)
{
	sane_map<smrbdd *, msmrbdd *> memo;
	return from_smrbdd(scp, what, memo);
}

smrbdd *
msmrbdd::ignore_invalid(smrbdd::scope *scp, msmrbdd *what, sane_map<msmrbdd *, smrbdd *> &memo)
{
	if (!what) {
		return NULL;
	}
	if (what->isLeaf()) {
		if (what->leaf().valid) {
			return scp->cnst(what->leaf().content);
		} else {
			return NULL;
		}
	}
	auto it_did_insert = memo.insert(what, (smrbdd *)0xbeef);
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert) {
		return it->second;
	}
	auto t = ignore_invalid(scp, what->internal().trueBranch, memo);
	auto f = ignore_invalid(scp, what->internal().falseBranch, memo);
	if (!t) {
		it->second = f;
	} else if (!f) {
		it->second = t;
	} else {
		it->second = scp->node(what->internal().condition,
				       what->internal().rank,
				       t,
				       f);
	}
	return it->second;
}
smrbdd *
msmrbdd::ignore_invalid(smrbdd::scope *scp)
{
	sane_map<msmrbdd *, smrbdd *> memo;
	return ignore_invalid(scp, this, memo);
}

/* Bit of a hack */
static msmrbdd::scope *global_msmr_scope;

struct compileMachineToBddParams {
	typedef msmrbdd *resultT;
	static msmrbdd *initialResult(SMScopes *, StateMachineRes) {
		return global_msmr_scope->cnst(Maybe<StateMachineRes>());
	}
	static void suppressUnreached(SMScopes *,
				      StateMachineRes,
				      const resultT &) {
	}
	static void addPathToTerminal(SMScopes *,
				      resultT &result,
				      smrbdd *stateRes,
				      bbdd *pathConstraint) {
		result = msmrbdd::ifelse(
			global_msmr_scope,
			pathConstraint,
			msmrbdd::from_smrbdd(global_msmr_scope, stateRes),
			result);
	}
	static void addPathToUnreached(bbdd::scope *bscope,
				       resultT &result,
				       bbdd *pathConstraint,
				       bbdd *branchConstraint) {
		result = msmrbdd::ifelse(
			global_msmr_scope,
			bbdd::And(bscope, pathConstraint, branchConstraint),
			global_msmr_scope->cnst(smr_unreached),
			result);
	}
};

/* Compile a state machine down to an msmrbdd which tells you what
   would happen if you ran it atomically in some initial state. */
smrbdd *
compileMachineToBdd(SMScopes *scopes,
		    const VexPtr<MaiMap, &ir_heap> &mai,
		    const VexPtr<StateMachine, &ir_heap> &sm,
		    VexPtr<OracleInterface> &oracle,
		    const IRExprOptimisations &opt,
		    GarbageCollectionToken token)
{
	msmrbdd::scope msmr_scope(&scopes->ordering);
	global_msmr_scope = &msmr_scope;
	compileMachineToBddParams::resultT res;
	res = enumEvalPaths<compileMachineToBddParams>(scopes,
						       mai,
						       sm,
						       scopes->bools.cnst(true),
						       oracle,
						       opt,
						       smr_unreached,
						       token);
	global_msmr_scope = NULL;
	return res->msmrbdd::ignore_invalid(&scopes->smrs);
	
}
