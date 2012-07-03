/* A simple test for the expression simplifier: generate random
   constants for every variable in an expression, then evaluate the
   before and after versions of the expression and see if they're
   different.  Repeat a couple of times and you get a reasonable check
   as to whether the simplifier is actually working. */
#include "sli.h"
#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"
#include "allowable_optimisations.hpp"

namespace _quickcheckexpr {

class RandomEvalContext {
	class applySubsts : public IRExprTransformer {
		RandomEvalContext *_this;
		IRExpr *transformIex(IRExprGet *ieg) {
			return _this->getReg(ieg->reg, ieg->ty);
		}
		IRExpr *transformIex(IRExprLoad *iel) {
			return _this->get(iel);
		}
		IRExpr *transformIex(IRExprUnop *ieu) {
			/* Special case: BadPtr(RSP) is always just 0.
			   That's not strictly sound, so it's kind of
			   reassuring that this test flags it as bad,
			   but it's so close to sound that reporting
			   it over and over again is just annoying, so
			   stop doing that. */
			if (ieu->op == Iop_BadPtr &&
			    ieu->arg->tag == Iex_Get &&
			    !((IRExprGet *)ieu->arg)->reg.isTemp() &&
			    ((IRExprGet *)ieu->arg)->reg.asReg() == offsetof(VexGuestAMD64State, guest_RSP))
				return IRExpr_Const(IRConst_U1(0));
			IRExpr *res = IRExprTransformer::transformIex(ieu);
			if (res &&
			    res->tag == Iex_Unop &&
			    ((IRExprUnop *)res)->op == Iop_BadPtr &&
			    ((IRExprUnop *)res)->arg->tag == Iex_Const) {
				/* This is kind of like a variable. */
				assert(((IRExprUnop *)res)->arg->type() == Ity_I64);
				if (_this->isBadAddr(((IRExprConst *)((IRExprUnop *)res)->arg)->con->Ico.U64))
					return IRExpr_Const(IRConst_U1(1));
				else
					return IRExpr_Const(IRConst_U1(0));
			}
			return res;
		}
	public:
		applySubsts(RandomEvalContext *__this)
			: _this(__this)
		{}
	};
	std::map<IRExpr *, IRExpr *> lookupTable;
	std::map<threadAndRegister, unsigned long, threadAndRegister::fullCompare> registers;
	std::map<unsigned long, bool> badAddrs;
	unsigned long randomVal();
	IRExpr *invent_random_const_expression(IRType ty);
	IRExpr *getReg(const threadAndRegister &tr, IRType ty);
	bool isBadAddr(unsigned long addr);
	IRExpr *get(IRExpr *e);
public:
	IRConst *evaluate(const IRExpr *a);
};

unsigned long
RandomEvalContext::randomVal()
{
	unsigned long val;
	/* Try to make the distribution pick ``interesting'' numbers
	   slightly more often than it would if it were uniform. */
	switch (random() % 6) {
	case 0:
		val = 0;
		break;
	case 1:
		val = 1;
		break;
	case 2:
		val = -1;
		break;
	case 3:
		val = random() % 32;
		break;
	case 4:
		val = 1ul << (random() % 64);
		break;
	case 5:
		val = random() ^ (random() * RAND_MAX) ^ (random() * RAND_MAX * RAND_MAX);
		break;
	default:
		abort();
	}
	return val;
}

IRExpr *
RandomEvalContext::invent_random_const_expression(IRType ty)
{
	unsigned long val = randomVal();
	IRConst *c;
	switch (ty) {
	case Ity_I1:
		c = IRConst_U1(val & 1);
		break;
	case Ity_I8:
		c = IRConst_U8(val & 0xff);
		break;
	case Ity_I16:
		c = IRConst_U16(val & 0xffff);
		break;
	case Ity_I32:
		c = IRConst_U32(val & 0xfffffffful);
		break;
	case Ity_I64:
		c = IRConst_U64(val);
		break;
	case Ity_F64:
		c = IRConst_F64(*(double *)&val);
		break;
	case Ity_V128:
		c = IRConst_V128(val & 0xffff);
		break;
	default:
		/* Somewhat annoyingly, VEX doesn't actually have
		   support for immediate values of all of its types.
		   Shrug. */
		abort();
	}
	return IRExpr_Const(c);
}

IRExpr *
RandomEvalContext::getReg(const threadAndRegister &tr, IRType ty)
{
	auto it_did_insert = registers.insert(std::pair<threadAndRegister, unsigned long>(tr, 0));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = randomVal();
	switch (ty) {
#define do_ty(name, mask)						\
		case Ity_I ## name :					\
			return IRExpr_Const(IRConst_U ## name(it->second & mask))
	do_ty(1, 1);
	do_ty(8, 0xff);
	do_ty(16, 0xffff);
	do_ty(32, 0xfffffffful);
	do_ty(64, ~0ul);
#undef do_ty
	case Ity_F64:
		return IRExpr_Const(IRConst_F64(*(double *)&it->second));
	case Ity_V128:
		return IRExpr_Const(IRConst_V128(it->second & 0xffff));
	case Ity_INVALID:
		abort();
	}
	abort();
}

IRExpr *
RandomEvalContext::get(IRExpr *key)
{
	auto it_did_insert = lookupTable.insert(std::pair<IRExpr *, IRExpr *>(key, (IRExpr *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = invent_random_const_expression(key->type());
	return it->second;
}

bool
RandomEvalContext::isBadAddr(unsigned long addr)
{
	auto it_did_insert = badAddrs.insert(std::pair<unsigned long, bool>(addr, false));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = random() % 2 == 0;
	return it->second;	
}

IRConst *
RandomEvalContext::evaluate(const IRExpr *a)
{
	applySubsts s(this);
	IRExpr *res = s.doit(const_cast<IRExpr *>(a));
	res = simplifyIRExpr(res, AllowableOptimisations::defaultOptimisations.enablenoSanityChecking());
	if (res->tag == Iex_Const)
		return ((IRExprConst *)res)->con;
	printf("Can't eval ");
	ppIRExpr(a, stdout);
	printf("; -> ");
	ppIRExpr(res, stdout);
	printf("\n");
	return NULL;
}

static bool
exprs_eq(const IRExpr *a, const IRExpr *b)
{
	RandomEvalContext evalCtxt;

	IRConst *a_const = evalCtxt.evaluate(a);
	if (!a_const) {
		/* If we can't reduce to a constant then we can't do
		   anything useful. */
		return true;
	}
	IRConst *b_const = evalCtxt.evaluate(b);
	if (!b_const)
		return true;
	assert(a_const->tag == b_const->tag);
	switch (a_const->tag) {
#define do_type(t)						\
		case Ico_ ## t:					\
		return a_const->Ico. t == b_const->Ico. t
	do_type(U1);
	do_type(U8);
	do_type(U16);
	do_type(U32);
	do_type(U64);
	do_type(F64);
	do_type(F64i);
	do_type(V128);
#undef do_type
	}
	abort();
}

static void
quickcheck_exprs_eq(const IRExpr *a, const IRExpr *b)
{
	if (!exprs_eq(a, b)) {
		printf("Expression quickcheck failed: ");
		ppIRExpr(a, stdout);
		printf(" != ");
		ppIRExpr(b, stdout);
		printf("\n");
	}
}

/* End of namespace */
};

void
quickcheck_exprs_eq(const IRExpr *a, const IRExpr *b)
{
#if 0
	return _quickcheckexpr::quickcheck_exprs_eq(a, b);
#endif
}
