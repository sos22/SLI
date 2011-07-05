#include <time.h>

#include "sli.h"
#include "state_machine.hpp"

#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"

#include "libvex_guest_offsets.h"
#include "../VEX/priv/guest_generic_bb_to_IR.h"
#include "../VEX/priv/guest_amd64_defs.h"

/* Returns true if the operation definitely commutes, or false if
 * we're not sure. */
static bool
operationCommutes(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) ||
		(op >= Iop_CmpEQ8 && op <= Iop_CmpEQ64) ||
		(op == Iop_And1) ||
		(op == Iop_Or1) ||
		(op == Iop_Xor1);
}

/* Returns true if the operation definitely associates in the sense
 * that (a op b) op c == a op (b op c), or false if we're not sure. */
static bool
operationAssociates(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) || (op == Iop_And1) ||
		(op >= Iop_And8 && op <= Iop_And64) || (op >= Iop_Xor8 && op <= Iop_Xor64) ||
		(op >= Iop_Or8 && op <= Iop_Or64) || (op == Iop_Or1) ||
		(op == Iop_Xor1)
		;
}

static bool
physicallyEqual(const IRConst *a, const IRConst *b)
{
	if (a->tag != b->tag)
		return false;
	switch (a->tag) {
#define do_case(t)					\
		case Ico_ ## t:				\
			return a->Ico. t == b->Ico. t
		do_case(U1);
		do_case(U8);
		do_case(U16);
		do_case(U32);
		do_case(U64);
		do_case(F64);
		do_case(F64i);
		do_case(V128);
#undef do_case
	}
	abort();
}

static bool
physicallyEqual(const IRRegArray *a, const IRRegArray *b)
{
	return a->base == b->base && a->elemTy == b->elemTy && a->nElems == b->nElems;
}

static bool
physicallyEqual(const IRCallee *a, const IRCallee *b)
{
	return a->addr == b->addr;
}

static bool
physicallyEqual(const IRExpr *a, const IRExpr *b)
{
	if (a == b)
		return true;
	if (a->tag != b->tag)
		return false;
	switch (a->tag) {
	case Iex_Binder:
		return a->Iex.Binder.binder == b->Iex.Binder.binder;
	case Iex_Get:
		return a->Iex.Get.offset == b->Iex.Get.offset &&
			a->Iex.Get.ty == b->Iex.Get.ty;
	case Iex_GetI:
		return a->Iex.GetI.bias == b->Iex.GetI.bias &&
			physicallyEqual(a->Iex.GetI.descr,
					b->Iex.GetI.descr) &&
			physicallyEqual(a->Iex.GetI.ix,
					b->Iex.GetI.ix);
	case Iex_RdTmp:
		return a->Iex.RdTmp.tmp == b->Iex.RdTmp.tmp;

	case Iex_Qop:
		if (!physicallyEqual(a->Iex.Qop.arg4,
				     b->Iex.Qop.arg4))
			return false;
	case Iex_Triop:
		if (!physicallyEqual(a->Iex.Qop.arg3,
				     b->Iex.Qop.arg3))
			return false;
	case Iex_Binop:
		if (!physicallyEqual(a->Iex.Qop.arg2,
				     b->Iex.Qop.arg2))
			return false;
	case Iex_Unop:
		if (!physicallyEqual(a->Iex.Qop.arg1,
				     b->Iex.Qop.arg1))
			return false;
		return a->Iex.Qop.op == b->Iex.Qop.op;
	case Iex_Load:
		return a->Iex.Load.isLL == b->Iex.Load.isLL &&
			a->Iex.Load.end == b->Iex.Load.end &&
			a->Iex.Load.ty == b->Iex.Load.ty &&
			physicallyEqual(a->Iex.Load.addr, b->Iex.Load.addr);
	case Iex_Const:
		return physicallyEqual(a->Iex.Const.con, b->Iex.Const.con);
	case Iex_CCall: {
		if (a->Iex.CCall.retty != b->Iex.CCall.retty ||
		    !physicallyEqual(a->Iex.CCall.cee, b->Iex.CCall.cee))
			return false;
		int x;
		for (x = 0; a->Iex.CCall.args[x]; x++) {
			if (!b->Iex.CCall.args[x])
				return false;
			if (!physicallyEqual(a->Iex.CCall.args[x],
					     b->Iex.CCall.args[x]))
				return false;
		}
		if (b->Iex.CCall.args[x])
			return false;
		return true;
	}
	case Iex_Mux0X:
		return physicallyEqual(a->Iex.Mux0X.cond,
				       b->Iex.Mux0X.cond) &&
			physicallyEqual(a->Iex.Mux0X.expr0,
					b->Iex.Mux0X.expr0) &&
			physicallyEqual(a->Iex.Mux0X.exprX,
					b->Iex.Mux0X.exprX);
	case Iex_Associative:
		if (a->Iex.Associative.op != b->Iex.Associative.op ||
		    a->Iex.Associative.nr_arguments != b->Iex.Associative.nr_arguments)
			return false;
		for (int x = 0; x < a->Iex.Associative.nr_arguments; x++)
			if (!physicallyEqual(a->Iex.Associative.contents[x],
					     b->Iex.Associative.contents[x]))
				return false;
		return true;
	case Iex_FreeVariable:
		return a->Iex.FreeVariable.key == b->Iex.FreeVariable.key;
	}
	abort();
}

static IRExpr *
optimise_condition_calculation(
	IRExpr *_cond,
	IRExpr *cc_op,
	IRExpr *dep1,
	IRExpr *dep2,
	IRExpr *ndep,
	const AllowableOptimisations &opt)
{
	unsigned long cond;
	IRExpr *res;
	bool invert;
	IRExpr *sf, *cf, *zf, *of;

	/* We only handle a few very special cases here. */
	if (_cond->tag != Iex_Const || cc_op->tag != Iex_Const)
		return NULL;
	cond = _cond->Iex.Const.con->Ico.U64;
	invert = cond & 1;
	cond &= ~1ul;
	res = NULL;
	sf = cf = zf = of = NULL;

	switch (cc_op->Iex.Const.con->Ico.U64) {
	case AMD64G_CC_OP_SUBB:
		zf = IRExpr_Binop(Iop_CmpEQ8, dep1, dep2);
		break;
	case AMD64G_CC_OP_SUBW:
		zf = IRExpr_Binop(Iop_CmpEQ16, dep1, dep2);
		break;
	case AMD64G_CC_OP_SUBL:
	case AMD64G_CC_OP_SUBQ:
		zf = IRExpr_Binop(
			Iop_CmpEQ64,
			dep1,
			dep2);
		cf = IRExpr_Binop(
			Iop_CmpLT64U,
			dep1,
			dep2);
		sf = IRExpr_Binop(
			Iop_CmpLT64S,
			dep1,
			dep2);
		of = IRExpr_Binop(
			Iop_CC_OverflowSub,
			dep1,
			dep2);
		break;
	case AMD64G_CC_OP_LOGICB:
	case AMD64G_CC_OP_LOGICL:
	case AMD64G_CC_OP_LOGICQ:
		zf = IRExpr_Binop(
			Iop_CmpEQ64,
			dep1,
			IRExpr_Const(IRConst_U64(0)));
		sf = IRExpr_Binop(
			Iop_CmpLT64S,
			dep1,
			IRExpr_Const(IRConst_U32(0)));
		of = IRExpr_Const(IRConst_U1(0));
		break;
	case AMD64G_CC_OP_ADDW:
		sf = IRExpr_Binop(
			Iop_CmpLT32S,
			IRExpr_Binop(
				Iop_Add16,
				dep1,
				dep2),
			IRExpr_Const(IRConst_U16(0)));
		break;
	default:
		printf("Unknown CC op %llx\n", cc_op->Iex.Const.con->Ico.U64);
		break;
	}

	switch (cond) {
	case AMD64CondZ:
		res = zf;
		break;
	case AMD64CondB:
		res = cf;
		break;
	case AMD64CondBE:
		if (cf && zf)
			res = IRExpr_Binop(
				Iop_Or1,
				cf,
				zf);
		break;
	case AMD64CondS:
		res = sf;
		break;
	case AMD64CondL:
		if (sf && of)
			res = IRExpr_Binop(
				Iop_Xor1,
				sf,
				of);
		else
			printf("CondL needs both sf and of; op %llx\n", cc_op->Iex.Const.con->Ico.U64);
		break;
	case AMD64CondLE:
		if (sf && of && zf)
			res = IRExpr_Binop(
				Iop_Or1,
				IRExpr_Binop(
					Iop_Xor1,
					sf,
					of),
				zf);
		else
			printf("CondLE needs sf, of, and zf; op %llx\n", cc_op->Iex.Const.con->Ico.U64);
		break;
	default:
		break;
	}
	if (!res)
		printf("Cannot handle CC condition %ld, op %lld\n",
		       cond, cc_op->Iex.Const.con->Ico.U64);
	if (res && invert)
		res = IRExpr_Unop(Iop_Not1, res);
	return res;
}

/* Wherever we have a choice as to the ordering of an expression's
   sub-expressions, we sort them into ascending order of complexity,
   where complexity is defined by this function.  The main requirement
   is that if both x and -x occur in the argument list, x will occur
   before -x. */
/* If two expressions have the same complexity, we use a lexicographic
   ordering to distinguish them. */
int
exprComplexity(const IRExpr *e)
{
	switch (e->tag) {
	case Iex_Binder:
		return 10;
	case Iex_Get:
		return 20;
	case Iex_GetI:
		return 20 + exprComplexity(e->Iex.GetI.ix);
	case Iex_RdTmp:
		return 30;
	case Iex_Qop:
		return 10 +
			exprComplexity(e->Iex.Qop.arg1) +
			exprComplexity(e->Iex.Qop.arg2) +
			exprComplexity(e->Iex.Qop.arg3) +
			exprComplexity(e->Iex.Qop.arg4);
	case Iex_Triop:
		return 10 +
			exprComplexity(e->Iex.Qop.arg1) +
			exprComplexity(e->Iex.Qop.arg2) +
			exprComplexity(e->Iex.Qop.arg3);
	case Iex_Binop:
		return 10 +
			exprComplexity(e->Iex.Qop.arg1) +
			exprComplexity(e->Iex.Qop.arg2);
	case Iex_Unop:
		return 10 + exprComplexity(e->Iex.Qop.arg1);
	case Iex_Load:
		return 10 + exprComplexity(e->Iex.Load.addr);
	case Iex_Const:
		return 0;
	case Iex_Mux0X:
		return 10 + exprComplexity(e->Iex.Mux0X.cond) +
			exprComplexity(e->Iex.Mux0X.expr0) +
			exprComplexity(e->Iex.Mux0X.exprX);
	case Iex_CCall: {
		int acc = 50;
		for (int x = 0; e->Iex.CCall.args[x]; x++)
			acc += exprComplexity(e->Iex.CCall.args[x]);
		return acc;
	}
	case Iex_Associative: {
		int acc = 10;
		for (int x = 0; x < e->Iex.Associative.nr_arguments; x++)
			acc += exprComplexity(e->Iex.Associative.contents[x]);
		return acc;
	}
	case Iex_FreeVariable:
		return 100;
	}
	abort();
}

static int
ordering_iex_tag(IRExprTag a)
{
	switch (a) {
	case Iex_Const: return 0;
	case Iex_Binder: return 1;
	case Iex_Get: return 2;
	case Iex_GetI: return 3;
	case Iex_RdTmp: return 4;
	case Iex_FreeVariable: return 5;
	case Iex_Unop: return 6;
	case Iex_Binop: return 7;
	case Iex_Triop: return 8;
	case Iex_Qop: return 9;
	case Iex_Associative: return 10;
	case Iex_Mux0X: return 11;
	case Iex_Load: return 12;
	case Iex_CCall: return 13;
	}
	abort();
}

static bool
IexTagLessThan(IRExprTag a, IRExprTag b)
{
	if (a == b)
		return false;

	int _a = ordering_iex_tag(a);
	int _b = ordering_iex_tag(b);
	return _a < _b;
}

static bool
sortIRConsts(IRConst *a, IRConst *b)
{
	if (a->tag < b->tag)
		return true;
	if (a->tag > b->tag)
		return false;
	switch (a->tag) {
#define do_type(t)					\
		case Ico_ ## t :			\
			return a->Ico. t < b->Ico. t
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

static bool
sortIRExprs(IRExpr *a, IRExpr *b)
{
	int ac = exprComplexity(a);
	int bc = exprComplexity(b);
	if (ac < bc)
		return true;
	if (ac > bc)
		return false;
	if (IexTagLessThan(a->tag, b->tag)) {
		return true;
	} else if (a->tag != b->tag) {
		return false;
	}

	switch (a->tag) {
	case Iex_Binder:
		return a->Iex.Binder.binder < b->Iex.Binder.binder;
	case Iex_Get:
		return a->Iex.Get.offset < b->Iex.Get.offset;
	case Iex_GetI:
		return sortIRExprs(a->Iex.GetI.ix, b->Iex.GetI.ix);
	case Iex_RdTmp:
		return a->Iex.RdTmp.tmp < b->Iex.RdTmp.tmp;
	case Iex_Qop:
		if (a->Iex.Qop.op < b->Iex.Qop.op)
			return true;
		if (a->Iex.Qop.op > b->Iex.Qop.op)
			return false;
		if (physicallyEqual(a->Iex.Qop.arg1, b->Iex.Qop.arg1)) {
			if (physicallyEqual(a->Iex.Qop.arg2,
					    b->Iex.Qop.arg2)) {
				if (physicallyEqual(a->Iex.Qop.arg3,
						    b->Iex.Qop.arg3))
					return sortIRExprs(a->Iex.Qop.arg4,
							   b->Iex.Qop.arg4);
				else
					return sortIRExprs(a->Iex.Qop.arg3,
							   b->Iex.Qop.arg3);
			} else
				return sortIRExprs(a->Iex.Qop.arg2,
						   b->Iex.Qop.arg2);
		} else {
			return sortIRExprs(a->Iex.Qop.arg1,
					   b->Iex.Qop.arg1);
		}
	case Iex_Triop:
		if (a->Iex.Qop.op < b->Iex.Qop.op)
			return true;
		if (a->Iex.Qop.op > b->Iex.Qop.op)
			return false;
		if (physicallyEqual(a->Iex.Qop.arg1, b->Iex.Qop.arg1)) {
			if (physicallyEqual(a->Iex.Qop.arg2,
					    b->Iex.Qop.arg2)) {
				return sortIRExprs(a->Iex.Qop.arg3,
						   b->Iex.Qop.arg3);
			} else
				return sortIRExprs(a->Iex.Qop.arg2,
						   b->Iex.Qop.arg2);
		} else {
			return sortIRExprs(a->Iex.Qop.arg1,
					   b->Iex.Qop.arg1);
		}
	case Iex_Binop:
		if (a->Iex.Qop.op < b->Iex.Qop.op)
			return true;
		if (a->Iex.Qop.op > b->Iex.Qop.op)
			return false;
		if (physicallyEqual(a->Iex.Qop.arg1, b->Iex.Qop.arg1)) {
			return sortIRExprs(a->Iex.Qop.arg2,
					   b->Iex.Qop.arg2);
		} else {
			return sortIRExprs(a->Iex.Qop.arg1,
					   b->Iex.Qop.arg1);
		}
	case Iex_Unop:
		if (a->Iex.Qop.op < b->Iex.Qop.op)
			return true;
		if (a->Iex.Qop.op > b->Iex.Qop.op)
			return false;
		return sortIRExprs(a->Iex.Qop.arg1,
				   b->Iex.Qop.arg1);
	case Iex_Load:
		return sortIRExprs(a->Iex.Load.addr, b->Iex.Load.addr);
	case Iex_Const:
		return sortIRConsts(a->Iex.Const.con, b->Iex.Const.con);
	case Iex_CCall: {
		int r = strcmp(a->Iex.CCall.cee->name,
			       b->Iex.CCall.cee->name);
		if (r < 0)
			return true;
		else if (r > 0)
			return false;
		for (int x = 0; 1; x++) {
			if (!a->Iex.CCall.args[x] &&
			    !b->Iex.CCall.args[x])
				return false;
			if (!a->Iex.CCall.args[x])
				return false;
			if (!b->Iex.CCall.args[x])
				return false;
			if (!physicallyEqual(a->Iex.CCall.args[x],
					     b->Iex.CCall.args[x]))
				return sortIRExprs(a->Iex.CCall.args[x],
						   b->Iex.CCall.args[x]);
		}
	}
	case Iex_Mux0X:
		if (!physicallyEqual(a->Iex.Mux0X.cond,
				     b->Iex.Mux0X.cond))
			return sortIRExprs(a->Iex.Mux0X.cond,
					   b->Iex.Mux0X.cond);
		if (!physicallyEqual(a->Iex.Mux0X.expr0,
				     b->Iex.Mux0X.expr0))
			return sortIRExprs(a->Iex.Mux0X.expr0,
					   b->Iex.Mux0X.expr0);
		return sortIRExprs(a->Iex.Mux0X.exprX,
				   b->Iex.Mux0X.exprX);
	case Iex_Associative: {
		if (a->Iex.Associative.op < b->Iex.Associative.op)
			return true;
		if (a->Iex.Associative.op > b->Iex.Associative.op)
			return false;
		int x;
		x = 0;
		while (1) {
			if (x == a->Iex.Associative.nr_arguments &&
			    x == b->Iex.Associative.nr_arguments)
				return false;
			if (x == a->Iex.Associative.nr_arguments)
				return true;
			if (x == b->Iex.Associative.nr_arguments)
				return false;
			if (!physicallyEqual( a->Iex.Associative.contents[x],
					      b->Iex.Associative.contents[x] ))
				return sortIRExprs( a->Iex.Associative.contents[x],
						    b->Iex.Associative.contents[x] );
			x++;
		}
	}
	case Iex_FreeVariable:
		return a->Iex.FreeVariable.key < b->Iex.FreeVariable.key;
	}

	abort();
}

static void
addArgumentToAssoc(IRExpr *e, IRExpr *arg)
{
	assert( (e->optimisationsApplied & ~arg->optimisationsApplied) == 0);
	if (e->Iex.Associative.nr_arguments == e->Iex.Associative.nr_arguments_allocated) {
		e->Iex.Associative.nr_arguments_allocated += 8;
		e->Iex.Associative.contents = (IRExpr **)
			LibVEX_realloc(&ir_heap,
				       e->Iex.Associative.contents,
				       sizeof(IRExpr *) * e->Iex.Associative.nr_arguments_allocated);
	}
	e->Iex.Associative.contents[e->Iex.Associative.nr_arguments] = arg;
	e->Iex.Associative.nr_arguments++;
}

static void
purgeAssocArgument(IRExpr *e, int idx)
{
	assert(e->tag == Iex_Associative);
	assert(idx < e->Iex.Associative.nr_arguments);
	memmove(e->Iex.Associative.contents + idx,
		e->Iex.Associative.contents + idx + 1,
		sizeof(IRExpr *) * (e->Iex.Associative.nr_arguments - idx - 1));
	e->Iex.Associative.nr_arguments--;
}

class CnfExpression : public GarbageCollected<CnfExpression>, public Named {
public:
	virtual CnfExpression *CNF(void) = 0;
	virtual CnfExpression *invert() = 0;
	virtual IRExpr *asIRExpr(std::map<int, IRExpr *> &,
				 IRExprTransformer &) = 0;
	virtual int complexity() = 0;
	NAMED_CLASS
};

class CnfAtom : public CnfExpression {
public:
	virtual int getId() = 0;
};

class CnfVariable : public CnfAtom {
	static int nextId;
protected:
	char *mkName() const { return my_asprintf("v%d", id); }
public:
	CnfExpression *CNF() { return this; }
	CnfVariable() : id(nextId++) {}
	void visit(HeapVisitor &hv) {}
	CnfExpression *invert();
	int getId() { return id; }
	IRExpr *asIRExpr(std::map<int, IRExpr *> &m,
			 IRExprTransformer &t)
	{
		bool ign;
		return t.transformIRExpr(m[id], &ign);
	}
	int complexity() { return 0; }
	int id;
};
int CnfVariable::nextId = 450;

class CnfNot : public CnfAtom {
protected:
	char *mkName() const { return my_asprintf("(~%s)", arg->name()); }
public:
	CnfNot(CnfExpression *a) : arg(a) {}
	void visit(HeapVisitor &hv) { hv(arg); }
	CnfExpression *invert() { return arg; }
	CnfExpression *CNF();
	int getId() {
		CnfAtom *a = dynamic_cast<CnfAtom *>(arg);
		assert(a);
		return a->getId();
	}
	IRExpr *asIRExpr(std::map<int, IRExpr *> &m,
			 IRExprTransformer &t)
	{
		return IRExpr_Unop(Iop_Not1, arg->asIRExpr(m, t));
	}
	int complexity() { return arg->complexity() + 1; }
	CnfExpression *arg;
};

class CnfGrouping : public CnfExpression {
protected:
	virtual char op() const = 0;
	char *mkName() const {
		char *acc = NULL;
		char *acc2;
		if (args.size() == 0)
			return my_asprintf("(%c)", op());
		for (unsigned x = 0; x < args.size(); x++) {
			if (x == 0)
				acc2 = my_asprintf("(%s", args[x]->name());
			else
				acc2 = my_asprintf("%s %c %s", acc, op(), args[x]->name());
			free(acc);
			acc = acc2;
		}
		acc2 = my_asprintf("%s)", acc);
		free(acc);
		return acc2;
	}
public:
	void visit(HeapVisitor &hv) {
		for (unsigned x; x < args.size(); x++)
			hv(args[x]);
	}
	void addChild(CnfExpression *e) { args.push_back(e); }
	int complexity() {
		if (args.size() == 0)
			return 0;
		int acc = 1;
		for (unsigned x = 0; x < args.size(); x++)
			acc += args[x]->complexity();
		return acc;
	}
	std::vector<CnfExpression *> args;
};

class CnfOr : public CnfGrouping {
protected:
	char op() const { return '|'; }
public:
	CnfExpression *CNF();
	CnfExpression *invert();
	void sort();
	CnfAtom *getArg(unsigned x) {
		assert(x < args.size());
		CnfAtom *r = dynamic_cast<CnfAtom *>(args[x]);
		assert(r);
		return r;
	}
	IRExpr *asIRExpr(std::map<int, IRExpr *> &m, IRExprTransformer &t) {
		if (args.size() == 0) {
			return IRExpr_Const(IRConst_U1(0));
		} else if (args.size() == 1) {
			return args[0]->asIRExpr(m, t);
		} else {
			IRExpr *work = IRExpr_Associative(Iop_Or1, NULL);
			for (unsigned x = 0; x < args.size(); x++)
				addArgumentToAssoc(work, args[x]->asIRExpr(m, t));
			return work;
		}
	}
};

class CnfAnd : public CnfGrouping {
	class myTransformer : public IRExprTransformer {
	public:
		std::map<IRExpr *, IRExpr *> cnstTable;
		IRExprTransformer &underlying;
		IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
			if (cnstTable.count(e)) {
				*done_something = true;
				e = cnstTable[e];
			}
			e = IRExprTransformer::transformIRExpr(e, done_something);
			e = underlying.transformIRExpr(e, done_something);
			return e;
		}
		myTransformer(IRExprTransformer &_underlying)
			: underlying(_underlying)
		{}
	};
protected:
	char op() const { return '&'; }
public:
	CnfExpression *CNF();
	CnfExpression *invert();
	void sort();
	CnfOr *getArg(unsigned x) {
		assert(x < args.size());
		CnfOr *r = dynamic_cast<CnfOr *>(args[x]);
		assert(r);
		return r;
	}
	void optimise();
	IRExpr *asIRExpr(std::map<int, IRExpr *> &m, IRExprTransformer &t) {
		if (args.size() == 0) {
			return IRExpr_Const(IRConst_U1(1));
		} else {
			IRExpr *work = IRExpr_Associative(Iop_And1, NULL);
			myTransformer trans(t);
			for (unsigned x = 0; x < args.size(); x++) {
				IRExpr *exp = args[x]->asIRExpr(m, trans);
				addArgumentToAssoc(work, exp);
				if (exp->tag == Iex_Binop &&
				    exp->Iex.Binop.op == Iop_CmpEQ64 &&
				    exp->Iex.Binop.arg1->tag == Iex_Const)
					trans.cnstTable[exp->Iex.Binop.arg2] = exp->Iex.Binop.arg1;
			}
			return work;
		}
	}
};

CnfExpression *
CnfVariable::invert(void)
{
	return new CnfNot(this);
}

CnfExpression *
CnfNot::CNF()
{
	if (dynamic_cast<CnfVariable *>(arg))
		return this;
	return arg->invert()->CNF();
}

static bool
__comparator1(CnfExpression *_a, CnfExpression *_b)
{
	CnfAtom *a = dynamic_cast<CnfAtom *>(_a);
	CnfAtom *b = dynamic_cast<CnfAtom *>(_b);
	assert(a && b);
	return a->getId() < b->getId();
}

void
CnfOr::sort()
{
	std::sort(args.begin(), args.end(), __comparator1);
}

static bool
__comparator2(CnfExpression *_a, CnfExpression *_b)
{
	CnfOr *a = dynamic_cast<CnfOr *>(_a);
	CnfOr *b = dynamic_cast<CnfOr *>(_b);
	assert(a && b);
	for (unsigned x = 0;
	     x < a->args.size() && x < b->args.size();
	     x++) {
		if (a->getArg(x)->getId() <
		    b->getArg(x)->getId())
			return true;
		if (a->getArg(x)->getId() >
		    b->getArg(x)->getId())
			return false;
	}
	if (a->args.size() < b->args.size())
		return true;
	return false;
}

void
CnfAnd::sort()
{
	for (unsigned x = 0; x < args.size(); x++)
		getArg(x)->sort();
	std::sort(args.begin(), args.end(), __comparator2);
}

/* Or expressions are allowed to have variables or negations of
   variables as arguments, but not other or expressions or and
   expressions. */
CnfExpression *
CnfOr::CNF()
{
	for (unsigned x = 0; x < args.size(); x++)
		args[x] = args[x]->CNF();
	for (unsigned x = 0; x < args.size(); x++) {
		if (dynamic_cast<CnfNot *>(args[x]) ||
		    dynamic_cast<CnfVariable *>(args[x]))
			continue;
		if (CnfOr *cor = dynamic_cast<CnfOr *>(args[x])) {
			/* Flatten nested ORs. */
			for (unsigned y = 0; y < cor->args.size(); y++) {
				args.push_back(cor->args[y]);
			}
			args.erase(args.begin() + x);
			x--;
		} else {
			/* Deal with these in a second pass */
			assert(dynamic_cast<CnfAnd *>(args[x]));
		}
	}

	for (unsigned x = 0; x < args.size(); x++) {
		CnfAnd *cad = dynamic_cast<CnfAnd *>(args[x]);
		if (!cad)
			continue;
		if (args.size() == 1)
			return args[0];
		if (cad->args.size() == 1) {
			args[x] = cad->args[0];
			continue;
		}
		/* Okay, we have something of the form
		   a | b | c | (1 & 2 & 3 & ...) ... .
		   Convert it to
		   (a | b | c | 1) & (a | b | c | 2) & (a | b | c | 3) & ...

		*/
		CnfAnd *newRoot = new CnfAnd();
		std::vector<CnfExpression *> newArgs = args;
		newArgs.erase(newArgs.begin() + x);
		newRoot->args.resize(cad->args.size());
		for (unsigned y = 0; y < cad->args.size(); y++) {
			CnfGrouping *cg = new CnfOr();
			cg->args = newArgs;
			cg->addChild(cad->args[y]);
			newRoot->args[y] = cg;
		}
		return newRoot->CNF();
	}
	return this;
}

/* And expressions are only allowed to have or expressions as
 * children. */
CnfExpression *
CnfAnd::CNF()
{
	for (unsigned x = 0; x < args.size(); x++)
		args[x] = args[x]->CNF();
	for (unsigned x = 0; x < args.size(); x++) {
		if (dynamic_cast<CnfNot *>(args[x]) ||
		    dynamic_cast<CnfVariable *>(args[x])) {
			CnfGrouping *n = new CnfOr();
			n->addChild(args[x]);
			args[x] = n;
			continue;
		}
		if (CnfAnd *car = dynamic_cast<CnfAnd *>(args[x])) {
			for (unsigned y = 0; y < car->args.size(); y++) {
				args.push_back(car->args[y]);
			}
			args.erase(args.begin() + x);
			x--;
		}
	}
	return this;
}

CnfExpression *
CnfOr::invert()
{
	CnfAnd *a = new CnfAnd();
	a->args.resize(args.size());
	for (unsigned x = 0; x < args.size(); x++)
		a->args[x] = args[x]->invert();
	return a;
}

CnfExpression *
CnfAnd::invert()
{
	CnfOr *a = new CnfOr();
	a->args.resize(args.size());
	for (unsigned x = 0; x < args.size(); x++)
		a->args[x] = args[x]->invert();
	return a;
}

void
CnfAnd::optimise()
{
	bool progress;
	do {
		progress = false;

		if (TIMEOUT)
			return;

		/* First rule: (A | b) & (A | ~b) -> just A. */
		for (unsigned i = 0; i < args.size(); i++) {
			for (unsigned j = i + 1; j < args.size(); j++) {
				/* If two terms differ in a single
				   atom, and that difference is just
				   whether the atom is negatated, they
				   can be merged. */
				bool haveDifference;
				bool haveDisallowedDifference;
				CnfOr *argi = getArg(i);
				CnfOr *argj = getArg(j);
				if (argi->args.size() !=
				    argj->args.size())
					continue;
				haveDifference = false;
				haveDisallowedDifference = false;
				for (unsigned k = 0;
				     k < argi->args.size();
				     k++) {
					if (argi->getArg(k)->getId() !=
					    argj->getArg(k)->getId())
						haveDisallowedDifference = true;
					if (!!dynamic_cast<CnfNot *>(argi->getArg(k)) !=
					    !!dynamic_cast<CnfNot *>(argj->getArg(k))) {
						if (haveDifference)
							haveDisallowedDifference = true;
						else
							haveDifference = true;
					}
				}
				if (haveDisallowedDifference)
					continue;
				if (!haveDifference) {
					/* i and j are identical ->
					 * just kill of j */
				} else {
					/* Yay.  We're going to
					   eliminate a single atom
					   from argi, and eliminate
					   argj completely. */
					for (unsigned k = 0;
					     1;
					     k++) {
						assert(k < argi->args.size());
						assert(argi->getArg(k)->getId() ==
						       argj->getArg(k)->getId());
						if (!!dynamic_cast<CnfNot *>(argi->getArg(k)) !=
						    !!dynamic_cast<CnfNot *>(argj->getArg(k))) {
							/* This is the one */
							argi->args.erase(argi->args.begin() + k);
							argi->clearName();
							break;
						}
					}
				}
				args.erase(args.begin() + j);
				clearName();
				progress = true;
				j--;
			}
		}

		/* Second rule: A & (A | B) -> A */
		for (unsigned i = 0; i < args.size(); i++) {
			for (unsigned j = 0; j < args.size(); j++) {
				if (i == j)
					continue;
				CnfOr *argi = getArg(i);
				CnfOr *argj = getArg(j);
				bool iSubsetJ = true;
				for (unsigned k = 0; iSubsetJ && k < argi->args.size(); k++) {
					bool present = false;
					for (unsigned m = 0; !present && m < argj->args.size(); m++) {
						if (argi->getArg(k)->getId() ==
						    argj->getArg(m)->getId() &&
						    !!dynamic_cast<CnfNot *>(argi->getArg(k)) ==
						    !!dynamic_cast<CnfNot *>(argj->getArg(m)))
							present = true;
					}
					if (!present)
						iSubsetJ = false;
				}
				if (iSubsetJ) {
					/* argi is a subset of argj,
					 * so argj can be safely
					 * eliminated. */
					progress = true;
					args.erase(args.begin() + j);
					clearName();
					/* Start again from the
					 * beginning. */
					i = j = 0;
				}
			}
		}

		/* Third rule: a & (B | ~a) -> a & B. */
		for (unsigned i = 0; i < args.size(); i++) {
			CnfOr *argi = getArg(i);
			if (argi->args.size() != 1)
				continue;
			CnfAtom *argiA = argi->getArg(0);
			for (unsigned j = 0; j < args.size(); j++) {
				if (j == i)
					continue;
				CnfOr *argj = getArg(j);
				for (unsigned k = 0; k < argj->args.size(); k++) {
					CnfAtom *argjA = argj->getArg(k);
					if (argjA->getId() != argiA->getId())
						continue;
					/* Normally, the second rule
					   would have already
					   eliminated argj if this
					   were true, but that isn't
					   always the case if we've
					   modified the structure so
					   that rule 2 now fires where
					   it wouldn't before.  Just
					   leave it until the next
					   iteration. */
					if (!!dynamic_cast<CnfNot *>(argjA) ==
					    !!dynamic_cast<CnfNot *>(argiA)) {
						continue;
					}
					progress = true;
					argj->args.erase(argj->args.begin() + k);
					argj->clearName();
					k--;
				}
			}
		}
	} while (progress);
}

static void
buildVarMap(IRExpr *inp, std::map<IRExpr *, CnfExpression *> &toVars,
	    std::map<int, IRExpr *> &toExprs)
{
	if (toVars.count(inp))
		return;
	if (inp->tag == Iex_Associative &&
	    (inp->Iex.Associative.op == Iop_And1 ||
	     inp->Iex.Associative.op == Iop_Or1)) {
		for (int x = 0; x < inp->Iex.Associative.nr_arguments; x++)
			buildVarMap(inp->Iex.Associative.contents[x],
				    toVars,
				    toExprs);
	} else if (inp->tag == Iex_Unop &&
		   inp->Iex.Unop.op == Iop_Not1) {
		buildVarMap(inp->Iex.Unop.arg, toVars, toExprs);
	} else {
		CnfVariable *v = new CnfVariable();
		toExprs[v->id] = inp;
		toVars[inp] = v;
	}
}

static CnfExpression *
convertIRExprToCNF(IRExpr *inp, std::map<IRExpr *, CnfExpression *> &m)
{
	CnfExpression *r;
	if (m.count(inp))
		return m[inp];
	if (inp->tag == Iex_Unop) {
		assert(inp->Iex.Unop.op == Iop_Not1);
		r = new CnfNot(convertIRExprToCNF(inp->Iex.Unop.arg, m));
	} else {
		CnfGrouping *r2;
		assert(inp->tag == Iex_Associative);
		if (inp->Iex.Associative.op == Iop_And1) {
			r2 = new CnfAnd();
		} else {
			assert(inp->Iex.Associative.op == Iop_Or1);
			r2 = new CnfOr();
		}
		for (int x = 0; x < inp->Iex.Associative.nr_arguments; x++)
			r2->addChild(convertIRExprToCNF(inp->Iex.Associative.contents[x], m));
		r = r2;
	}
	return r;
}

static IRExpr *
internIRExpr(IRExpr *e, std::map<IRExpr *, IRExpr *> &lookupTable)
{
	if (lookupTable.count(e))
		return lookupTable[e];
	switch (e->tag) {
	case Iex_Binder:
	case Iex_Get:
	case Iex_RdTmp:
	case Iex_Const:
	case Iex_FreeVariable:
		break;
	case Iex_GetI:
		e->Iex.GetI.ix = internIRExpr(e->Iex.GetI.ix, lookupTable);
		break;
	case Iex_Qop:
		e->Iex.Qop.arg4 = internIRExpr(e->Iex.Qop.arg4, lookupTable);
	case Iex_Triop:
		e->Iex.Qop.arg3 = internIRExpr(e->Iex.Qop.arg3, lookupTable);
	case Iex_Binop:
		e->Iex.Qop.arg2 = internIRExpr(e->Iex.Qop.arg2, lookupTable);
	case Iex_Unop:
		e->Iex.Qop.arg1 = internIRExpr(e->Iex.Qop.arg1, lookupTable);
		break;
	case Iex_Load:
		e->Iex.Load.addr = internIRExpr(e->Iex.Load.addr, lookupTable);
		break;
	case Iex_CCall:
		for (int x = 0; e->Iex.CCall.args[x]; x++)
			e->Iex.CCall.args[x] =
				internIRExpr(e->Iex.CCall.args[x], lookupTable);
		break;
	case Iex_Mux0X:
		e->Iex.Mux0X.cond = internIRExpr(e->Iex.Mux0X.cond, lookupTable);
		e->Iex.Mux0X.expr0 = internIRExpr(e->Iex.Mux0X.expr0, lookupTable);
		e->Iex.Mux0X.exprX = internIRExpr(e->Iex.Mux0X.exprX, lookupTable);
		break;
	case Iex_Associative:
		for (int x = 0; x < e->Iex.Associative.nr_arguments; x++)
			e->Iex.Associative.contents[x] =
				internIRExpr(e->Iex.Associative.contents[x], lookupTable);
		break;
	}
	for (std::map<IRExpr *, IRExpr *>::iterator it = lookupTable.begin();
	     it != lookupTable.end();
	     it++) {
		IRExpr *other = it->first;
		if (other->tag != e->tag)
			continue;
		switch (e->tag) {
			/* For some structures, equality can be
			   checked by bitwise comparison. */
#define do_case(n)							\
			case Iex_ ## n:					\
				if (memcmp(&other->Iex. n,		\
					   &e->Iex. n,			\
					   sizeof(e->Iex. n)))		\
					continue;			\
			break
			do_case(Binder);
			do_case(Get);
			do_case(GetI);
			do_case(RdTmp);
			do_case(Qop);
			do_case(Triop);
			do_case(Binop);
			do_case(Unop);
			do_case(Load);
			do_case(Mux0X);
			do_case(FreeVariable);
#undef do_case
			/* Others are harder. */
		case Iex_CCall: {
			bool bad;
			if (other->Iex.CCall.retty != e->Iex.CCall.retty)
				continue;
			bad = false;
			for (int x = 0; !bad && e->Iex.CCall.args[x]; x++) {
				if (e->Iex.CCall.args[x] !=
				    other->Iex.CCall.args[x])
					bad = true;
			}
			if (bad)
				continue;
			break;
		}

		case Iex_Associative: {
			if (other->Iex.Associative.op != e->Iex.Associative.op ||
			    other->Iex.Associative.nr_arguments != e->Iex.Associative.nr_arguments)
				continue;
			bool bad = false;
			for (int x = 0; !bad && x < e->Iex.Associative.nr_arguments; x++)
				if (e->Iex.Associative.contents[x] !=
				    other->Iex.Associative.contents[x])
					bad = true;
			if (bad)
				continue;
			break;
		}

		case Iex_Const:
			if (!physicallyEqual(e->Iex.Const.con,
					     other->Iex.Const.con))
				continue;
			break;
		}

		/* If we get here, they match and we're done. */

		/* If the expressions are equal, then any optimisation
		   which has been applied to one can be assumed to
		   have been applied to the other. */
		e->optimisationsApplied |= it->second->optimisationsApplied;
		it->second->optimisationsApplied |= e->optimisationsApplied;

		lookupTable[e] = it->second;
		return it->second;
	}
	/* No duplicates of this IRExpr found so far */
	lookupTable[e] = e;
	return e;
}

static IRExpr *
internIRExpr(IRExpr *x)
{
	std::map<IRExpr *, IRExpr *> t;
	return internIRExpr(x, t);
}

/* A different kind of simplification: assume that @inp is a boolean
   expression, and consists of some tree of And1, Or1, and Not1
   expressions with other stuff at the leaves.  Treat all of the other
   stuff as opaque boolean variables, and then convert to CNF.  Try to
   simplify it there.  If we make any reasonable progress, convert
   back to the standard IRExpr form and return the result.  Otherwise,
   just return @inp. */
static IRExpr *
simplifyIRExprAsBoolean(IRExpr *inp)
{
	std::map<IRExpr *, CnfExpression *> exprsToVars;
	std::map<int, IRExpr *> varsToExprs;
	CnfExpression *root;
	CnfAnd *a;
	int nr_terms;

	if (!((inp->tag == Iex_Unop &&
	       inp->Iex.Unop.op == Iop_Not1) ||
	      (inp->tag == Iex_Associative &&
	       (inp->Iex.Associative.op == Iop_Or1 ||
		inp->Iex.Associative.op == Iop_And1))))
		return inp;

	inp = internIRExpr(inp);

	buildVarMap(inp, exprsToVars, varsToExprs);
	root = convertIRExprToCNF(inp, exprsToVars);
	nr_terms = root->complexity();
	root = root->CNF();
	a = dynamic_cast<CnfAnd *>(root);
	if (!a) {
		CnfOr *o = dynamic_cast<CnfOr *>(root);
		if (!o) {
			assert(dynamic_cast<CnfNot *>(root) ||
			       dynamic_cast<CnfVariable *>(root));
			o = new CnfOr();
			o->addChild(root);
		}
		a = new CnfAnd();
		a->addChild(o);
	}
	a->sort();
	a->optimise();
	IRExprTransformer t;
	IRExpr *r = root->asIRExpr(varsToExprs, t);
	if (exprComplexity(r) < exprComplexity(inp))
		return r;
	else
		return inp;
}

static IRExpr *optimiseIRExpr(IRExpr *src, const AllowableOptimisations &opt, bool *done_something);

IRExpr *
optimiseIRExprFP(IRExpr *e, const AllowableOptimisations &opt, bool *done_something)
{
	bool progress;
	progress = false;
	e = optimiseIRExpr(e, opt, &progress);
	if (progress) {
		*done_something = true;
		while (progress) {
			if (TIMEOUT)
				return e;
			progress = false;
			e = optimiseIRExpr(e, opt, &progress);
		}
	}
	e->optimisationsApplied |= opt.asUnsigned();
	return e;
}

static IRExpr *
optimiseIRExpr(IRExpr *src, const AllowableOptimisations &opt, bool *done_something)
{
	if (TIMEOUT)
		return src;

	if (!(opt.asUnsigned() & ~src->optimisationsApplied))
		return src;
	/* First, recursively optimise our arguments. */
	switch (src->tag) {
	case Iex_Qop:
		src->Iex.Qop.arg4 = optimiseIRExprFP(src->Iex.Qop.arg4, opt, done_something);
	case Iex_Triop:
		src->Iex.Triop.arg3 = optimiseIRExprFP(src->Iex.Triop.arg3, opt, done_something);
	case Iex_Binop:
		src->Iex.Binop.arg2 = optimiseIRExprFP(src->Iex.Binop.arg2, opt, done_something);
	case Iex_Unop:
		src->Iex.Unop.arg = optimiseIRExprFP(src->Iex.Unop.arg, opt, done_something);
		break;
	case Iex_Load:
		src->Iex.Load.addr = optimiseIRExprFP(src->Iex.Load.addr, opt, done_something);
#if 0
		if (src->Iex.Load.addr->tag == Iex_Const &&
		    (long)src->Iex.Load.addr->Iex.Const.con->Ico.U64 < 4096)
			dbg_break("optimising load to load of strange constant address (IRExpr *)%p\n",
				  src);
#endif
		break;
	case Iex_CCall: {
		for (int x = 0; src->Iex.CCall.args[x]; x++) {
			src->Iex.CCall.args[x] =
				optimiseIRExprFP(src->Iex.CCall.args[x], opt, done_something);
		}
		/* Special cases for amd64g_calculate_condition. */
		if (!strcmp(src->Iex.CCall.cee->name,
			    "amd64g_calculate_condition")) {
			IRExpr *e;
			e = optimise_condition_calculation(
				src->Iex.CCall.args[0],
				src->Iex.CCall.args[1],
				src->Iex.CCall.args[2],
				src->Iex.CCall.args[3],
				src->Iex.CCall.args[4],
				opt);
			if (e) {
				*done_something = true;
				src = e;
			}
		}
		break;
	}
	case Iex_Mux0X:
		src->Iex.Mux0X.cond = optimiseIRExprFP(src->Iex.Mux0X.cond, opt, done_something);
		src->Iex.Mux0X.expr0 = optimiseIRExprFP(src->Iex.Mux0X.expr0, opt, done_something);
		src->Iex.Mux0X.exprX = optimiseIRExprFP(src->Iex.Mux0X.exprX, opt, done_something);
		break;
	case Iex_Associative:
		for (int x = 0; x < src->Iex.Associative.nr_arguments; x++)
			src->Iex.Associative.contents[x] =
				optimiseIRExprFP(src->Iex.Associative.contents[x], opt, done_something);
		break;
	default:
		break;
	}

	if (src->tag == Iex_Associative) {
		/* Drag up nested associatives. */
		bool haveNestedAssocs = false;
		for (int x = 0; !haveNestedAssocs && x < src->Iex.Associative.nr_arguments; x++)
			if (src->Iex.Associative.contents[x]->tag == Iex_Associative &&
			    src->Iex.Associative.contents[x]->Iex.Associative.op ==
				src->Iex.Associative.op)
				haveNestedAssocs = true;
		if (haveNestedAssocs) {
			IRExpr *e = IRExpr_Associative(src->Iex.Associative.op, NULL);
			for (int x = 0; x < src->Iex.Associative.nr_arguments; x++) {
				IRExpr *arg = src->Iex.Associative.contents[x];
				if (arg->tag == Iex_Associative &&
				    arg->Iex.Associative.op == src->Iex.Associative.op) {
					for (int y = 0; y < arg->Iex.Associative.nr_arguments; y++)
						addArgumentToAssoc(e, arg->Iex.Associative.contents[y]);
				} else {
					addArgumentToAssoc(e, arg);
				}
			}
			src = e;
			*done_something = true;
		}

		/* Sort IRExprs so that ``related'' expressions are likely to
		 * be close together. */
		if (operationCommutes(src->Iex.Associative.op))
			std::sort(src->Iex.Associative.contents,
				  src->Iex.Associative.contents + src->Iex.Associative.nr_arguments,
				  sortIRExprs);
		/* Fold together constants.  For commutative
		   operations they'll all be at the beginning, but
		   don't assume that associativity implies
		   commutativity. */
		for (int x = 0; x + 1 < src->Iex.Associative.nr_arguments; x++) {
			IRExpr *a, *b;
			a = src->Iex.Associative.contents[x];
			b = src->Iex.Associative.contents[x+1];
			if (a->tag == Iex_Const && b->tag == Iex_Const) {
				IRExpr *res;
				IRConst *l, *r;
				l = a->Iex.Const.con;
				r = b->Iex.Const.con;
				switch (src->Iex.Associative.op) {
				case Iop_Add8:
					res = IRExpr_Const(
						IRConst_U8((l->Ico.U8 + r->Ico.U8) & 0xff));
					break;
				case Iop_Add16:
					res = IRExpr_Const(
						IRConst_U16((l->Ico.U16 + r->Ico.U16) & 0xffff));
					break;
				case Iop_Add32:
					res = IRExpr_Const(
						IRConst_U32((l->Ico.U32 + r->Ico.U32) & 0xffffffff));
					break;
				case Iop_Add64:
					res = IRExpr_Const(IRConst_U64(l->Ico.U64 + r->Ico.U64));
					break;
				case Iop_And1:
					res = IRExpr_Const(IRConst_U1(l->Ico.U1 & r->Ico.U1));
					break;
				case Iop_Or1:
					res = IRExpr_Const(IRConst_U1(l->Ico.U1 | r->Ico.U1));
					break;
				case Iop_And8:
					res = IRExpr_Const(IRConst_U8(l->Ico.U8 & r->Ico.U8));
					break;
				case Iop_And32:
					res = IRExpr_Const(IRConst_U32(l->Ico.U32 & r->Ico.U32));
					break;
				case Iop_Or32:
					res = IRExpr_Const(IRConst_U32(l->Ico.U32 | r->Ico.U32));
					break;
				case Iop_And64:
					res = IRExpr_Const(IRConst_U64(l->Ico.U64 & r->Ico.U64));
					break;
				case Iop_Xor32:
					res = IRExpr_Const(IRConst_U32(l->Ico.U32 ^ r->Ico.U32));
					break;
				default:
					printf("Warning: can't constant-fold in ");
					ppIRExpr(src, stdout);
					printf("\n");
					res = NULL;
					break;
				}
				if (res) {
					res = optimiseIRExprFP(res, opt, done_something);
					memmove(src->Iex.Associative.contents + x + 1,
						src->Iex.Associative.contents + x + 2,
						sizeof(IRExpr *) * (src->Iex.Associative.nr_arguments - x - 2));
					src->Iex.Associative.nr_arguments--;
					src->Iex.Associative.contents[x] = res;
					x--;
					*done_something = true;
				}
			}
		}
		/* Some special cases for And1: 1 & x -> x, 0 & x -> 0 */
		if (src->Iex.Associative.op == Iop_And1) {
			/* If there are any constants, they'll be at the start. */
			while (src->Iex.Associative.nr_arguments > 1 &&
			       src->Iex.Associative.contents[0]->tag == Iex_Const) {
				IRConst *c = src->Iex.Associative.contents[0]->Iex.Const.con;
				*done_something = true;
				if (c->Ico.U1) {
					purgeAssocArgument(src, 0);
				} else {
					return src->Iex.Associative.contents[0];
				}
			}
		}
		/* Likewise for Or1 */
		if (src->Iex.Associative.op == Iop_Or1) {
			while (src->Iex.Associative.nr_arguments > 1 &&
			       src->Iex.Associative.contents[0]->tag == Iex_Const) {
				IRConst *c = src->Iex.Associative.contents[0]->Iex.Const.con;
				*done_something = true;
				if (!c->Ico.U1) {
					purgeAssocArgument(src, 0);
				} else {
					return src->Iex.Associative.contents[0];
				}
			}
		}

		/* x & x -> x, for any and-like operator */
		if (src->Iex.Associative.op >= Iop_And8 && src->Iex.Associative.op <= Iop_And64) {
			for (int it1 = 0;
			     it1 < src->Iex.Associative.nr_arguments;
			     it1++) {
				for (int it2 = it1 + 1;
				     it2 < src->Iex.Associative.nr_arguments;
					) {
					if (definitelyEqual(src->Iex.Associative.contents[it1],
							    src->Iex.Associative.contents[it2],
							    opt)) {
						*done_something = true;
						purgeAssocArgument(src, it2);
					} else {
						it2++;
					}
				}
			}
		}

		/* x + -x -> 0, for any plus-like operator, so remove
		 * both x and -x from the list. */
		/* Also do x & ~x -> 0, x ^ x -> 0, while we're here. */
		if (opt.xPlusMinusX) {
			bool plus_like;
			bool and_like;
			bool xor_like;
			plus_like = src->Iex.Associative.op >= Iop_Add8 && src->Iex.Associative.op <= Iop_Add64;
			and_like = (src->Iex.Associative.op >= Iop_And8 && src->Iex.Associative.op <= Iop_And64) ||
				src->Iex.Associative.op == Iop_And1;
			xor_like = src->Iex.Associative.op >= Iop_Xor8 && src->Iex.Associative.op <= Iop_Xor64;
			if (plus_like || and_like || xor_like) {
				for (int it1 = 0;
				     it1 < src->Iex.Associative.nr_arguments;
					) {
					IRExpr *l = src->Iex.Associative.contents[it1];
					int it2;
					for (it2 = 0;
					     it2 < src->Iex.Associative.nr_arguments;
					     it2++) {
						if (it2 == it1)
							continue;
						IRExpr *r = src->Iex.Associative.contents[it2];
						bool purge;
						if (plus_like) {
							if (r->tag == Iex_Unop) {
								purge = r->Iex.Unop.op >= Iop_Neg8 &&
									r->Iex.Unop.op <= Iop_Neg64;
							} else {
								purge = false;
							}
							if (purge)
								purge = definitelyEqual(l, r->Iex.Unop.arg,
											opt.disablexPlusMinusX());
						} else if (and_like) {
							if (r->tag == Iex_Unop)
								purge = (r->Iex.Unop.op >= Iop_Not8 &&
									 r->Iex.Unop.op <= Iop_Not64) ||
									r->Iex.Unop.op == Iop_Not1;
							else
								purge = false;
							if (purge)
								purge = definitelyEqual(l, r->Iex.Unop.arg,
											opt.disablexPlusMinusX());
						} else {
							assert(xor_like);
							purge = definitelyEqual(l, r,
										opt.disablexPlusMinusX());
						}

						if (purge) {
							/* Careful: do the largest index first so that the
							   other index remains valid. */
							*done_something = true;
							if (it1 < it2) {
								purgeAssocArgument(src, it2);
								src->Iex.Associative.contents[it1] =
									IRExpr_Const(IRConst_U64(0));
							} else {
								purgeAssocArgument(src, it1);
								src->Iex.Associative.contents[it2] =
									IRExpr_Const(IRConst_U64(0));
							}
							break;
						}
					}
					if (it2 == src->Iex.Associative.nr_arguments)
						it1++;
				}
			}
			if (src->Iex.Associative.nr_arguments == 0) {
				*done_something = true;
				switch (src->Iex.Associative.op) {
				case Iop_Add8:
				case Iop_Xor8:
					return IRExpr_Const(IRConst_U8(0));
				case Iop_Add16:
				case Iop_Xor16:
					return IRExpr_Const(IRConst_U16(0));
				case Iop_Add32:
				case Iop_Xor32:
					return IRExpr_Const(IRConst_U32(0));
				case Iop_Add64:
				case Iop_Xor64:
					return IRExpr_Const(IRConst_U64(0));

				case Iop_And1:
					return IRExpr_Const(IRConst_U1(1));
				case Iop_And8:
					return IRExpr_Const(IRConst_U8(0xff));
				case Iop_And16:
					return IRExpr_Const(IRConst_U16(0xffff));
				case Iop_And32:
					return IRExpr_Const(IRConst_U32(0xffffffff));
				case Iop_And64:
					return IRExpr_Const(IRConst_U64(0xfffffffffffffffful));

				case Iop_Or1:
					return IRExpr_Const(IRConst_U1(0));

				default:
					abort();
				}
			}
		}

		/* If the size is reduced to one, eliminate the assoc list */
		if (src->Iex.Associative.nr_arguments == 1) {
			*done_something = true;
			return src->Iex.Associative.contents[0];
		}
	}

	/* Now use some special rules to simplify a few classes of binops and unops. */
	if (src->tag == Iex_Unop) {
		if (src->Iex.Unop.op == Iop_64to1 &&
		    ((src->Iex.Unop.arg->tag == Iex_Associative &&
		      (src->Iex.Unop.arg->Iex.Associative.op == Iop_And1 ||
		       src->Iex.Unop.arg->Iex.Associative.op == Iop_Or1)) ||
		     (src->Iex.Unop.arg->tag == Iex_Binop &&
		      ((src->Iex.Unop.arg->Iex.Binop.op >= Iop_CmpEQ8 &&
			src->Iex.Unop.arg->Iex.Binop.op <= Iop_CmpNE64) ||
		       (src->Iex.Unop.arg->Iex.Binop.op >= Iop_CmpLT32S &&
			src->Iex.Unop.arg->Iex.Binop.op <= Iop_CmpLE64U))))) {
			/* This can happen sometimes because of the
			   way we simplify condition codes.  Very easy
			   fix: strip off the outer 64to1. */
			*done_something = true;
			return src->Iex.Unop.arg;
		}

		if (src->Iex.Unop.op >= Iop_8Uto16 &&
		    src->Iex.Unop.op <= Iop_32Uto64) {
			/* Get rid of signed upcasts; they tend to
			   show up where you don't want them, and they
			   don't actually do anything useful. */
			*done_something = true;
			return src->Iex.Unop.arg;
		}

		if (src->Iex.Unop.op == Iop_Not1 &&
		    src->Iex.Unop.arg->tag == Iex_Unop &&
		    src->Iex.Unop.arg->Iex.Unop.op == src->Iex.Unop.op) {
			*done_something = true;
			return src->Iex.Unop.arg->Iex.Unop.arg;
		}

		if (src->Iex.Unop.op == Iop_Not1 &&
		    src->Iex.Unop.arg->tag == Iex_Associative &&
		    (src->Iex.Unop.arg->Iex.Associative.op == Iop_And1 ||
		     src->Iex.Unop.arg->Iex.Associative.op == Iop_Or1)) {
			/* Convert ~(x & y) to ~x | ~y */
			IRExpr *a = IRExpr_Associative(src->Iex.Unop.arg);
			for (int i = 0;
			     i < a->Iex.Associative.nr_arguments;
			     i++) {
				a->Iex.Associative.contents[i] =
					optimiseIRExprFP(
						IRExpr_Unop(
							Iop_Not1,
							a->Iex.Associative.contents[i]),
						opt,
						done_something);
			}
			if (a->Iex.Associative.op == Iop_And1)
				a->Iex.Associative.op = Iop_Or1;
			else
				a->Iex.Associative.op = Iop_And1;
			*done_something = true;
			return a;
		}
		if (src->Iex.Unop.op == Iop_BadPtr &&
		    src->Iex.Unop.arg->tag == Iex_Associative &&
		    src->Iex.Unop.arg->Iex.Associative.op == Iop_Add64 &&
		    src->Iex.Unop.arg->Iex.Associative.nr_arguments == 2 &&
		    src->Iex.Unop.arg->Iex.Associative.contents[0]->tag == Iex_Const) {
			/* BadPtr(k + x) -> BadPtr(x) if k is a
			 * constant.  That's not strictly speaking
			 * true, because it's always possible that k
			 * is enough to push you over the boundary
			 * between valid and invalid memory, but
			 * that's so rare that I'm willing to ignore
			 * it. */
			*done_something = true;
			src->Iex.Unop.arg = src->Iex.Unop.arg->Iex.Associative.contents[1];
			return src;
		}
		if (src->Iex.Unop.arg->tag == Iex_Const) {
			IRConst *c = src->Iex.Unop.arg->Iex.Const.con;
			switch (src->Iex.Unop.op) {
			case Iop_Neg8:
				*done_something = true;
				return IRExpr_Const(IRConst_U8(-c->Ico.U8));
			case Iop_Neg16:
				*done_something = true;
				return IRExpr_Const(IRConst_U16(-c->Ico.U16));
			case Iop_Neg32:
				*done_something = true;
				return IRExpr_Const(IRConst_U32(-c->Ico.U32));
			case Iop_Neg64:
				*done_something = true;
				return IRExpr_Const(IRConst_U64(-c->Ico.U64));
			case Iop_Not1:
				*done_something = true;
				return IRExpr_Const(IRConst_U1(c->Ico.U1 ^ 1));
			case Iop_32Uto64:
				*done_something = true;
				return IRExpr_Const(IRConst_U64(c->Ico.U32));
			case Iop_32Sto64:
				*done_something = true;
				return IRExpr_Const(IRConst_U64((int)c->Ico.U32));
			case Iop_1Uto8:
				*done_something = true;
				return IRExpr_Const(IRConst_U8(c->Ico.U1));
			case Iop_64to1:
				*done_something = true;
				return IRExpr_Const(IRConst_U1(!!c->Ico.U64));
			case Iop_64to32:
				*done_something = true;
				return IRExpr_Const(IRConst_U32(c->Ico.U64));
			case Iop_BadPtr:
				if (c->Ico.U64 < 4096) {
					*done_something = true;
					return IRExpr_Const(IRConst_U1(1));
				}
				/* Could sensibly just check that the
				 * target address isn't mapped here,
				 * on the assumption that anything not
				 * in the binary won't have a fixed
				 * address, but that then depends on
				 * the machine state, and I don't want
				 * to make optimiseIRExpr depend on
				 * machine state just for that. */
				break;
			default:
				break;
			}
		}
	} else if (src->tag == Iex_Binop) {
		IRExpr *l = src->Iex.Binop.arg1;
		IRExpr *r = src->Iex.Binop.arg2;
		if (src->Iex.Binop.op == Iop_Xor1) {
			/* Convert A ^ B to (A & ~B) | (~A & B).  It's
			   bigger, but it's worth it just normalise
			   things. */
			*done_something = true;
			return optimiseIRExpr(
				IRExpr_Associative(
					Iop_Or1,
					IRExpr_Associative(
						Iop_And1,
						src->Iex.Binop.arg1,
						IRExpr_Unop(Iop_Not1, src->Iex.Binop.arg2),
						NULL),
					IRExpr_Associative(
						Iop_And1,
						src->Iex.Binop.arg2,
						IRExpr_Unop(Iop_Not1, src->Iex.Binop.arg1),
						NULL),
					NULL),
				opt,
				done_something);
		}
		if (operationAssociates(src->Iex.Binop.op)) {
			/* Convert to an associative operation. */
			*done_something = true;
			return optimiseIRExpr(
				IRExpr_Associative(
					src->Iex.Binop.op,
					l,
					r,
					NULL),
				opt,
				done_something);
		}
		if (src->Iex.Binop.op >= Iop_Sub8 &&
		    src->Iex.Binop.op <= Iop_Sub64) {
			/* Replace a - b with a + (-b), so as to
			   eliminate binary -. */
			*done_something = true;
			src->Iex.Binop.op = (IROp)(src->Iex.Binop.op - Iop_Sub8 + Iop_Add8);
			r = src->Iex.Binop.arg2 =
				optimiseIRExprFP(
					IRExpr_Unop( (IROp)((src->Iex.Binop.op - Iop_Add8) + Iop_Neg8),
						     r ),
					opt,
					done_something);
		}
		/* If a op b commutes, sort the arguments. */
		if (operationCommutes(src->Iex.Binop.op) &&
		    sortIRExprs(r, l)) {
			src->Iex.Binop.arg1 = r;
			src->Iex.Binop.arg2 = l;
			l = src->Iex.Binop.arg1;
			r = src->Iex.Binop.arg2;
			*done_something = true;
		}

		/* x << 0 -> x */
		if (src->Iex.Binop.op >= Iop_Shl8 && src->Iex.Binop.op <= Iop_Shl64 &&
		    src->Iex.Binop.arg2->tag == Iex_Const &&
		    src->Iex.Binop.arg2->Iex.Const.con->Ico.U8 == 0) {
			*done_something = true;
			return src->Iex.Binop.arg1;
		}

		/* We simplify == expressions with sums on the left
		   and right by trying to move all of the constants to
		   the left and all of the non-constants to the
		   right. */
		if (src->Iex.Binop.op == Iop_CmpEQ64) {
			if (r->tag == Iex_Associative &&
			    r->Iex.Associative.op == Iop_Add64 &&
			    r->Iex.Associative.contents[0]->tag == Iex_Const) {
				assert(r->Iex.Associative.nr_arguments > 1);
				/* a == C + b -> -C + a == b */
				IRExpr *cnst = r->Iex.Associative.contents[0];
				IRExpr *newRight = IRExpr_Associative(r);
				purgeAssocArgument(newRight, 0);
				IRExpr *newLeft = IRExpr_Associative(
					Iop_Add64,
					IRExpr_Unop(
						Iop_Neg64,
						cnst),
					l,
					NULL);
				l = src->Iex.Binop.arg1 = optimiseIRExprFP(newLeft, opt, done_something);
				r = src->Iex.Binop.arg2 = optimiseIRExprFP(newRight, opt, done_something);
				*done_something = true;
			}
			if (l->tag == Iex_Associative &&
			    l->Iex.Associative.op == Iop_Add64) {
				/* C + a == b -> C == b - a */
				assert(l->Iex.Associative.nr_arguments > 1);
				IRExpr *newR = IRExpr_Associative(Iop_Add64, r, NULL);
				for (int it = 1;
				     it < l->Iex.Associative.nr_arguments;
				     it++)
					addArgumentToAssoc(newR,
							   IRExpr_Unop(
								   Iop_Neg64,
								   l->Iex.Associative.contents[it]));
				IRExpr *cnst = l->Iex.Associative.contents[0];
				if (cnst->tag != Iex_Const) {
					addArgumentToAssoc(newR,
							   IRExpr_Unop(
								   Iop_Neg64,
								   cnst));
					cnst = IRExpr_Const(IRConst_U64(0));
				}
				l = src->Iex.Binop.arg1 = cnst;
				r = src->Iex.Binop.arg2 = optimiseIRExprFP(newR, opt, done_something);
				*done_something = true;
			}
			/* If, in a == b, a and b are physically
			 * identical, the result is a constant 1. */
			if (physicallyEqual(l, r)) {
				*done_something = true;
				return IRExpr_Const(IRConst_U1(1));
			}

			/* Otherwise, a == b -> 0 == b - a, provided that a is not a constant. */
			if (l->tag != Iex_Const) {
				src->Iex.Binop.arg1 = IRExpr_Const(IRConst_U64(0));
				src->Iex.Binop.arg2 =
					IRExpr_Binop(
						Iop_Add64,
						r,
						IRExpr_Unop(
							Iop_Neg64,
							l));
				*done_something = true;
				return optimiseIRExpr(src, opt, done_something);
			}
		}

		/* And another one: -x == c -> x == -c if c is a constant. */
		if (src->Iex.Binop.op == Iop_CmpEQ64 &&
		    src->Iex.Binop.arg1->tag == Iex_Unop &&
		    src->Iex.Binop.arg1->Iex.Unop.op == Iop_Neg64 &&
		    src->Iex.Binop.arg2->tag == Iex_Const) {
			src->Iex.Binop.arg1 = src->Iex.Binop.arg1->Iex.Unop.arg;
			src->Iex.Binop.arg2 = IRExpr_Const(
				IRConst_U64(-src->Iex.Binop.arg2->Iex.Const.con->Ico.U64));
			*done_something = true;
			return optimiseIRExpr(src, opt, done_something);
		}

		/* If enabled, assume that the stack is ``private'',
		   in the sense that it doesn't alias with any global
		   variables, and is therefore never equal to any
		   constants which are present in the machine code. */
		if (opt.assumePrivateStack &&
		    src->Iex.Binop.op == Iop_CmpEQ64 &&
		    src->Iex.Binop.arg2->tag == Iex_Get &&
		    src->Iex.Binop.arg2->Iex.Get.offset == OFFSET_amd64_RSP &&
		    src->Iex.Binop.arg1->tag == Iex_Const) {
			*done_something = true;
			return IRExpr_Const(IRConst_U1(0));
		}

		/* If both arguments are constant, try to constant
		 * fold everything away. */
		if (src->Iex.Binop.arg1->tag == Iex_Const &&
		    src->Iex.Binop.arg2->tag == Iex_Const) {
			switch (src->Iex.Binop.op) {
			case Iop_CmpEQ32:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U1(
						src->Iex.Binop.arg1->Iex.Const.con->Ico.U32 ==
						src->Iex.Binop.arg2->Iex.Const.con->Ico.U32));
			case Iop_CmpLT64S:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U1(
						(long)src->Iex.Binop.arg1->Iex.Const.con->Ico.U64 <
						(long)src->Iex.Binop.arg2->Iex.Const.con->Ico.U64));
			case Iop_CmpEQ64:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U1(
						src->Iex.Binop.arg1->Iex.Const.con->Ico.U64 ==
						src->Iex.Binop.arg2->Iex.Const.con->Ico.U64));
			case Iop_Sar32:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U32(
						src->Iex.Binop.arg1->Iex.Const.con->Ico.U32 <<
						src->Iex.Binop.arg2->Iex.Const.con->Ico.U8));
			case Iop_Sar64:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U64(
						src->Iex.Binop.arg1->Iex.Const.con->Ico.U32 <<
						src->Iex.Binop.arg2->Iex.Const.con->Ico.U8));
			default:
				break;
			}
		}

	} else if (src->tag == Iex_Mux0X) {
		if (src->Iex.Mux0X.cond->tag == Iex_Const) {
			*done_something = true;
			if (src->Iex.Mux0X.cond->Iex.Const.con->Ico.U1)
				return src->Iex.Mux0X.exprX;
			else
				return src->Iex.Mux0X.expr0;
		}
	}

	return src;
}

static IRExpr *
optimiseIRExpr(IRExpr *e, const AllowableOptimisations &opt)
{
	bool ign;
	ign = false;
	e = optimiseIRExprFP(e, opt, &ign);
	e = simplifyIRExprAsBoolean(e);
	e = optimiseIRExprFP(e, opt, &ign);
	return e;
}

IRExpr *
simplifyIRExpr(IRExpr *a, const AllowableOptimisations &opt)
{
	bool done_something;

	do {
		done_something = false;
		if (TIMEOUT)
			return a;
		a = optimiseIRExpr(a, opt, &done_something);
		a = internIRExpr(a);
		a = simplifyIRExprAsBoolean(a);
		a = optimiseIRExpr(a, opt, &done_something);
	} while (done_something);

	return a;
}

bool
definitelyEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt)
{
	IRExpr *r = optimiseIRExpr(IRExpr_Binop(Iop_CmpEQ64, a, b), opt);
	return r->tag == Iex_Const && r->Iex.Const.con->Ico.U1;
}
bool
definitelyNotEqual(IRExpr *a, IRExpr *b, const AllowableOptimisations &opt)
{
	IRExpr *r = optimiseIRExpr(IRExpr_Binop(Iop_CmpEQ64, a, b), opt);
	return r->tag == Iex_Const && !r->Iex.Const.con->Ico.U1;
}

bool
isBadAddress(IRExpr *e, const AllowableOptimisations &opt, OracleInterface *oracle)
{
	return e->tag == Iex_Const &&
		(long)e->Iex.Const.con->Ico.U64 < 4096;
}

bool
definitelyUnevaluatable(IRExpr *e, const AllowableOptimisations &opt, OracleInterface *oracle)
{
	if (TIMEOUT)
		return false;
	switch (e->tag) {
	case Iex_Binder:
	case Iex_Get:
	case Iex_RdTmp:
	case Iex_Const:
	case Iex_FreeVariable:
		return false;
	case Iex_GetI:
		return definitelyUnevaluatable(e->Iex.GetI.ix, opt, oracle);
	case Iex_Qop:
		if (definitelyUnevaluatable(e->Iex.Qop.arg4, opt, oracle))
			return true;
	case Iex_Triop:
		if (definitelyUnevaluatable(e->Iex.Qop.arg3, opt, oracle))
			return true;
	case Iex_Binop:
		if (definitelyUnevaluatable(e->Iex.Qop.arg2, opt, oracle))
			return true;
	case Iex_Unop:
		if (definitelyUnevaluatable(e->Iex.Qop.arg1, opt, oracle))
			return true;
		return false;
	case Iex_CCall:
		for (int x = 0; e->Iex.CCall.args[x]; x++)
			if (definitelyUnevaluatable(e->Iex.CCall.args[x], opt, oracle))
				return true;
		return false;
	case Iex_Mux0X:
		return definitelyUnevaluatable(e->Iex.Mux0X.cond, opt, oracle);
	case Iex_Associative:
		for (int x = 0; x < e->Iex.Associative.nr_arguments; x++)
			if (definitelyUnevaluatable(e->Iex.Associative.contents[x], opt, oracle))
				return true;
		return false;
	case Iex_Load:
		return isBadAddress(e->Iex.Load.addr, opt, oracle) ||
			definitelyUnevaluatable(e->Iex.Load.addr, opt, oracle);
	}
	abort();
}

static IRType
random_irtype(void)
{
       return (IRType)((unsigned long)Ity_I8 + random() % 7);
}

static IRConst *
random_irconst(void)
{
	switch (random_irtype()) {
	case Ity_I8:
		return IRConst_U8(random() % 256);
	case Ity_I16:
		return IRConst_U16(random() % 65536);
	case Ity_I32:
		return IRConst_U32(random());
	case Ity_I64:
		return IRConst_U64(random());
	case Ity_F32:
	case Ity_I128:
		return random_irconst();
	case Ity_F64:
		return IRConst_F64(random() / (double)random());
	case Ity_V128:
		return IRConst_V128(random());
	default:
		abort();
	}
}

/* The random IRexprs consist of a possible-empty layer of And1, Or1,
 * Xor1, and Not1 operations, followed by a layer of comparisons and
 * boolean functions, and then other stuff underneath. */

static IRExpr *random_irexpr1(unsigned depth);

/* Build arithmetic layer */
static IRExpr *
random_irexpr3(unsigned depth)
{
	if (!depth)
		return IRExpr_Const(IRConst_U64(random()));
	switch (random() % 12) {
	case 0:
		return IRExpr_Const(IRConst_U64(random()));
	case 1:
		return IRExpr_Mux0X(
			random_irexpr1(depth - 1),
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 2:
		return IRExpr_Binop(
			Iop_Add64,
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 3:
		return IRExpr_Binop(
			Iop_And64,
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 4:
		return IRExpr_Binop(
			Iop_Or64,
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 5:
		return IRExpr_Binop(
			Iop_Xor64,
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 6:
		return IRExpr_Unop(
			Iop_Neg64,
			random_irexpr3(depth - 1));
	case 7:
		return IRExpr_Unop(
			Iop_Not64,
			random_irexpr3(depth - 1));
	case 8:
		return IRExpr_Binop(
			Iop_Sub64,
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 9:
		return IRExpr_Binop(
			Iop_Sar64,
			random_irexpr3(depth - 1),
			random_irexpr3(depth - 1));
	case 10:
		return IRExpr_Get(
			(random() % 40) * 8,
			Ity_I64,
			73);
	case 11:
		return IRExpr_RdTmp(random() % 16, 73);
	}
	abort();
}

/* Build comparator layer */
static IRExpr *
random_irexpr2(unsigned depth)
{
	if (!depth)
		return IRExpr_Const(IRConst_U1(random() % 2));
	switch (random() % 6) {
	case 0:
		return IRExpr_Unop(Iop_BadPtr, random_irexpr3(depth - 1));
	case 1:
		return IRExpr_Binop(Iop_CmpEQ64,
				    random_irexpr3(depth - 1),
				    random_irexpr3(depth - 1));
	case 2:
		return IRExpr_Binop(Iop_CmpLT64U,
				    random_irexpr3(depth - 1),
				    random_irexpr3(depth - 1));
	case 3:
		return IRExpr_Binop(Iop_CmpLT64S,
				    random_irexpr3(depth - 1),
				    random_irexpr3(depth - 1));
	case 4:
		return IRExpr_Binop(Iop_CC_OverflowSub,
				    random_irexpr3(depth - 1),
				    random_irexpr3(depth - 1));
	case 5: {
		unsigned op;
		switch (random() % 4) {
		case 0:
			op = AMD64G_CC_OP_COPY;
			break;
		case 1:
			op = AMD64G_CC_OP_ADDQ;
			break;
		case 2:
			op = AMD64G_CC_OP_SUBQ;
			break;
		case 3:
			op = AMD64G_CC_OP_LOGICQ;
			break;
		default:
			abort();
		}
		
		return mkIRExprCCall(
			Ity_I64,
			0,
			"amd64g_calculate_condition",
			(void *)amd64g_calculate_condition,
			mkIRExprVec_5(IRExpr_Const(IRConst_U64(random() % 16)),
				      IRExpr_Const(IRConst_U64(op)),
				      random_irexpr3(depth - 1),
				      random_irexpr3(depth - 1),
				      random_irexpr3(depth - 1)));
	}
	}
	abort();
}

/* Build boolean layer */
static IRExpr *
random_irexpr1(unsigned depth)
{
	if (!depth)
		return IRExpr_Const(IRConst_U1(random() % 2));
	switch (random() % 5) {
	case 0:
		return IRExpr_Binop(Iop_And1,
				    random_irexpr1(depth - 1),
				    random_irexpr1(depth - 1));
	case 1:
		return IRExpr_Binop(Iop_Xor1,
				    random_irexpr1(depth - 1),
				    random_irexpr1(depth - 1));
	case 2:
		return IRExpr_Binop(Iop_Or1,
				    random_irexpr1(depth - 1),
				    random_irexpr1(depth - 1));
	case 3:
		return IRExpr_Unop(Iop_Not1,
				   random_irexpr1(depth - 1));
	case 4:
		return random_irexpr2(depth);
	}
	abort();
}

/* Check that sortIRExprs() produces vaguely sane results. */
void
sanity_check_irexpr_sorter(void)
{
	srandom(time(NULL));
#define NR_EXPRS 10000
	IRExpr *exprs[NR_EXPRS];
	int x;
	int y;

	printf("Generating %d random expressions\n", NR_EXPRS);
	for (x = 0; x < NR_EXPRS; x++)
		exprs[x] = random_irexpr1(3);

	printf("Ordering should be anti-reflexive.\n");
	for (x = 0; x < NR_EXPRS; x++)
		assert(!sortIRExprs(exprs[x], exprs[x]));

	printf("Ordering should be anti-symmetric.\n");
	for (x = 0; x < NR_EXPRS; x++) {
		for (y = x + 1; y < NR_EXPRS; y++) {
			if (sortIRExprs(exprs[x], exprs[y]))
				assert(!sortIRExprs(exprs[y], exprs[x]));
		}
	}

	/* Ordering must be transitive and total.  We check this by
	 * performing a naive topological sort on the expressions and
	 * then checking that whenever x < y exprs[x] < exprs[y]. */
	IRExpr *exprs2[NR_EXPRS];

	int nr_exprs2 = 0;
	int candidate;
	int probe;
	bool progress = true;
	printf("Toposorting...\n");
	while (nr_exprs2 < NR_EXPRS) {
		/* Try to find an ordering-minimal entry in the
		 * array.  */
		assert(progress);
		progress = false;
		for (candidate = 0; candidate < NR_EXPRS; candidate++) {
			if (!exprs[candidate])
				continue;
			for (probe = 0; probe < NR_EXPRS; probe++) {
				if (!exprs[probe])
					continue;
				if (sortIRExprs(exprs[probe], exprs[candidate])) {
					/* probe is less than
					   candidate, so candidate
					   fails. */
					break;
				}
			}
			if (probe == NR_EXPRS) {
				/* This candidate passes.  Add it to
				   the list. */
				exprs2[nr_exprs2] = exprs[candidate];
				exprs[candidate] = NULL;
				nr_exprs2++;
				progress = true;
			}
		}
	}

	/* Okay, have a topo sort.  The ordering is supposed to be
	   total, so that should have just been an O(n^3) selection
	   sort, and the array should now be totally sorted.  check
	   it. */
	printf("Check toposort is total...\n");
	for (x = 0; x < NR_EXPRS; x++)
		for (y = x + 1; y < NR_EXPRS; y++)
			assert(!sortIRExprs(exprs2[y], exprs2[x]));
#undef NR_EXPRS
}

class RandomExpressionEvalCtxt {
public:
	std::map<std::pair<IRTemp, unsigned>, unsigned long> temporaries;
	std::map<std::pair<unsigned, unsigned>, unsigned long> registers;
	std::map<unsigned long, int> badAddress;
};

static unsigned long
randomEvalExpression(RandomExpressionEvalCtxt &ctxt, IRExpr *expr)
{
	switch (expr->tag) {
	case Iex_Const:
		return expr->Iex.Const.con->Ico.U64;
	case Iex_RdTmp: {
		std::pair<IRTemp, unsigned> k(expr->Iex.RdTmp.tmp, expr->Iex.RdTmp.tid);
		if (!ctxt.temporaries.count(k))
			ctxt.temporaries[k] = random();
		return ctxt.temporaries[k];
	}
	case Iex_Get: {
		std::pair<unsigned, unsigned> k(expr->Iex.Get.offset, expr->Iex.Get.tid);
		if (!ctxt.registers.count(k))
			ctxt.registers[k] = random();
		return ctxt.registers[k];
		
	}
	case Iex_Mux0X:
		if (randomEvalExpression(ctxt, expr->Iex.Mux0X.cond))
			return randomEvalExpression(ctxt, expr->Iex.Mux0X.exprX);
		else
			return randomEvalExpression(ctxt, expr->Iex.Mux0X.expr0);
	case Iex_Binop: {
		unsigned long l = randomEvalExpression(ctxt, expr->Iex.Binop.arg1);
		unsigned long r = randomEvalExpression(ctxt, expr->Iex.Binop.arg2);
		switch (expr->Iex.Binop.op) {
		case Iop_And1:
		case Iop_And64:
			return l & r;
		case Iop_Xor1:
		case Iop_Xor64:
			return l ^ r;
		case Iop_Or1:
		case Iop_Or64:
			return l | r;
		case Iop_Sar64:
			return l >> r;
		case Iop_CmpEQ64:
			return l == r;
		case Iop_CmpLT64U:
			return l < r;
		case Iop_CmpLT64S:
			return (long)l < (long)r;
		case Iop_CC_OverflowSub:
			return ((l ^ r) & (l ^ (l - r))) >> 63;
		default:
			abort();
			return 0;
		}
	}
	case Iex_Associative: {
		std::vector<unsigned long> args;
		args.resize(expr->Iex.Associative.nr_arguments);
		for (int i = 0; i < expr->Iex.Associative.nr_arguments; i++)
			args[i] = randomEvalExpression(ctxt, expr->Iex.Associative.contents[i]);
		unsigned long acc;
		switch (expr->Iex.Associative.op) {
		case Iop_And1:
			acc = 1;
			for (unsigned i = 0; i < args.size(); i++)
				acc &= args[i];
			return acc;
		case Iop_And64:
			acc = ~0ul;
			for (unsigned i = 0; i < args.size(); i++)
				acc &= args[i];
			return acc;
		case Iop_Xor1:
		case Iop_Xor64:
			acc = 0;
			for (unsigned i = 0; i < args.size(); i++)
				acc ^= args[i];
			return acc;
		case Iop_Or1:
		case Iop_Or64:
			acc = 0;
			for (unsigned i = 0; i < args.size(); i++)
				acc |= args[i];
			return acc;
		case Iop_Add64:
			acc = 0;
			for (unsigned i = 0; i < args.size(); i++)
				acc += args[i];
			return acc;
		default:
			abort();
		}
	}
	case Iex_Unop: {
		unsigned long a = randomEvalExpression(ctxt, expr->Iex.Unop.arg);
		switch (expr->Iex.Unop.op) {
		case Iop_Not1:
			return !a;
		case Iop_Neg64:
			return -a;
		case Iop_Not64:
			return ~a;
		case Iop_BadPtr:
			if (a < 4096)
				return 1;
			if (!ctxt.badAddress.count(a / 4096))
				ctxt.badAddress[a/4096] = random() % 2;
			return ctxt.badAddress[a/4096];
		default:
			abort();
		}
	}
	case Iex_CCall:
		assert(!strcmp(expr->Iex.CCall.cee->name, "amd64g_calculate_condition"));
		return amd64g_calculate_condition(
			randomEvalExpression(ctxt, expr->Iex.CCall.args[0]),
			randomEvalExpression(ctxt, expr->Iex.CCall.args[1]),
			randomEvalExpression(ctxt, expr->Iex.CCall.args[2]),
			randomEvalExpression(ctxt, expr->Iex.CCall.args[3]),
			randomEvalExpression(ctxt, expr->Iex.CCall.args[4]));
	default:
		abort();
	}
	abort();
	return 0;
}

void
sanity_check_optimiser(void)
{
	/* x + -x -> 0 */
	IRExpr *start =
		IRExpr_Associative(
			Iop_Add64,
			IRExpr_Get(0, Ity_I64, 0),
			IRExpr_Unop(
				Iop_Neg64,
				IRExpr_Get(0, Ity_I64, 0)),
			NULL);
	IRExpr *end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	assert(physicallyEqual(end, IRExpr_Const(IRConst_U64(0))));
	/* x & ~x -> 0 */
	start = IRExpr_Associative(
		Iop_And1,
		IRExpr_Unop(
			Iop_Not1,
			IRExpr_Get(0, Ity_I64, 0)),
		IRExpr_Get(0, Ity_I64, 0),
		NULL);
	end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	end = optimiseIRExpr(start, AllowableOptimisations::defaultOptimisations);
	assert(physicallyEqual(end, IRExpr_Const(IRConst_U64(0))));

	for (unsigned cntr1 = 0; cntr1 < 10000; cntr1++) {
		IRExpr *orig;
		IRExpr *optimised;
		do {
			orig = random_irexpr1(4);
			optimised = simplifyIRExpr(orig, AllowableOptimisations::defaultOptimisations);
		} while (physicallyEqual(orig, optimised));

		for (unsigned cntr2 = 0; cntr2 < 100; cntr2++) {
			RandomExpressionEvalCtxt ctxt;
			assert(ctxt.temporaries.size() == 0);
			assert(randomEvalExpression(ctxt, orig) == randomEvalExpression(ctxt, optimised));
		}
	}
}
