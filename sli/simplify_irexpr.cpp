#include <time.h>

#include "sli.h"
#include "state_machine.hpp"

#include "simplify_irexpr.hpp"

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
		(op == Iop_Or1);
}

/* Returns true if the operation definitely associates in the sense
 * that (a op b) op c == a op (b op c), or false if we're not sure. */
static bool
operationAssociates(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) || (op == Iop_And1) ||
		(op >= Iop_And8 && op <= Iop_And64) || (op >= Iop_Xor8 && op <= Iop_Xor64);
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

	/* We only handle a few very special cases here. */
	if (_cond->tag != Iex_Const || cc_op->tag != Iex_Const)
		return NULL;
	cond = _cond->Iex.Const.con->Ico.U64;
	invert = cond & 1;
	cond &= ~1ul;
	res = NULL;
	switch (cond) {
	case AMD64CondZ:
		switch (cc_op->Iex.Const.con->Ico.U64) {
		case AMD64G_CC_OP_SUBL:
			res = IRExpr_Binop(
				Iop_CmpEQ32,
				dep1,
				dep2);
			break;
		case AMD64G_CC_OP_SUBQ:
			res = IRExpr_Binop(
				Iop_CmpEQ64,
				dep1,
				dep2);
			break;
		case AMD64G_CC_OP_LOGICL:
		case AMD64G_CC_OP_LOGICQ:
			res = IRExpr_Binop(
				Iop_CmpEQ64,
				dep1,
				IRExpr_Const(IRConst_U64(0)));
			break;
		}
		break;
	case AMD64CondB:
		switch (cc_op->Iex.Const.con->Ico.U64) {
		case AMD64G_CC_OP_SUBQ:
			res = IRExpr_Binop(
				Iop_CmpLT64U,
				dep1,
				dep2);
			break;
		}
		break;
	case AMD64CondS:
		switch (cc_op->Iex.Const.con->Ico.U64) {
		case AMD64G_CC_OP_ADDW:
			res = IRExpr_Binop(
				Iop_CmpLT32S,
				IRExpr_Binop(
					Iop_Add16,
					dep1,
					dep2),
				IRExpr_Const(IRConst_U16(0)));
			break;
		}
		break;
	}
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
	}
	abort();
}

static bool
IexTagLessThan(IRExprTag a, IRExprTag b)
{
	if (a == b)
		return false;
	if (a == Iex_Const)
		return true;
	if (b == Iex_Const)
		return false;
	if (a == Iex_Get)
		return true;
	if (b == Iex_Get)
		return false;
	if (a == Iex_GetI)
		return true;
	if (b == Iex_GetI)
		return false;
	if (a == Iex_RdTmp)
		return true;
	if (b == Iex_RdTmp)
		return false;
	if (b == Iex_Qop || b == Iex_Triop || b == Iex_Binop || b == Iex_Unop || b == Iex_Associative)
		return false;
	if (a == Iex_Qop || a == Iex_Triop || a == Iex_Binop || a == Iex_Unop || a == Iex_Associative)
		return true;
	if (a == Iex_Mux0X)
		return true;
	if (b == Iex_Mux0X)
		return false;
	if (a == Iex_Load)
		return true;
	if (b == Iex_Load)
		return false;
	if (a == Iex_CCall)
		return true;
	if (b == Iex_CCall)
		return false;
	abort();
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
	virtual IRExpr *asIRExpr(std::map<int, IRExpr *> &) = 0;
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
	IRExpr *asIRExpr(std::map<int, IRExpr *> &m) { return m[id]; }
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
	IRExpr *asIRExpr(std::map<int, IRExpr *> &m) { return IRExpr_Unop(Iop_Not1, arg->asIRExpr(m)); }
	int complexity() { return arg->complexity() + 1; }
	CnfExpression *arg;
};

class CnfGrouping : public CnfExpression {
protected:
	virtual char op() const = 0;
	virtual IROp irexpr_op() const = 0;
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
	IRExpr *asIRExpr(std::map<int, IRExpr *> &m) {
		if (args.size() == 0) {
			if (irexpr_op() == Iop_Or1)
				return IRExpr_Const(IRConst_U1(0));
			else
				return IRExpr_Const(IRConst_U1(1));
		} else {
			IRExpr *work = IRExpr_Associative(irexpr_op(), NULL);
			for (unsigned x = 0; x < args.size(); x++) {
				addArgumentToAssoc(work, args[x]->asIRExpr(m));
			}
			return work;
		}
	}
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
	IROp irexpr_op() const { return Iop_Or1; }
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
};

class CnfAnd : public CnfGrouping {
protected:
	char op() const { return '&'; }
	IROp irexpr_op() const { return Iop_And1; }
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
	if (nr_terms > a->complexity()) {
		return a->asIRExpr(varsToExprs);
	} else {
		return inp;
	}
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
		if (src->Iex.Load.addr->tag == Iex_Const &&
		    (long)src->Iex.Load.addr->Iex.Const.con->Ico.U64 < 4096)
			dbg_break("optimising load to load of strange constant address (IRExpr *)%p\n",
				  src);
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
		    src->Iex.Unop.arg->tag == Iex_Binop &&
		    (src->Iex.Unop.arg->Iex.Binop.op == Iop_CmpEQ64 ||
		     src->Iex.Unop.arg->Iex.Binop.op == Iop_CmpEQ32)) {
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
			default:
				break;
			}
		}
	} else if (src->tag == Iex_Binop) {
		IRExpr *l = src->Iex.Binop.arg1;
		IRExpr *r = src->Iex.Binop.arg2;
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
			src->Iex.Binop.arg2 =
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
			case Iop_CmpEQ64:
				*done_something = true;
				return IRExpr_Const(
					IRConst_U1(
						src->Iex.Binop.arg1->Iex.Const.con->Ico.U64 ==
						src->Iex.Binop.arg2->Iex.Const.con->Ico.U64));
			default:
				break;
			}
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
		a = optimiseIRExpr(a, opt, &done_something);
		a = internIRExpr(a);
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
isBadAddress(IRExpr *e, const AllowableOptimisations &opt, Oracle *oracle)
{
	return e->tag == Iex_Const &&
		(long)e->Iex.Const.con->Ico.U64 < 4096;
}

bool
definitelyUnevaluatable(IRExpr *e, const AllowableOptimisations &opt, Oracle *oracle)
{
	switch (e->tag) {
	case Iex_Binder:
	case Iex_Get:
	case Iex_RdTmp:
	case Iex_Const:
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



static IROp
random_irop(void)
{
	return (IROp)((unsigned long)Iop_Add8 + random() % (Iop_Perm8x16 - Iop_Add8 + 1));
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

static IRRegArray *
random_irregarray(void)
{
	return mkIRRegArray( (random() % 10) * 8,
			     random_irtype(),
			     random() % 16 );
}

static IRExpr *
random_irexpr(unsigned depth)
{
	if (!depth)
		return IRExpr_Const(random_irconst());
	switch (random() % 8) {
	case 0:
		return IRExpr_Binder(random() % 30);
	case 1:
		return IRExpr_Get((random() % 40) * 8,
				  random_irtype(),
				  73);
	case 2:
		return IRExpr_RdTmp(random() % 5, 73);
	case 3:
		switch (random() % 5) {
		case 0:
			return IRExpr_Unop(random_irop(), random_irexpr(depth - 1));
		case 1:
			return IRExpr_Binop(
				random_irop(),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1));
		case 2:
			return IRExpr_Triop(
				random_irop(),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1));
		case 3:
			return IRExpr_Qop(
				random_irop(),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1));
		case 4: {
			IRExpr *e = IRExpr_Associative(
				random_irop(),
				random_irexpr(depth - 1),
				random_irexpr(depth - 1),
				NULL);
			while (random() % 2)
				addArgumentToAssoc(e, random_irexpr(depth - 1));
			return e;
		}
		default:
			abort();
		}
	case 4:
		return IRExpr_Load(
			False,
			Iend_LE,
			random_irtype(),
			random_irexpr(depth - 1));
	case 5:
		return IRExpr_Const(random_irconst());
	case 6: {
		IRExpr **args;
		switch (random() % 4) {
		case 0:
			args = mkIRExprVec_0();
			break;
		case 1:
			args = mkIRExprVec_1(random_irexpr(depth - 1));
			break;
		case 2:
			args = mkIRExprVec_2(random_irexpr(depth - 1), random_irexpr(depth - 1));
			break;
		case 3:
			args = mkIRExprVec_3(random_irexpr(depth - 1), random_irexpr(depth - 1), random_irexpr(depth - 1));
			break;
		default:
			abort();
		}
		return IRExpr_CCall(mkIRCallee(0, "random_ccall", (void *)0x52),
				    random_irtype(),
				    args);
	}
	case 7:
		return IRExpr_Mux0X(random_irexpr(depth - 1), random_irexpr(depth - 1), random_irexpr(depth - 1));
	case 8:
		return IRExpr_GetI(random_irregarray(), random_irexpr(depth - 1), (random() % 20) * 8, 98);
	default:
		abort();
	}		
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
		exprs[x] = random_irexpr(3);

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
	assert(physicallyEqual(end, IRExpr_Const(IRConst_U1(0))));
}
