#include "sli.h"
#include "smb_builder.hpp"
#include "state_machine.hpp"
#include "simplify_irexpr.hpp"

SMBPtr<SMBExpression>
operator+(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(a.content->what->type() == b.content->what->type());
	IROp op = Iop_INVALID;
	switch (a.content->what->type()) {
	case Ity_I1:
		abort();
	case Ity_I8:
		op = Iop_Add8;
		break;
	case Ity_I16:
		op = Iop_Add16;
		break;
	case Ity_I32:
		op = Iop_Add32;
		break;
	case Ity_I64:
		op = Iop_Add64;
		break;
	case Ity_I128:
		abort();
	case Ity_INVALID:
		abort();
	}
	assert(op != Iop_INVALID);
	return SMBPtr<SMBExpression>(
		new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.content->what,
					       (IRExpr *)b.content->what)));
				     
}
SMBPtr<SMBExpression>
operator*(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(a.content->what->type() == b.content->what->type());
	IROp op = Iop_INVALID;
	switch (a.content->what->type()) {
	case Ity_I1:
		abort();
	case Ity_I8:
		op = Iop_Mul8;
		break;
	case Ity_I16:
		op = Iop_Mul16;
		break;
	case Ity_I32:
		op = Iop_Mul32;
		break;
	case Ity_I64:
		op = Iop_Mul64;
		break;
	case Ity_I128:
		abort();
	case Ity_INVALID:
		abort();
	}
	assert(op != Iop_INVALID);
	return SMBPtr<SMBExpression>(
		new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.content->what,
					       (IRExpr *)b.content->what)));
}

SMBPtr<SMBExpression>
operator&(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(a.content->what->type() == b.content->what->type());
	IROp op = Iop_INVALID;
	switch (a.content->what->type()) {
	case Ity_I1:
		op = Iop_And1;
		break;
	case Ity_I8:
		op = Iop_And8;
		break;
	case Ity_I16:
		op = Iop_And16;
		break;
	case Ity_I32:
		op = Iop_And32;
		break;
	case Ity_I64:
		op = Iop_And64;
		break;
	case Ity_I128:
		abort();
	case Ity_INVALID:
		abort();
	}
	assert(op != Iop_INVALID);
	return SMBPtr<SMBExpression>(
		new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.content->what,
					       (IRExpr *)b.content->what)));
}

SMBPtr<SMBExpression>
operator|(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(a.content->what->type() == b.content->what->type());
	IROp op = Iop_INVALID;
	switch (a.content->what->type()) {
	case Ity_I1:
		op = Iop_Or1;
		break;
	case Ity_I8:
		op = Iop_Or8;
		break;
	case Ity_I16:
		op = Iop_Or16;
		break;
	case Ity_I32:
		op = Iop_Or32;
		break;
	case Ity_I64:
		op = Iop_Or64;
		break;
	case Ity_I128:
		abort();
	case Ity_INVALID:
		abort();
	}
	assert(op != Iop_INVALID);
	return SMBPtr<SMBExpression>(
		new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.content->what,
					       (IRExpr *)b.content->what)));
}

SMBPtr<SMBExpression>
operator<<(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(b.content->what->type() == Ity_I8);
	IROp op = Iop_INVALID;
	switch (a.content->what->type()) {
	case Ity_I1:
		abort();
	case Ity_I8:
		op = Iop_Shl8;
		break;
	case Ity_I16:
		op = Iop_Shl16;
		break;
	case Ity_I32:
		op = Iop_Shl32;
		break;
	case Ity_I64:
		op = Iop_Shl64;
		break;
	case Ity_I128:
		abort();
	case Ity_INVALID:
		abort();
	}
	assert(op != Iop_INVALID);
	return SMBPtr<SMBExpression>(
		new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.content->what,
					       (IRExpr *)b.content->what)));
}

SMBPtr<SMBExpression>
operator==(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(a.content->what->type() == b.content->what->type());
	return SMBPtr<SMBExpression>(
		new SMBExpression(expr_eq((IRExpr *)a.content->what,
					  (IRExpr *)b.content->what)));
}

SMBPtr<SMBExpression>
operator!=(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	return SMBPtr<SMBExpression>(
		new SMBExpression(
			IRExpr_Unop(
				Iop_Not1,
				expr_eq((IRExpr *)a.content->what,
					(IRExpr *)b.content->what))));
}

SMBPtr<SMBExpression>
operator<=(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(a.content->what->type() == b.content->what->type());
	IROp op;
	/* Shut compiler up */
	op = Iop_INVALID;
	switch (a.content->what->type()) {
	case Ity_I1:
		abort();
	case Ity_I8:
		abort();
	case Ity_I16:
		abort();
	case Ity_I32:
		op = Iop_CmpLE32U;
		break;
	case Ity_I64:
		op = Iop_CmpLE64U;
		break;
	case Ity_I128:
		abort();
	case Ity_INVALID:
		abort();
	}
	assert(op != Iop_INVALID);
	return SMBPtr<SMBExpression>(
		new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.content->what,
					       (IRExpr *)b.content->what)));
}

StateMachineState *
SMBState::compile(std::map<const SMBState *, StateMachineState *> &m,
		  std::vector<reloc_t> &relocs,
		  std::vector<reloc2> &relocs2,
		  SMBCompilerState &state) const
{
	auto it_did_insert = m.insert(std::pair<const SMBState *, StateMachineState *>(this, (StateMachineState *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = _compile(relocs, relocs2, state);
	return it->second;
}

StateMachineState *
SMBState::compile(std::vector<reloc_t> &relocs,
		  SMBCompilerState &state) const
{
	std::map<const SMBState *, StateMachineState *> m;
	std::vector<reloc2> relocs2;
	StateMachineState *res;
	res = NULL;
	relocs2.push_back(reloc2(this, &res));
	while (!relocs2.empty()) {
		reloc2 r2(relocs2.back());
		relocs2.pop_back();
		assert(!*r2.t);
		*r2.t = r2.target->compile(m, relocs, relocs2, state);
		assert(*r2.t);
	}
	assert(res);
	return res;
}
