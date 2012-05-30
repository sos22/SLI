#include "sli.h"
#include "smb_builder.hpp"
#include "state_machine.hpp"

SMBPtr<SMBExpression>
operator+(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(a.content->what->type() == b.content->what->type());
	IROp op;
	switch (a.content->what->type()) {
	case Ity_I1:
		op = Iop_Xor1;
		break;
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
	case Ity_F32:
		abort();
	case Ity_F64:
		op = Iop_AddF64;
		break;
	case Ity_V128:
		abort();
	case Ity_INVALID:
		abort();
	}
	return SMBPtr<SMBExpression>(
		new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.content->what,
					       (IRExpr *)b.content->what)));
				     
}

SMBPtr<SMBExpression>
operator&(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(a.content->what->type() == b.content->what->type());
	IROp op;
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
	case Ity_F32:
		abort();
	case Ity_F64:
		abort();
	case Ity_V128:
		op = Iop_AndV128;
		break;
	case Ity_INVALID:
		abort();
	}
	return SMBPtr<SMBExpression>(
		new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.content->what,
					       (IRExpr *)b.content->what)));
}

SMBPtr<SMBExpression>
operator|(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(a.content->what->type() == b.content->what->type());
	IROp op;
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
	case Ity_F32:
		abort();
	case Ity_F64:
		abort();
	case Ity_V128:
		op = Iop_OrV128;
		break;
	case Ity_INVALID:
		abort();
	}
	return SMBPtr<SMBExpression>(
		new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.content->what,
					       (IRExpr *)b.content->what)));
}

SMBPtr<SMBExpression>
operator<<(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(b.content->what->type() == Ity_I8);
	IROp op;
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
	case Ity_F32:
		abort();
	case Ity_F64:
		abort();
	case Ity_V128:
		op = Iop_ShlV128;
		break;
	case Ity_INVALID:
		abort();
	}
	return SMBPtr<SMBExpression>(
		new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.content->what,
					       (IRExpr *)b.content->what)));
}

SMBPtr<SMBExpression>
operator==(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(a.content->what->type() == b.content->what->type());
	IROp op;
	switch (a.content->what->type()) {
	case Ity_I1:
		op = Iop_CmpEQ1;
		break;
	case Ity_I8:
		op = Iop_CmpEQ8;
		break;
	case Ity_I16:
		op = Iop_CmpEQ16;
		break;
	case Ity_I32:
		op = Iop_CmpEQ32;
		break;
	case Ity_I64:
		op = Iop_CmpEQ64;
		break;
	case Ity_I128:
		op = Iop_CmpEQI128;
		break;
	case Ity_V128:
		op = Iop_CmpEQV128;
		break;
	case Ity_F32:
		op = Iop_CmpEQF32;
		break;
	case Ity_F64:
		op = Iop_CmpEQF64;
		break;
	case Ity_INVALID:
		abort();
	}
	return SMBPtr<SMBExpression>(
		new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.content->what,
					       (IRExpr *)b.content->what)));
}

SMBPtr<SMBExpression>
operator<=(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b)
{
	assert(a.content->what->type() == b.content->what->type());
	IROp op;
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
	case Ity_V128:
	case Ity_F32:
	case Ity_F64:
		abort();
	case Ity_INVALID:
		abort();
	}
	return SMBPtr<SMBExpression>(
		new SMBExpression(IRExpr_Binop(op, (IRExpr *)a.content->what,
					       (IRExpr *)b.content->what)));
}

StateMachineState *
SMBState::compile(const ThreadRip &tr,
		  std::map<const SMBState *, StateMachineState *> &m,
		  std::vector<reloc_t> &relocs,
		  std::vector<reloc2> &relocs2) const
{
	auto it_did_insert = m.insert(std::pair<const SMBState *, StateMachineState *>(this, (StateMachineState *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = _compile(tr, relocs, relocs2);
	return it->second;
}

StateMachineState *
SMBState::compile(const ThreadRip &vr, std::vector<reloc_t> &relocs) const
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
		*r2.t = r2.target->compile(vr, m, relocs, relocs2);
		assert(*r2.t);
	}
	assert(res);
	return res;
}
