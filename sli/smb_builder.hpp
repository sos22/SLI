/* Relatively simple way of building state machines.  Vaguely inspired
   by Haskell's monad combinators. */
#ifndef SMB_BUILDER_HPP__
#define SMB_BUILDER_HPP__

#include "state_machine.hpp"

class CFGNode;

/* XXX doesn't really belong here */
struct reloc_t {
	StateMachineState **ptr;
	CFGNode *target;
	reloc_t(StateMachineState **_ptr,
		CFGNode *_target)
		: ptr(_ptr), target(_target)
	{}
};

/* The various SMB structures are in the GC heap, so need to be
   referred to by pointers, but overloading pointer types is generally
   a bad idea, so we wrap them all in SMBPtr. */
template <typename t> struct SMBPtr {
	const t *content;
	explicit SMBPtr(const t *_content)
		: content(_content)
	{}
	SMBPtr()
		: content((t *)0xf001dead)
	{}
};

/* ------------------ Stuff for building up expressions ---------------- */
class SMBExpression : public GarbageCollected<SMBExpression, &ir_heap> {
public:
	const IRExpr *what;
	IRExpr *compile() const {
		return (IRExpr *)what;
	}
	SMBExpression(const IRExpr *_what)
		: what(_what)
	{}
	void visit(HeapVisitor &hv) {
		hv(what);
	}
	NAMED_CLASS
};
/* Introductions */
static inline SMBPtr<SMBExpression>
smb_const64(uint64_t k)
{
	return SMBPtr<SMBExpression>(new SMBExpression(IRExpr_Const(IRConst_U64(k))));
}
static inline SMBPtr<SMBExpression>
smb_const8(uint8_t k)
{
	return SMBPtr<SMBExpression>(new SMBExpression(IRExpr_Const(IRConst_U8(k))));
}
static inline SMBPtr<SMBExpression>
smb_reg(const threadAndRegister &tr, IRType ty)
{
	return SMBPtr<SMBExpression>(new SMBExpression(IRExpr_Get(tr, ty)));
}
/* Builders */
SMBPtr<SMBExpression> operator+(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b);
SMBPtr<SMBExpression> operator==(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b);
SMBPtr<SMBExpression> operator<=(SMBPtr<SMBExpression> a, SMBPtr<SMBExpression> b);

/* --------------------------- Memory references ------------------------------------ */
class SMBMemoryReference : public GarbageCollected<SMBMemoryReference, &ir_heap> {
public:
	SMBPtr<SMBExpression> addr;
	IRExpr *compile() const {
		return addr.content->compile();
	}
	explicit SMBMemoryReference(SMBPtr<SMBExpression> a)
		: addr(a)
	{
	}
	void visit(HeapVisitor &hv)
	{
		hv(addr.content);
	}
	NAMED_CLASS
};
/* Introductions */
static inline SMBPtr<SMBMemoryReference>
operator*(SMBPtr<SMBExpression> a)
{
	return SMBPtr<SMBMemoryReference>(new SMBMemoryReference(a));
}

/* ---------------------------- Register references ------------------------------ */
class SMBRegisterReference : public GarbageCollected<SMBRegisterReference, &ir_heap> {
public:
	threadAndRegister compile() const {
		return tr;
	}
	threadAndRegister tr;
	explicit SMBRegisterReference(const threadAndRegister &_tr)
		: tr(_tr)
	{
	}
	void visit(HeapVisitor &) {}
	NAMED_CLASS
};
/* Introductions */
/* You could argue that this should be *, not !, because it's a kind
   of dereference, but it's different to a memory dereference, and I'd
   rather have the extra check that I'm not using them
   inconsistently. */
static inline SMBPtr<SMBRegisterReference>
operator!(const threadAndRegister &tr)
{
	return SMBPtr<SMBRegisterReference>(new SMBRegisterReference(tr));
}

/* ------------------------------ Statements ------------------------------------- */
class SMBStatement : public GarbageCollected<SMBStatement, &ir_heap> {
public:
	virtual StateMachineSideEffect *compile(const ThreadRip &vr) const = 0;
	NAMED_CLASS
};
class SMBStatementCopy : public SMBStatement {
	StateMachineSideEffect *compile(const ThreadRip &) const {
		return new StateMachineSideEffectCopy(
			lvalue.content->compile(),
			rvalue.content->compile());
	}
public:
	SMBPtr<SMBRegisterReference> lvalue;
	SMBPtr<SMBExpression> rvalue;
	void visit(HeapVisitor &hv) {
		hv(lvalue.content);
		hv(rvalue.content);
	}
	explicit SMBStatementCopy(SMBPtr<SMBRegisterReference> _lvalue, SMBPtr<SMBExpression> _rvalue)
		: lvalue(_lvalue), rvalue(_rvalue)
	{}
};
class SMBStatementStore : public SMBStatement {
	StateMachineSideEffect *compile(const ThreadRip &vr) const {
		return new StateMachineSideEffectStore(
			addr.content->compile(),
			value.content->compile(),
			MemoryAccessIdentifier(vr,
					       MemoryAccessIdentifier::static_generation));
	}
public:
	SMBPtr<SMBMemoryReference> addr;
	SMBPtr<SMBExpression> value;

	void visit(HeapVisitor &hv) {
		hv(addr.content);
		hv(value.content);
	}
	explicit SMBStatementStore(SMBPtr<SMBMemoryReference> _addr, SMBPtr<SMBExpression> _value)
		: addr(_addr), value(_value)
	{
	}
};
class SMBStatementLoad : public SMBStatement {
	StateMachineSideEffect *compile(const ThreadRip &vr) const {
		return new StateMachineSideEffectLoad(
			target.content->compile(),
			addr.content->compile(),
			MemoryAccessIdentifier(vr,
					       MemoryAccessIdentifier::static_generation),
			type);
	}
public:
	SMBPtr<SMBRegisterReference> target;
	SMBPtr<SMBMemoryReference> addr;
	IRType type;

	void visit(HeapVisitor &hv) {
		hv(target.content);
		hv(addr.content);
	}
	explicit SMBStatementLoad(SMBPtr<SMBRegisterReference> _target,
				  SMBPtr<SMBMemoryReference> _addr,
				  IRType _type)
		: target(_target), addr(_addr), type(_type)
	{
	}
};

/* Introductions */
/* Assign a value to a register.  I'd like to use = for this, but C++
 * doesn't allow you to overload = from a non-member function, for
 * some obscure reason. */
static inline SMBPtr<SMBStatement>
operator <<=(SMBPtr<SMBRegisterReference> target, SMBPtr<SMBExpression> value)
{
	return SMBPtr<SMBStatement>(new SMBStatementCopy(target, value));
}
/* Store a value in a memory location */
static inline SMBPtr<SMBStatement>
operator <<=(SMBPtr<SMBMemoryReference> target, SMBPtr<SMBExpression> value)
{
	return SMBPtr<SMBStatement>(new SMBStatementStore(target, value));
}
/* Load a value from memory into a register.  No operator because you
   need the addition ty argument */
static inline SMBPtr<SMBStatement>
Load(SMBPtr<SMBRegisterReference> target, SMBPtr<SMBMemoryReference> addr, IRType ty)
{
	return SMBPtr<SMBStatement>(new SMBStatementLoad(target, addr, ty));
}

/* ------------------------------------ States ----------------------------------- */
class SMBState : public GarbageCollected<SMBState, &ir_heap> {
protected:
	struct reloc2 {
		const SMBState *target;
		StateMachineState **t;
		reloc2(const SMBState *_target, StateMachineState **_t)
			: target(_target), t(_t)
		{}
	};
	virtual StateMachineState *_compile(const ThreadRip &vr,
					    std::vector<reloc_t> &relocs,
					    std::vector<reloc2> &relocs2) const = 0;
private:
	StateMachineState *compile(const ThreadRip &vr,
				   std::map<const SMBState *, StateMachineState *> &m,
				   std::vector<reloc_t> &relocs,
				   std::vector<reloc2> &relocs2) const;
public:
	StateMachineState *compile(const ThreadRip &vr, std::vector<reloc_t> &relocs) const;
	NAMED_CLASS
};
class SMBStateStatement : public SMBState {
	StateMachineState *_compile(const ThreadRip &vr,
				    std::vector<reloc_t> &,
				    std::vector<reloc2> &relocs2) const {
		StateMachineSideEffecting *smse =
			new StateMachineSideEffecting(
				vr.rip,
				first.content->compile(vr),
				NULL);
		relocs2.push_back(reloc2(second.content, &smse->target));
		return smse;
	}
public:
	SMBPtr<SMBStatement> first;
	SMBPtr<SMBState> second;
	explicit SMBStateStatement(SMBPtr<SMBStatement> _first, SMBPtr<SMBState> _second)
		: first(_first), second(_second)
	{}
	void visit(HeapVisitor &hv)
	{
		hv(first.content);
		hv(second.content);
	}
};
class SMBStateIf : public SMBState {
	StateMachineState *_compile(const ThreadRip &tr,
				    std::vector<reloc_t> &,
				    std::vector<reloc2> &relocs2) const {
		StateMachineBifurcate *smb =
			new StateMachineBifurcate(tr.rip,
						  cond.content->compile(),
						  NULL,
						  NULL);
		relocs2.push_back(reloc2(trueTarg.content, &smb->trueTarget));
		relocs2.push_back(reloc2(falseTarg.content, &smb->falseTarget));
		return smb;
	}
public:
	SMBPtr<SMBExpression> cond;
	SMBPtr<SMBState> trueTarg;
	SMBPtr<SMBState> falseTarg;
	explicit SMBStateIf(SMBPtr<SMBExpression> _cond, SMBPtr<SMBState> _trueTarg,
			    SMBPtr<SMBState> _falseTarg)
		: cond(_cond), trueTarg(_trueTarg), falseTarg(_falseTarg)
	{}
	void visit(HeapVisitor &hv)
	{
		hv(cond.content);
		hv(trueTarg.content);
		hv(falseTarg.content);
	}	
};
class SMBStateProxy : public SMBState {
	StateMachineState *_compile(const ThreadRip &tr,
				    std::vector<reloc_t> &relocs,
				    std::vector<reloc2> &) const {
		StateMachineSideEffecting *smse =
			new StateMachineSideEffecting(tr.rip, NULL, NULL);
		relocs.push_back(reloc_t(&smse->target, target));
		return smse;
	}
public:
	CFGNode *target;
	explicit SMBStateProxy(CFGNode *_target)
		: target(_target)
	{
		assert(target);
	}
	void visit(HeapVisitor &hv)
	{
		hv(target);
	}
};

/* Introductions */
/* Simple sequencing. */
static inline SMBPtr<SMBState>
operator>>(SMBPtr<SMBStatement> a, SMBPtr<SMBState> b)
{
	return SMBPtr<SMBState>(new SMBStateStatement(a, b));
}
/* Conditional branch */
static inline SMBPtr<SMBState>
If(SMBPtr<SMBExpression> a, SMBPtr<SMBState> trueTarg, SMBPtr<SMBState> falseTarg)
{
	return SMBPtr<SMBState>(new SMBStateIf(a, trueTarg, falseTarg));
}
/* Something to mark the end of the machine i.e. where we branch from
   the machine we're currently building back into the underlying
   CFG */
static inline SMBPtr<SMBState>
Proxy(CFGNode *n)
{
	return SMBPtr<SMBState>(new SMBStateProxy(n));
}


#endif /* !SMB_BUILDER_HPP__ */
