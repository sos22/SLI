#include <sys/fcntl.h>
#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"
#include "inferred_information.hpp"
#include "oracle.hpp"
#include "offline_analysis.hpp"
#include "cnf.hpp"
#include "genfix.hpp"
#include "dnf.hpp"
#include "simplify_ordering.hpp"
#include "zapBindersAndFreeVariables.hpp"
#include "enforce_crash.hpp"

class EnforceCrashCFG : public CFG<ThreadRip> {
	std::set<ThreadRip> &neededInstructions;
public:
	bool instructionUseful(Instruction<ThreadRip> *i) {
		return neededInstructions.count(i->rip) != 0;
	}
	EnforceCrashCFG(AddressSpace *as, std::set<ThreadRip> &ni)
		: CFG<ThreadRip>(as), neededInstructions(ni)
	{}
};

struct DirectRip {
	unsigned long rip;
	DirectRip(unsigned long _rip) : rip(_rip) {}
	DirectRip() : rip(0) {}
	bool operator==(const DirectRip &d) const { return rip == d.rip; }
};

void
instrToInstrSetMap::print(FILE *f)
{
	for (iterator it = begin(); it != end(); it++) {
		fprintf(f, "%d:%lx[%p] -> {", it->first->rip.thread, it->first->rip.rip, it->first);
		for (std::set<Instruction<ThreadRip> *>::iterator it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			fprintf(f, "%d:%lx[%p]", (*it2)->rip.thread, (*it2)->rip.rip, *it2);
		}
		fprintf(f, "}\n");
	}
}

unsigned long __trivial_hash_function(const ClientRip &k)
{
	return k.rip;
}

static EarlyRelocation<ClientRip> *
convertDirectRelocToClientReloc(EarlyRelocation<DirectRip> *er, const std::set<unsigned> &threads)
{
	if (RipRelativeRelocation<DirectRip> *rrr =
	    dynamic_cast<RipRelativeRelocation<DirectRip> *>(er)) {
		return new RipRelativeRelocation<ClientRip>(rrr->offset, rrr->size,
							    ClientRip(rrr->target.rip, threads, ClientRip::start_of_instruction),
							    rrr->nrImmediateBytes);
	} else if (RipRelativeBranchRelocation<DirectRip> *rrbr =
		   dynamic_cast<RipRelativeBranchRelocation<DirectRip> *>(er)) {
		return new RipRelativeBranchRelocation<ClientRip>(rrbr->offset, rrbr->size,
								  ClientRip(rrbr->target.rip, threads, ClientRip::start_of_instruction));

	} else {
		abort();
	}
}

template <typename src, typename dest> void
setToVector(const std::set<src> &in, std::vector<dest> &out)
{
	out.reserve(in.size());
	for (typename std::set<src>::iterator it = in.begin();
	     it != in.end();
	     it++)
		out.push_back(*it);
}

unsigned long
__trivial_hash_function(const DirectRip &r)
{
	return r.rip;
}
DirectRip
__threadRipToDirectRip(const ThreadRip &r)
{
	return DirectRip(r.rip);
}

class RexPrefix {
	RexPrefix() : w(false), r(false), x(false), b(false) {}
public:
	bool w, r, x, b;
	static RexPrefix wide() {
		RexPrefix r;
		r.w = true;
		return r;
	}
	static RexPrefix none() { return RexPrefix(); }
	unsigned char asByte() const {
		unsigned char res = 0x40;
		if (w)
			res |= 8;
		if (r)
			res |= 4;
		if (x)
			res |= 2;
		if (b)
			res |= 1;
		return res;
	}
	bool emit() const { return w || r || x || b; }
};

static Instruction<ClientRip> *
instrNoImmediatesNoModrm(unsigned opcode)
{
	Instruction<ClientRip> *work = new Instruction<ClientRip>();
	if (opcode >= 0x100) {
		assert((opcode & 0xff00) == 0x0f00);
		work->emit(0x0f);
		work->emit(opcode & 0xff);
	} else {
		work->emit(opcode);
	}
	return work;
}

static Instruction<ClientRip> *
instrNoImmediatesModrmOpcode(unsigned opcode, RegisterOrOpcodeExtension reg, const ModRM &rm, RexPrefix rex)
{
	Instruction<ClientRip> *work = new Instruction<ClientRip>();
	assert(!rex.b);
	if (reg.isOpcodeExtension && reg.opcodeExtension >= 8) {
		rex.r = true;
		reg.opcodeExtension -= 8;
	} else if (!reg.isOpcodeExtension && reg.idx.idx >= 8) {
		rex.r = true;
		reg.idx.idx -= 8;
	}
	if (rm.extendRm)
		rex.r = true;
	if (rex.emit())
		work->emit(rex.asByte());
	if (opcode >= 0x100) {
		assert((opcode & 0xff00) == 0x0f00);
		work->emit(0x0f);
		work->emit(opcode & 0xff);
	} else {
		work->emit(opcode);
	}
	work->emitModrm(rm, reg);
	return work;
}

static ModRM
modrmForSlot(simulationSlotT slot)
{
	return ModRM::absoluteAddress(slot.idx * 8);
}

static void
addGsPrefix(Instruction<ClientRip> *work)
{
	assert(work->len < sizeof(work->content));
	memmove(work->content + 1, work->content, work->len);
	work->len++;
	work->content[0] = 0x65;
}

class jcc_code {
	jcc_code(Byte _code) : code(_code) {}
public:
	Byte code;
	static jcc_code nonzero;
	static jcc_code zero;
};

jcc_code jcc_code::zero(0x84);
jcc_code jcc_code::nonzero(0x85);

/* Basic instructions */
static Instruction<ClientRip> *
instrPushReg(RegisterIdx reg)
{
	Instruction<ClientRip> *work = new Instruction<ClientRip>();
	if (reg.idx >= 8) {
		work->emit(0x41);
		reg.idx -= 8;
	}
	work->emit(0x50 + reg.idx);
	return work;
}
static Instruction<ClientRip> *
instrPopReg(RegisterIdx reg)
{
	Instruction<ClientRip> *work = new Instruction<ClientRip>();
	if (reg.idx >= 8) {
		work->emit(0x41);
		reg.idx -= 8;
	}
	work->emit(0x58 + reg.idx);
	return work;
}
static Instruction<ClientRip> *
instrPushf(void)
{
	return instrNoImmediatesNoModrm(0x9C);
}
static Instruction<ClientRip> *
instrPopf(void)
{
	return instrNoImmediatesNoModrm(0x9D);
}
static Instruction<ClientRip> *
instrPushModrm(const ModRM &mrm)
{
	if ((mrm.content[0] & 0xc0) == 0xc0) {
		/* modrm encodes direct register -> better way of doing this */
		unsigned k = mrm.content[0] & 7;
		if (mrm.extendRm)
			k |= 8;
		return instrPushReg(RegisterIdx::fromRaw(k));
	}
	return instrNoImmediatesModrmOpcode(0xFF, RegisterOrOpcodeExtension::opcode(6), mrm, RexPrefix::none());
}
static Instruction<ClientRip> *
instrPopModrm(const ModRM &mrm)
{
	if ((mrm.content[0] & 0xc0) == 0xc0) {
		/* modrm encodes direct register -> better way of doing this */
		unsigned k = mrm.content[0] & 7;
		if (mrm.extendRm)
			k |= 8;
		return instrPopReg(RegisterIdx::fromRaw(k));
	}
	return instrNoImmediatesModrmOpcode(0x8F, RegisterOrOpcodeExtension::opcode(0), mrm, RexPrefix::none());
}


static Instruction<ClientRip> *
instrMovRegisterToModrm(RegisterIdx reg, const ModRM &rm)
{
	return instrNoImmediatesModrmOpcode(0x89, reg, rm, RexPrefix::wide());
}
static Instruction<ClientRip> *
instrMovModrmToRegister(const ModRM &rm, RegisterIdx reg)
{
	return instrNoImmediatesModrmOpcode(0x8B, reg, rm, RexPrefix::wide());
}

static Instruction<ClientRip> *
instrLea(const ModRM &modrm, RegisterIdx reg)
{
	return instrNoImmediatesModrmOpcode(0x8d, reg, modrm, RexPrefix::wide());
}

static Instruction<ClientRip> *
instrMovImm64ToReg(unsigned long val, RegisterIdx reg)
{
	Instruction<ClientRip> *work = new Instruction<ClientRip>();
	if (reg.idx < 8) {
		work->emit(0x48);
	} else {
		work->emit(0x49);
		reg.idx -= 8;
	}
	work->emit(0xb8 + reg.idx);
	work->emitQword(val);
	return work;
}

static Instruction<ClientRip> *
instrCallModrm(const ModRM &mrm)
{
	return instrNoImmediatesModrmOpcode(0xff, RegisterOrOpcodeExtension::opcode(2), mrm, RexPrefix::none());
}

static Instruction<ClientRip> *
instrTestRegModrm(RegisterIdx reg, const ModRM &mrm)
{
	return instrNoImmediatesModrmOpcode(0x85, reg, mrm, RexPrefix::wide());
}

static Instruction<ClientRip> *
instrAddRegToModrm(RegisterIdx reg, const ModRM &mrm)
{
	return instrNoImmediatesModrmOpcode(0x01, reg, mrm, RexPrefix::wide());
}
static Instruction<ClientRip> *
instrAddModrmToReg(const ModRM &mrm, RegisterIdx reg)
{
	return instrNoImmediatesModrmOpcode(0x03, reg, mrm, RexPrefix::wide());
}

static Instruction<ClientRip> *
instrCmpModrmToReg(const ModRM &mrm, RegisterIdx reg)
{
	return instrNoImmediatesModrmOpcode(0x39, reg, mrm, RexPrefix::wide());
}
static Instruction<ClientRip> *
instrCmpRegToModrm(RegisterIdx reg, const ModRM &mrm)
{
	return instrNoImmediatesModrmOpcode(0x3b, reg, mrm, RexPrefix::wide());
}

static Instruction<ClientRip> *
instrNegModrm(const ModRM &mrm)
{
	return instrNoImmediatesModrmOpcode(0xf7, RegisterOrOpcodeExtension::opcode(3), mrm, RexPrefix::wide());
}

/* Special case: we don't try to do the generic encoding, because this
   is byte-addressed, and our modrm infratstructure can't cope. */
static Instruction<ClientRip> *
instrSetEqAl(void)
{
	Instruction<ClientRip> *work = new Instruction<ClientRip>();
	work->emit(0x0f);
	work->emit(0x94);
	work->emit(0xc0);
	return work;
}

/* Somewhat higher-level instruction-like things */
static Instruction<ClientRip> *
instrSkipRedZone(void)
{
	return instrLea(ModRM::memAtRegisterPlusOffset(RegisterIdx::RSP, -128),
			RegisterIdx::RSP);
}
static Instruction<ClientRip> *
instrRestoreRedZone(void)
{
	return instrLea(ModRM::memAtRegisterPlusOffset(RegisterIdx::RSP, 128),
			RegisterIdx::RSP);
}

static Instruction<ClientRip> *
instrMovRegToSlot(RegisterIdx offset, simulationSlotT slot)
{
	Instruction<ClientRip> *work = instrMovRegisterToModrm(offset, modrmForSlot(slot));
	addGsPrefix(work);
	return work;
}
static Instruction<ClientRip> *
instrMovSlotToReg(simulationSlotT slot, RegisterIdx offset)
{
	Instruction<ClientRip> *work = instrMovModrmToRegister(modrmForSlot(slot), offset);
	addGsPrefix(work);
	return work;
}

#define mk_slot_instr(name)						\
	static Instruction<ClientRip> *					\
	instr ## name ## RegToSlot(RegisterIdx reg, simulationSlotT slot) \
	{								\
		Instruction<ClientRip> *work = instr ## name ## RegToModrm(reg, modrmForSlot(slot)); \
		addGsPrefix(work);					\
		return work;						\
	}								\
	static Instruction<ClientRip> *					\
	instr ## name ## SlotToReg(simulationSlotT slot, RegisterIdx reg) \
	{								\
		Instruction<ClientRip> *work = instr ## name ## ModrmToReg(modrmForSlot(slot), reg); \
		addGsPrefix(work);					\
		return work;						\
	}
mk_slot_instr(Cmp)
mk_slot_instr(Add)

static Instruction<ClientRip> *
instrPushSlot(simulationSlotT slot)
{
	Instruction<ClientRip> *work = instrPushModrm(modrmForSlot(slot));
	addGsPrefix(work);
	return work;
}
static Instruction<ClientRip> *
instrPopSlot(simulationSlotT slot)
{
	Instruction<ClientRip> *work = instrPopModrm(modrmForSlot(slot));
	addGsPrefix(work);
	return work;
}

static Instruction<ClientRip> *
instrMovLabelToRegister(const char *label, RegisterIdx reg)
{
	Instruction<ClientRip> *work = instrMovImm64ToReg(0, reg);
	work->lateRelocs.push_back(new LateRelocation(work->len - 8,
						      8,
						      label,
						      0,
						      false));
	return work;
}

static Instruction<ClientRip> *
instrJcc(ClientRip target, jcc_code branchType)
{
	Instruction<ClientRip> *work = new Instruction<ClientRip>();
	work->emit(0x0f);
	work->emit(branchType.code);
	work->relocs.push_back(new RipRelativeBranchRelocation<ClientRip>(work->len,
									  4,
									  target));
	work->len += 4;
	return work;
}

/* ``composite'' instructions */
static Instruction<ClientRip> *
instrSaveRflags(Instruction<ClientRip> *start, slotMapT &exprsToSlots)
{
	Instruction<ClientRip> *cursor = start;

	cursor = cursor->defaultNextI = instrSkipRedZone();
	cursor = cursor->defaultNextI = instrPushf();
	cursor = cursor->defaultNextI = instrPopSlot(exprsToSlots.rflagsSlot());
	cursor = cursor->defaultNextI = instrRestoreRedZone();
	return cursor;
}
static Instruction<ClientRip> *
instrRestoreRflags(Instruction<ClientRip> *start, slotMapT &exprsToSlots)
{
	Instruction<ClientRip> *cursor = start;

	cursor = cursor->defaultNextI = instrSkipRedZone();
	cursor = cursor->defaultNextI = instrPushSlot(exprsToSlots.rflagsSlot());
	cursor = cursor->defaultNextI = instrPopf();
	cursor = cursor->defaultNextI = instrRestoreRedZone();
	return cursor;
}

static Instruction<ClientRip> *
instrCallSequence(Instruction<ClientRip> *start, const char *name)
{
	Instruction<ClientRip> *cursor = start;
	cursor = cursor->defaultNextI = instrSkipRedZone();
	cursor = cursor->defaultNextI = instrPushReg(RegisterIdx::RSI);
	cursor = cursor->defaultNextI = instrMovLabelToRegister(name, RegisterIdx::RSI);
	cursor = cursor->defaultNextI = instrCallModrm(ModRM::directRegister(RegisterIdx::RSI));
	cursor = cursor->defaultNextI = instrPopReg(RegisterIdx::RSI);
	cursor = cursor->defaultNextI = instrRestoreRedZone();
	return cursor;
}

static Instruction<ClientRip> *
instrLoadMessageToSlot(Instruction<ClientRip> *start,
		       unsigned msg_id,
		       unsigned msg_slot,
		       simulationSlotT simslot,
		       RegisterIdx spill)
{
	Instruction<ClientRip> *cursor = start;
	cursor = cursor->defaultNextI = instrMovLabelToRegister(
		vex_asprintf("(unsigned long)&__msg_%d_slot_%d", msg_id, msg_slot),
		spill);
	cursor = cursor->defaultNextI = instrMovModrmToRegister(ModRM::memAtRegister(spill), spill);
	cursor = cursor->defaultNextI = instrMovRegToSlot(spill, simslot);
	return cursor;
}

static Instruction<ClientRip> *
instrStoreSlotToMessage(Instruction<ClientRip> *start,
			unsigned msg_id,
			unsigned msg_slot,
			simulationSlotT simslot,
			RegisterIdx spill1,
			RegisterIdx spill2)
{
	start = start->defaultNextI = instrMovLabelToRegister(
		vex_asprintf("(unsigned long)&__msg_%d_slot_%d", msg_id, msg_slot),
		spill1);
	start = start->defaultNextI = instrMovSlotToReg(simslot, spill2);
	start = start->defaultNextI = instrMovRegisterToModrm(spill2, ModRM::memAtRegister(spill1));
	return start;
}

typedef std::pair<ClientRip, Instruction<ClientRip> **> relocEntryT;

static Instruction<ClientRip> *
instrHappensBeforeEdgeAfter(const happensBeforeEdge *hb, Instruction<ClientRip> *start,
			    slotMapT &exprsToSlots, ClientRip nextRip,
			    std::vector<relocEntryT> &relocs)
{
	Instruction<ClientRip> *cursor;

	cursor = instrSaveRflags(start, exprsToSlots);
	simulationSlotT rdi = exprsToSlots.allocateSlot();
	simulationSlotT rax = exprsToSlots.allocateSlot();
	cursor = cursor->defaultNextI = instrMovRegToSlot(RegisterIdx::RDI, rdi);
	cursor = cursor->defaultNextI = instrMovRegToSlot(RegisterIdx::RAX, rax);
	cursor = cursor->defaultNextI = instrMovImm64ToReg(hb->msg_id, RegisterIdx::RDI);
	cursor = instrCallSequence(cursor, "(unsigned long)happensBeforeEdge__after");
	cursor = cursor->defaultNextI = instrMovSlotToReg(rdi, RegisterIdx::RDI);
	cursor = cursor->defaultNextI = instrTestRegModrm(RegisterIdx::RAX, ModRM::directRegister(RegisterIdx::RAX));
	cursor = cursor->defaultNextI = instrMovSlotToReg(rax, RegisterIdx::RAX);

	ClientRip destinationIfThisFails = nextRip;
	destinationIfThisFails.eraseThread(hb->after.thread);
	destinationIfThisFails.type = ClientRip::restore_flags_and_branch;
	cursor = cursor->defaultNextI = instrJcc(destinationIfThisFails, jcc_code::zero);

	relocs.push_back(relocEntryT(destinationIfThisFails, &cursor->branchNextI));

	for (unsigned x = 0; x < hb->content.size(); x++) {
		simulationSlotT s = exprsToSlots(hb->after.thread, hb->content[x]);
		cursor = instrLoadMessageToSlot(cursor, hb->msg_id, x, s, RegisterIdx::RDI);
	}
	cursor = cursor->defaultNextI = instrMovSlotToReg(rdi, RegisterIdx::RDI);
	cursor = instrRestoreRflags(cursor, exprsToSlots);
	return cursor;
}

static Instruction<ClientRip> *
instrHappensBeforeEdgeBefore(Instruction<ClientRip> *start, const happensBeforeEdge *hb,
			     slotMapT &exprsToSlots)
{
	simulationSlotT rdi = exprsToSlots.allocateSlot();
	start = start->defaultNextI = instrMovRegToSlot(RegisterIdx::RDI, rdi);
	simulationSlotT r13 = exprsToSlots.allocateSlot();
	start = start->defaultNextI = instrMovRegToSlot(RegisterIdx::R13, r13);

	for (unsigned x = 0; x < hb->content.size(); x++) {
		simulationSlotT s = exprsToSlots(hb->before.thread, hb->content[x]);
		start = instrStoreSlotToMessage(start, hb->msg_id, x, s, RegisterIdx::RDI, RegisterIdx::R13);
	}
	start = start->defaultNextI = instrMovImm64ToReg(hb->msg_id, RegisterIdx::RDI);
	start = instrCallSequence(start, "(unsigned long)happensBeforeEdge__before");
	start = start->defaultNextI = instrMovSlotToReg(r13, RegisterIdx::R13);
	start = start->defaultNextI = instrMovSlotToReg(rdi, RegisterIdx::RDI);
	return start;
}

static Instruction<ClientRip> *
instrEvalExpr(Instruction<ClientRip> *start, unsigned thread, IRExpr *e, RegisterIdx reg,
	      slotMapT &exprsToSlots)
{
	{
		slotMapT::iterator it = exprsToSlots.find(std::pair<unsigned, IRExpr *>(thread, e));
		if (it != exprsToSlots.end()) {
			start = start->defaultNextI = instrMovSlotToReg(it->second, reg);
			return start;
		}
	}

	Instruction<ClientRip> *cursor;

	switch (e->tag) {
	case Iex_Const:
		start = start->defaultNextI = instrMovImm64ToReg(e->Iex.Const.con->Ico.U64, reg);
		return start;

	case Iex_Unop:
		switch (e->Iex.Unop.op) {
		case Iop_Neg64:
			cursor = instrEvalExpr(start, thread, e->Iex.Unop.arg, reg, exprsToSlots);
			if (!cursor)
				return NULL;
			cursor = cursor->defaultNextI = instrNegModrm(ModRM::directRegister(reg));
			return cursor;
		default:
			break;
		}
		break;

	case Iex_Binop:
		switch (e->Iex.Binop.op) {
		case Iop_CmpEQ64: {
			simulationSlotT old_rax = exprsToSlots.allocateSlot();
			Instruction<ClientRip> *head = new Instruction<ClientRip>();
			Instruction<ClientRip> *cursor;

			cursor = instrEvalExpr(head, thread, e->Iex.Binop.arg1, reg, exprsToSlots);
			if (!cursor)
				return NULL;
			simulationSlotT t = exprsToSlots.allocateSlot();
			cursor = cursor->defaultNextI = instrMovRegToSlot(reg, t);
			cursor = instrEvalExpr(cursor, thread, e->Iex.Binop.arg2, reg, exprsToSlots);
			if (!cursor)
				return NULL;
			cursor = cursor->defaultNextI = instrCmpRegToSlot(reg, t);

			if (reg != RegisterIdx::RAX)
				cursor = cursor->defaultNextI = instrMovRegToSlot(RegisterIdx::RAX, old_rax);
			cursor = cursor->defaultNextI = instrMovImm64ToReg(0, RegisterIdx::RAX);
			cursor = cursor->defaultNextI = instrSetEqAl();
			if (reg != RegisterIdx::RAX) {
				cursor = cursor->defaultNextI = instrMovRegisterToModrm(RegisterIdx::RAX, ModRM::directRegister(reg));
				cursor = cursor->defaultNextI = instrMovSlotToReg(old_rax, RegisterIdx::RAX);
			}
			start->defaultNextI = head->defaultNextI;
			return cursor;
		}
		default:
			break;
		}
		break;
	case Iex_Associative:
		switch (e->Iex.Associative.op) {
		case Iop_Add64: {
			Instruction<ClientRip> *head = new Instruction<ClientRip>();
			Instruction<ClientRip> *cursor;
			cursor = instrEvalExpr(head, thread, e->Iex.Associative.contents[0], reg, exprsToSlots);
			if (!cursor)
				return NULL;
			if (e->Iex.Associative.nr_arguments == 1) {
				start->defaultNextI = head->defaultNextI;
				return cursor;
			}

			simulationSlotT acc = exprsToSlots.allocateSlot();
			cursor = cursor->defaultNextI = instrMovRegToSlot(reg, acc);
			for (int x = 1; x < e->Iex.Associative.nr_arguments - 1; x++) {
				cursor = instrEvalExpr(cursor, thread, e->Iex.Associative.contents[x], reg, exprsToSlots);
				if (!cursor)
					return NULL;
				cursor = cursor->defaultNextI = instrAddRegToSlot(reg, acc);
			}
			cursor = instrEvalExpr(cursor, thread, e->Iex.Associative.contents[e->Iex.Associative.nr_arguments - 1],
					       reg, exprsToSlots);
			if (!cursor)
				return NULL;
			cursor = cursor->defaultNextI = instrAddSlotToReg(acc, reg);
			start->defaultNextI = head->defaultNextI;
			return cursor;
		}
		default:
			break;
		}
		break;
	default:
		break;
	}

	fprintf(stderr, "WARNING: Cannot evaluate ");
	ppIRExpr(e, stderr);
	fprintf(stderr, "\n");
	dbg_break("Hello");
	return NULL;
}

static Instruction<ClientRip> *
instrCompareExprToZero(Instruction<ClientRip> *start, unsigned thread, IRExpr *expr,
		       slotMapT &exprsToSlots)
{
	RegisterIdx reg = RegisterIdx::RAX;
	simulationSlotT spill = exprsToSlots.allocateSlot();
	Instruction<ClientRip> *cursor, *first;
	cursor = first = instrMovRegToSlot(reg, spill);
	cursor = instrEvalExpr(cursor, thread, expr, reg, exprsToSlots);
	if (!cursor)
		return NULL;
	cursor = cursor->defaultNextI = instrTestRegModrm(reg, ModRM::directRegister(reg));
	cursor = cursor->defaultNextI = instrMovSlotToReg(spill, reg);
	start->defaultNextI = first;
	return cursor;
}

static Instruction<ClientRip> *
instrCheckExpressionOrEscape(Instruction<ClientRip> *start,
			     const exprEvalPoint &e,
			     ClientRip failTarget,
			     slotMapT &exprsToSlots)
{
	/* Bit of a hack: the fail target's thread set is the set of
	   threads which are currently live. */
	if (!failTarget.threadLive(e.thread))
		return start;
	IRExpr *expr = e.e;
	bool invert = e.invert;

	/* Special case: if the expression is already in the form x == 0
	   then we can just flip the invert flag and then evaluate x
	   directly. */
	if (expr->tag == Iex_Binop &&
	    expr->Iex.Binop.op == Iop_CmpEQ64 &&
	    expr->Iex.Binop.arg1->tag == Iex_Const &&
	    expr->Iex.Binop.arg1->Iex.Const.con->Ico.U64 == 0) {
		invert = !invert;
		expr = expr->Iex.Binop.arg2;
	}

	Instruction<ClientRip> *cursor = instrCompareExprToZero(start, e.thread, expr, exprsToSlots);
	if (!cursor)
		return start;

	jcc_code branch_type = invert ? jcc_code::nonzero : jcc_code::zero;
	failTarget.eraseThread(e.thread);
	failTarget.type = ClientRip::restore_flags_and_branch;
	cursor = cursor->defaultNextI = instrJcc(failTarget, branch_type);
	return cursor;
}

/* Is this opcode byte a prefix opcode? */
static bool
isPrefix(unsigned char opcode)
{
	return ((opcode >= 0x40 && opcode <= 0x4f) ||
		(opcode == 0x26) ||
		(opcode == 0x2E) ||
		(opcode == 0x36) ||
		(opcode == 0x3D) ||
		(opcode >= 64 && opcode <= 0x67) ||
		(opcode == 0xF0) ||
		(opcode == 0xF2) ||
		(opcode == 0xF3));
}

static unsigned
instrOpcode(Instruction<DirectRip> *i)
{
	unsigned j;
	j = 0;
	/* Skip prefixes */
	while (j < i->len && isPrefix(i->content[j]))
		j++;
	assert(j < i->len);
	if (i->content[j] == 0x0F) {
		/* Two-byte opcode */
		assert(j+1 < i->len);
		return 0x0F00 | i->content[j+1];
	} else {
		return i->content[j];
	}
}

static RegisterIdx
instrModrmReg(Instruction<DirectRip> *i)
{
	unsigned j;
	bool extend;

	j = 0;
	extend = false;

	/* Skip prefixes */
	while (j < i->len && isPrefix(i->content[j])) {
		if (i->content[j] >= 0x40 && i->content[j] <= 0x4f)
			if (i->content[j] & 4)
				extend = true;
		j++;
	}
	assert(j < i->len);
	/* Skip opcode */
	if (i->content[j] == 0x0F)
		j++;
	j++;
	assert(j < i->len);
	/* Next one must be modrm */
	unsigned char modrm = i->content[j];
	unsigned res = (modrm >> 3) & 7;
	if (extend)
		res |= 8;
	RegisterIdx r = RegisterIdx::RAX;
	r.idx = res;
	return r;
}

static CFG<ClientRip> *
convertCFGFromThreadRipToClientRips(CFG<ThreadRip> *cfg,
				    std::set<ClientRip> &roots,
				    expressionStashMapT &neededExpressions,
				    slotMapT &exprsToSlots,
				    std::map<unsigned long, std::set<happensBeforeEdge *> > &happensBeforePoints,
				    expressionEvalMapT &expressionEvalPoints)
{
	CFG<DirectRip> *degraded = cfg->degrade<DirectRip, __threadRipToDirectRip>();
	CFG<ClientRip> *res = new CFG<ClientRip>(cfg->as);
	std::vector<ClientRip> neededRips;
	setToVector(roots, neededRips);
	std::vector<relocEntryT> relocs;

	/* Expand the CFG up by inserting the necessary extra
	   instructions to actually perform all of our checking. */
	while (1) {
		if (neededRips.empty()) {
			if (relocs.empty())
				break;
			for (unsigned x = 0;
			     x < relocs.size();
				) {
				relocEntryT re = relocs[x];
				if (res->ripToInstr->hasKey(re.first)) {
					*re.second = res->ripToInstr->get(re.first);
					relocs.erase(relocs.begin() + x);
				} else {
					neededRips.push_back(re.first);
					x++;
				}
			}
			if (neededRips.empty()) {
				assert(relocs.empty());
				break;
			}
		}
		ClientRip cr = neededRips.back();
		neededRips.pop_back();

		if (res->ripToInstr->hasKey(cr))
			continue;

		Instruction<ClientRip> *newInstr = new Instruction<ClientRip>();

		res->ripToInstr->set(cr, newInstr);

		newInstr->rip = cr;

		switch (cr.type) {
		case ClientRip::start_of_instruction:
			if (neededExpressions.count(cr.rip)) {
				std::set<std::pair<unsigned, IRExpr *> > *neededExprs = &neededExpressions[cr.rip];
				for (std::set<std::pair<unsigned, IRExpr *> >::iterator it = neededExprs->begin();
				     it != neededExprs->end();
				     it++) {
					if (!cr.threadLive(it->first))
						continue;
					IRExpr *e = it->second;
					if (e->tag == Iex_Get) {
						/* Easy case: just store the register in its slot */
						simulationSlotT s = exprsToSlots(it->first, e);
						newInstr->defaultNextI =
							instrMovRegToSlot(RegisterIdx::fromVexOffset(e->Iex.Get.offset), s);
						newInstr = newInstr->defaultNextI;
					} else if (e->tag == Iex_ClientCall || e->tag == Iex_Load) {
						/* Do this after emitting the instruction */
					} else {
						abort();
					}
				}
			}
			relocs.push_back(relocEntryT(ClientRip(cr, ClientRip::receive_messages),
						     &newInstr->defaultNextI));
			break;
		case ClientRip::receive_messages:
			if (happensBeforePoints.count(cr.rip)) {
				printf("%lx has HB after edges\n", cr.rip);
				std::set<happensBeforeEdge *> *hbEdges = &happensBeforePoints[cr.rip];
				for (std::set<happensBeforeEdge *>::iterator it = hbEdges->begin();
				     it != hbEdges->end();
				     it++) {
					const happensBeforeEdge *hb = *it;
					if (hb->after.rip == cr.rip &&
					    cr.threadLive(hb->after.thread)) {
						printf("Instantiate %lx:%d <-< %lx:%d\n",
						       hb->before.rip, hb->before.thread,
						       hb->after.rip, hb->after.thread);
						newInstr = instrHappensBeforeEdgeAfter(hb, newInstr, exprsToSlots, cr, relocs);
					} else {
						printf("Skip %lx:%d <-< %lx:%d\n",
						       hb->before.rip, hb->before.thread,
						       hb->after.rip, hb->after.thread);
					}
				}
			} else {
				printf("%lx has no HB edges\n", cr.rip);
			}
			relocs.push_back(relocEntryT(ClientRip(cr, ClientRip::original_instruction),
						     &newInstr->defaultNextI));
			break;
		case ClientRip::original_instruction: {
			Instruction<DirectRip> *underlying = degraded->ripToInstr->get(cr.rip);
			assert(underlying);
			if (underlying->defaultNextI) {
				ClientRip c(cr, ClientRip::post_instr_generate);
				relocs.push_back(relocEntryT(c, &newInstr->defaultNextI));
			} else if (underlying->defaultNext.rip) {
				/* If we have a defaultNext but not a
				   defaultNextI then that means that
				   the default next has been pruned
				   from the patch, so we should just
				   get out rather than trying to
				   insert additional checks. */
				newInstr->defaultNext = ClientRip(cr, underlying->defaultNext.rip, ClientRip::start_of_instruction);
			}

			/* XXX we pretty much assume that branches
			   can't have post-instruction events
			   (generate value, eval expression, or
			   originate message), because otherwise we
			   won't bother generating them when the
			   branch is taken. */
			if (underlying->branchNext.rip)
				newInstr->branchNext = ClientRip(cr, underlying->branchNext.rip, ClientRip::start_of_instruction);
			if (underlying->branchNextI) {
				ClientRip c(cr, underlying->branchNextI->rip.rip, ClientRip::start_of_instruction);
				relocs.push_back(relocEntryT(c, &newInstr->branchNextI));
			}
			memcpy(newInstr->content, underlying->content, underlying->len);
			newInstr->len = underlying->len;
			newInstr->pfx = underlying->pfx;
			newInstr->nr_prefixes = underlying->nr_prefixes;
			for (auto it = underlying->relocs.begin(); it != underlying->relocs.end(); it++)
				newInstr->relocs.push_back(convertDirectRelocToClientReloc(*it, cr.threads));
			break;
		}
		case ClientRip::post_instr_generate:
			if (neededExpressions.count(cr.rip)) {
				std::set<std::pair<unsigned, IRExpr *> > *neededExprs = &neededExpressions[cr.rip];
				Instruction<DirectRip> *underlying = degraded->ripToInstr->get(cr.rip);
				assert(underlying);
				for (std::set<std::pair<unsigned, IRExpr *> >::iterator it = neededExprs->begin();
				     it != neededExprs->end();
				     it++) {
					if (!cr.threadLive(it->first))
						continue;
					IRExpr *e = it->second;
					if (e->tag == Iex_Get) {
						/* Already handled */
					} else if (e->tag == Iex_ClientCall) {
						/* The result of the call should now be in %rax */
						simulationSlotT s = exprsToSlots(it->first, e);
						newInstr->defaultNextI = instrMovRegToSlot(RegisterIdx::RAX, s);
						newInstr = newInstr->defaultNextI;
					} else {
						assert(e->tag == Iex_Load);
						switch (instrOpcode(underlying)) {
						case 0x8b: {
							/* Load from memory to modrm.
							 * Nice and easy. */
							simulationSlotT s = exprsToSlots(it->first, e);
							newInstr->defaultNextI = instrMovRegToSlot(instrModrmReg(underlying), s);
							newInstr = newInstr->defaultNextI;
							break;
						}
						default:
							abort();
						}
					}
				}
			}
			relocs.push_back(relocEntryT(ClientRip(cr, ClientRip::post_instr_checks),
						     &newInstr->defaultNextI));
			break;
		case ClientRip::post_instr_checks:
			if (expressionEvalPoints.count(cr.rip)) {
				std::set<exprEvalPoint> &expressionsToEval(expressionEvalPoints[cr.rip]);
				Instruction<DirectRip> *underlying = degraded->ripToInstr->get(cr.rip);
				assert(underlying);
				DirectRip _fallThrough = underlying->defaultNextI ? underlying->defaultNextI->rip : underlying->defaultNext;
				ClientRip fallThrough(cr, _fallThrough.rip, ClientRip::start_of_instruction);
				
				bool doit = false;
				for (std::set<exprEvalPoint>::iterator it = expressionsToEval.begin();
				     !doit && it != expressionsToEval.end();
				     it++)
					if (cr.threadLive(it->thread))
						doit = true;
				if (doit) {
					newInstr = instrSaveRflags(newInstr, exprsToSlots);
					for (std::set<exprEvalPoint>::iterator it = expressionsToEval.begin();
					     it != expressionsToEval.end();
					     it++)
						newInstr = instrCheckExpressionOrEscape(newInstr, *it, fallThrough, exprsToSlots);
					newInstr = instrRestoreRflags(newInstr, exprsToSlots);
				}
			}
			relocs.push_back(relocEntryT(ClientRip(cr, ClientRip::generate_messages),
						     &newInstr->defaultNextI));
			break;
		case ClientRip::generate_messages:
			if (happensBeforePoints.count(cr.rip)) {
				std::set<happensBeforeEdge *> *hbEdges = &happensBeforePoints[cr.rip];
				for (std::set<happensBeforeEdge *>::iterator it = hbEdges->begin();
				     it != hbEdges->end();
				     it++) {
					happensBeforeEdge *hb = *it;
					if (hb->before.rip == cr.rip &&
					    cr.threadLive(hb->before.thread))
						newInstr = instrHappensBeforeEdgeBefore(newInstr, hb, exprsToSlots);
				}
			}

			/* Where do we go next? */
			{
				Instruction<DirectRip> *underlying = degraded->ripToInstr->get(cr.rip);
				assert(underlying);
				if (underlying->defaultNext.rip)
					newInstr->defaultNext = ClientRip(cr, underlying->defaultNext.rip, ClientRip::start_of_instruction);
				if (underlying->defaultNextI) {
					ClientRip c(cr, underlying->defaultNextI->rip.rip, ClientRip::start_of_instruction);
					relocs.push_back(relocEntryT(c, &newInstr->defaultNextI));
				}
			}
			break;

		case ClientRip::restore_flags_and_branch:
			newInstr = instrRestoreRflags(newInstr, exprsToSlots);

			cr.type = ClientRip::post_instr_checks;
			relocs.push_back(relocEntryT(cr, &newInstr->defaultNextI));
			break;

		case ClientRip::uninitialised: /* Shouldn't happen. */
			abort();
		}
	}

	return res;
}

static void
partitionCrashCondition(DNF_Conjunction &c, FreeVariableMap &fv,
			std::map<unsigned, ThreadRip> &roots,
			AddressSpace *as)
{
	/* Figure out what we actually need to keep track of */
	std::set<IRExpr *> neededExpressions;
	for (unsigned x = 0; x < c.size(); x++)
		enumerateNeededExpressions(c[x].second, neededExpressions);

	/* and where the needed expressions are calculated */
	std::set<ThreadRip> neededRips;
	for (std::set<IRExpr *>::iterator it = neededExpressions.begin();
	     it != neededExpressions.end();
	     it++) {
		IRExpr *e = *it;
		if (e->tag == Iex_Get) {
			neededRips.insert(roots[e->Iex.Get.tid]);
		} else if (e->tag == Iex_ClientCall) {
			neededRips.insert(e->Iex.ClientCall.callSite);
		} else if (e->tag == Iex_Load) {
			neededRips.insert(e->Iex.Load.rip);
		} else if (e->tag == Iex_HappensBefore) {
			neededRips.insert(e->Iex.HappensBefore.before);
			neededRips.insert(e->Iex.HappensBefore.after);
		} else {
			abort();
		}
	}

	/* and which threads are relevant */
	std::set<unsigned> neededThreads;
	for (std::set<ThreadRip>::iterator it = neededRips.begin();
	     it != neededRips.end();
	     it++)
		neededThreads.insert(it->thread);

	/* Build the CFG */
	EnforceCrashCFG *cfg = new EnforceCrashCFG(as, neededRips);
	for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
	     it != roots.end();
	     it++) {
		printf("Root %d:%lx\n", it->second.thread, it->second.rip);
		cfg->add_root(it->second, 100);
	}
	cfg->doit();
	
	/* Figure out where the various expressions should be
	 * evaluated. */
	expressionDominatorMapT exprDominatorMap(c, cfg, neededRips);

	/* Figure out where we need to stash the various necessary
	 * expressions.  This is a map from RIPs to <thread,expr>
	 * pairs, where we need to stash @expr if we execute
	 * instruction @RIP in thread @thread. */
	expressionStashMapT exprStashPoints(neededExpressions, roots);

	/* And where we need to calculate them. */
	expressionEvalMapT exprEvalPoints(exprDominatorMap);

	/* Find out where the happens-before edges start and end. */
	std::map<unsigned long, std::set<happensBeforeEdge *> > happensBeforePoints;
	for (unsigned x = 0; x < c.size(); x++) {
		IRExpr *e = c[x].second;
		bool invert = c[x].first;
		if (e->tag == Iex_HappensBefore) {
			IRExpr::HappensBefore *hb = &e->Iex.HappensBefore;
			happensBeforeEdge *hbe = new happensBeforeEdge(invert, *hb, exprDominatorMap.idom,
								       cfg, exprStashPoints);
			happensBeforePoints[hbe->before.rip].insert(hbe);
			happensBeforePoints[hbe->after.rip].insert(hbe);
		}
	}

	/* Figure out what slots to use for the various
	 * expressions. */
	slotMapT slotMap(exprStashPoints, happensBeforePoints);

	/* The patch needs to be built in direct RIP space, rather
	 * than in ThreadRip space.  That means we need to degrade the
	 * CFG. */
	std::set<ClientRip> entryPoints;
	std::map<unsigned long, std::set<unsigned> > threadsRelevantAtEachEntryPoint;
	for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
	     it != roots.end();
	     it++)
		threadsRelevantAtEachEntryPoint[it->second.rip].insert(it->first);
	for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
	     it != roots.end();
	     it++) {
		std::set<unsigned> &threads(threadsRelevantAtEachEntryPoint[it->second.rip]);
		entryPoints.insert(ClientRip(it->second.rip, threads, ClientRip::start_of_instruction));
	}
	CFG<ClientRip> *degradedCfg = convertCFGFromThreadRipToClientRips(
		cfg,
		entryPoints,
		exprStashPoints,
		slotMap,
		happensBeforePoints,
		exprEvalPoints
		);

	/* Now build the patch */
	EnforceCrashPatchFragment *pf = new EnforceCrashPatchFragment(happensBeforePoints);
	pf->fromCFG(degradedCfg);

	printf("Fragment:\n");
	printf("%s", pf->asC("ident", entryPoints));
}

static bool
analyseHbGraph(DNF_Conjunction &c, CrashSummary *summary)
{
	std::set<IRExpr::HappensBefore> hb;
	std::set<IRExpr::HappensBefore> assumption;

	extractImplicitOrder(summary->loadMachine, assumption);
	for (unsigned x = 0; x < summary->storeMachines.size(); x++)
		extractImplicitOrder(summary->storeMachines[x]->machine, assumption);
	for (unsigned x = 0; x < c.size(); x++) {
		if (c[x].second->tag == Iex_HappensBefore) {
			IRExpr::HappensBefore h;
			if (c[x].first) {
				h.before = c[x].second->Iex.HappensBefore.after;
				h.after = c[x].second->Iex.HappensBefore.before;
			} else {
				h = c[x].second->Iex.HappensBefore;
			}
			hb.insert(h);
		}
	}

	if (!simplifyOrdering(hb, assumption)) {
		/* Contradiction, get out */
		return false;
	}

	/* Build the results */
	DNF_Conjunction out;
	for (unsigned x = 0; x < c.size(); x++)
		if (c[x].second->tag != Iex_HappensBefore)
			out.push_back(c[x]);
	for (std::set<IRExpr::HappensBefore>::iterator it = hb.begin();
	     it != hb.end();
	     it++)
		out.push_back(std::pair<bool, IRExpr *>(
				      false,
				      IRExpr_HappensBefore(it->before, it->after)));

	c = out;

	return true;
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	int fd = open(argv[4], O_RDONLY);
	if (fd < 0)
		err(1, "opening %s", argv[4]);
	VexPtr<CrashSummary, &ir_heap> summary(readCrashSummary(fd));
	close(fd);

	printf("Machines to enforce:\n");
	printCrashSummary(summary, stdout);

	IRExpr *requirement = findHappensBeforeRelations(summary, oracle, ALLOW_GC);
	fprintf(_logfile, "Crash requirement:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");

	std::map<unsigned, ThreadRip> roots;
	roots[summary->loadMachine->tid] = ThreadRip::mk(summary->loadMachine->tid, summary->loadMachine->origin);
	
	FreeVariableMap m(summary->loadMachine->freeVariables);
	zapBindersAndFreeVariables(m, summary->loadMachine);
	for (unsigned x = 0; x < summary->storeMachines.size(); x++) {
		FreeVariableMap n(summary->storeMachines[x]->machine->freeVariables);
		zapBindersAndFreeVariables(n, summary->storeMachines[x]->machine);
		m.merge(n);
		roots[summary->storeMachines[x]->machine->tid] =
			ThreadRip::mk(summary->storeMachines[x]->machine->tid,
				      summary->storeMachines[x]->machine->origin);
	}

	requirement = internIRExpr(zapFreeVariables(requirement, m));
	fprintf(_logfile, "After free variable removal:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");

	DNF_Disjunction d;
	if (TIMEOUT || !dnf(requirement, d)) {
		fprintf(_logfile, "failed to convert to DNF\n");
		return 1;
	}
	for (unsigned x = 0; x < d.size(); ) {
		if (analyseHbGraph(d[x], summary)) {
			x++;
		} else {
			d.erase(d.begin() + x);
		}
	}

	printDnf(d, _logfile);
       
	for (unsigned x = 0; x < d.size(); x++) {
		printf("Examine clause %d\n", x);
		partitionCrashCondition(d[x], m, roots, ms->addressSpace);
	}

	return 0;
}
