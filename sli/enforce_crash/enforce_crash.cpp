#include <sys/fcntl.h>
#include <sys/wait.h>
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
public:
	std::set<ThreadRip> usefulInstrs;
	bool instructionUseful(Instruction<ThreadRip> *i) {
		if (usefulInstrs.count(i->rip))
			return true;
		else
			return false;
	}
	bool exploreFunction(ThreadRip rip) {
		return true;
	}
	EnforceCrashCFG(AddressSpace *as,
			const std::set<ThreadRip> &_usefulInstrs)
		: CFG<ThreadRip>(as), usefulInstrs(_usefulInstrs)
	{}
};

struct DirectRip {
	unsigned long rip;
	DirectRip(unsigned long _rip) : rip(_rip) {}
	DirectRip() : rip(0) {}
	bool operator==(const DirectRip &d) const { return rip == d.rip; }
	DirectRip operator+(long offset) const { return DirectRip(rip + offset); }
};

void
instrToInstrSetMap::print(FILE *f)
{
	for (iterator it = begin(); it != end(); it++) {
		fprintf(f, "%s[%p] -> {", it->first->rip.name(), it->first);
		for (std::set<Instruction<ThreadRip> *>::iterator it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			if (it2 != it->second.begin())
				fprintf(f, ", ");
			fprintf(f, "%s[%p]", (*it2)->rip.name(), *it2);
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
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1);
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
	int opcode_bytes = 1;
	if (rex.emit())
		opcode_bytes++;
	if (opcode >= 0x100)
		opcode_bytes++;
	Instruction<ClientRip> *work = new Instruction<ClientRip>(opcode_bytes);
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
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1);
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
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1);
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
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1);
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
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1);
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
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1);
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
instrMovModrmToSlot(Instruction<ClientRip> *start, const ModRM &modrm, simulationSlotT slot, simulationSlotT spill)
{
	if (modrm.isRegister()) {
		return start->defaultNextI = instrMovRegToSlot(modrm.getRegister(), slot);
	} else {
		RegisterIdx tmp = modrm.selectNonConflictingRegister();
		start = start->defaultNextI = instrMovRegToSlot(tmp, spill);
		start = start->defaultNextI = instrMovModrmToRegister(modrm, tmp);
		start = start->defaultNextI = instrMovRegToSlot(tmp, slot);
		start = start->defaultNextI = instrMovSlotToReg(spill, tmp);
		return start;
	}
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
		start = start->defaultNextI = instrMovImm64ToReg(((IRExprConst *)e)->con->Ico.U64, reg);
		return start;

	case Iex_Unop:
		switch (((IRExprUnop *)e)->op) {
		case Iop_Neg64:
			cursor = instrEvalExpr(start, thread, ((IRExprUnop *)e)->arg, reg, exprsToSlots);
			if (!cursor)
				return NULL;
			cursor = cursor->defaultNextI = instrNegModrm(ModRM::directRegister(reg));
			return cursor;
		default:
			break;
		}
		break;

	case Iex_Binop:
		switch (((IRExprBinop *)e)->op) {
		case Iop_CmpEQ64: {
			simulationSlotT old_rax = exprsToSlots.allocateSlot();
			Instruction<ClientRip> *head = new Instruction<ClientRip>(-1);
			Instruction<ClientRip> *cursor;

			cursor = instrEvalExpr(head, thread, ((IRExprBinop *)e)->arg1, reg, exprsToSlots);
			if (!cursor)
				return NULL;
			simulationSlotT t = exprsToSlots.allocateSlot();
			cursor = cursor->defaultNextI = instrMovRegToSlot(reg, t);
			cursor = instrEvalExpr(cursor, thread, ((IRExprBinop *)e)->arg2, reg, exprsToSlots);
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
		switch (((IRExprAssociative *)e)->op) {
		case Iop_Add64: {
			Instruction<ClientRip> *head = new Instruction<ClientRip>(-1);
			Instruction<ClientRip> *cursor;
			cursor = instrEvalExpr(head, thread, ((IRExprAssociative *)e)->contents[0], reg, exprsToSlots);
			if (!cursor)
				return NULL;
			if (((IRExprAssociative *)e)->nr_arguments == 1) {
				start->defaultNextI = head->defaultNextI;
				return cursor;
			}

			simulationSlotT acc = exprsToSlots.allocateSlot();
			cursor = cursor->defaultNextI = instrMovRegToSlot(reg, acc);
			for (int x = 1; x < ((IRExprAssociative *)e)->nr_arguments - 1; x++) {
				cursor = instrEvalExpr(cursor, thread, ((IRExprAssociative *)e)->contents[x], reg, exprsToSlots);
				if (!cursor)
					return NULL;
				cursor = cursor->defaultNextI = instrAddRegToSlot(reg, acc);
			}
			cursor = instrEvalExpr(cursor, thread, ((IRExprAssociative *)e)->contents[((IRExprAssociative *)e)->nr_arguments - 1],
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
	    ((IRExprBinop *)expr)->op == Iop_CmpEQ64 &&
	    ((IRExprBinop *)expr)->arg1->tag == Iex_Const &&
	    ((IRExprConst *)((IRExprBinop *)expr)->arg1)->con->Ico.U64 == 0) {
		invert = !invert;
		expr = ((IRExprBinop *)expr)->arg2;
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

static ModRM
instrModrm(const Instruction<DirectRip> *i)
{
	assert(i->modrm_start != -1);
	assert(i->modrm_start < (int)i->len);

	return ModRM::fromBytes(i->content + i->modrm_start);
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

class happensBeforeMapT : public std::map<unsigned long, std::set<happensBeforeEdge *> >,
			  private GcCallback<&ir_heap> {
	void runGc(HeapVisitor &hv) {
		for (auto it = begin(); it != end(); it++)
			visit_set(it->second, hv);
	}
public:
	happensBeforeMapT() {}
	happensBeforeMapT(DNF_Conjunction &c,
			  expressionDominatorMapT &exprDominatorMap,
			  EnforceCrashCFG *cfg,
			  expressionStashMapT &exprStashPoints)
	{
		for (unsigned x = 0; x < c.size(); x++) {
			IRExpr *e = c[x].second;
			bool invert = c[x].first;
			if (e->tag == Iex_HappensBefore) {
				IRExprHappensBefore *hb = (IRExprHappensBefore *)e;
				happensBeforeEdge *hbe = new happensBeforeEdge(invert, hb, exprDominatorMap.idom,
									       cfg, exprStashPoints);
				(*this)[hbe->before.rip].insert(hbe);
				(*this)[hbe->after.rip].insert(hbe);
			}
		}
	}
	void operator|=(const happensBeforeMapT &hbm) {
		for (auto it = hbm.begin(); it != hbm.end(); it++) {
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				(*this)[it->first].insert(*it2);
		}
	}
};

class crashEnforcementRoots : public std::set<ClientRip> {
public:
	crashEnforcementRoots() {}

	crashEnforcementRoots(std::map<unsigned, ThreadRip> &roots) {
		std::map<unsigned long, std::set<unsigned> > threadsRelevantAtEachEntryPoint;
		for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
		     it != roots.end();
		     it++)
			threadsRelevantAtEachEntryPoint[it->second.rip].insert(it->first);
		for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
		     it != roots.end();
		     it++) {
			std::set<unsigned> &threads(threadsRelevantAtEachEntryPoint[it->second.rip]);
			insert(ClientRip(it->second.rip, threads, ClientRip::start_of_instruction));
		}
	}

	void operator|=(const crashEnforcementRoots &cer) {
		for (auto it = cer.begin(); it != cer.end(); it++)
			insert(*it);
	}
};

/* Map that tells us where the various threads have to exit. */
class abstractThreadExitPointsT : public std::map<unsigned long, std::set<unsigned> > {
public:
	abstractThreadExitPointsT() {}
	abstractThreadExitPointsT(EnforceCrashCFG *cfg, happensBeforeMapT &);
	void operator|=(const abstractThreadExitPointsT &atet) {
		for (auto it = atet.begin(); it != atet.end(); it++)
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				(*this)[it->first].insert(*it2);
	}
};
abstractThreadExitPointsT::abstractThreadExitPointsT(EnforceCrashCFG *cfg,
						     happensBeforeMapT &happensBeforePoints)
{
	/* We need to exit thread X if we reach instruction Y and
	   there is some message which is needed by thread X such that
	   Y cannot have already received that message and cannot
	   subsequently send it.  We also exit if Y can neither send
	   nor receive any further messages. */

	typedef Instruction<ThreadRip> instrT;

	/* Step one: build control-flow reachability maps */

	/* forwardReachable[x] -> the set of instructions y such that
	   there's some control flow path from x to y */
	instrToInstrSetMap forwardReachable;
	/* backwardReachable[x] -> the set of instructions y such that
	   there's some control flow path from y to x */
	instrToInstrSetMap backwardReachable;

	for (auto it = cfg->ripToInstr->begin(); it != cfg->ripToInstr->end(); it++) {
		if (it.value()) {
			forwardReachable[it.value()].insert(it.value());
			backwardReachable[it.value()].insert(it.value());
		}
	}

	bool progress;
	do {
		progress = false;
		for (auto it = cfg->ripToInstr->begin(); it != cfg->ripToInstr->end(); it++) {
			instrT *i = it.value();
			if (!i)
				continue;
			instrT *successors[2];
			int nr_successors;
			nr_successors = 0;
			if (i->defaultNextI)
				successors[nr_successors++] = i->defaultNextI;
			if (i->branchNextI)
				successors[nr_successors++] = i->branchNextI;
			if (nr_successors == 0)
				continue;

			/* Forward reachability: look at our
			   successors, and make sure that anything
			   which they can reach is reachable from us
			   as well. */
			std::set<instrT *> &f(forwardReachable[i]);
			for (int j = 0; j < nr_successors; j++) {
				instrT *successor = successors[j];
				std::set<instrT *> &f2(forwardReachable[successor]);
				for (auto it2 = f2.begin(); it2 != f2.end(); it2++) {
					if (!f.count(*it2)) {
						progress = true;
						f.insert(*it2);
					}
				}
			}
		}
	} while (progress);
	do {
		progress = false;
		for (auto it = cfg->ripToInstr->begin(); it != cfg->ripToInstr->end(); it++) {
			instrT *i = it.value();
			if (!i)
				continue;

			instrT *successors[2];
			int nr_successors;
			nr_successors = 0;
			if (i->defaultNextI)
				successors[nr_successors++] = i->defaultNextI;
			if (i->branchNextI)
				successors[nr_successors++] = i->branchNextI;
			if (nr_successors == 0)
				continue;

			/* Backward reachability: anything which can
			   reach us can also reach our successors. */
			std::set<instrT *> &b(backwardReachable[i]);
			for (int j = 0; j < nr_successors; j++) {
				instrT *successor = successors[j];
				std::set<instrT *> &b2(backwardReachable[successor]);
				for (auto it2 = b.begin(); it2 != b.end(); it2++) {
					if (!b2.count(*it2)) {
						progress = true;
						b2.insert(*it2);
					}
				}
			}
			
		}
	} while (progress);

	/* Figure out which instructions should be present. */
	std::set<instrT *> instructionPresence;
	for (auto it = cfg->ripToInstr->begin(); it != cfg->ripToInstr->end(); it++) {
		instrT *i = it.value();
		if (!i)
			continue;

		unsigned thread = it.key().thread;

		/* Should @i be present in thread @thread? */
		bool should_be_present = false;
		/* Must be able to send or receive some message */
		for (auto it3 = happensBeforePoints.begin();
		     !should_be_present && it3 != happensBeforePoints.end();
		     it3++) {
			for (auto it4 = it3->second.begin();
			     it4 != it3->second.end();
			     it4++) {
				happensBeforeEdge *hbe = *it4;
				if (hbe->before.thread == thread) {
					/* Can we send this message? */
					instrT *sender = cfg->ripToInstr->get(hbe->before);
					if (forwardReachable[i].count(sender))
						should_be_present = true;
				} else if (hbe->after.thread == thread) {
					/* Can we receive this message? */
					instrT *receiver = cfg->ripToInstr->get(hbe->after);
					if (forwardReachable[i].count(receiver))
						should_be_present = true;
				}
			}
		}

		/* Not only must some send or receive be
		   forward-reachable, every receive must be
		   either forward or backwards reachable. */
		for (auto it3 = happensBeforePoints.begin();
		     should_be_present && it3 != happensBeforePoints.end();
		     it3++) {
			for (auto it4 = it3->second.begin();
			     it4 != it3->second.end();
			     it4++) {
				happensBeforeEdge *hbe = *it4;
				if (hbe->after.thread == thread) {
					instrT *receiver = cfg->ripToInstr->get(hbe->after);
					if (!forwardReachable[i].count(receiver) &&
					    !backwardReachable[i].count(receiver)) {
						/* No path between this instruction and this
						   receive point -> not in patch */
						should_be_present = false;
					}
				}
			}
		}

		if (should_be_present)
			instructionPresence.insert(i);
	}

	/* Now figure out the transitions.  We're looking for any
	   instructions which are present but which have a successor
	   which is not present.  That successor will then be marked
	   as an exit instruction for the relevant thread. */
	for (auto it = instructionPresence.begin(); it != instructionPresence.end(); it++) {
		instrT *i = *it;

		if (i->defaultNextI && !instructionPresence.count(i->defaultNextI))
			(*this)[i->defaultNextI->rip.rip].insert(i->rip.thread);
		if (i->branchNextI && !instructionPresence.count(i->branchNextI))
			(*this)[i->branchNextI->rip.rip].insert(i->rip.thread);
	}

}

class crashEnforcementData {
public:
	crashEnforcementRoots roots;
	expressionStashMapT exprStashPoints;
	happensBeforeMapT happensBeforePoints;
	slotMapT exprsToSlots;
	expressionEvalMapT expressionEvalPoints;
	abstractThreadExitPointsT threadExitPoints;

	crashEnforcementData(std::set<IRExpr *> &neededExpressions,
			     std::map<unsigned, ThreadRip> &_roots,
			     expressionDominatorMapT &exprDominatorMap,
			     DNF_Conjunction &conj,
			     EnforceCrashCFG *cfg)
		: roots(_roots),
		  exprStashPoints(neededExpressions, _roots),
		  happensBeforePoints(conj, exprDominatorMap, cfg, exprStashPoints),
		  exprsToSlots(exprStashPoints, happensBeforePoints),
		  expressionEvalPoints(exprDominatorMap),
		  threadExitPoints(cfg, happensBeforePoints)
	{}

	crashEnforcementData() {}

	void operator|=(const crashEnforcementData &ced) {
		roots |= ced.roots;
		exprStashPoints |= ced.exprStashPoints;
		happensBeforePoints |= ced.happensBeforePoints;
		exprsToSlots |= ced.exprsToSlots;
		expressionEvalPoints |= ced.expressionEvalPoints;
		threadExitPoints |= ced.threadExitPoints;
	}
};

static CFG<ClientRip> *
enforceCrash(crashEnforcementData &data, AddressSpace *as)
{
	class __decoder {
	public:
		AddressSpace *as;
		Instruction<DirectRip> *operator()(unsigned long r) {
			return Instruction<DirectRip>::decode(as, r, NULL);
		}
		__decoder(AddressSpace *_as)
			: as(_as)
		{}
	} decoder(as);
	CFG<ClientRip> *res = new CFG<ClientRip>(as);
	std::vector<ClientRip> neededRips;
	setToVector(data.roots, neededRips);
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

		Instruction<ClientRip> *newInstr = new Instruction<ClientRip>(-1);

		res->ripToInstr->set(cr, newInstr);

		newInstr->rip = cr;

		switch (cr.type) {
		case ClientRip::start_of_instruction:
			/* If we're supposed to be dropping out of a thread here then do so. */
			{
				auto it = data.threadExitPoints.find(cr.rip);
				if (it != data.threadExitPoints.end()) {
					auto &threadsToExit(it->second);
					bool doit = false;
					for (auto it2 = threadsToExit.begin(); it2 != threadsToExit.end(); it2++) {
						if (cr.threads.count(*it2)) {
							doit = true;
							cr.eraseThread(*it2);
						}
					}
					if (doit) {
						relocs.push_back(relocEntryT(cr, &newInstr->defaultNextI));
						break;
					}
				}
			}
			/* Stash anything which needs to be stashed. */
			if (data.exprStashPoints.count(cr.rip)) {
				std::set<std::pair<unsigned, IRExpr *> > *neededExprs = &data.exprStashPoints[cr.rip];
				for (std::set<std::pair<unsigned, IRExpr *> >::iterator it = neededExprs->begin();
				     it != neededExprs->end();
				     it++) {
					if (!cr.threadLive(it->first))
						continue;
					IRExpr *e = it->second;
					if (e->tag == Iex_Get) {
						/* Easy case: just store the register in its slot */
						simulationSlotT s = data.exprsToSlots(it->first, e);
						assert(!((IRExprGet *)e)->reg.isTemp());
						newInstr->defaultNextI =
							instrMovRegToSlot(RegisterIdx::fromVexOffset(((IRExprGet *)e)->reg.asReg()), s);
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
			if (data.happensBeforePoints.count(cr.rip)) {
				std::set<happensBeforeEdge *> *hbEdges = &data.happensBeforePoints[cr.rip];
				for (std::set<happensBeforeEdge *>::iterator it = hbEdges->begin();
				     it != hbEdges->end();
				     it++) {
					const happensBeforeEdge *hb = *it;
					if (hb->after.rip == cr.rip &&
					    cr.threadLive(hb->after.thread)) {
						printf("Instantiate %s <-< %s\n",
						       hb->before.name(),
						       hb->after.name());
						newInstr = instrHappensBeforeEdgeAfter(hb, newInstr, data.exprsToSlots, cr, relocs);
					} else {
						printf("Skip %s <-< %s\n",
						       hb->before.name(),
						       hb->after.name());
					}
				}
			} else {
				printf("%lx has no HB edges\n", cr.rip);
			}
			relocs.push_back(relocEntryT(ClientRip(cr, ClientRip::original_instruction),
						     &newInstr->defaultNextI));
			break;
		case ClientRip::original_instruction: {
			Instruction<DirectRip> *underlying = decoder(cr.rip);
			assert(underlying);
			if (underlying->defaultNextI || underlying->defaultNext.rip) {
				ClientRip c(cr, ClientRip::post_instr_generate);
				relocs.push_back(relocEntryT(c, &newInstr->defaultNextI));
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
			if (data.exprStashPoints.count(cr.rip)) {
				std::set<std::pair<unsigned, IRExpr *> > *neededExprs = &data.exprStashPoints[cr.rip];
				Instruction<DirectRip> *underlying = decoder(cr.rip);
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
						simulationSlotT s = data.exprsToSlots(it->first, e);
						newInstr->defaultNextI = instrMovRegToSlot(RegisterIdx::RAX, s);
						newInstr = newInstr->defaultNextI;
					} else {
						assert(e->tag == Iex_Load);
						switch (instrOpcode(underlying)) {
						case 0x3B: { /* 32 bit compare rm32, r32.  Handle this by converting
								it into:

								-- load rm32 to the slot
								-- compare register to r32
							     */
							simulationSlotT slot = data.exprsToSlots(it->first, e);
							simulationSlotT spill = data.exprsToSlots.allocateSlot();
							newInstr = instrMovModrmToSlot(newInstr, instrModrm(underlying), slot, spill);
							newInstr = newInstr->defaultNextI = instrCmpRegToSlot(instrModrmReg(underlying), slot);
							break;
						}
							
						case 0x8b:
							/* Load from memory to modrm.
							 * Nice and easy. */
						case 0x0FB6:
							/* Load with
							   zero-extend.
							   Equivalent,
							   for our
							   purposes. */
						{
							simulationSlotT s = data.exprsToSlots(it->first, e);
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
			if (data.expressionEvalPoints.count(cr.rip)) {
				std::set<exprEvalPoint> &expressionsToEval(data.expressionEvalPoints[cr.rip]);
				Instruction<DirectRip> *underlying = decoder(cr.rip);
				DirectRip _fallThrough = underlying->defaultNextI ? underlying->defaultNextI->rip : underlying->defaultNext;
				ClientRip fallThrough(cr, _fallThrough.rip, ClientRip::start_of_instruction);
				
				bool doit = false;
				for (std::set<exprEvalPoint>::iterator it = expressionsToEval.begin();
				     !doit && it != expressionsToEval.end();
				     it++)
					if (cr.threadLive(it->thread))
						doit = true;
				if (doit) {
					newInstr = instrSaveRflags(newInstr, data.exprsToSlots);
					for (std::set<exprEvalPoint>::iterator it = expressionsToEval.begin();
					     it != expressionsToEval.end();
					     it++)
						newInstr = instrCheckExpressionOrEscape(newInstr, *it, fallThrough, data.exprsToSlots);
					newInstr = instrRestoreRflags(newInstr, data.exprsToSlots);
				}
			}
			relocs.push_back(relocEntryT(ClientRip(cr, ClientRip::generate_messages),
						     &newInstr->defaultNextI));
			break;
		case ClientRip::generate_messages:
			if (data.happensBeforePoints.count(cr.rip)) {
				std::set<happensBeforeEdge *> *hbEdges = &data.happensBeforePoints[cr.rip];
				for (std::set<happensBeforeEdge *>::iterator it = hbEdges->begin();
				     it != hbEdges->end();
				     it++) {
					happensBeforeEdge *hb = *it;
					if (hb->before.rip == cr.rip &&
					    cr.threadLive(hb->before.thread))
						newInstr = instrHappensBeforeEdgeBefore(newInstr, hb, data.exprsToSlots);
				}
			}

			/* Where do we go next? */
			{
				Instruction<DirectRip> *underlying = decoder(cr.rip);
				if (underlying->defaultNext.rip) {
					ClientRip c(cr, underlying->defaultNext.rip, ClientRip::start_of_instruction);
					relocs.push_back(relocEntryT(c, &newInstr->defaultNextI));
				} else if (underlying->defaultNextI) {
					ClientRip c(cr, underlying->defaultNextI->rip.rip, ClientRip::start_of_instruction);
					relocs.push_back(relocEntryT(c, &newInstr->defaultNextI));
				}
			}
			break;

		case ClientRip::restore_flags_and_branch:
			newInstr = instrRestoreRflags(newInstr, data.exprsToSlots);

			cr.type = ClientRip::post_instr_checks;
			relocs.push_back(relocEntryT(cr, &newInstr->defaultNextI));
			break;

		case ClientRip::uninitialised: /* Shouldn't happen. */
			abort();
		}
	}

	return res;
}

static bool
buildCED(DNF_Conjunction &c, FreeVariableMap &fv,
	 std::map<unsigned, ThreadRip> &roots,
	 AddressSpace *as, crashEnforcementData *out)
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
			neededRips.insert(roots[((IRExprGet *)e)->reg.tid()]);
		} else if (e->tag == Iex_ClientCall) {
			neededRips.insert(((IRExprClientCall *)e)->callSite);
		} else if (e->tag == Iex_Load) {
			neededRips.insert(((IRExprLoad *)e)->rip);
		} else if (e->tag == Iex_HappensBefore) {
			neededRips.insert(((IRExprHappensBefore *)e)->before);
			neededRips.insert(((IRExprHappensBefore *)e)->after);
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
		printf("Root %s\n", it->second.name());
		cfg->add_root(it->second, 100);
	}
	cfg->doit();
	
	/* Figure out where the various expressions should be
	 * evaluated. */
	expressionDominatorMapT exprDominatorMap;
	if (!exprDominatorMap.init(c, cfg, neededRips))
		return false;

	*out = crashEnforcementData(neededExpressions, roots, exprDominatorMap, c, cfg);
	return true;
}

static bool
analyseHbGraph(DNF_Conjunction &c, CrashSummary *summary)
{
	std::set<IRExprHappensBefore *, HBOrdering> hb;
	std::set<IRExprHappensBefore *, HBOrdering> assumption;

	extractImplicitOrder(summary->loadMachine, assumption);
	for (unsigned x = 0; x < summary->storeMachines.size(); x++)
		extractImplicitOrder(summary->storeMachines[x]->machine, assumption);
	for (unsigned x = 0; x < c.size(); x++) {
		if (c[x].second->tag == Iex_HappensBefore) {
			IRExprHappensBefore *g = (IRExprHappensBefore *)c[x].second;
			IRExprHappensBefore *h;
			if (c[x].first) {
				h = (IRExprHappensBefore *)IRExpr_HappensBefore(g->after, g->before);
			} else {
				h = g;
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
	for (auto it = hb.begin();
	     it != hb.end();
	     it++)
		out.push_back(NF_Atom(false, *it));

	c = out;

	return true;
}

static crashEnforcementData
enforceCrashForMachine(VexPtr<CrashSummary, &ir_heap> summary,
		       VexPtr<Oracle> &oracle,
		       GarbageCollectionToken token)
{
	printf("Machines to enforce:\n");
	printCrashSummary(summary, stdout);

	IRExpr *requirement =
		findHappensBeforeRelations(summary, oracle,
					   AllowableOptimisations::defaultOptimisations,
					   token);
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
	requirement = simplifyIRExpr(requirement, AllowableOptimisations::defaultOptimisations);
	fprintf(_logfile, "After free variable removal:\n");
	ppIRExpr(requirement, _logfile);
	fprintf(_logfile, "\n");

	if (TIMEOUT) {
		fprintf(_logfile, "Killed by a timeout during simplification\n");
		exit(1);
	}
	DNF_Disjunction d;
	auto dnfres(dnf(requirement, d));
	if (!dnfres.valid) {
		fprintf(_logfile, "failed to convert to DNF\n");
		exit(1);
	}
	if (!dnfres.content) {
		/* Okay, so once we've converted to DNF we find that
		   the expression is always true and that the program
		   will always crash.  That seems kind of unlikely,
		   but it's fortunately easy to handle: just don't add
		   any more enforcement infrastructure. */
		fprintf(_logfile, "program is doomed to die?\n");
		return crashEnforcementData();
	}

	for (unsigned x = 0; x < d.size(); ) {
		if (analyseHbGraph(d[x], summary)) {
			x++;
		} else {
			d.erase(d.begin() + x);
		}
	}

	printDnf(d, _logfile);
       
	if (d.size() == 0)
		return crashEnforcementData();

	crashEnforcementData accumulator;
	for (unsigned x = 0; x < d.size(); x++) {
		crashEnforcementData tmp;
		if (buildCED(d[x], m, roots, oracle->ms->addressSpace, &tmp))
			accumulator |= tmp;
	}
	return accumulator;
}

static void
my_system(const char *arg1, ...)
{
	pid_t pid = fork();
	if (pid == -1)
		err(1, "fork(%s)", arg1);
	if (pid == 0) {
		va_list va;
		unsigned nr_args;

		va_start(va, arg1);
		for (nr_args = 1; va_arg(va, const char *); nr_args++)
			;
		va_end(va);

		const char **args = (const char **)calloc(sizeof(args[0]), nr_args + 1);
		args[0] = arg1;
		va_start(va, arg1);
		for (nr_args = 1; ; nr_args++) {
			args[nr_args] = va_arg(va, const char *);
			if (!args[nr_args])
				break;
		}
		execvp(arg1, (char *const *)args);
		err(1, "execvp(%s)", arg1);
	}

	int status;
	pid_t opid;
	opid = waitpid(pid, &status, 0);
	if (opid < 0) err(1, "waitpid() for %s", arg1);
	assert(opid == pid);
	if (WIFEXITED(status)) {
		if (WEXITSTATUS(status) == 0)
			return;
		errx(1, "%s returned %d", arg1, WEXITSTATUS(status));
	}
	if (WIFSIGNALED(status))
		errx(1, "%s died with signal %d", arg1, WTERMSIG(status));
	errx(1, "unknown wait status %x from %s", status, arg1);
}

class AtExit {
	static std::set<AtExit *> allHandlers;
	static void run_handlers(void) {
		for (auto it = allHandlers.begin(); it != allHandlers.end(); it++)
			(*it)->doit();
	}
protected:
	AtExit() { allHandlers.insert(this); }
	~AtExit() { allHandlers.erase(this); }
	virtual void doit() = 0;
public:
	static void init() {
		atexit(run_handlers);
	}
};
std::set<AtExit *> AtExit::allHandlers;

class DeleteTmpFile : AtExit {
	const char *name;
	void doit() {
		unlink(name);
	}
public:
	DeleteTmpFile(const char *n)
		: name(n)
	{}
};

int
main(int argc, char *argv[])
{
	init_sli();

	AtExit::init();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));
	VexPtr<Thread> thr(ms->findThread(ThreadId(1)));
	VexPtr<Oracle> oracle(new Oracle(ms, thr, argv[2]));
	oracle->loadCallGraph(oracle, argv[3], ALLOW_GC);

	crashEnforcementData accumulator;
	for (int i = 5; i < argc; i++) {
		int fd = open(argv[i], O_RDONLY);
		if (fd < 0)
			err(1, "opening %s", argv[i]);
		VexPtr<CrashSummary, &ir_heap> summary(readCrashSummary(fd));
		close(fd);

		accumulator |= enforceCrashForMachine(summary, oracle, ALLOW_GC);
	}

	/* Now build the patch */
	CFG<ClientRip> *cfg = enforceCrash(accumulator, ms->addressSpace);
	EnforceCrashPatchFragment *pf = new EnforceCrashPatchFragment(accumulator.happensBeforePoints);
	pf->fromCFG(cfg);
	char *patch = pf->asC("ident", accumulator.roots);

	/* Dump it to a file and build it. */
	char *tmpfile = my_asprintf("enforce_crash_XXXXXX");
	int fd = mkstemp(tmpfile);
	if (fd < 0) err(1, "mkstemp(%s)", tmpfile);
	DeleteTmpFile __df(tmpfile);
	FILE *f = fdopen(fd, "w");
	if (!f) err(1, "fdopen(%d) (from %s)", fd, tmpfile);
	if (fputs(patch, f) == EOF)
		err(1, "writing to %s", tmpfile);
	if (fclose(f) == EOF)
		err(1, "closing %s", tmpfile);

	my_system(
		"gcc",
		"-Wall",
		"-fPIC",
		"-shared",
		"-I.",
		vex_asprintf("-Dthe_patch=\"%s\"", tmpfile),
		"../sli/enforce_crash/patch_core.c",
		"-o",
		argv[4],
		NULL);

	return 0;
}
