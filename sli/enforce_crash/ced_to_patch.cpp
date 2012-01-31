#include <sys/wait.h>
#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"
#include "oracle.hpp"
#include "genfix.hpp"
#include "enforce_crash.hpp"

/* If this is 1 then all of the enforcement machinery is turned off,
   which is occasionally useful for testing. */
#define NO_OP_PATCH 0
/* Build a patch which stashes all of the intermediate values, but
   never sends any messages or introduces any delays. */
#define STASH_ONLY_PATCH 0

typedef std::pair<ClientRip, Instruction<ClientRip> **> relocEntryT;

#undef LOUD
#ifdef LOUD
#define dbg printf
#else
#define dbg(...)
#endif

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
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1, false);
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
instrImm32NoModrm(unsigned opcode, int val)
{
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1, false);
	if (opcode >= 0x100) {
		assert((opcode & 0xff00) == 0x0f00);
		work->emit(0x0f);
		work->emit(opcode & 0xff);
	} else {
		work->emit(opcode);
	}
	work->emitDword(val);
	return work;
}

static Instruction<ClientRip> *
instrNoImmediatesModrmOpcode(unsigned opcode, RegisterOrOpcodeExtension reg, const ModRM &rm, RexPrefix rex, bool isCall = false)
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
	Instruction<ClientRip> *work = new Instruction<ClientRip>(opcode_bytes, isCall);
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
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1, false);
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
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1, false);
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
instrPushImm32(int val)
{
	return instrImm32NoModrm(0x68, val);
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
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1, false);
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
instrMovImm32ToModrm64(int val, const ModRM &mrm)
{
	Instruction<ClientRip> *work = instrNoImmediatesModrmOpcode(0xc7, RegisterOrOpcodeExtension::opcode(0),
								    mrm, RexPrefix::wide());
	work->emitDword(val);
	return work;
}

static Instruction<ClientRip> *
instrMovImmediateToReg(unsigned long imm, RegisterIdx reg)
{
	if ((long)imm == (int)imm)
		return instrMovImm32ToModrm64(imm, ModRM::directRegister(reg));
	else
		return instrMovImm64ToReg(imm, reg);
}

static Instruction<ClientRip> *
instrCallModrm(const ModRM &mrm)
{
	return instrNoImmediatesModrmOpcode(0xff, RegisterOrOpcodeExtension::opcode(2), mrm, RexPrefix::none(), true);
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
instrAddImm32ToModrm(int imm32, const ModRM &mrm)
{
	Instruction<ClientRip> *work = instrNoImmediatesModrmOpcode(0x81, RegisterOrOpcodeExtension::opcode(0), mrm, RexPrefix::wide());
	work->emitDword(imm32);
	return work;
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
instrCmpImm32ToModrm(int imm32, const ModRM &mrm)
{
	Instruction<ClientRip> *work = instrNoImmediatesModrmOpcode(0x81, RegisterOrOpcodeExtension::opcode(7), mrm, RexPrefix::wide());
	work->emitDword(imm32);
	return work;
}

/* Don't really want to break the nice macro, but also don't want
   compiler warnings because not all of the generated functions are
   used. */
static Instruction<ClientRip> *instrCmpSlotToReg(simulationSlotT slot, RegisterIdx reg) __attribute__((unused));

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
instrNegModrm(const ModRM &mrm)
{
	return instrNoImmediatesModrmOpcode(0xf7, RegisterOrOpcodeExtension::opcode(3), mrm, RexPrefix::wide());
}

/* Special case: we don't try to do the generic encoding, because this
   is byte-addressed, and our modrm infratstructure can't cope. */
static Instruction<ClientRip> *
instrSetEqAl(void)
{
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1, false);
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
instrJcc(ClientRip target, jcc_code branchType, std::vector<relocEntryT> &relocs)
{
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1, false);
	work->emit(0x0f);
	work->emit(branchType.code);
	work->relocs.push_back(new RipRelativeBranchRelocation<ClientRip>(work->len,
									  4,
									  target));
	work->len += 4;
	relocs.push_back(relocEntryT(target, &work->branchNextI));
	return work;
}

static Instruction<ClientRip> *
instrJmpToHost(unsigned long rip)
{
	Instruction<ClientRip> *work = new Instruction<ClientRip>(-1, false);
	work->emit(0xe9);
	work->emit(0);
	work->emit(0);
	work->emit(0);
	work->emit(0);
	work->lateRelocs.push_back(new LateRelocation(1,
						      4,
						      vex_asprintf("0x%lx", rip),
						      0,
						      true));
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
	cursor = cursor->defaultNextI = instrPushReg(RegisterIdx::RSI);
	cursor = cursor->defaultNextI = instrMovLabelToRegister(name, RegisterIdx::RSI);
	cursor = cursor->defaultNextI = instrCallModrm(ModRM::directRegister(RegisterIdx::RSI));
	cursor = cursor->defaultNextI = instrPopReg(RegisterIdx::RSI);
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

static void
instrHappensBeforeEdgeAfter(std::set<const happensBeforeEdge *> &hb,
			    Instruction<ClientRip> *start,
			    slotMapT &exprsToSlots,
			    ClientRip nextRip,
			    std::vector<relocEntryT> &relocs)
{
	if (hb.size() == 0) {
		relocs.push_back(relocEntryT(ClientRip(nextRip, ClientRip::original_instruction),
					     &start->defaultNextI));
		return;
	}

	Instruction<ClientRip> *cursor;

	cursor = start;
	cursor = cursor->defaultNextI = instrSkipRedZone();
	cursor = cursor->defaultNextI = instrPushf();

	cursor = cursor->defaultNextI = instrPushReg(RegisterIdx::RAX);
	cursor = cursor->defaultNextI = instrPushReg(RegisterIdx::RDI);

	for (auto it = hb.begin(); it != hb.end(); it++)
		cursor = cursor->defaultNextI = instrPushImm32((*it)->msg_id);

	cursor = cursor->defaultNextI = instrMovImmediateToReg(hb.size(), RegisterIdx::RDI);
	cursor = instrCallSequence(cursor, "(unsigned long)happensBeforeEdge__after");

	cursor = cursor->defaultNextI = instrAddImm32ToModrm(hb.size() * 8, ModRM::directRegister(RegisterIdx::RSP));
	cursor = cursor->defaultNextI = instrPopReg(RegisterIdx::RDI);

	for (auto it = hb.begin(); it != hb.end(); it++) {
		ClientRip dest = nextRip;
		dest.exit_threads.clear();
		for (auto it2 = hb.begin(); it2 != hb.end(); it2++) {
			dest.threads.erase((*it2)->after.thread);
			dest.exit_threads.insert((*it2)->after.thread);
		}
		dest.threads.insert((*it)->after.thread);
		dest.exit_threads.erase((*it)->after.thread);
		dest.type = ClientRip::exit_threads_and_rx_message;
		dest.completed_edge = *it;
		dest.clearName();
		dbg("\tSuccess destination: %s\n", dest.name());
		cursor = cursor->defaultNextI = instrCmpImm32ToModrm((*it)->msg_id, ModRM::directRegister(RegisterIdx::RAX));
		cursor = cursor->defaultNextI = instrJcc(dest, jcc_code::zero, relocs);
	}

	ClientRip dest = nextRip;
	dest.exit_threads.clear();
	for (auto it = hb.begin(); it != hb.end(); it++) {
		dest.threads.erase((*it)->after.thread);
		dest.exit_threads.insert((*it)->after.thread);
	}
	dest.type = ClientRip::exit_threads_and_pop_regs_restore_flags_and_branch_orig_instruction;
	relocs.push_back(relocEntryT(dest, &cursor->defaultNextI));
	dest.clearName();
	dbg("\tFailure destination: %s\n", dest.name());
}

static Instruction<ClientRip> *
instrHappensBeforeEdgeBefore(Instruction<ClientRip> *start, const happensBeforeEdge *hb,
			     slotMapT &exprsToSlots)
{
	simulationSlotT rdi = exprsToSlots.allocateSlot();
	start = start->defaultNextI = instrMovRegToSlot(RegisterIdx::RDI, rdi);
	simulationSlotT r13 = exprsToSlots.allocateSlot();
	start = start->defaultNextI = instrMovRegToSlot(RegisterIdx::R13, r13);

	dbg("\tTemporary slot for RDI %d, R13 %d\n", rdi.idx, r13.idx);
	for (unsigned x = 0; x < hb->content.size(); x++) {
		simulationSlotT s = exprsToSlots(hb->before.thread, hb->content[x]);
#ifdef LOUD
		printf("\tStore slot %d (", s.idx);
		ppIRExpr(hb->content[x], stdout);
		printf(") into msg %d slot %d\n", hb->msg_id, x);
#endif
		start = instrStoreSlotToMessage(start, hb->msg_id, x, s, RegisterIdx::RDI, RegisterIdx::R13);
	}
	start = start->defaultNextI = instrMovImm64ToReg(hb->msg_id, RegisterIdx::RDI);
	start = start->defaultNextI = instrSkipRedZone();
	start = instrCallSequence(start, "(unsigned long)happensBeforeEdge__before");
	start = start->defaultNextI = instrRestoreRedZone();
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
			fprintf(stderr, "WARNING: Cannot evaluate unop ");
			ppIRExpr(e, stderr);
			fprintf(stderr, " (%x)\n", ((IRExprUnop *)e)->op);
			break;
		}
		break;

	case Iex_Binop:
		switch (((IRExprBinop *)e)->op) {
		case Iop_CmpEQ64: {
			simulationSlotT old_rax = exprsToSlots.allocateSlot();
			Instruction<ClientRip> *head = new Instruction<ClientRip>(-1, false);
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
			fprintf(stderr, "WARNING: Cannot evaluate binop ");
			ppIRExpr(e, stderr);
			fprintf(stderr, " (%x)\n", ((IRExprBinop *)e)->op);
			break;
		}
		break;
	case Iex_Associative:
		switch (((IRExprAssociative *)e)->op) {
		case Iop_Add64: {
			Instruction<ClientRip> *head = new Instruction<ClientRip>(-1, false);
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
			fprintf(stderr, "WARNING: Cannot evaluate associative ");
			ppIRExpr(e, stderr);
			fprintf(stderr, " (%x)\n", ((IRExprAssociative *)e)->op);
			break;
		}
		break;
	default:
		fprintf(stderr, "WARNING: Cannot evaluate ");
		ppIRExpr(e, stderr);
		fprintf(stderr, " (%x)\n", e->tag);
		break;
	}

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
			     slotMapT &exprsToSlots,
			     std::vector<relocEntryT> &relocs)
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
	failTarget.exit_threads.clear();
	failTarget.exit_threads.insert(e.thread);
	failTarget.type = ClientRip::exit_threads_and_restore_flags_and_branch_post_instr_checks;
	cursor = cursor->defaultNextI = instrJcc(failTarget, branch_type, relocs);
	return cursor;
}

static Instruction<ClientRip> *
exitThreadSequence(Instruction<ClientRip> *cursor, const std::set<int> &threads, const crashEnforcementData &data)
{
	if (threads.empty())
		return cursor;
	std::set<unsigned> msg_ids;
	for (auto it = data.happensBeforePoints.begin(); it != data.happensBeforePoints.end(); it++) {
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			auto hb = *it2;
			if (threads.count(hb->before.thread))
				msg_ids.insert(hb->msg_id);
		}
	}

	cursor = cursor->defaultNextI = instrSkipRedZone();
	cursor = cursor->defaultNextI = instrPushReg(RegisterIdx::RDI);
	for (auto it = msg_ids.begin(); it != msg_ids.end(); it++)
		cursor = cursor->defaultNextI = instrPushImm32(*it);
	cursor = cursor->defaultNextI = instrMovImmediateToReg(msg_ids.size(), RegisterIdx::RDI);
	cursor = instrCallSequence(cursor, "(unsigned long)clearMessage");
	cursor = cursor->defaultNextI = instrAddImm32ToModrm(msg_ids.size() * 8,
							     ModRM::directRegister(RegisterIdx::RSP));
	cursor = cursor->defaultNextI = instrPopReg(RegisterIdx::RDI);
	cursor = cursor->defaultNextI = instrRestoreRedZone();
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

	/* Make sure we have instructions which shadow all of the
	   instructions which are going to get clobbered by our jump
	   instructions. */
	for (auto it = data.roots.begin(); it != data.roots.end(); it++) {
		ClientRip startOfJumpInstruction = *it;
		Instruction<DirectRip> *i = decoder(startOfJumpInstruction.rip);
		assert(i);
		while (1) {
			std::set<unsigned> empty;
			Instruction<ClientRip> *i2 = new Instruction<ClientRip>(i->modrm_start, i->isCall);
			ClientRip cr(i->rip.rip, empty, ClientRip::start_of_instruction);
			i2->rip = cr;

			if (i->branchNext.rip) {
				i2->branchNext = ClientRip(cr, i->branchNext.rip, ClientRip::start_of_instruction);
				relocs.push_back(relocEntryT(i2->branchNext, &i2->branchNextI));
			}
			memcpy(i2->content, i->content, i->len);
			i2->len = i->len;
			i2->pfx = i->pfx;
			i2->nr_prefixes = i->nr_prefixes;
			for (auto it = i->relocs.begin(); it != i->relocs.end(); it++)
				i2->relocs.push_back(convertDirectRelocToClientReloc(*it, empty));

			res->ripToInstr->set(cr, i2);
			res->ripToInstr->set(ClientRip(cr, ClientRip::restore_flags_and_branch_post_instr_checks), i2);

			if (!i->defaultNext.rip)
				break;
			if (i->defaultNext.rip - startOfJumpInstruction.rip >= 5) {
				i2->defaultNextI = instrJmpToHost(i->defaultNext.rip);
				break;
			}
			relocs.push_back(relocEntryT(ClientRip(i->defaultNext.rip,
							       empty,
							       ClientRip::start_of_instruction),
						     &i2->defaultNextI));
			i = decoder(i->defaultNext.rip);
			assert(i);
		}
	}

	/* Those relocs are special because they don't trigger
	   additional decoding; process them now. */
	for (unsigned x = 0; x < relocs.size(); x++) {
		relocEntryT re = relocs[x];
		if (res->ripToInstr->hasKey(re.first)) {
			*re.second = res->ripToInstr->get(re.first);
		}
	}
	relocs.clear();

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

		Instruction<ClientRip> *newInstr = new Instruction<ClientRip>(-1, false);

		res->ripToInstr->set(cr, newInstr);

		newInstr->rip = cr;

		cr.clearName();
		dbg("Considering instruction %s\n", cr.name());
		switch (cr.type) {
		case ClientRip::start_of_instruction: {
			Instruction<DirectRip> *underlying = decoder(cr.rip);
			assert(underlying);
			assert(!underlying->defaultNextI);
			assert(!underlying->branchNextI);
			/* If we're supposed to be dropping out of a thread here then do so. */
			{
				auto it = data.threadExitPoints.find(cr.rip);
				if (it != data.threadExitPoints.end()) {
					auto &threadsToExit(it->second);
					bool doit = false;
					for (auto it2 = threadsToExit.begin(); it2 != threadsToExit.end(); it2++) {
						if (cr.threads.count(*it2)) {
							doit = true;
							dbg("\tExit thread %d\n", *it2);
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
			if (!NO_OP_PATCH && data.exprStashPoints.count(cr.rip)) {
				std::set<std::pair<unsigned, IRExpr *> > *neededExprs = &data.exprStashPoints[cr.rip];
				for (std::set<std::pair<unsigned, IRExpr *> >::iterator it = neededExprs->begin();
				     it != neededExprs->end();
				     it++) {
					if (!cr.threadLive(it->first))
						continue;
#ifdef LOUD
					printf("\tStash %d", it->first);
					ppIRExpr(it->second, stdout);
					printf("\n");
#endif
					IRExpr *e = it->second;
					if (e->tag == Iex_Get) {
						/* Easy case: just store the register in its slot */
						simulationSlotT s = data.exprsToSlots(it->first, e);
						assert(!((IRExprGet *)e)->reg.isTemp());
						newInstr->defaultNextI =
							instrMovRegToSlot(RegisterIdx::fromVexOffset(((IRExprGet *)e)->reg.asReg()), s);
						newInstr = newInstr->defaultNextI;
					} else if (e->tag == Iex_ClientCall) {
						/* Do this after emitting the instruction */
					} else if (e->tag == Iex_Load) {
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
							cr.skip_orig = true;
							break;
						}
						default:
							/* Do these after emitting the instruction. */
							break;
						}
					} else {
						abort();
					}
				}
			}
			relocs.push_back(relocEntryT(ClientRip(cr, ClientRip::receive_messages),
						     &newInstr->defaultNextI));
			break;
		}

		case ClientRip::receive_messages:
			if (!NO_OP_PATCH && !STASH_ONLY_PATCH && data.happensBeforePoints.count(cr.rip)) {
				std::set<happensBeforeEdge *> *hbEdges = &data.happensBeforePoints[cr.rip];
				std::set<const happensBeforeEdge *> relevantEdges;

				for (std::set<happensBeforeEdge *>::iterator it = hbEdges->begin();
				     it != hbEdges->end();
				     it++) {
					const happensBeforeEdge *hb = *it;
					if (hb->after.rip == cr.rip &&
					    cr.threadLive(hb->after.thread)) {
						dbg("\tReceive message: %s\n", hb->name());
						relevantEdges.insert(hb);
					}
				}
				instrHappensBeforeEdgeAfter(relevantEdges, newInstr, data.exprsToSlots, cr, relocs);
			} else {
				relocs.push_back(relocEntryT(ClientRip(cr, ClientRip::original_instruction),
							     &newInstr->defaultNextI));
			}
			newInstr = NULL;
			break;
		case ClientRip::original_instruction: {
			Instruction<DirectRip> *underlying = decoder(cr.rip);
			assert(underlying);
			if (underlying->defaultNext.rip) {
				ClientRip c(cr, ClientRip::post_instr_generate);
				relocs.push_back(relocEntryT(c, &newInstr->defaultNextI));
			}

			/* XXX we pretty much assume that branches
			   can't have post-instruction events
			   (generate value, eval expression, or
			   originate message), because otherwise we
			   won't bother generating them when the
			   branch is taken. */
			if (underlying->branchNext.rip) {
				newInstr->branchNext = ClientRip(cr, underlying->branchNext.rip, ClientRip::start_of_instruction);
				relocs.push_back(relocEntryT(newInstr->branchNext, &newInstr->branchNextI));
			}
			if (!cr.skip_orig) {
				memcpy(newInstr->content, underlying->content, underlying->len);
				newInstr->len = underlying->len;
				newInstr->pfx = underlying->pfx;
				newInstr->nr_prefixes = underlying->nr_prefixes;
				for (auto it = underlying->relocs.begin(); it != underlying->relocs.end(); it++)
					newInstr->relocs.push_back(convertDirectRelocToClientReloc(*it, cr.threads));
			}
			break;
		}
		case ClientRip::post_instr_generate:
			dbg("\tdata.exprStashPoints.count(%lx) = %zd\n",
			    cr.rip, data.exprStashPoints.count(cr.rip));
			if (!NO_OP_PATCH && data.exprStashPoints.count(cr.rip)) {
				std::set<std::pair<unsigned, IRExpr *> > *neededExprs = &data.exprStashPoints[cr.rip];
				Instruction<DirectRip> *underlying = decoder(cr.rip);
				if (neededExprs->empty())
					dbg("\tneededExprs set is empty?\n");
				for (std::set<std::pair<unsigned, IRExpr *> >::iterator it = neededExprs->begin();
				     it != neededExprs->end();
				     it++) {
#ifdef LOUD
					printf("\tLate stash %d:", it->first);
					ppIRExpr(it->second, stdout);
					printf("\n");
#endif
					if (!cr.threadLive(it->first)) {
						dbg("\tSkip because thread not live.\n");
						continue;
					}
					IRExpr *e = it->second;
					if (e->tag == Iex_Get) {
						dbg("\tGets already handled\n");
						/* Already handled */
					} else if (e->tag == Iex_ClientCall) {
						/* The result of the call should now be in %rax */
						dbg("\tClient call\n");
						simulationSlotT s = data.exprsToSlots(it->first, e);
						newInstr->defaultNextI = instrMovRegToSlot(RegisterIdx::RAX, s);
						newInstr = newInstr->defaultNextI;
					} else {
						assert(e->tag == Iex_Load);
						switch (instrOpcode(underlying)) {
						case 0x3b: /* already handled */
							dbg("\tAlready handled\n");
							break;
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
							dbg("\tstash as load\n");
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
			if (!NO_OP_PATCH && !STASH_ONLY_PATCH && data.expressionEvalPoints.count(cr.rip)) {
				std::set<exprEvalPoint> &expressionsToEval(data.expressionEvalPoints[cr.rip]);
				
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
					     it++) {
#ifdef LOUD
						printf("\tCheck ");
						it->prettyPrint(stdout);
						printf("\n");
#endif
						newInstr = instrCheckExpressionOrEscape(newInstr, *it, cr, data.exprsToSlots,
											relocs);
					}
					newInstr = instrRestoreRflags(newInstr, data.exprsToSlots);
				}
			}
			relocs.push_back(relocEntryT(ClientRip(cr, ClientRip::generate_messages),
						     &newInstr->defaultNextI));
			break;
		case ClientRip::generate_messages:
			if (!NO_OP_PATCH && !STASH_ONLY_PATCH && data.happensBeforePoints.count(cr.rip)) {
				std::set<happensBeforeEdge *> *hbEdges = &data.happensBeforePoints[cr.rip];
				for (std::set<happensBeforeEdge *>::iterator it = hbEdges->begin();
				     it != hbEdges->end();
				     it++) {
					happensBeforeEdge *hb = *it;
					if (hb->before.rip == cr.rip &&
					    cr.threadLive(hb->before.thread)) {
						dbg("\tGenerate %s\n", hb->name());
						newInstr = instrHappensBeforeEdgeBefore(newInstr, hb, data.exprsToSlots);
					}
				}
			}

			/* Where do we go next? */
			{
				Instruction<DirectRip> *underlying = decoder(cr.rip);
				if (underlying->defaultNext.rip) {
					ClientRip c(cr, underlying->defaultNext.rip, ClientRip::start_of_instruction);
					relocs.push_back(relocEntryT(c, &newInstr->defaultNextI));
				}
			}
			break;

		case ClientRip::exit_threads_and_restore_flags_and_branch_post_instr_checks: {
			assert(cr.exit_threads_valid());
			newInstr = exitThreadSequence(newInstr, cr.exit_threads, data);
			cr.type = ClientRip::restore_flags_and_branch_post_instr_checks;
			relocs.push_back(relocEntryT(cr, &newInstr->defaultNextI));
			break;
		}

		case ClientRip::restore_flags_and_branch_post_instr_checks:
			newInstr = instrRestoreRflags(newInstr, data.exprsToSlots);
			cr.type = ClientRip::post_instr_checks;
			relocs.push_back(relocEntryT(cr, &newInstr->defaultNextI));
			cr.clearName();
			dbg("\tRestored flags, going to %s\n", cr.name());
			break;

		case ClientRip::exit_threads_and_rx_message: {
			assert(cr.exit_threads_valid());
			newInstr = exitThreadSequence(newInstr, cr.exit_threads, data);
			cr.type = ClientRip::rx_message;
			relocs.push_back(relocEntryT(cr, &newInstr->defaultNextI));
			break;
		}
		case ClientRip::rx_message: {
			auto hb = cr.completed_edge;
			for (unsigned x = 0; x < hb->content.size(); x++) {
				simulationSlotT s = data.exprsToSlots(hb->after.thread, hb->content[x]);
				newInstr = instrLoadMessageToSlot(newInstr, hb->msg_id, x, s, RegisterIdx::RAX);
			}
			cr.type = ClientRip::pop_regs_restore_flags_and_branch_orig_instruction;
			relocs.push_back(relocEntryT(cr, &newInstr->defaultNextI));
			cr.clearName();
			dbg("\tAfter receiving message, go to %s\n", cr.name());
			break;
		}

		case ClientRip::exit_threads_and_pop_regs_restore_flags_and_branch_orig_instruction: {
			assert(cr.exit_threads_valid());
			newInstr = exitThreadSequence(newInstr, cr.exit_threads, data);
			cr.type = ClientRip::pop_regs_restore_flags_and_branch_orig_instruction;
			relocs.push_back(relocEntryT(cr, &newInstr->defaultNextI));
			break;
		}
		case ClientRip::pop_regs_restore_flags_and_branch_orig_instruction:
			newInstr = newInstr->defaultNextI = instrPopReg(RegisterIdx::RAX);
			newInstr = newInstr->defaultNextI = instrPopf();
			newInstr = newInstr->defaultNextI = instrRestoreRedZone();
			cr.type = ClientRip::original_instruction;
			relocs.push_back(relocEntryT(cr, &newInstr->defaultNextI));
			cr.clearName();
			dbg("\tRestore flags etc. then go to %s\n", cr.name());
			break;

		case ClientRip::uninitialised: /* Shouldn't happen. */
			abort();
		}
	}

	return res;
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

static void
loadCrashEnforcementData(crashEnforcementData &ced, int fd)
{
	char *buf = readfile(fd);
	const char *suffix;
	if (!ced.parse(buf, &suffix))
		errx(1, "cannot parse crash enforcement data");
	free(buf);
}

int
main(int argc, char *argv[])
{
	init_sli();

	AtExit::init();

	VexPtr<MachineState> ms(MachineState::readELFExec(argv[1]));

	int fd = open(argv[2], O_RDONLY);
	if (fd < 0)
		err(1, "open(%s)", argv[2]);
	crashEnforcementData ced;
	loadCrashEnforcementData(ced, fd);
	close(fd);

	ced.prettyPrint(stdout);

	/* Now build the patch */
	CFG<ClientRip> *cfg = enforceCrash(ced, ms->addressSpace);
	EnforceCrashPatchFragment *pf = new EnforceCrashPatchFragment(ced.happensBeforePoints, ced.roots);
	pf->fromCFG(cfg);
	char *patch = pf->asC("ident");

	/* Dump it to a file and build it. */
	char *tmpfile = my_asprintf("enforce_crash_XXXXXX");
	fd = mkstemp(tmpfile);
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
		"-g",
		"-I.",
		vex_asprintf("-Dthe_patch=\"%s\"", tmpfile),
		"-Dprogram_to_patch=\"/local/scratch/sos22/mysql-5.5.6-rc/sql/mysqld\"",
		"../sli/enforce_crash/patch_core.c",
		"-o",
		argv[3],
		NULL);

	return 0;
}
