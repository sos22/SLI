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

#ifndef NDEBUG
static bool debug_main_loop = false;
static bool debug_find_successors = false;
static bool debug_receive_messages = false;
static bool debug_send_messages = false;
static bool debug_compile_cfg = false;
#else
#define debug_main_loop false
#define debug_find_successors false
#define debug_receive_messages false
#define debug_send_messages false
#define debug_compile_cfg false
#endif

#undef LOUD
#ifdef LOUD
#define dbg printf
#else
#define dbg(...)
#endif

unsigned long
__trivial_hash_function(const VexRip &vr)
{
	return vr.hash();
}

class C2PRip;

template <typename t> static char *
name_set(const std::set<t> &s)
{
	std::vector<const char *> items;
	items.push_back("{");
	for (auto it = s.begin(); it != s.end(); it++) {
		if (it != s.begin())
			items.push_back(", ");
		items.push_back(it->name());
	}
	items.push_back("}");
	return flattenStringFragments(items);
}
template <typename t> unsigned long
hash_set(const std::set<t> &s)
{
	unsigned long acc = 0;
	for (auto it = s.begin(); it != s.end(); it++)
		acc = acc * 572519 + it->hash() * 5235359;
	return acc;
}
template <typename t> void
operator &=(std::set<t> &a, const std::set<t> &b)
{
	for (auto it = a.begin(); it != a.end(); )
		if (b.count(*it))
			it++;
		else
			a.erase(it++);
}

class CrossLabel : public Named {
	char *mkName() const {
		std::vector<const char *> fragments;
		fragments.push_back(label.name());
		fragments.push_back(":{");
		for (auto it = sent_messages.begin();
		     it != sent_messages.end();
		     it++) {
			if (it != sent_messages.begin())
				fragments.push_back(", ");
			fragments.push_back(vex_asprintf("%d", *it));
		}
		fragments.push_back("}");
		char *vex_res = flattenStringFragments(fragments);
		char *malloc_res = strdup(vex_res);
		_LibVEX_free(&main_heap, vex_res);
		return malloc_res;
	}
public:
	ThreadCfgLabel label;
	std::set<unsigned> sent_messages;
	CrossLabel(const ThreadCfgLabel &_label)
		: label(_label)
	{}
	CrossLabel(const ThreadCfgLabel &_label, const std::set<unsigned> &_sent_messages)
		: label(_label),
		  sent_messages(_sent_messages)
	{}
	unsigned long hash() const {
		unsigned long acc = label.hash() * 17;
		for (auto it = sent_messages.begin(); it != sent_messages.end(); it++)
			acc = acc * 19 + *it;
		return acc;
	}
	bool operator<(const CrossLabel &o) const {
		if (label < o.label)
			return true;
		if (o.label < label)
			return false;
		return sent_messages < o.sent_messages;
	}
	bool operator==(const CrossLabel &o) const {
		return label == o.label && sent_messages == o.sent_messages;
	}
};

/* The patch we generate effectively simulates the instructions in the
 * underlying CFG whilst adding various annotations.  The next
 * annotation to add is indicated by the phase. */
class C2PPhase : public Named {
	C2PPhase()
		: phase(_phase(-1))
	{}
	char *mkName() const;
public:
	enum _phase {
		CheckForThreadStart,
		StartThread,
		ReceiveMessages,
		OrigInstrAndStash,
		CheckSideConditions,
		SendMessages,
		FindSuccessors,
		ReceivedMessage,
		ExitThreads,
	} phase;
	
	static C2PPhase *checkForThreadStart() {
		C2PPhase *work = new C2PPhase();
		work->phase = CheckForThreadStart;
		return work;
	}
	static C2PPhase *receiveMessages() {
		C2PPhase *work = new C2PPhase();
		work->phase = ReceiveMessages;
		return work;
	}
	static C2PPhase *checkSideConditions() {
		C2PPhase *work = new C2PPhase();
		work->phase = CheckSideConditions;
		return work;
	}
	static C2PPhase *checkSideConditions(const std::set<ThreadCfgLabel> &threadsProcessed) {
		C2PPhase *work = new C2PPhase();
		work->phase = CheckSideConditions;
		work->_threads = threadsProcessed;
		return work;
	}
	static C2PPhase *origInstrAndStash() {
		C2PPhase *work = new C2PPhase();
		work->phase = OrigInstrAndStash;
		return work;
	}
	static C2PPhase *sendMessages() {
		C2PPhase *work = new C2PPhase();
		work->phase = SendMessages;
		return work;
	}
	static C2PPhase *findSuccessors() {
		C2PPhase *work = new C2PPhase();
		work->phase = FindSuccessors;
		return work;
	}
	static C2PPhase *startThread(const ThreadCfgLabel &_label) {
		C2PPhase *work = new C2PPhase();
		work->phase = StartThread;
		work->_thread = _label;
		return work;
	}
	static C2PPhase *receivedMessage(const happensBeforeEdge *edge) {
		C2PPhase *work = new C2PPhase();
		work->phase = ReceivedMessage;
		work->_edge = edge;
		return work;
	}
	static C2PPhase *exitThreads(const std::set<CrossLabel> &threadsToExit,
				     C2PPhase *followup,
				     unsigned long escapeRip) {
		C2PPhase *work = new C2PPhase();
		work->phase = ExitThreads;
		work->_threadsToExit = threadsToExit;
		work->_exitTo = followup;
		work->_escapeRip = escapeRip;
		return work;
	}

	~C2PPhase() {
		if (phase == ExitThreads)
			delete _exitTo;
	}

	/* Only for CheckSideConditions state */
	const std::set<ThreadCfgLabel> &threadsProcessed() const {
		assert(phase == CheckSideConditions);
		return _threads;
	}

	/* Only for ExitThreads state */
	const std::set<CrossLabel> &threadsToExit() const {
		assert(phase == ExitThreads);
		return _threadsToExit;
	}
	C2PPhase *exitTo() {
		assert(phase == ExitThreads);
		return _exitTo;
	}
	unsigned long escapeRip() const {
		assert(phase == ExitThreads);
		return _escapeRip;
	}

	/* Only for ReceivedMessage */
	const happensBeforeEdge *msgReceived() const {
		assert(phase == ReceivedMessage);
		return _edge;
	}

	/* Only for StartThread state */
	const ThreadCfgLabel &threadToStart() const {
		assert(phase == StartThread);
		return _thread;
	}

	ThreadCfgLabel _thread;
	std::set<ThreadCfgLabel> _threads;
	std::set<CrossLabel> _threadsToExit;
	const happensBeforeEdge *_edge;
	C2PPhase *_exitTo;
	unsigned long _escapeRip;

	C2PPhase(const C2PPhase &o);
	void operator=(const C2PPhase &o);
	bool operator==(const C2PPhase &o) const;
	bool operator!=(const C2PPhase &o) const { return !(*this == o); }
	unsigned long hash() const;
};

/* A C2PRip is effectively a pointer into the patch generated by
 * ced_to_patch.  It's used both for scheduling which bits to generate
 * next and for resolving relocations inside the patch.
 */
class C2PRip : public Named {
	char *mkName() const {
		return my_asprintf("C2PRip{%s}(%s)",
				   phase ? phase->name() : "<nil>",
				   name_set(crossMachineState));
	}
public:
	/* The state of the cross-product machine which we're
	   simulating.  The inner set is the set of messages which
	   we've sent so far. */
	std::set<CrossLabel> crossMachineState;
	/* What phase of the instruction are we at? */
	C2PPhase *phase;
	C2PRip(const std::set<CrossLabel> &_crossMachineState,
	       C2PPhase *_phase)
		: crossMachineState(_crossMachineState), phase(_phase)
	{}
	C2PRip(const C2PRip &o)
		: crossMachineState(o.crossMachineState),
		  phase(o.phase ? new C2PPhase(*o.phase) : NULL)
	{
	}
	C2PRip()
		: phase(NULL)
	{}
	~C2PRip() {
		if (phase)
			delete phase;
	}
	void operator=(const C2PRip &o) {
		if (phase)
			delete phase;
		crossMachineState = o.crossMachineState;
		if (o.phase)
			phase = new C2PPhase(*o.phase);
		else
			phase = NULL;
	}
	bool isNil() const {
		return crossMachineState.empty() && phase == NULL;
	}

	bool operator==(const C2PRip &o) const {
		if (crossMachineState != o.crossMachineState)
			return false;
		if (!phase && !o.phase)
			return true;
		if (!phase || !o.phase)
			return false;
		return *phase == *o.phase;
	}
	unsigned long hash() const {
		unsigned long acc = hash_set(crossMachineState);
		if (phase)
			acc += phase->hash();
		return acc;
	}
	bool operator!=(const C2PRip &o) const {
		return !(*this == o);
	}
	VexRip vexrip(crashEnforcementData &) const;

	unsigned long unwrap_vexrip() const; /* Never called, never
						even referenced by
						linker, but necessary
						to shut the compiler
						up. */
};

unsigned long
__trivial_hash_function(const C2PRip &r)
{
	return r.hash();
}

C2PPhase::C2PPhase(const C2PPhase &o)
	: phase(o.phase),
	  _thread(o._thread),
	  _threads(o._threads),
	  _threadsToExit(o._threadsToExit),
	  _edge(o._edge),
	  _escapeRip(o._escapeRip)
{
	if (phase == ExitThreads)
		_exitTo = new C2PPhase(*o._exitTo);
}

bool
C2PPhase::operator==(const C2PPhase &o) const
{
	if (phase != o.phase)
		return false;
	switch (phase) {
	case CheckForThreadStart:
		return true;
	case StartThread:
		return _thread == o._thread;
	case ReceiveMessages:
		return true;
	case CheckSideConditions:
		return _threads == o._threads;
	case OrigInstrAndStash:
		return true;
	case SendMessages:
		return true;
	case FindSuccessors:
		return true;
	case ReceivedMessage:
		return _edge == o._edge;
	case ExitThreads:
		return _threadsToExit == o._threadsToExit && _escapeRip == o._escapeRip && *_exitTo == *o._exitTo;
	}
	abort();
}
unsigned long
C2PPhase::hash() const
{
	unsigned long acc;
	acc = (int)phase * 674273;
	switch (phase) {
	case CheckForThreadStart:
		return acc;
	case StartThread:
		return acc * 696691 + _thread.hash() * 700573;
	case ReceiveMessages:
		return acc;
	case CheckSideConditions:
		for (auto it = _threads.begin(); it != _threads.end(); it++)
			acc = acc * 679033 + it->hash() * 681673;
		return acc;
	case OrigInstrAndStash:
		return acc;
	case SendMessages:
		return acc;
	case FindSuccessors:
		return acc;
	case ReceivedMessage:
		return acc * 685459 + (unsigned long)_edge * 694829;
	case ExitThreads:
		acc = hash_set(_threadsToExit) + _exitTo->hash();
		acc = acc * 12841 + _escapeRip * 14831;
		return acc;
	}
	abort();
}
char *
C2PPhase::mkName() const
{
	switch (phase) {
	case CheckForThreadStart:
		return strdup("CheckForThreadStart");
	case StartThread:
		return my_asprintf("StartThread(%s)",
				   _thread.name());
	case ReceiveMessages:
		return my_asprintf("ReceiveMessages");
	case CheckSideConditions:
		return my_asprintf("CheckSideConditions(%s)",
				   name_set(_threads));
	case ExitThreads:
		return my_asprintf("ExitThreads(%s, 0x%lx, %s)",
				   name_set(_threadsToExit), _escapeRip, _exitTo->name());
	case OrigInstrAndStash:
		return strdup("OrigInstrAndStash");
	case SendMessages:
		return strdup("SendMessages");
	case FindSuccessors:
		return strdup("FindSuccessors");
	case ReceivedMessage:
		return my_asprintf("ReceivedMessage(%d)", _edge->msg_id);
	}
	abort();
}

struct reloc {
	C2PRip target;
	Instruction<C2PRip> **ptr;
	reloc(const C2PRip &_target, Instruction<C2PRip> **_ptr)
		: target(_target), ptr(_ptr)
	{}
};

static void
loadCrashEnforcementData(crashEnforcementData &ced, AddressSpace *as, int fd)
{
	char *buf = readfile(fd);
	const char *suffix;
	if (!ced.parse(as, buf, &suffix))
		errx(1, "cannot parse crash enforcement data");
	free(buf);
}

static Instruction<C2PRip> *
instrNoImmediatesNoModrm(CfgLabelAllocator &allocLabel, unsigned opcode)
{
	Instruction<C2PRip> *work = new Instruction<C2PRip>(-1, allocLabel());
	if (opcode >= 0x100) {
		assert((opcode & 0xff00) == 0x0f00);
		work->emit(0x0f);
		work->emit(opcode & 0xff);
	} else {
		work->emit(opcode);
	}
	return work;
}

static Instruction<C2PRip> *
instrImm32NoModrm(CfgLabelAllocator &allocLabel, unsigned opcode, int val)
{
	Instruction<C2PRip> *work = instrNoImmediatesNoModrm(allocLabel, opcode);
	work->emitDword(val);
	return work;
}

static Instruction<C2PRip> *
instrNoImmediatesModrmOpcode(CfgLabelAllocator &allocLabel,
			     unsigned opcode,
			     RegisterOrOpcodeExtension reg,
			     const ModRM &rm,
			     Prefixes rex)
{
	assert(!rex.rex_b);
	if (reg.isOpcodeExtension && reg.opcodeExtension >= 8) {
		rex.rex_r = true;
		reg.opcodeExtension -= 8;
	} else if (!reg.isOpcodeExtension && reg.idx.idx >= 8) {
		rex.rex_r = true;
		reg.idx.idx -= 8;
	}
	if (rm.extendRm)
		rex.rex_r = true;
	int opcode_bytes = 1;
	if (rex.anything_set())
		opcode_bytes++;
	if (opcode >= 0x100)
		opcode_bytes++;
	Instruction<C2PRip> *work = new Instruction<C2PRip>(opcode_bytes, allocLabel());
	if (rex.anything_set())
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

static Instruction<C2PRip> *
instrMovRegisterToModrm(CfgLabelAllocator &allocLabel, RegisterIdx reg, const ModRM &rm)
{
	return instrNoImmediatesModrmOpcode(allocLabel, 0x89, reg, rm, Prefixes::rex_wide());
}

static void
addGsPrefix(Instruction<C2PRip> *work)
{
	assert(work->len < sizeof(work->content));
	memmove(work->content + 1, work->content, work->len);
	work->len++;
	work->content[0] = 0x65;
	work->nr_prefixes++;
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
static Instruction<C2PRip> *
instrPushReg64(CfgLabelAllocator &allocLabel, RegisterIdx reg)
{
	Instruction<C2PRip> *work = new Instruction<C2PRip>(-1, allocLabel());
	if (reg.idx >= 8) {
		work->emit(0x41);
		reg.idx -= 8;
	}
	work->emit(0x50 + reg.idx);
	return work;
}
static Instruction<C2PRip> *
instrPopReg64(CfgLabelAllocator &allocLabel, RegisterIdx reg)
{
	Instruction<C2PRip> *work = new Instruction<C2PRip>(-1, allocLabel());
	if (reg.idx >= 8) {
		work->emit(0x41);
		reg.idx -= 8;
	}
	work->emit(0x58 + reg.idx);
	return work;
}
static Instruction<C2PRip> *
instrPushf(CfgLabelAllocator &allocLabel)
{
	return instrNoImmediatesNoModrm(allocLabel, 0x9C);
}
static Instruction<C2PRip> *
instrPopf(CfgLabelAllocator &allocLabel)
{
	return instrNoImmediatesNoModrm(allocLabel, 0x9D);
}
static Instruction<C2PRip> *
instrPushImm32(CfgLabelAllocator &allocLabel, int val)
{
	return instrImm32NoModrm(allocLabel, 0x68, val);
}

static Instruction<C2PRip> *
instrMovModrmToRegister(CfgLabelAllocator &allocLabel, const ModRM &rm, RegisterIdx reg)
{
	return instrNoImmediatesModrmOpcode(allocLabel, 0x8B, reg, rm, Prefixes::rex_wide());
}

static Instruction<C2PRip> *
instrLea(CfgLabelAllocator &allocLabel, const ModRM &modrm, RegisterIdx reg)
{
	return instrNoImmediatesModrmOpcode(allocLabel, 0x8d, reg, modrm, Prefixes::rex_wide());
}

static Instruction<C2PRip> *
instrMovImm64ToReg(CfgLabelAllocator &allocLabel, unsigned long val, RegisterIdx reg)
{
	Instruction<C2PRip> *work = new Instruction<C2PRip>(-1, allocLabel());
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

static Instruction<C2PRip> *
instrMovImm32ToModrm64(CfgLabelAllocator &allocLabel, int val, const ModRM &mrm)
{
	Instruction<C2PRip> *work =
		instrNoImmediatesModrmOpcode(
			allocLabel,
			0xc7,
			RegisterOrOpcodeExtension::opcode(0),
			mrm,
			Prefixes::rex_wide());
	work->emitDword(val);
	return work;
}

static Instruction<C2PRip> *
instrMovImmediateToReg(CfgLabelAllocator &allocLabel, unsigned long imm, RegisterIdx reg)
{
	if ((long)imm == (int)imm)
		return instrMovImm32ToModrm64(allocLabel, imm, ModRM::directRegister(reg));
	else
		return instrMovImm64ToReg(allocLabel, imm, reg);
}

static Instruction<C2PRip> *
instrCallModrm(CfgLabelAllocator &allocLabel, const ModRM &mrm)
{
	return instrNoImmediatesModrmOpcode(allocLabel, 0xff, RegisterOrOpcodeExtension::opcode(2), mrm, Prefixes());
}

static Instruction<C2PRip> *
instrAddImm32ToModrm(CfgLabelAllocator &allocLabel, int imm32, const ModRM &mrm)
{
	Instruction<C2PRip> *work = instrNoImmediatesModrmOpcode(
		allocLabel,
		0x81,
		RegisterOrOpcodeExtension::opcode(0),
		mrm,
		Prefixes::rex_wide());
	work->emitDword(imm32);
	return work;
}

static Instruction<C2PRip> *
instrCmpImm32ToModrm(CfgLabelAllocator &allocLabel, int imm32, const ModRM &mrm)
{
	Instruction<C2PRip> *work =
		instrNoImmediatesModrmOpcode(
			allocLabel,
			0x81,
			RegisterOrOpcodeExtension::opcode(7),
			mrm,
			Prefixes::rex_wide());
	work->emitDword(imm32);
	return work;
}

static Instruction<C2PRip> *
instrSkipRedZone(CfgLabelAllocator &allocLabel)
{
	return instrLea(allocLabel,
			ModRM::memAtRegisterPlusOffset(RegisterIdx::RSP, -128),
			RegisterIdx::RSP);
}
static Instruction<C2PRip> *
instrRestoreRedZone(CfgLabelAllocator &allocLabel)
{
	return instrLea(allocLabel,
			ModRM::memAtRegisterPlusOffset(RegisterIdx::RSP, 128),
			RegisterIdx::RSP);
}

static Instruction<C2PRip> *
instrMovRegToSlot(CfgLabelAllocator &allocLabel, RegisterIdx offset, simulationSlotT slot)
{
	Instruction<C2PRip> *work = instrMovRegisterToModrm(allocLabel, offset, modrmForSlot(slot));
	addGsPrefix(work);
	return work;
}

static Instruction<C2PRip> *
instrMovSlotToReg(CfgLabelAllocator &allocLabel, simulationSlotT slot, RegisterIdx offset)
{
	Instruction<C2PRip> *work = instrMovModrmToRegister(allocLabel, modrmForSlot(slot), offset);
	addGsPrefix(work);
	return work;
}

static Instruction<C2PRip> *
instrMovLabelToRegister(CfgLabelAllocator &allocLabel, const char *label, RegisterIdx reg)
{
	Instruction<C2PRip> *work = instrMovImm64ToReg(allocLabel, 0, reg);
	work->lateRelocs.push_back(new LateRelocation(work->len - 8,
						      8,
						      label,
						      0,
						      false));
	return work;
}

static Instruction<C2PRip> *
instrJcc(CfgLabelAllocator &allocLabel, const C2PRip &target, jcc_code branchType, std::queue<reloc> &relocs)
{
	Instruction<C2PRip> *work = new Instruction<C2PRip>(-1, allocLabel());
	work->emit(0x0f);
	work->emit(branchType.code);
	work->relocs.push_back(new RipRelativeBranchRelocation<C2PRip>(work->len,
								       4,
								       target));
	work->len += 4;
	work->successors.push_back(
		Instruction<C2PRip>::successor_t::branch(target));
	relocs.push(reloc(target, &work->successors[0].instr));
	return work;
}

static Instruction<C2PRip> *
convertSimpleInstr(CfgLabelAllocator &allocLabel, CFGNode *simple)
{
	assert(simple->lateRelocs.size() == 0);
	Instruction<C2PRip> *work = new Instruction<C2PRip>(simple->modrm_start, allocLabel());
	work->len = simple->len;
	memcpy(work->content, simple->content, simple->len);
	for (auto it = simple->relocs.begin(); it != simple->relocs.end(); it++) {
		EarlyRelocation<VexRip> *r = *it;
		if (auto rrr = dynamic_cast<RipRelativeRelocation<VexRip> *>(r)) {
			work->relocs.push_back(
				new RipRelativeDataRelocation<C2PRip>(
					rrr->offset,
					rrr->size,
					rrr->target.unwrap_vexrip(),
					rrr->nrImmediateBytes));
		} else {
			/* Either this is a branch relocation, which
			   we can't really handle from here, or it's a
			   relocation type which we don't know about.
			   Either is very bad. */
			abort();
		}
	}
	return work;
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
instrOpcode(CFGNode *i)
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
instrModrmReg(CFGNode *i)
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

static jcc_code
getJccCode(CFGNode *instr)
{
	switch (instrOpcode(instr)) {
	case 0xf84:
		return jcc_code::zero;
	default:
		abort();
	}
}

/* Dummy no-op instruction */
static Instruction<C2PRip> *
instrNoop(CfgLabelAllocator &allocLabel)
{
	return new Instruction<C2PRip>(-1, allocLabel());
}

/* A simple instruction which just acts as a proxy to a given
 * C2PRip. */
static Instruction<C2PRip> *
noopRelocation(CfgLabelAllocator &allocLabel,
	       const C2PRip &target,
	       std::queue<reloc> &relocs)
{
	Instruction<C2PRip> *work = instrNoop(allocLabel);
	work->addDefault(NULL);
	relocs.push(reloc(target, &work->successors[0].instr));
	return work;
}

VexRip
C2PRip::vexrip(crashEnforcementData &ced) const
{
	assert(crossMachineState.size() != 0);
	auto it = crossMachineState.begin();
	VexRip vr(ced.threadCfg.findInstr(it->label)->rip);
	for (it++; it != crossMachineState.end(); it++)
		assert(vr == ced.threadCfg.findInstr(it->label)->rip);
	return vr;
}

class AncillaryData {
	std::map<VexRip, std::set<ThreadCfgLabel> > threadsEnteringAtRip;
	AddressSpace *as;
public:
	AncillaryData(AddressSpace *as, crashEnforcementData &ced);
	std::set<ThreadCfgLabel> findThreadsEnteringAtRip(const VexRip &vr) {
		auto it = threadsEnteringAtRip.find(vr);
		if (it == threadsEnteringAtRip.end())
			return std::set<ThreadCfgLabel>();
		else
			return it->second;
	}
	CFGNode *decodeUnderlyingInstr(const VexRip &vr) {
		return CFGNode::decode(CfgLabel::uninitialised(),
				       as,
				       vr,
				       NULL);
	}
};

AncillaryData::AncillaryData(AddressSpace *_as, crashEnforcementData &ced)
	: as(_as)
{
	for (auto it = ced.roots.begin(); it != ced.roots.end(); it++)
		threadsEnteringAtRip[ced.threadCfg.findInstr(*it)->rip].insert(*it);
}

static Instruction<C2PRip> *
checkForThreadStart(const C2PRip &c2p_rip,
		    std::queue<reloc> &relocs,
		    crashEnforcementData &ced,
		    AncillaryData &ad,
		    CfgLabelAllocator &allocLabel)
{
	std::set<ThreadCfgLabel> newThreads;
	std::set<ThreadCfgLabel> neededThreads(ad.findThreadsEnteringAtRip(c2p_rip.vexrip(ced)));
	for (auto it2 = neededThreads.begin();
	     it2 != neededThreads.end();
	     it2++) {
		if (!c2p_rip.crossMachineState.count(CrossLabel(*it2)))
			newThreads.insert(*it2);
	}
	C2PPhase *newPhase;
	if (newThreads.empty()) {
		newPhase = C2PPhase::receiveMessages();
	} else {
		/* Just do one at a time, because that's a bit easier. */
		newPhase = C2PPhase::startThread(*newThreads.begin());
	}
	return noopRelocation(allocLabel,
			      C2PRip(c2p_rip.crossMachineState, newPhase),
			      relocs);
}

std::set<std::pair<RegisterIdx, simulationSlotT> >
registersToStash(const ThreadCfgLabel &label,
		 crashEnforcementData &ced)
{
	std::set<std::pair<RegisterIdx, simulationSlotT> > res;
	const std::set<IRExpr *> &exprs(ced.exprStashPoints[label]);
	for (auto it = exprs.begin(); it != exprs.end(); it++) {
		assert((*it)->tag == Iex_Get);
		IRExprGet *ieg = (IRExprGet *)*it;
		if (ieg->reg.isReg())
			res.insert(std::pair<RegisterIdx, simulationSlotT>(
					   RegisterIdx::fromVexOffset(ieg->reg.asReg()),
					   ced.exprsToSlots(label.thread, ieg)));
	}
	return res;
}

static Instruction<C2PRip> *
startThread(const C2PRip &c2p_rip,
	    std::queue<reloc> &relocs,
	    crashEnforcementData &ced,
	    AncillaryData &ad,
	    CfgLabelAllocator &allocLabel)
{
	const ThreadCfgLabel &newThread(c2p_rip.phase->threadToStart());
	std::set<std::pair<RegisterIdx, simulationSlotT> > stashRegisters(registersToStash(newThread, ced));
	std::set<CrossLabel> newCrossMachineState(c2p_rip.crossMachineState);
	bool did_insert =
		newCrossMachineState.insert(CrossLabel(newThread)).second;
	assert(did_insert);

	Instruction<C2PRip> *start = NULL;
	Instruction<C2PRip> *cursor = NULL;
	Instruction<C2PRip> *n = NULL;
	for (auto it = stashRegisters.begin(); it != stashRegisters.end(); it++) {
		n = instrMovRegToSlot(allocLabel,
				      it->first,
				      it->second);
		if (cursor) {
			cursor = cursor->addDefault(n);
		} else {
			start = cursor = n;
		}
	}

	n = noopRelocation(allocLabel,
			   C2PRip(newCrossMachineState,
				  C2PPhase::receiveMessages()),
			   relocs);
	if (cursor)
		cursor->addDefault(n);
	else
		start = n;
	return start;
}

static Instruction<C2PRip> *
receiveMessages(const C2PRip &c2p_rip,
		std::queue<reloc> &relocs,
		crashEnforcementData &ced,
		AncillaryData &ad,
		CfgLabelAllocator &allocLabel)
{
	if (debug_receive_messages)
		printf("%s(%s)\n", __func__, c2p_rip.name());
	/* Figure out which messages we need to receive */
	std::set<const happensBeforeEdge *> messagesToReceive;
	for (auto it = c2p_rip.crossMachineState.begin();
	     it != c2p_rip.crossMachineState.end();
	     it++) {
		ThreadCfgLabel thread(it->label);
		const std::set<happensBeforeEdge *> &edges(ced.happensBeforePoints[thread]);
		for (auto it2 = edges.begin(); it2 != edges.end(); it2++) {
			const happensBeforeEdge *edge = *it2;
			if (edge->after.tid == (int)thread.thread &&
			    edge->after.where == thread.label) {
				if (debug_receive_messages)
					printf("\tReceive %d for %s\n", edge->msg_id, it->name());
				messagesToReceive.insert(edge);
			}
		}
	}

	if (messagesToReceive.empty()) {
		if (debug_receive_messages)
			printf("\tNo messages to receive\n");
		return noopRelocation(allocLabel,
				      C2PRip(c2p_rip.crossMachineState,
					     C2PPhase::origInstrAndStash()),
				      relocs);
	}

	/* Now do a multi-receive on every outstanding message. */
	Instruction<C2PRip> *start;
	Instruction<C2PRip> *cursor;

	start = cursor = instrSkipRedZone(allocLabel);
	cursor = cursor->addDefault(instrPushf(allocLabel));
	cursor = cursor->addDefault(instrPushReg64(allocLabel, RegisterIdx::RAX));
	cursor = cursor->addDefault(instrPushReg64(allocLabel, RegisterIdx::RDI));
	for (auto it = messagesToReceive.begin(); it != messagesToReceive.end(); it++)
		cursor = cursor->addDefault(instrPushImm32(allocLabel, (*it)->msg_id ));
	cursor = cursor->addDefault(instrMovImmediateToReg(allocLabel, messagesToReceive.size(), RegisterIdx::RDI));
	cursor = cursor->addDefault(instrMovLabelToRegister(allocLabel, "(unsigned long)happensBeforeEdge__after", RegisterIdx::RAX));
	cursor = cursor->addDefault(instrCallModrm(allocLabel, ModRM::directRegister(RegisterIdx::RAX)));
	cursor = cursor->addDefault(instrAddImm32ToModrm(allocLabel, messagesToReceive.size() * 8, ModRM::directRegister(RegisterIdx::RSP)));
	cursor = cursor->addDefault(instrPopReg64(allocLabel, RegisterIdx::RDI));
	for (auto it = messagesToReceive.begin(); it != messagesToReceive.end(); it++) {
		cursor = cursor->addDefault(
			instrCmpImm32ToModrm(
				allocLabel,
				(*it)->msg_id,
				ModRM::directRegister(RegisterIdx::RAX)));
		C2PRip rxState(c2p_rip.crossMachineState,
			       C2PPhase::receivedMessage(*it));
		if (debug_receive_messages)
			printf("\tReceive %d, go to %s\n",
			       (*it)->msg_id, rxState.name());
		cursor = cursor->addDefault(
			instrJcc(allocLabel, rxState, jcc_code::zero, relocs));
	}
	/* If none of those branches are taken then the message
	 * receive failed.  Get out. */
	cursor = cursor->addDefault(instrPopReg64(allocLabel, RegisterIdx::RAX));
	cursor = cursor->addDefault(instrPopf(allocLabel));
	cursor = cursor->addDefault(instrRestoreRedZone(allocLabel));
	/* All of the threads which tried to receive have now
	 * failed. */
	std::set<CrossLabel> failedThreads;
	for (auto it = c2p_rip.crossMachineState.begin(); it != c2p_rip.crossMachineState.end(); it++) {
		const ThreadCfgLabel &tl(it->label);
		for (auto it2 = messagesToReceive.begin(); it2 != messagesToReceive.end(); it2++) {
			const happensBeforeEdge *hb = *it2;
			if (hb->after.tid == (int)tl.thread &&
			    hb->after.where == tl.label) {
				failedThreads.insert(*it);
				break;
			}
		}
	}
	C2PRip failState(c2p_rip.crossMachineState,
			 C2PPhase::exitThreads(failedThreads,
					       C2PPhase::origInstrAndStash(),
					       c2p_rip.vexrip(ced).unwrap_vexrip()));
	if (debug_receive_messages)
		printf("\tReceive failed, go to %s\n", failState.name());
	cursor->addDefault(
		noopRelocation(allocLabel, failState, relocs));
	return start;
}

static Instruction<C2PRip> *
origInstrAndStash(const C2PRip &c2p_rip,
		  std::queue<reloc> &relocs,
		  crashEnforcementData &ced,
		  AncillaryData &ad,
		  CfgLabelAllocator &allocLabel)
{
	std::set<simulationSlotT> stashSlots;

	for (auto it = c2p_rip.crossMachineState.begin();
	     it != c2p_rip.crossMachineState.end();
	     it++) {
		auto it2 = ced.exprStashPoints.find(it->label);
		if (it2 != ced.exprStashPoints.end()) {
			for (auto it3 = it2->second.begin(); it3 != it2->second.end(); it3++) {
				IRExpr *e = *it3;
				assert(e->tag == Iex_Get);
				if (!((IRExprGet *)e)->reg.isReg())
					stashSlots.insert(ced.exprsToSlots(it->label.thread, e));
			}
		}
	}

	/* Now we know what we need to store the loaded value to.  Now
	 * examine the actual instruction to figure out how to get it.
	 * All of the underlying instructions should be the same, so
	 * just arbitrarily pick the first one. */
	CFGNode *underlyingInstr = ced.threadCfg.findInstr(c2p_rip.crossMachineState.begin()->label);
	assert(underlyingInstr);
	Instruction<C2PRip> *start;
	Instruction<C2PRip> *cursor;
	switch (instrOpcode(underlyingInstr)) {
	case 0x8b: { /* mov modrm, reg */
		cursor = start = convertSimpleInstr(allocLabel, underlyingInstr);
		for (auto it = stashSlots.begin(); it != stashSlots.end(); it++)
			cursor = cursor->addDefault(instrMovRegToSlot(allocLabel, instrModrmReg(underlyingInstr), *it));
		break;
	}
	case 0x83: /* cmp reg, modrm */
		/* These can generate stashes, but that's not
		 * currently implemented */
		assert(stashSlots.empty());
		cursor = start = convertSimpleInstr(allocLabel, underlyingInstr);
		break;

	case 0x89: /* mov reg, modrm */
	case 0xc7: /* mov imm, modrm */
		/* These shouldn't generate any stashes */
		assert(stashSlots.empty());
		cursor = start = convertSimpleInstr(allocLabel, underlyingInstr);
		break;

	case 0xf84: /* Conditional branches.  These get special
		       handling in findSuccessors() */
		cursor = start = instrNoop(allocLabel);
		break;
	default:
		fail("don't know how to stash for opcode 0x%x\n",
		     instrOpcode(underlyingInstr));
	}

	/* Done; move on to next phase. */
	cursor->addDefault(
		noopRelocation(allocLabel,
			       C2PRip(c2p_rip.crossMachineState,
				      C2PPhase::checkSideConditions()),
			       relocs));
	return start;
}

static Instruction<C2PRip> *
checkSideConditions(const C2PRip &c2p_rip,
		    std::queue<reloc> &relocs,
		    crashEnforcementData &ced,
		    AncillaryData &ad,
		    CfgLabelAllocator &allocLabel)
{
	std::set<ThreadCfgLabel> threadsProcessed(c2p_rip.phase->threadsProcessed());
	std::map<ThreadCfgLabel, std::set<exprEvalPoint> > thingsToEval;

	for (auto it = c2p_rip.crossMachineState.begin();
	     it != c2p_rip.crossMachineState.end();
	     it++) {
		const ThreadCfgLabel &label(it->label);
		if (threadsProcessed.count(label))
			continue;
		const std::set<exprEvalPoint> &thingsToEvalHere(ced.expressionEvalPoints[label]);
		if (!thingsToEvalHere.empty())
			thingsToEval[label] = thingsToEvalHere;
	}

	if (thingsToEval.empty()) {
		/* Nothing to do */
		return noopRelocation(allocLabel,
				      C2PRip(c2p_rip.crossMachineState,
					     C2PPhase::sendMessages()),
				      relocs);
	}

	/* Not implemented yet */
	abort();
}

static Instruction<C2PRip> *
sendMessages(const C2PRip &c2p_rip,
	     std::queue<reloc> &relocs,
	     crashEnforcementData &ced,
	     AncillaryData &ad,
	     CfgLabelAllocator &allocLabel)
{
	if (debug_send_messages)
		printf("%s(%s)\n", __func__, c2p_rip.name());

	/* Figure out which messages we need to send */
	std::set<const happensBeforeEdge *> messagesToSend;
	std::map<ThreadCfgLabel, std::set<unsigned> > messagesSentInEachThread;
	for (auto it = c2p_rip.crossMachineState.begin();
	     it != c2p_rip.crossMachineState.end();
	     it++) {
		ThreadCfgLabel thread(it->label);
		const std::set<happensBeforeEdge *> &edges(ced.happensBeforePoints[thread]);
		for (auto it2 = edges.begin(); it2 != edges.end(); it2++) {
			const happensBeforeEdge *edge = *it2;
			if (edge->before.tid == (int)thread.thread &&
			    edge->before.where == thread.label) {
				messagesToSend.insert(edge);
				messagesSentInEachThread[thread].insert(edge->msg_id);
				if (debug_send_messages)
					printf("\tSend %d in %s\n",
					       edge->msg_id, thread.name());
			}
		}
	}

	if (messagesToSend.empty()) {
		if (debug_send_messages)
			printf("\tNothing to send\n");
		return noopRelocation(allocLabel,
				      C2PRip(c2p_rip.crossMachineState,
					     C2PPhase::findSuccessors()),
				      relocs);
	}

	Instruction<C2PRip> *start;
	Instruction<C2PRip> *cursor;
	start = cursor = instrSkipRedZone(allocLabel);
	cursor = cursor->addDefault(instrPushReg64(allocLabel, RegisterIdx::RDI));
	cursor = cursor->addDefault(instrPushReg64(allocLabel, RegisterIdx::RSI));
	cursor = cursor->addDefault(instrPushReg64(allocLabel, RegisterIdx::RBP));
	cursor = cursor->addDefault(
		instrMovLabelToRegister(
			allocLabel,
			"(unsigned long)happensBeforeEdge__before",
			RegisterIdx::RBP));
	for (auto it = messagesToSend.begin(); it != messagesToSend.end(); it++) {
		const happensBeforeEdge *hb = *it;
		for (unsigned x = 0; x < hb->content.size(); x++) {
			simulationSlotT slot = ced.exprsToSlots(hb->before.tid,
								hb->content[x]);
			cursor = cursor->addDefault(
				instrMovLabelToRegister(
					allocLabel,
					vex_asprintf("(unsigned long)&__msg_%d_slot_%d", hb->msg_id, x),
					RegisterIdx::RSI));
			cursor = cursor->addDefault(instrMovSlotToReg(allocLabel, slot, RegisterIdx::RDI));
			cursor = cursor->addDefault(instrMovRegisterToModrm(
							    allocLabel,
							    RegisterIdx::RDI,
							    ModRM::memAtRegister(RegisterIdx::RSI)));
		}
		cursor = cursor->addDefault(instrMovImmediateToReg(allocLabel, hb->msg_id, RegisterIdx::RDI));
		cursor = cursor->addDefault(instrCallModrm(allocLabel, ModRM::directRegister(RegisterIdx::RBP)));
	}
	cursor = cursor->addDefault(instrPopReg64(allocLabel, RegisterIdx::RBP));
	cursor = cursor->addDefault(instrPopReg64(allocLabel, RegisterIdx::RSI));
	cursor = cursor->addDefault(instrPopReg64(allocLabel, RegisterIdx::RDI));
	cursor = cursor->addDefault(instrRestoreRedZone(allocLabel));

	std::set<CrossLabel> newCrossMachineState;
	for (auto it = c2p_rip.crossMachineState.begin(); it != c2p_rip.crossMachineState.end(); it++) {
		auto it2 = messagesSentInEachThread.find(it->label);
		if (it2 != messagesSentInEachThread.end()) {
			std::set<unsigned> newSentMessages(it->sent_messages);
			for (auto it3 = it2->second.begin();
			     it3 != it2->second.end();
			     it3++)
				newSentMessages.insert(*it3);
			newCrossMachineState.insert(CrossLabel(it->label, newSentMessages));
		} else {
			newCrossMachineState.insert(*it);
		}
	}
	C2PRip next(newCrossMachineState, C2PPhase::findSuccessors());
	if (debug_send_messages)
		printf("\tNext state %s\n", next.name());
	cursor->addDefault(noopRelocation(allocLabel, next, relocs));
	return start;
}

static Instruction<C2PRip> *
findSuccessors(const C2PRip &c2p_rip,
	       std::queue<reloc> &relocs,
	       crashEnforcementData &ced,
	       AncillaryData &ad,
	       CfgLabelAllocator &allocLabel)
{
	/* This is fiddly.  The aim is to match the CFG which we want
	 * to simulate up against the instruction which we're actually
	 * going to run, basically using a whole serious of fiddly
	 * special cases. */
	CFGNode *underlying = ad.decodeUnderlyingInstr(c2p_rip.vexrip(ced));
	assert(underlying);

	if (debug_find_successors) {
		printf("find_successors(%s)\n\tunderlying = ", c2p_rip.name());
		underlying->prettyPrint(stdout);
	}

	if (underlying->successors.size() == 0) {
		/* This is a terminal instruction.  The CFG node
		 * should also be terminal in this case, in which case
		 * things are very easy. */
		/* (This is actually very rare, to the point that it's
		   not clear that it needs to be handled at all, but
		   it's also very easy, so do it anyway.) */
		for (auto it = c2p_rip.crossMachineState.begin();
		     it != c2p_rip.crossMachineState.end();
		     it++)
			assert(ced.threadCfg.findInstr(it->label)->successors.size() == 0);
		C2PRip next(c2p_rip.crossMachineState,
			    C2PPhase::exitThreads(c2p_rip.crossMachineState, NULL, 0xf001));
		if (debug_find_successors)
			printf("\tunderlying instruction has no successors; next state %s\n",
			       next.name());
		return noopRelocation(allocLabel, next, relocs);
	} else if (underlying->successors.size() == 1) {
		/* The underlying instruction is single-exit.  Figure
		   out what happens to the various abstract threads.
		   There are three cases:

		   -- The abstract thread might have a single exit,
		      in which case we just advance the underlying thread
		      to that node.
		   -- The abstract thread might have no exits, in
		      which case we need to exit that thread.
		   -- The abstract thread might have multiple exits,
		      in which case we need to fork it.

		   Useful fact: the CFG node should not have any
		   successors which do not match up with the
		   underlying instruction's successor. */
		VexRip realExit(underlying->successors[0].rip);

		if (debug_find_successors)
			printf("\tunderlying instruction has a single successor, %s\n", realExit.name());

#ifndef NDEBUG
		/* First, do a quick check that all of the successors
		   go to something which matches realExit. */
		for (auto it = c2p_rip.crossMachineState.begin();
		     it != c2p_rip.crossMachineState.end();
		     it++) {
			const ThreadCfgLabel &thisLabel(it->label);
			CFGNode *thisNode = ced.threadCfg.findInstr(thisLabel);
			assert(thisNode);
			for (auto it = thisNode->successors.begin();
			     it != thisNode->successors.end();
			     it++) {
				if (it->instr) {
					if (debug_find_successors)
						printf("\tcfg successor: %s, %s\n",
						       it->instr->label.name(),
						       it->instr->rip.name());
					assert(it->instr->rip == realExit);
				}
			}
		}
#endif

		/* Now figure out which threads need to exit. */
		std::set<CrossLabel> threadsToExit;
		for (auto it = c2p_rip.crossMachineState.begin();
		     it != c2p_rip.crossMachineState.end();
		     it++) {
			const ThreadCfgLabel &thisLabel(it->label);
			CFGNode *thisNode = ced.threadCfg.findInstr(thisLabel);
			assert(thisNode);
			bool hasSuccessors = false;
			for (auto it2 = thisNode->successors.begin();
			     !hasSuccessors && it2 != thisNode->successors.end();
			     it2++)
				if (it2->instr)
					hasSuccessors = true;
			if (!hasSuccessors)
				threadsToExit.insert(*it);
		}

		/* If anything needs to exit, go to ExitThreads() and
		   then come back here afterwards. */
		if (!threadsToExit.empty()) {
			C2PRip next(c2p_rip.crossMachineState,
				    C2PPhase::exitThreads(
					    threadsToExit,
					    C2PPhase::findSuccessors(),
					    realExit.unwrap_vexrip()));
			if (debug_find_successors)
				printf("\tNeed to exit threads; going to %s\n",
				       next.name());
			return noopRelocation(allocLabel, next, relocs);
		}

		/* Okay, we don't need to exit any threads.  Advance
		   the ones we have. */
		std::set<CrossLabel> newCrossMachineState;
		for (auto it = c2p_rip.crossMachineState.begin();
		     it != c2p_rip.crossMachineState.end();
		     it++) {
			CFGNode *thisNode = ced.threadCfg.findInstr(it->label);
			assert(thisNode);
			for (auto it2 = thisNode->successors.begin();
			     it2 != thisNode->successors.end();
			     it2++) {
				if (it2->instr) {
					CrossLabel newEntry(
						ThreadCfgLabel(it->label.thread, it2->instr->label),
						it->sent_messages);
					if (debug_find_successors)
						printf("\tAdvance %s to %s\n",
						       it->name(),
						       newEntry.name());
					newCrossMachineState.insert(newEntry);
				}
			}
		}
		C2PRip next(newCrossMachineState, C2PPhase::checkForThreadStart());
		if (debug_find_successors)
			printf("\tNext state %s\n", next.name());
		return noopRelocation(allocLabel, next, relocs);
	} else if (underlying->successors.size() == 2) {
		/* This is a conditional branch instruction.  Unlike
		 * all of the other instruction types, it won't have
		 * been emitted in the origInstrAndStash phase, and we
		 * have to do it here instead. */
		VexRip defaultRip;
		VexRip branchRip;
		for (auto it = underlying->successors.begin();
		     it != underlying->successors.end();
		     it++) {
			if (it->type == CFGNode::successor_t::succ_default)
				defaultRip = it->rip;
			else if (it->type == CFGNode::successor_t::succ_branch)
				branchRip = it->rip;
			else
				abort();
		}
		assert(defaultRip.isValid());
		assert(branchRip.isValid());

		if (debug_find_successors)
			printf("\tUnderlying is a branch; targets %s, %s\n",
			       defaultRip.name(), branchRip.name());

		/* Now we need to match the two instructions up.
		   There are a couple of things we could do next:

		   -- Exit if the branch is taken
		   -- Exit if the branch is not taken
		   -- Continue if the branch is taken
		   -- Continue if the branch is not taken
		*/
		std::set<CrossLabel> branchExitTarget;
		std::set<CrossLabel> defaultExitTarget;
		std::set<CrossLabel> branchTarget;
		std::set<CrossLabel> defaultTarget;
		for (auto it = c2p_rip.crossMachineState.begin();
		     it != c2p_rip.crossMachineState.end();
		     it++) {
			/* Assume that we're at @currentLabel in the
			   CFG.  What might happen next? */
			const ThreadCfgLabel &currentLabel(it->label);
			CFGNode *thisNode = ced.threadCfg.findInstr(currentLabel);

			/* Where might we go if the branch is taken? */
			std::set<ThreadCfgLabel> currentBranchTargets;
			/* Where might we go if it isn't taken? */
			std::set<ThreadCfgLabel> currentDefaultTargets;
			for (auto it2 = thisNode->successors.begin();
			     it2 != thisNode->successors.end();
			     it2++) {
				if (it2->instr) {
					if (it2->instr->rip == defaultRip)
						currentDefaultTargets.insert(
							ThreadCfgLabel(currentLabel.thread, it2->instr->label));
					else if (it2->instr->rip == branchRip)
						currentBranchTargets.insert(
							ThreadCfgLabel(currentLabel.thread, it2->instr->label));
					else
						abort();
				}
			}

			if (debug_find_successors)
				printf("\tTargets of %s: branch = %s, default = %s\n",
				       it->name(), name_set(currentBranchTargets), name_set(currentDefaultTargets));

			if (currentBranchTargets.empty() &&
			    currentDefaultTargets.empty()) {
				/* If both possible exits are empty
				   then we should have killed this
				   node off earlier in the
				   analysis. */
				abort();
			}

			if (currentBranchTargets.empty()) {
				/* If we can't go anywhere after
				   taking the branch then the branch
				   target is an exit. */
				if (debug_find_successors)
					printf("\tBranch exit target %s\n", it->name());
				branchExitTarget.insert(*it);
			} else {
				/* Otherwise, we have to introduce
				   branch targets for every possible
				   target in the CFG node */
				for (auto it2 = currentBranchTargets.begin();
				     it2 != currentBranchTargets.end();
				     it2++) {
					CrossLabel cl(*it2, it->sent_messages);
					if (debug_find_successors)
						printf("\tBranch target %s for %s\n",
						       cl.name(), it->name());
					branchTarget.insert(cl);
				}
			}

			/* Likewise for default targets */
			if (currentDefaultTargets.empty()) {
				if (debug_find_successors)
					printf("\tDefault exit target %s\n", it->name());
				defaultExitTarget.insert(*it);
			} else {
				/* Otherwise, we have to introduce
				   branch targets for every possible
				   target in the CFG node */
				for (auto it2 = currentDefaultTargets.begin();
				     it2 != currentDefaultTargets.end();
				     it2++) {
					CrossLabel cl(*it2, it->sent_messages);
					if (debug_find_successors)
						printf("\tDefault target %s for %s\n",
						       cl.name(), it->name());
					defaultTarget.insert(cl);
				}
			}
		}

		for (auto it = branchExitTarget.begin(); it != branchExitTarget.end(); it++)
			branchTarget.insert(*it);
		for (auto it = defaultExitTarget.begin(); it != defaultExitTarget.end(); it++)
			defaultTarget.insert(*it);
		assert(!branchTarget.empty());
		assert(!defaultTarget.empty());

		/* Now we get to issue the actual jump instruction. */
		C2PRip branchC2PRip(branchTarget,
				    C2PPhase::exitThreads(
					    branchExitTarget,
					    C2PPhase::checkForThreadStart(),
					    branchRip.unwrap_vexrip()));
		C2PRip defaultC2PRip(defaultTarget,
				     C2PPhase::exitThreads(
					     defaultExitTarget,
					     C2PPhase::checkForThreadStart(),
					     defaultRip.unwrap_vexrip()));
		if (debug_find_successors)
			printf("\tdefault %s, branch %s\n",
			       defaultC2PRip.name(),
			       branchC2PRip.name());
		Instruction<C2PRip> *instr =
			instrJcc(allocLabel, branchC2PRip, getJccCode(underlying), relocs);
		instr->addDefault(
			noopRelocation(allocLabel, defaultC2PRip, relocs));
		return instr;
	} else {
		/* Not implemented yet */
		abort();
	}
}

static Instruction<C2PRip> *
exitThreads(const C2PRip &c2p_rip,
	    std::queue<reloc> &relocs,
	    crashEnforcementData &ced,
	    AncillaryData &ad,
	    CfgLabelAllocator &allocLabel)
{
	Instruction<C2PRip> *start;
	Instruction<C2PRip> *cursor;
	start = cursor = NULL;

	std::set<unsigned> messagesToCancel;
	for (auto it = c2p_rip.phase->threadsToExit().begin();
	     it != c2p_rip.phase->threadsToExit().end();
	     it++) {
		if (it == c2p_rip.phase->threadsToExit().begin())
			messagesToCancel = it->sent_messages;
		else
			messagesToCancel &= it->sent_messages;
	}
	if (!messagesToCancel.empty()) {
		start = cursor = instrSkipRedZone(allocLabel);
		cursor = cursor->addDefault(instrPushReg64(allocLabel, RegisterIdx::RDI));
		cursor = cursor->addDefault(instrPushReg64(allocLabel, RegisterIdx::RBP));
		cursor = cursor->addDefault(instrMovLabelToRegister(
						    allocLabel,
						    "(unsigned long)clearMessage",
						    RegisterIdx::RBP));
		for (auto it = messagesToCancel.begin(); it != messagesToCancel.end(); it++) {
			cursor = cursor->addDefault(
				instrMovImmediateToReg(allocLabel, *it, RegisterIdx::RDI));
			cursor = cursor->addDefault(
				instrCallModrm(allocLabel, ModRM::directRegister(RegisterIdx::RBP)));
		}
		cursor = cursor->addDefault(instrPopReg64(allocLabel, RegisterIdx::RBP));
		cursor = cursor->addDefault(instrPopReg64(allocLabel, RegisterIdx::RDI));
		cursor = cursor->addDefault(instrRestoreRedZone(allocLabel));
	}

	std::set<CrossLabel> newState(c2p_rip.crossMachineState);
	for (auto it = c2p_rip.phase->threadsToExit().begin();
	     it != c2p_rip.phase->threadsToExit().end();
	     it++) {
		int b = newState.erase(*it);
		assert(b == 1);
	}

	Instruction<C2PRip> *end;
	if (newState.empty()) {
		end = new Instruction<C2PRip>(-1, allocLabel());
		end->len = 5;
		end->content[0] = 0xe9;
		end->lateRelocs.push_back(
			new LateRelocation(1,
					   4,
					   vex_asprintf("0x%lx", c2p_rip.phase->escapeRip()),
					   0,
					   true));
	} else {
		end = noopRelocation(allocLabel,
				     C2PRip(newState,
					    new C2PPhase(*c2p_rip.phase->exitTo())),
				     relocs);
	}
	if (cursor)
		cursor->addDefault(end);
	else
		start = end;
	return start;
}

static Instruction<C2PRip> *
receivedMessage(const C2PRip &c2p_rip,
		std::queue<reloc> &relocs,
		crashEnforcementData &ced,
		AncillaryData &ad,
		CfgLabelAllocator &allocLabel)
{
	if (debug_receive_messages)
		printf("%s(%s)\n", __func__, c2p_rip.name());

	Instruction<C2PRip> *start;
	Instruction<C2PRip> *cursor;

	/* Undo the stash operations we did in receiveMessages() */
	start = cursor = instrPopReg64(allocLabel, RegisterIdx::RAX);
	cursor = cursor->addDefault(instrPopf(allocLabel));
	cursor = cursor->addDefault(instrRestoreRedZone(allocLabel));

	/* We received one message, which means that we failed to
	   receive all of the other messages which we were looking
	   for.  That means that we might have to exit a whole bunch
	   of threads. */
	std::set<CrossLabel> failedThreads;
#ifndef NDEBUG
	bool found_received_message = false;
#endif
	for (auto it = c2p_rip.crossMachineState.begin(); it != c2p_rip.crossMachineState.end(); it++) {
		const ThreadCfgLabel &thread(it->label);
		const std::set<happensBeforeEdge *> &edges(ced.happensBeforePoints[thread]);
		for (auto it2 = edges.begin(); it2 != edges.end(); it2++) {
			const happensBeforeEdge *hb = *it2;
			if (hb == c2p_rip.phase->msgReceived()) {
#ifndef NDEBUG
				found_received_message = true;
#endif
				continue;
			}
			if (hb->after.tid == (int)thread.thread &&
			    hb->after.where == thread.label) {
				failedThreads.insert(*it);
				break;
			}
		}
	}
	assert(found_received_message);

	C2PRip next(c2p_rip.crossMachineState,
		    C2PPhase::exitThreads(failedThreads,
					  C2PPhase::origInstrAndStash(),
					  c2p_rip.vexrip(ced).unwrap_vexrip()));
	if (debug_receive_messages)
		printf("\tNext state %s\n", next.name());
	cursor->addDefault(
		noopRelocation(allocLabel, next, relocs));
	return start;
}

static Instruction<C2PRip> *
generateInstruction(const C2PRip &c2p_rip,
		    std::queue<reloc> &relocs,
		    crashEnforcementData &ced,
		    AncillaryData &ad,
		    CfgLabelAllocator &allocLabel)
{
	if (debug_main_loop)
		printf("Generate %s\n", c2p_rip.name());
	assert(c2p_rip.phase);
	switch (c2p_rip.phase->phase) {
	case C2PPhase::CheckForThreadStart:
		return checkForThreadStart(c2p_rip, relocs, ced, ad, allocLabel);
	case C2PPhase::StartThread:
		return startThread(c2p_rip, relocs, ced, ad, allocLabel);
	case C2PPhase::ReceiveMessages:
		return receiveMessages(c2p_rip, relocs, ced, ad, allocLabel);
	case C2PPhase::OrigInstrAndStash:
		return origInstrAndStash(c2p_rip, relocs, ced, ad, allocLabel);
	case C2PPhase::CheckSideConditions:
		return checkSideConditions(c2p_rip, relocs, ced, ad, allocLabel);
	case C2PPhase::SendMessages:
		return sendMessages(c2p_rip, relocs, ced, ad, allocLabel);
	case C2PPhase::FindSuccessors:
		return findSuccessors(c2p_rip, relocs, ced, ad, allocLabel);
	case C2PPhase::ExitThreads:
		return exitThreads(c2p_rip, relocs, ced, ad, allocLabel);
	case C2PPhase::ReceivedMessage:
		return receivedMessage(c2p_rip, relocs, ced, ad, allocLabel);
	}
	abort();
}

static CFG<C2PRip> *
enforce_crash(AddressSpace *as, CfgLabelAllocator &allocLabel, crashEnforcementData &ced,
	      AncillaryData &ad, std::map<VexRip, Instruction<C2PRip> *> &patchPoints)
{
	CFG<C2PRip> *work = new CFG<C2PRip>(as);
	std::queue<reloc> relocs;

	for (auto it = ced.roots.begin(); it != ced.roots.end(); it++)
		patchPoints[ced.threadCfg.findInstr(*it)->rip] = NULL;
	for (auto it = ced.roots.begin(); it != ced.roots.end(); it++) {
		std::set<CrossLabel> initialCrossMachineState;
		relocs.push(reloc(C2PRip(initialCrossMachineState,
					 C2PPhase::startThread(*it)),
				  &patchPoints[ced.threadCfg.findInstr(*it)->rip]));
	}

	while (!relocs.empty()) {
		reloc r(relocs.front());
		relocs.pop();

		if (!work->ripToInstr->hasKey(r.target)) {
			Instruction<C2PRip> *head = generateInstruction(r.target, relocs, ced, ad, allocLabel);
			head->rip = r.target;
			work->ripToInstr->set(r.target, head);
		}
		assert(work->ripToInstr->hasKey(r.target));
		*r.ptr = work->ripToInstr->get(r.target);
		assert(r.ptr);
	}

	return work;
}

static void
printDetailedCfg(Instruction<C2PRip> *root, std::set<Instruction<C2PRip> *> &printed, FILE *f)
{
	if (printed.count(root))
		return;
	fprintf(f, "%-6s: %-50s", root->label.name(), root->rip.isNil() ? "" : root->rip.name());
	for (auto it = root->successors.begin();
	     it != root->successors.end();
	     it++) {
		if (it->instr) {
			if (it->type == Instruction<C2PRip>::successor_t::succ_default)
				fprintf(f,
					" defaultSucc = %-6s",
					it->instr->label.name());
			else if (it->type == Instruction<C2PRip>::successor_t::succ_branch)
				fprintf(f,
					" branchSucc  = %-6s",
					it->instr->label.name());
			else
				abort();
		}
	}
	if (root->len != 0) {
		fprintf(f, " [");
		for (unsigned x = 0; x < root->len; x++) {
			if (x != 0)
				fprintf(f, ", ");
			fprintf(f, "%02x", root->content[x]);
		}
		fprintf(f, "]");
	}
	if (!root->relocs.empty()) {
		fprintf(f, " relocs = [");
		for (auto it = root->relocs.begin();
		     it != root->relocs.end();
		     it++) {
			if (it != root->relocs.begin())
				fprintf(f, ", ");
			fprintf(f, "%s", (*it)->name());
		}
		fprintf(f, "]");
	}
	if (!root->lateRelocs.empty()) {
		fprintf(f, " lateRelocs = [");
		for (auto it = root->lateRelocs.begin();
		     it != root->lateRelocs.end();
		     it++) {
			if (it != root->lateRelocs.begin())
				fprintf(f, ", ");
			fprintf(f, "%s", (*it)->name());
		}
		fprintf(f, "]");
	}
	fprintf(f, "\n");
	printed.insert(root);
	for (auto it = root->successors.begin();
	     it != root->successors.end();
	     it++)
		if (it->instr)
			printDetailedCfg(it->instr, printed, f);
}

class CompiledCfg {
	std::vector<unsigned char> content;
	std::vector<LateRelocation *> lateRelocs;
public:
	unsigned currentSize() const {
		assert(content.size() < (1u << 31));
		return content.size();
	}
	void addInstr(unsigned sz, const unsigned char *bytes) {
		for (unsigned x = 0; x < sz; x++)
			content.push_back(bytes[x]);
	}
	void addLateReloc(LateRelocation *reloc) {
		lateRelocs.push_back(reloc);
	}
	void writeBytes(unsigned offset, unsigned sz, const void *bytes) {
		assert(content.size() >= offset + sz);
		for (unsigned x = 0; x < sz; x++)
			content[x + offset] = ((const unsigned char *)bytes)[x];
	}
	void dumpToFile(const char *path) const {
		FILE *f = fopen(path, "w");
		if (!f) err(1, "opening %s");
		for (unsigned x = 0; x < content.size(); x++)
			fputc(content[x], f);
		fclose(f);
	}
};

class LookupCfgNode {
	CFG<C2PRip> *cfg;
public:	
	LookupCfgNode(CFG<C2PRip> *_cfg)
		: cfg(_cfg)
	{}
	const Instruction<C2PRip> *operator()(const C2PRip &l) const {
		assert(cfg->ripToInstr->hasKey(l));
		return cfg->ripToInstr->get(l);
	}
};

static void
compileCfg(const Instruction<C2PRip> *root,
	   std::map<const Instruction<C2PRip> *, unsigned> &offsetInCompiledPatch,
	   std::queue<RipRelativeBranchRelocation<C2PRip> *> &earlyRelocs,
	   LookupCfgNode &lookupNode,
	   CompiledCfg &result)
{
	if (offsetInCompiledPatch.count(root))
		return;
top:
	unsigned offset = result.currentSize();
	offsetInCompiledPatch[root] = offset;

	if (debug_compile_cfg)
		printf("Compile %s -> %x\n", root->label.name(), offset);

	/* Emit the instruction itself. */
	if (root->len != 0) {
		result.addInstr(root->len, root->content);
		/* Early relocations */
		for (auto it = root->relocs.begin();
		     it != root->relocs.end();
		     it++) {
			const EarlyRelocation<C2PRip> *earlyReloc = *it;
			if (dynamic_cast<const RipRelativeRelocation<C2PRip> *>(earlyReloc)) {
				abort(); /* shouldn't be any of these here */
			} else if (auto rrdr = dynamic_cast<const RipRelativeDataRelocation<C2PRip> *>(earlyReloc)) {
				result.addLateReloc(new LateRelocation(rrdr->offset + offset,
								       rrdr->size,
								       vex_asprintf("0x%lx", rrdr->target),
								       rrdr->nrImmediateBytes,
								       true));
			} else if (auto rrbr = dynamic_cast<const RipRelativeBranchRelocation<C2PRip> *>(earlyReloc)) {
				auto it_o = offsetInCompiledPatch.find(lookupNode(rrbr->target));
				if (it_o == offsetInCompiledPatch.end()) {
					earlyRelocs.push(new RipRelativeBranchRelocation<C2PRip>(
								 rrbr->offset + offset,
								 rrbr->size,
								 rrbr->target));
				} else {
					int delta = it_o->second - offset - rrbr->offset - rrbr->size;
					result.writeBytes(offset + rrbr->offset,
							  rrbr->size,
							  &delta);
				}
			} else {
				abort();
			}
		}
		/* Late relocations */
		for (auto it = root->lateRelocs.begin();
		     it != root->lateRelocs.end();
		     it++) {
			const LateRelocation *inp = *it;
			result.addLateReloc(new LateRelocation(inp->offset + offset,
							       inp->size,
							       inp->target,
							       inp->nrImmediateBytes,
							       inp->relative));
		}
	} else {
		assert(root->relocs.empty());
		assert(root->lateRelocs.empty());
	}

	/* Now make sure that the successors get emitted. */
	Instruction<C2PRip> *nextInstr = NULL;
	for (auto it = root->successors.begin(); it != root->successors.end(); it++) {
		if (it->instr) {
			if (it->type == Instruction<C2PRip>::successor_t::succ_default) {
				/* Should only have one default exit */
				assert(nextInstr == NULL);
				nextInstr = it->instr;
			} else {
				/* Branches should be handled as early relocs */
				assert(it->type == Instruction<C2PRip>::successor_t::succ_branch);
				assert(!root->relocs.empty());
			}
		}
	}
	if (!nextInstr) {
		/* This instruction never falls through, so we're
		 * fine. */
		return;
	}
	if (offsetInCompiledPatch.count(nextInstr)) {
		/* The desired fall-through has already been emitted
		 * somewhere else.  Have to emit a branch to make it
		 * work nicely. */
		unsigned delta = (unsigned)((int)offsetInCompiledPatch[nextInstr] - (int)result.currentSize() - 5);
		unsigned char branchInstr[5];
		/* jmp rel32 instruction */
		branchInstr[0] = 0xe9;
		branchInstr[1] = delta & 0xff;
		branchInstr[2] = (delta >> 8) & 0xff;
		branchInstr[3] = (delta >> 16) & 0xff;
		branchInstr[4] = (delta >> 24) & 0xff;
		result.addInstr(5, branchInstr);
		return;
	}

	/* The fall-through instruction hasn't been emitted yet, so
	 * let's just emit it here. */
	root = nextInstr;
	goto top;
}

static void
compileCfg(CFG<C2PRip> *cfg,
	   const std::map<VexRip, Instruction<C2PRip> *> &roots,
	   CompiledCfg &result)
{
	std::map<const Instruction<C2PRip> *, unsigned> offsetInCompiledPatch;
	std::queue<RipRelativeBranchRelocation<C2PRip> *> earlyRelocs;
	LookupCfgNode lookupNode(cfg);

	for (auto it = roots.begin(); it != roots.end(); it++) {
		compileCfg(it->second, offsetInCompiledPatch, earlyRelocs, lookupNode, result);
		while (!earlyRelocs.empty()) {
			RipRelativeBranchRelocation<C2PRip> *r = earlyRelocs.front();
			earlyRelocs.pop();
			const Instruction<C2PRip> *targetInstr = lookupNode(r->target);
			auto it_f = offsetInCompiledPatch.find(targetInstr);
			if (it_f == offsetInCompiledPatch.end()) {
				compileCfg(targetInstr, offsetInCompiledPatch, earlyRelocs, lookupNode, result);
				it_f = offsetInCompiledPatch.find(targetInstr);
				assert(it_f != offsetInCompiledPatch.end());
			}
			int delta = it_f->second - r->offset - r->size;
			result.writeBytes(r->offset,
					  r->size,
					  &delta);
		}
	}
	
	
}

int
main(int argc, char *argv[])
{
	if (argc != 5)
		errx(1, "not enough arguments");
	const char *binary = argv[1];
	const char *ced_path = argv[2];
	const char *topdir = argv[3];
	const char *output = argv[4];
	init_sli();

	VexPtr<MachineState> ms(MachineState::readELFExec(binary));

	int fd = open(ced_path, O_RDONLY);
	if (fd < 0)
		err(1, "open(%s)", ced_path);
	crashEnforcementData ced;
	loadCrashEnforcementData(ced, ms->addressSpace, fd);
	close(fd);

	ced.prettyPrint(stdout, true);

	simulationSlotT next_slot(1);
	for (auto it = ced.exprsToSlots.begin(); it != ced.exprsToSlots.end(); it++)
		if (it->second.idx >= next_slot.idx)
			next_slot.idx = it->second.idx + 1;

	CfgLabelAllocator allocLabel;
	ced.threadCfg.prepLabelAllocator(allocLabel);

	AncillaryData ad(ms->addressSpace, ced);

	std::map<VexRip, Instruction<C2PRip> *> patchPoints;
	CFG<C2PRip> *cfg = enforce_crash(ms->addressSpace,
					 allocLabel,
					 ced,
					 ad,
					 patchPoints);

	printf("Build augmented CFG:\n");
	std::set<Instruction<C2PRip> *> printed;
	for (auto it = patchPoints.begin();
	     it != patchPoints.end();
	     it++) {
		printf("Root %s:\n", it->first.name());
		printDetailedCfg(it->second, printed, stdout);
	}

	CompiledCfg result;
	compileCfg(cfg, patchPoints, result);

	result.dumpToFile(output);

#if 0
	CfgDecode decode;

	/* Now build the patch */
	int next_rx_site_id = 0;
	CFG<ClientRip> *cfg = enforceCrash(ced, decode, ms->addressSpace, next_slot, next_rx_site_id);
	EnforceCrashPatchFragment *pf = new EnforceCrashPatchFragment(ced.happensBeforePoints, ced.roots);
	CfgLabelAllocator alloc;
	pf->fromCFG(alloc, cfg);
	char *patch = pf->asC("ident", next_rx_site_id);

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

	char *real_inp = realpath(binary, NULL);
	my_system(
		"gcc",
		"-Wall",
		"-fPIC",
		"-shared",
		"-g",
		"-I.",
		vex_asprintf("-Dthe_patch=\"%s\"", tmpfile),
		vex_asprintf("-Dprogram_to_patch=\"%s\"", real_inp),
		vex_asprintf("%s/sli/enforce_crash/patch_core.c", topdir),
		"-o",
		output,
		NULL);
#endif

	return 0;
}
