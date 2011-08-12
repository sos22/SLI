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

happensAfterMapT::happensAfterMapT(DNF_Conjunction &c, CFG<ThreadRip> *cfg)
{
	for (unsigned x = 0; x < c.size(); x++) {
		if (c[x].second->tag == Iex_HappensBefore) {
			ThreadRip beforeRip = c[x].second->Iex.HappensBefore.before;
			ThreadRip afterRip = c[x].second->Iex.HappensBefore.after;
			Instruction<ThreadRip> *before = cfg->ripToInstr->get(beforeRip);
			Instruction<ThreadRip> *after = cfg->ripToInstr->get(afterRip);
			assert(before);
			assert(after);
			if (c[x].first) {
				Instruction<ThreadRip> *t = before;
				before = after;
				after = t;
			}
			happensAfter[before].insert(after);
			happensBefore[after].insert(before);
		}
	}
}

#define BASE_MESSAGE_ID 0xaabb
unsigned happensBeforeEdge::next_msg_id = BASE_MESSAGE_ID;

class expressionEvalMapT : public std::map<unsigned long, std::set<exprEvalPoint> > {
public:
	expressionEvalMapT(expressionDominatorMapT &exprDominatorMap) {
		for (expressionDominatorMapT::iterator it = exprDominatorMap.begin();
		     it != exprDominatorMap.end();
		     it++) {
			for (std::set<std::pair<bool, IRExpr *> >::iterator it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++)
				(*this)[it->first->rip.rip].insert(
					exprEvalPoint(
						it2->first,
						it->first->rip.thread,
						it2->second));
		}
	}
};


EnforceCrashPatchFragment::jcc_code EnforceCrashPatchFragment::jcc_code::zero(0x84);
EnforceCrashPatchFragment::jcc_code EnforceCrashPatchFragment::jcc_code::nonzero(0x85);

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
instrOpcode(Instruction<ClientRip> *i)
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

EnforceCrashPatchFragment::RegisterIdx
EnforceCrashPatchFragment::instrModrmReg(Instruction<ClientRip> *i)
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

void
EnforceCrashPatchFragment::emitMovRegToSlot(RegisterIdx offset, simulationSlotT slot)
{
	emitGsPrefix();
	emitMovRegisterToModrm(offset, modrmForSlot(slot));
}

void
EnforceCrashPatchFragment::emitMovSlotToReg(simulationSlotT slot, RegisterIdx offset)
{
	emitGsPrefix();
	emitMovModrmToRegister(modrmForSlot(slot), offset);
}

void
EnforceCrashPatchFragment::emitAddRegToSlot(RegisterIdx reg, simulationSlotT slot)
{
	emitGsPrefix();
	emitAddRegToModrm(reg, modrmForSlot(slot));
}

void
EnforceCrashPatchFragment::emitAddSlotToReg(simulationSlotT slot, RegisterIdx reg)
{
	emitGsPrefix();
	emitAddModrmToReg(modrmForSlot(slot), reg);
}

void
EnforceCrashPatchFragment::emitTestRegModrm(RegisterIdx reg, const ModRM &modrm)
{
	unsigned char rex = 0x48;
	if (reg.idx >= 8) {
		rex |= 4;
		reg.idx -= 8;
		assert(reg.idx < 8);
	}
	if (modrm.extendRm)
		rex |= 1;
	emitByte(rex);
	emitByte(0x85);
	emitModrm(modrm, reg);
}

void
EnforceCrashPatchFragment::emitJcc(ClientRip target, jcc_code branchType)
{
	emitByte(0x0F);
	emitByte(branchType.code);
	emitByte(0); /* Pad */
	emitByte(0); /* Pad */
	emitByte(0); /* Pad */
	emitByte(0); /* Pad */
	relocs.push_back(new RipRelativeBranchRelocation<ClientRip>(content.size() - 4,
								    4,
								    target));
}

simulationSlotT
EnforceCrashPatchFragment::emitSaveRflags()
{
	skipRedZone();
	emitPushf();
	simulationSlotT t = exprsToSlots.allocateSlot();
	emitMovRegToSlot(RegisterIdx::RAX, t);
	emitPopQ(RegisterIdx::RAX);
	restoreRedZone();
	simulationSlotT s = exprsToSlots.allocateSlot();
	emitMovRegToSlot(RegisterIdx::RAX, s);
	emitMovSlotToReg(t, RegisterIdx::RAX);

	return s;
}

void
EnforceCrashPatchFragment::emitRestoreRflags(simulationSlotT s)
{
	skipRedZone();
	simulationSlotT t = exprsToSlots.allocateSlot();
	emitMovRegToSlot(RegisterIdx::RAX, t);
	emitMovSlotToReg(s, RegisterIdx::RAX);
	emitPushQ(RegisterIdx::RAX);
	emitPopf();
	emitMovSlotToReg(t, RegisterIdx::RAX);
	restoreRedZone();
}

bool
EnforceCrashPatchFragment::emitEvalExpr(unsigned thread, IRExpr *e, RegisterIdx reg)
{
	{
		slotMapT::iterator it = exprsToSlots.find(std::pair<unsigned, IRExpr *>(thread, e));
		if (it != exprsToSlots.end()) {
			emitMovSlotToReg(it->second, reg);
			return true;
		}
	}

	switch (e->tag) {
	case Iex_Const:
		emitMovQ(reg, e->Iex.Const.con->Ico.U64);
		return true;

	case Iex_Unop:
		switch (e->Iex.Unop.op) {
		case Iop_Neg64:
			if (!emitEvalExpr(thread, e->Iex.Unop.arg, reg))
				return false;
			emitNegModrm(ModRM::directRegister(reg));
			return true;
		default:
			break;
		}
		break;

	case Iex_Binop:
		switch (e->Iex.Binop.op) {
		case Iop_CmpEQ64: {
			simulationSlotT old_rax = exprsToSlots.allocateSlot();
			if (!emitEvalExpr(thread, e->Iex.Binop.arg1, reg))
				return false;
			simulationSlotT t = exprsToSlots.allocateSlot();
			emitMovRegToSlot(reg, t);
			if (!emitEvalExpr(thread, e->Iex.Binop.arg2, reg))
				return false;
			emitGsPrefix();
			emitCmpRegModrm(reg, modrmForSlot(t));

			if (reg != RegisterIdx::RAX)
				emitMovRegToSlot(RegisterIdx::RAX, old_rax);
			/* Clear %rax */
			emitMovQ(RegisterIdx::RAX, 0);
			/* seteq al */
			emitByte(0x0F);
			emitByte(0x94);
			emitByte(0xC0); /* mod = 3, reg = 0, rm = 0 */
			if (reg != RegisterIdx::RAX) {
				emitMovRegisterToModrm(RegisterIdx::RAX, ModRM::directRegister(reg));
				emitMovSlotToReg(old_rax, RegisterIdx::RAX);
			}
			return true;
		}
		default:
			break;
		}
		break;
	case Iex_Associative:
		switch (e->Iex.Associative.op) {
		case Iop_Add64: {
			if (!emitEvalExpr(thread, e->Iex.Associative.contents[0], reg))
				return false;
			if (e->Iex.Associative.nr_arguments == 1)
				return true;
			simulationSlotT acc = exprsToSlots.allocateSlot();
			emitMovRegToSlot(reg, acc);
			for (int x = 1; x < e->Iex.Associative.nr_arguments - 1; x++) {
				if (!emitEvalExpr(thread, e->Iex.Associative.contents[x], reg))
					return false;
				emitAddRegToSlot(reg, acc);
			}
			if (!emitEvalExpr(thread, e->Iex.Associative.contents[e->Iex.Associative.nr_arguments - 1],
					  reg))
				return false;
			emitAddSlotToReg(acc, reg);
			return true;
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
	return false;
}

bool
EnforceCrashPatchFragment::emitCompareExprToZero(unsigned thread, IRExpr *e)
{
	RegisterIdx reg = RegisterIdx::RAX;
	bool r;
	simulationSlotT spill = exprsToSlots.allocateSlot();
	emitMovRegToSlot(reg, spill);
	r = emitEvalExpr(thread, e, reg);
	if (r)
		emitTestRegModrm(reg, ModRM::directRegister(reg));
	emitMovSlotToReg(spill, reg);
	return r;
}

void
EnforceCrashPatchFragment::emitCheckExpressionOrEscape(const exprEvalPoint &e,
						       Instruction<ClientRip> *i)
{
	if (!i->rip.threadLive(e.thread))
		return;
	assert(!i->branchNext.rip);
	IRExpr *expr;
	expr = e.e;
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

	if (!emitCompareExprToZero(e.thread, expr))
		return;

	jcc_code branch_type = invert ? jcc_code::nonzero : jcc_code::zero;
	assert(i->defaultNextI);
	ClientRip n = i->defaultNextI->rip;
	n.eraseThread(e.thread);
	/* XXX several things wrong here:

	   -- Don't restore rflags if we branch
	   -- Don't evaluate expressions from target thread if we branch to an instruction
	      with additional expressions.
	*/
	emitJcc(n, branch_type);
}

void
EnforceCrashPatchFragment::emitLoadMessageToSlot(unsigned msg_id, unsigned msgslot, simulationSlotT simslot,
						 RegisterIdx spill)
{
	emitMovQ(spill, 0);
	addLateReloc(late_relocation(content.size() - 8,
				     8,
				     vex_asprintf("(unsigned long)&__msg_%d_slot_%d", msg_id, msgslot),
				     0,
				     false));
	emitMovModrmToRegister(ModRM::memAtRegister(spill), spill);
	emitMovRegToSlot(spill, simslot);
}

void
EnforceCrashPatchFragment::emitStoreSlotToMessage(unsigned msg_id, unsigned msgslot, simulationSlotT simslot,
						  RegisterIdx spill1, RegisterIdx spill2)
{
	emitMovQ(spill1, 0);
	addLateReloc(late_relocation(content.size() - 8,
				     8,
				     vex_asprintf("(unsigned long)&__msg_%d_slot_%d", msg_id, msgslot),
				     0,
				     false));
	emitMovSlotToReg(simslot, spill2);
	emitMovRegisterToModrm(spill2, ModRM::memAtRegister(spill1));
}

void
EnforceCrashPatchFragment::emitHappensBeforeEdgeAfter(const happensBeforeEdge *hb,
						      Instruction<ClientRip> *i)
{
	assert(!i->branchNextI);

	simulationSlotT rflags = emitSaveRflags();
	simulationSlotT rdi = exprsToSlots.allocateSlot();
	simulationSlotT rax = exprsToSlots.allocateSlot();
	emitMovRegToSlot(RegisterIdx::RDI, rdi);
	emitMovRegToSlot(RegisterIdx::RAX, rax);
	emitMovQ(RegisterIdx::RDI, hb->msg_id);
	emitCallSequence("(unsigned long)happensBeforeEdge__after", false);
	emitMovSlotToReg(rdi, RegisterIdx::RDI);

	emitTestRegModrm(RegisterIdx::RAX, ModRM::directRegister(RegisterIdx::RAX));
	emitMovSlotToReg(rax, RegisterIdx::RAX);
	/* XXX as usual, not quite right */
	ClientRip destinationIfThisFails = i->defaultNextI ? i->defaultNextI->rip : i->defaultNext;
	destinationIfThisFails.eraseThread(hb->after.thread);
	emitJcc(destinationIfThisFails, jcc_code::zero);

	for (unsigned x = 0; x < hb->content.size(); x++) {
		simulationSlotT s = exprsToSlots(hb->after.thread, hb->content[x]);
		emitLoadMessageToSlot(hb->msg_id, x, s, RegisterIdx::RDI);
	}
	emitMovSlotToReg(rdi, RegisterIdx::RDI);
	emitRestoreRflags(rflags);
}

void
EnforceCrashPatchFragment::emitHappensBeforeEdgeBefore(const happensBeforeEdge *hb)
{
	simulationSlotT rdi = exprsToSlots.allocateSlot();
	emitMovRegToSlot(RegisterIdx::RDI, rdi);
	simulationSlotT r13 = exprsToSlots.allocateSlot();
	emitMovRegToSlot(RegisterIdx::R13, r13);

	for (unsigned x = 0; x < hb->content.size(); x++) {
		simulationSlotT s = exprsToSlots(hb->before.thread, hb->content[x]);
		emitStoreSlotToMessage(hb->msg_id, x, s, RegisterIdx::RDI, RegisterIdx::R13);
	}
	emitMovQ(RegisterIdx::RDI, hb->msg_id);
	emitCallSequence("(unsigned long)happensBeforeEdge__before", false);
	emitMovSlotToReg(r13, RegisterIdx::R13);
	emitMovSlotToReg(rdi, RegisterIdx::RDI);
}

void
EnforceCrashPatchFragment::emitInstruction(Instruction<ClientRip> *i)
{
	if (i->rip.noThreadsLive()) {
		emitJmpToRipHost(i->rip.rip);
		return;
	}
	std::set<std::pair<unsigned, IRExpr *> > *neededExprs = NULL;
	if (neededExpressions.count(i->rip.rip)) {
		neededExprs = &neededExpressions[i->rip.rip];
		/* Need to emit gunk to store the appropriate
		   generated expression.  That'll either be a simple
		   register access or a memory load of some sort. */
		for (std::set<std::pair<unsigned, IRExpr *> >::iterator it = neededExprs->begin();
		     it != neededExprs->end();
		     it++) {
			if (!i->rip.threadLive(it->first))
				continue;
			IRExpr *e = it->second;
			if (e->tag == Iex_Get) {
				/* Easy case: just store the register in its slot */
				simulationSlotT s = exprsToSlots(it->first, e);
				emitMovRegToSlot(RegisterIdx::fromVexOffset(e->Iex.Get.offset), s);
			} else if (e->tag == Iex_ClientCall) {
				/* Do this after emitting the instruction */
			} else {
				assert(e->tag == Iex_Load);
				assert(neededExprs->size() == 1);
				/* Much more difficult case.  This
				   depends on the type of instruction
				   which we're looking at. */
				switch (instrOpcode(i)) {
				case 0x8b:
					/* Simple load from modrm to
					 * register.  Deal with it
					 * later. */
					break;
				default:
					abort();
				}
			}
		}
	}

	/* If this instruction is supposed to happen after some other
	 * instruction then we might want to insert a delay before
	 * running it. */
	std::set<happensBeforeEdge *> *hbEdges = NULL;
	if (happensBeforePoints.count(i->rip.rip)) {
		hbEdges = &happensBeforePoints[i->rip.rip];
		for (std::set<happensBeforeEdge *>::iterator it = hbEdges->begin();
		     it != hbEdges->end();
		     it++) {
			const happensBeforeEdge *hb = *it;
			if (hb->after.rip == i->rip.rip &&
			    i->rip.threadLive(hb->after.thread))
				emitHappensBeforeEdgeAfter(hb, i);
		}
	}

	PatchFragment<ClientRip>::emitInstruction(i);

	if (neededExprs) {
		for (std::set<std::pair<unsigned, IRExpr *> >::iterator it = neededExprs->begin();
		     it != neededExprs->end();
		     it++) {
			if (!i->rip.threadLive(it->first))
				continue;
			IRExpr *e = it->second;
			if (e->tag == Iex_Get) {
				/* Already handled */
			} else if (e->tag == Iex_ClientCall) {
				/* The result of the call should now be in %rax */
				simulationSlotT s = exprsToSlots(it->first, e);
				emitMovRegToSlot(RegisterIdx::RAX, s);
			} else {
				assert(e->tag == Iex_Load);
				switch (instrOpcode(i)) {
				case 0x8b: {
					/* Load from memory to modrm.
					 * Nice and easy. */
					simulationSlotT s = exprsToSlots(it->first, e);
					emitMovRegToSlot(instrModrmReg(i), s);
					break;
				}
				default:
					abort();
				}
			}
		}
	}

	if (expressionEvalPoints.count(i->rip.rip)) {
		std::set<exprEvalPoint> &expressionsToEval(expressionEvalPoints[i->rip.rip]);

		bool doit = false;
		for (std::set<exprEvalPoint>::iterator it = expressionsToEval.begin();
		     !doit && it != expressionsToEval.end();
		     it++)
			if (i->rip.threadLive(it->thread))
				doit = true;
		if (doit) {
			simulationSlotT rflags = emitSaveRflags();
			for (std::set<exprEvalPoint>::iterator it = expressionsToEval.begin();
			     it != expressionsToEval.end();
			     it++)
				emitCheckExpressionOrEscape(*it, i);
			emitRestoreRflags(rflags);
		}
	}

	/* Now look at the before end of happens before
	 * relationships. */
	if (hbEdges) {
		for (std::set<happensBeforeEdge *>::iterator it = hbEdges->begin();
		     it != hbEdges->end();
		     it++) {
			happensBeforeEdge *hb = *it;
			if (hb->before.rip == i->rip.rip &&
			    i->rip.threadLive(hb->before.thread))
				emitHappensBeforeEdgeBefore(hb);
		}
	}
}

void
EnforceCrashPatchFragment::generateEpilogue(ClientRip exitRip)
{
	Instruction<ClientRip> *i = Instruction<ClientRip>::pseudo(exitRip);
	cfg->registerInstruction(i);
	registerInstruction(i, content.size());

	std::set<unsigned> msg_ids;
	for (std::map<unsigned long, std::set<happensBeforeEdge *> >::iterator it = happensBeforePoints.begin();
	     it != happensBeforePoints.end();
	     it++) {
		std::set<happensBeforeEdge *> &hb(it->second);
		for (std::set<happensBeforeEdge *>::iterator it2 = hb.begin();
		     it2 != hb.end();
		     it2++) {
			const happensBeforeEdge *hb = *it2;
			if (exitRip.origThreads.count(hb->before.thread))
				msg_ids.insert(hb->msg_id);
		}
	}

	if (msg_ids.size() != 0) {
		skipRedZone();
		emitPushQ(RegisterIdx::RBX);
		emitPushQ(RegisterIdx::RDI);
		emitMovQ(RegisterIdx::RBX, 0);
		lateRelocs.push_back(late_relocation(content.size() - 8,
						     8,
						     vex_asprintf("(unsigned long)clearMessage"),
						     0,
						     false));

		for (std::set<unsigned>::iterator it = msg_ids.begin();
		     it != msg_ids.end();
		     it++) {
			unsigned msg_id = *it;
			emitMovQ(RegisterIdx::RDI, msg_id);
			emitCallReg(RegisterIdx::RBX);
		}
		emitPopQ(RegisterIdx::RDI);
		emitPopQ(RegisterIdx::RBX);
		restoreRedZone();
	}

	emitJmpToRipHost(exitRip.rip);
}

char *
EnforceCrashPatchFragment::asC(const char *ident, std::set<ClientRip> &entryPoints)
{
	std::vector<const char *> fragments;

	fragments.push_back(vex_asprintf("#define MESSAGE_ID_BASE %d\n", BASE_MESSAGE_ID));
	fragments.push_back(vex_asprintf("#define MESSAGE_ID_END %d\n", happensBeforeEdge::next_msg_id));
	std::set<happensBeforeEdge *> emitted;
	for (std::map<unsigned long, std::set<happensBeforeEdge *> >::iterator it = happensBeforePoints.begin();
	     it != happensBeforePoints.end();
	     it++) {
		for (std::set<happensBeforeEdge *>::iterator it2 = it->second.begin();
		     it2 != it->second.end();
		     it2++) {
			happensBeforeEdge *hb = *it2;
			if (emitted.count(hb))
				continue;
			emitted.insert(hb);
			for (unsigned x = 0; x < hb->content.size(); x++)
				fragments.push_back(vex_asprintf("static unsigned long __msg_%d_slot_%d;\n", hb->msg_id, x));
		}
	}
	fragments.push_back(PatchFragment<ClientRip>::asC(ident, entryPoints));

	return flattenStringFragments(fragments);
}

ClientRip threadRipToClientRip(const ThreadRip &k)
{
	return ClientRip(k.rip);
}
unsigned long __trivial_hash_function(const ClientRip &k)
{
	return k.rip;
}

static EarlyRelocation<ClientRip> *
duplicateEarlyRelocAtNewThreadSet(EarlyRelocation<ClientRip> *er, const std::set<unsigned> &threads)
{
	if (RipRelativeRelocation<ClientRip> *rrr =
	    dynamic_cast<RipRelativeRelocation<ClientRip> *>(er)) {
		return new RipRelativeRelocation<ClientRip>(rrr->offset, rrr->size,
							    ClientRip(rrr->target.rip, threads),
							    rrr->nrImmediateBytes);
	} else if (RipRelativeBranchRelocation<ClientRip> *rrbr =
		   dynamic_cast<RipRelativeBranchRelocation<ClientRip> *>(er)) {
		return new RipRelativeBranchRelocation<ClientRip>(rrbr->offset, rrbr->size,
								  ClientRip(rrbr->target.rip, threads));

	} else {
		abort();
	}
}

template <typename k, typename v> void
mapKeys(std::set<k> &out, std::map<k, v> &m)
{
	for (typename std::map<k, v>::iterator it = m.begin();
	     it != m.end();
	     it++)
		out.insert(it->first);
}

template <typename t> void
powerSet(const std::set<t> &_in, std::set<std::set<t> > &out)
{
	/* It's useful to be able to refer to the elements of @_in by
	   index, which means we really want to put them in a
	   vector. */
	std::vector<t> in;
	in.reserve(_in.size());
	for (typename std::set<t>::iterator it = _in.begin();
	     it != _in.end();
	     it++)
		in.push_back(*it);
	/* @live tells you which elements of @in you want to include
	   in the next item.  It's pretty much the binary
	   representation of the number of items currently in @out,
	   and counts from 0 to 1111..., with an appropriate number of
	   ones, and hence covers every possible subvector of @in. */
	std::vector<bool> live;
	live.resize(in.size());
	while (1) {
		/* Insert new item */
		std::set<t> item;
		for (unsigned x = 0; x < live.size(); x++)
			if (live[x])
				item.insert(in[x]);
		out.insert(item);

		/* Advance @live.  This is just the add-one algorithm
		   in binary.  There might be a more efficient way to
		   do this. :) */
		unsigned x;
		for (x = 0; x < live.size(); x++) {
			if (live[x]) {
				live[x] = false;
			} else {
				live[x] = true;
				break;
			}
		}
		if (x == live.size())
			break;
	}
}

static void
duplicateCFGAtThreadSet(CFG<ClientRip> *cfg, std::set<unsigned long> &rips, const std::set<unsigned> &threads)
{
	std::map<Instruction<ClientRip> *, Instruction<ClientRip> *> m;

	for (std::set<unsigned long>::iterator it = rips.begin();
	     it != rips.end();
	     it++) {
		Instruction<ClientRip> *orig = cfg->ripToInstr->get(ClientRip(*it));
		ClientRip newRip(*it, threads);
		assert(!cfg->ripToInstr->hasKey(newRip));
		Instruction<ClientRip> *nr = new Instruction<ClientRip>(*orig);
		nr->rip = newRip;
		if (nr->defaultNext.rip)
			nr->defaultNext = ClientRip(nr->defaultNext.rip, threads);
		if (nr->branchNext.rip)
			nr->branchNext = ClientRip(nr->branchNext.rip, threads);
		for (unsigned x = 0; x < nr->relocs.size(); x++)
			nr->relocs[x] = duplicateEarlyRelocAtNewThreadSet(nr->relocs[x], threads);
		cfg->ripToInstr->set(newRip, nr);
		m[orig] = nr;
	}

	for (std::set<unsigned long>::iterator it = rips.begin();
	     it != rips.end();
	     it++) {
		ClientRip newRip(*it, threads);
		Instruction<ClientRip> *n = cfg->ripToInstr->get(newRip);
		assert(n);
		if (n->defaultNextI) {
			n->defaultNextI = m[n->defaultNextI];
			assert(n->defaultNextI);
		}
		if (n->branchNextI) {
			n->branchNextI = m[n->branchNextI];
			assert(n->branchNextI);
		}
	}
}

static CFG<ClientRip> *
convertCFGFromThreadRipToClientRips(CFG<ThreadRip> *cfg,
				    std::set<unsigned> &neededThreads,
				    expressionDominatorMapT &exprDominatorMap)
{
	CFG<ClientRip> *degradedCfg = cfg->degrade<ClientRip, threadRipToClientRip>();

	/* And now expand it again so that we can do the power-set
	 * construction. */
	std::set<std::set<unsigned> > threadPower;
	{
		std::set<std::set<unsigned> > threadPower1;
		powerSet(neededThreads, threadPower1);
		for (std::set<std::set<unsigned> >::iterator it = threadPower1.begin();
		     it != threadPower1.end();
		     it++)
			threadPower.insert(*it);
	}
	printf("Power threads:\n");
	for (std::set<std::set<unsigned> >::iterator it = threadPower.begin();
	     it != threadPower.end();
	     it++) {
		printf("\t");
		for (std::set<unsigned>::const_iterator it2 = it->begin();
		     it2 != it->end();
		     it2++)
			printf("%d ", *it2);
		printf("\n");
	}
	std::set<unsigned long> rawRips;
	for (CFG<ClientRip>::ripToInstrT::iterator it = degradedCfg->ripToInstr->begin();
	     it != degradedCfg->ripToInstr->end();
	     it++)
		rawRips.insert(it.key().rip);
	for (std::set<std::set<unsigned> >::iterator it = threadPower.begin();
	     it != threadPower.end();
	     it++) {
		if (it->size() != 0)
			duplicateCFGAtThreadSet(degradedCfg, rawRips, *it);
	}

	return degradedCfg;
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

	/* The patch needs to be built in direct RIP space, rather
	 * than in ThreadRip space.  That means we need to degrade the
	 * CFG. */
	CFG<ClientRip> *degradedCfg = convertCFGFromThreadRipToClientRips(cfg, neededThreads, exprDominatorMap);

	/* Figure out what slots to use for the various
	 * expressions. */
	slotMapT slotMap(exprStashPoints, happensBeforePoints);

	/* Now build the patch */
	EnforceCrashPatchFragment *pf = new EnforceCrashPatchFragment(slotMap, exprStashPoints, exprEvalPoints, happensBeforePoints);
	pf->fromCFG(degradedCfg);
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
		entryPoints.insert(ClientRip(it->second.rip, threads));
	}
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
