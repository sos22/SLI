#include "sli.h"
#include "enforce_crash.hpp"

#define BASE_MESSAGE_ID 0xaabb
unsigned happensBeforeEdge::next_msg_id = BASE_MESSAGE_ID;

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

EnforceCrashPatchFragment::jcc_code EnforceCrashPatchFragment::jcc_code::zero(0x84);
EnforceCrashPatchFragment::jcc_code EnforceCrashPatchFragment::jcc_code::nonzero(0x85);

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

