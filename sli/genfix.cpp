#include <map>
#include <set>

#include "sli.h"
#include "genfix.hpp"
#include "oracle.hpp"
#include "inferred_information.hpp"

void
__genfix_add_array_summary(std::vector<const char *> &out,
			   const char *t_ptr,
			   const char *nr_entries,
			   const char *table)
{
	out.push_back(
		vex_asprintf(
			"\t.%s = %s, .%s = sizeof(%s)/sizeof(%s[0]),\n",
			t_ptr,
			table,
			nr_entries,
			table,
			table));
}

class DcdCFG : public CFG<ThreadRip> {
	std::set<OracleRip> &neededInstructions;
public:
	bool instructionUseful(Instruction<ThreadRip> *i) { return neededInstructions.count(i->rip.rip) != 0; }
	DcdCFG(AddressSpace *as, std::set<OracleRip> &ni)
		: CFG<ThreadRip>(as), neededInstructions(ni)
	{}
};
char *
buildPatchForCrashSummary(Oracle *oracle, CrashSummary *summary, const char *ident)
{
	AddressSpace *as = oracle->ms->addressSpace;

	/* What instructions do we need to cover? */
	std::set<OracleRip> neededInstructions;
	summary->loadMachine->root->enumerateMentionedMemoryAccesses(neededInstructions);
	/* 5 bytes is the size of a 32-bit relative jump. */
	ThreadOracleRip root(summary->loadMachine->tid, oracle->dominator(neededInstructions, as, 5));
	if (!root.rip.rip) {
		fprintf(_logfile, "Patch generation fails because we can't find an appropriate dominating instruction for load machine.\n");
		return NULL;
	}
	for (std::vector<CrashSummary::StoreMachineData *>::iterator it = summary->storeMachines.begin();
	     it != summary->storeMachines.end();
	     it++)
		(*it)->machine->root->enumerateMentionedMemoryAccesses(neededInstructions);

	DcdCFG *cfg = new DcdCFG(as, neededInstructions);

	std::set<ThreadRip> roots;
	/* What are the entry points of the patch? */
	cfg->add_root(root, 100);
	roots.insert(root);
	for (std::vector<CrashSummary::StoreMachineData *>::iterator it = summary->storeMachines.begin();
	     it != summary->storeMachines.end();
	     it++) {
		std::set<OracleRip> instrs;
		(*it)->machine->root->enumerateMentionedMemoryAccesses(instrs);
		ThreadOracleRip r((*it)->machine->tid, oracle->dominator(instrs, as, 5));
		if (!r.rip.rip) {
			fprintf(_logfile, "Patch generation fails because we can't find an appropriate dominator instruction for one of the store machines.\n");
			return NULL;
		}
		cfg->add_root(r, 100);
		roots.insert(r);
	}
	try {
		cfg->doit();
	} catch (NotImplementedException &e) {
		/* This means that there's some instruction we can't
		   decode.  Dump a diagnostic and just continue on. */
		fprintf(_logfile,
			"Cannot build patch for crash summary.  Instruction decoder said %s\n",
			e.what());
		return NULL;
	}
	PatchFragment<ThreadRip> *pf = new PatchFragment<ThreadRip>(roots);
	pf->fromCFG(cfg);

	return pf->asC(ident);
}

unsigned long __trivial_hash_function(const ThreadRip &k)
{
	return k.rip;
}

unsigned long __trivial_hash_function(const unsigned long &k)
{
	return k;
}

char *
flattenStringFragments(std::vector<const char *> fragments)
{
	size_t sz = 1;
	for (unsigned x = 0; x < fragments.size(); x++)
		sz += strlen(fragments[x]);
	char *res = (char *)LibVEX_Alloc_Bytes(sz);
	char *cursor = res;
	for (unsigned x = 0; x < fragments.size(); x++) {
		memcpy(cursor, fragments[x], strlen(fragments[x]));
		cursor += strlen(fragments[x]);
	}
	*cursor = 0;
	assert(cursor == res + sz-1);
	return res;
}

const RegisterIdx RegisterIdx::RAX(0);
const RegisterIdx RegisterIdx::RCX(1);
const RegisterIdx RegisterIdx::RDX(2);
const RegisterIdx RegisterIdx::RBX(3);
const RegisterIdx RegisterIdx::RSP(4);
const RegisterIdx RegisterIdx::RBP(5);
const RegisterIdx RegisterIdx::RSI(6);
const RegisterIdx RegisterIdx::RDI(7);
const RegisterIdx RegisterIdx::R8(8);
const RegisterIdx RegisterIdx::R9(9);
const RegisterIdx RegisterIdx::R10(10);
const RegisterIdx RegisterIdx::R11(11);
const RegisterIdx RegisterIdx::R12(12);
const RegisterIdx RegisterIdx::R13(13);
const RegisterIdx RegisterIdx::R14(14);
const RegisterIdx RegisterIdx::R15(15);

RegisterIdx
RegisterIdx::fromVexOffset(unsigned offset)
{
	switch (offset) {
#define do_case(n)				\
	case OFFSET_amd64_ ## n: return n
		do_case(RAX);
		do_case(RCX);
		do_case(RDX);
		do_case(RBX);
		do_case(RSP);
		do_case(RBP);
		do_case(RSI);
		do_case(RDI);
		do_case(R8);
		do_case(R9);
		do_case(R10);
		do_case(R11);
		do_case(R12);
		do_case(R13);
		do_case(R14);
		do_case(R15);
#undef do_case
	default:
		abort();
	}
}

ModRM
ModRM::absoluteAddress(int address)
{
	ModRM res;
	/* modrm byte: mod = 0, rm = 4 */
	res.content.push_back(4);
	/* SIB byte.  base = 5, scale = 0, index = 4 */
	res.content.push_back(0x25);
	/* Displacement */
	unsigned char asBytes[4];
	toBytes(address, asBytes);
	for (unsigned x = 0; x < 4; x++)
		res.content.push_back(asBytes[x]);
	return res;
}

ModRM
ModRM::memAtRegisterPlusOffset(RegisterIdx reg, int offset)
{
	ModRM res;
	if (reg.idx >= 8) {
		res.extendRm = true;
		reg.idx -= 8;
	} else {
		res.extendRm = false;
	}

	if (offset == 0) {
		switch (reg.idx) {
		case 0: case 1: case 2: case 3: case 6: case 7:
			/* mod = 0, rm = register */
			res.content.push_back(reg.idx);
			break;
		case 4: 
			/* Use a SIB */
			res.content.push_back(0x04);
			/* base = 4, scale = 0, index = 4. */
			res.content.push_back(0x24);
			break;
		case 5:
			goto encode_8bit_offset;
		default:
			abort();
		}
	} else if (offset >= -0x80 && offset < 0x80) {
	encode_8bit_offset:
		switch (reg.idx) {
		case 0: case 1: case 2: case 3: case 5: case 6: case 7:
			/* mod = 1, rm = register */
			res.content.push_back(reg.idx | 0x40);
			break;
		case 4:
			/* mod = 1, rm = 4 */
			res.content.push_back(0x44);
			/* SIB byte, base = 4, scale = 0, index = 4 */
			res.content.push_back(0x24);
			break;
		default:
			abort();
		}
		/* 8 bit displacement */
		res.content.push_back(offset);
	} else {
		switch (reg.idx) {
		case 0: case 1: case 2: case 3: case 5: case 6: case 7:
			/* mod = 2, rm = register */
			res.content.push_back(reg.idx | 0x80);
			break;
		case 4:
			/* mod = 2, rm = 4 */
			res.content.push_back(0x84);
			/* SIB byte, base = 4, scale = 0, index = 4 */
			res.content.push_back(0x24);
			break;
		default:
			abort();
		}
		unsigned char asBytes[4];
		toBytes(offset, asBytes);
		for (unsigned x = 0; x < 4; x++)
			res.content.push_back(asBytes[x]);
	}
	return res;
}

ModRM
ModRM::directRegister(RegisterIdx reg)
{
	ModRM res;
	if (reg.idx >= 8) {
		res.extendRm = true;
		reg.idx -= 8;
	} else {
		res.extendRm = false;
	}
	assert(reg.idx < 8);
	/* mod = 3, rm = register */
	res.content.push_back(0xc0 | reg.idx);
	return res;
}

bool
ModRM::isRegister() const
{
	unsigned modrm = content[0];
	unsigned mod = modrm >> 6;
	return mod == 3;
}

RegisterIdx
ModRM::getRegister() const
{
	unsigned res;
	if (extendRm)
		res = 8;
	else
		res = 0;
	assert((content[0] & 0xc0) == 0xc0);
	res |= content[0];
	return RegisterIdx::fromRaw(res);
}

RegisterIdx
ModRM::selectNonConflictingRegister() const
{
	unsigned conflictingRegisters[4] = {};
	int nr_conflicting = 1;
	unsigned modrm = content[0];
	unsigned mod = modrm >> 6;
	unsigned rm = modrm & 7;
	unsigned sib;
	unsigned index;
	unsigned base;
	unsigned res;

	if (extendRm)
		rm |= 8;
	switch (mod) {
	case 0:
		if (rm == 4 || rm == 12)
			goto sib;
		if (rm != 5 && rm != 13)
			conflictingRegisters[nr_conflicting++] = rm;
		break;
	case 1:
	case 2:
		if (rm == 4 || rm == 12)
			goto sib;
		conflictingRegisters[nr_conflicting++] = rm;
		break;
	case 3:
		conflictingRegisters[nr_conflicting++] = rm;
		break;
	default:
		abort();
	}
	goto no_sib;
	
sib:
	sib = content[1];
	index = (sib >> 3) & 7;
	base = sib & 7;

	if (extendIndex)
		index |= 8;
	if (extendRm)
		base |= 8;
	if ((base != 5 && base != 13) || mod != 0)
		conflictingRegisters[nr_conflicting++] = base;
	if (index != 4)
		conflictingRegisters[nr_conflicting++] = index;

no_sib:
	/* So now we have a list of all of the possibly-conflicting
	   registers, so it should be pretty easy to pick one which
	   doesn't conflict. */
	for (res = 0; res < 16; res++) {
		bool is_good = true;
		for (int i = 0; is_good && i < nr_conflicting; i++)
			if (conflictingRegisters[i] == res)
				is_good = false;
		if (is_good)
			break;
	}
	assert(res != 16);
	return RegisterIdx::fromRaw(res);
}

ModRM
ModRM::fromBytes(const unsigned char *content)
{
	unsigned modrm = content[0];
	unsigned mod = modrm >> 6;
	unsigned rm = modrm & 7;
	unsigned disp;
	bool have_sib = false;

	have_sib = (rm == 4);
	switch (mod) {
	case 0:
		if (rm == 5) {
			disp = 4;
		} else {
			disp = 0;
		}
		break;
	case 1:
		disp = 1;
		break;
	case 2:
		disp = 4;
		break;
	case 3:
		disp = 0;
		have_sib = false;
		break;
	default:
		abort();
	}
	ModRM res;
	res.content.resize(1 + have_sib + disp);
	for (unsigned idx = 0; idx < res.content.size(); idx++)
		res.content[idx] = content[idx];
	return res;
}
