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

unsigned long __trivial_hash_function(const ThreadRip &k)
{
	return k.rip.hash();
}

unsigned long __trivial_hash_function(const unsigned long &k)
{
	return k;
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

/* Convert an int to its constituent bytes, in little-endian order. */
static void
toBytes(int i, unsigned char b[4])
{
	union {
		unsigned char asBytes[4];
		int j;
	};
	j = i;
	b[0] = asBytes[0];
	b[1] = asBytes[1];
	b[2] = asBytes[2];
	b[3] = asBytes[3];
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
