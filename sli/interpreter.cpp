#include <string.h>

extern "C" {
#include "libvex.h"
#include "libvex_ir.h"
#include "libvex_emwarn.h"
#include "libvex_guest_amd64.h"
#include "guest_generic_bb_to_IR.h"
#include "guest_amd64_defs.h"
};

#include "sli.h"

template <typename underlying> class PointerKeeper {
	underlying *x;
public:
	~PointerKeeper() { delete x; }
	PointerKeeper(underlying *y) : x(y) {}
};

template <typename underlying> class PointerKeeperArr {
	underlying *x;
public:
	~PointerKeeperArr() { delete [] x; }
	PointerKeeperArr(underlying *y) : x(y) {}
};

static Bool chase_into_ok(void *ignore1, Addr64 ignore2)
{
	return False;
}

struct abstract_interpret_value {
	unsigned long v;
	void *origin;
};

struct expression_result {
	struct abstract_interpret_value lo;
	struct abstract_interpret_value hi;
};

#define REG_LAST 128

#define tl_assert(x) assert(x)
#define expr_const(x) NULL
#define ASSUME assert

static unsigned long *
get_reg(Thread *state, unsigned offset)
{
	tl_assert(!(offset % 8));
	tl_assert(offset < sizeof(state->regs.regs));
	return &((unsigned long *)&state->regs.regs)[offset/8];
}

static const struct expression *
read_reg(Thread *state, unsigned offset, unsigned long *v)
{
	*v = *get_reg(state, offset);
	return NULL;
}

static void
write_reg(Thread *state, unsigned offset, unsigned long v)
{
	*get_reg(state, offset) = v;
}

static void
eval_expression(struct expression_result *temporaries,
		Thread *thr,
		struct expression_result *dest,
		IRExpr *expr)
{
#define ORIGIN(x)

	dest->lo.v = 0xdeadbeeff001f001;
	dest->hi.v = 0xaaaaaaaaaaaaaaaa;

	switch (expr->tag) {
	case Iex_Get: {
		unsigned long v1;
		const struct expression *src1;
		unsigned sub_word_offset = expr->Iex.Get.offset & 7;
		src1 = read_reg(thr,
				expr->Iex.Get.offset - sub_word_offset,
				&v1);
		switch (expr->Iex.Get.ty) {
		case Ity_I64:
			tl_assert(!sub_word_offset);
			dest->lo.v = v1;
			break;
		case Ity_V128:
			tl_assert(!sub_word_offset);
			dest->lo.v = v1;
			read_reg(thr,
				 expr->Iex.Get.offset - sub_word_offset,
				 &dest->hi.v);
			break;
		case Ity_I32:
			tl_assert(!(sub_word_offset % 4));
			dest->lo.v = (v1 >> (sub_word_offset * 8)) & 0xffffffff;
			break;
		case Ity_I16:
			tl_assert(!(sub_word_offset % 2));
			dest->lo.v = (v1 >> (sub_word_offset * 8)) & 0xffff;
			break;
		case Ity_I8:
			dest->lo.v = (v1 >> (sub_word_offset * 8)) & 0xff;
			break;
		default:
			abort();
		}
		break;
	}

	case Iex_RdTmp:
		*dest = temporaries[expr->Iex.RdTmp.tmp];
		break;

	case Iex_Const: {
		IRConst *cnst = expr->Iex.Const.con;
		dest->lo.origin = NULL;
		dest->hi.origin = NULL;
		switch (cnst->tag) {
		case Ico_U1:
			dest->lo.v = cnst->Ico.U1;
			break;
		case Ico_U8:
			dest->lo.v = cnst->Ico.U8;
			break;
		case Ico_U16:
			dest->lo.v = cnst->Ico.U16;
			break;
		case Ico_U32:
			dest->lo.v = cnst->Ico.U32;
			break;
		case Ico_U64:
		case Ico_F64:
		case Ico_F64i:
			dest->lo.v = cnst->Ico.U64;
			break;
		case Ico_V128:
			dest->lo.v = cnst->Ico.V128;
			dest->lo.v = dest->lo.v | (dest->lo.v << 16) | (dest->lo.v << 32) | (dest->lo.v << 48);
			dest->hi.v = dest->lo.v;
			dest->hi.origin = expr_const(dest->hi.v);
			break;
		default:
			ASSUME(0);
		}
		dest->lo.origin = expr_const(dest->lo.v);
		break;
	}

	case Iex_Binop: {
		struct expression_result arg1;
		struct expression_result arg2;
		eval_expression(temporaries, thr, &arg1, expr->Iex.Binop.arg1);
		eval_expression(temporaries, thr, &arg2, expr->Iex.Binop.arg2);
		switch (expr->Iex.Binop.op) {
		case Iop_Sub64:
			dest->lo.v = arg1.lo.v - arg2.lo.v;
			ORIGIN(expr_sub(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Sub32:
			dest->lo.v = (arg1.lo.v - arg2.lo.v) & 0xffffffff;
			ORIGIN(expr_and(expr_sub(arg1.lo.origin, arg2.lo.origin),
					expr_const(0xffffffff)));
			break;
		case Iop_Sub8:
			dest->lo.v = (arg1.lo.v - arg2.lo.v) & 0xff;
			ORIGIN(expr_and(expr_sub(arg1.lo.origin, arg2.lo.origin),
					expr_const(0xff)));
			break;
		case Iop_Add64:
			dest->lo.v = arg1.lo.v + arg2.lo.v;
			ORIGIN(expr_add(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Add64x2:
			dest->lo.v = arg1.lo.v + arg2.lo.v;
			dest->hi.v = arg1.hi.v + arg2.hi.v;
			break;
		case Iop_Add32:
			dest->lo.v = (arg1.lo.v + arg2.lo.v) & 0xffffffff;
			ORIGIN(expr_and(expr_add(arg1.lo.origin, arg2.lo.origin),
					expr_const(0xffffffff)));
			break;
		case Iop_And64:
		case Iop_And32:
		case Iop_And8:
			dest->lo.v = arg1.lo.v & arg2.lo.v;
			ORIGIN(expr_and(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Or8:
		case Iop_Or32:
		case Iop_Or64:
			dest->lo.v = arg1.lo.v | arg2.lo.v;
			ORIGIN(expr_or(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Shl32:
			dest->lo.v = (arg1.lo.v << arg2.lo.v) & 0xffffffff;
			ORIGIN(expr_and(expr_shl(arg1.lo.origin, arg2.lo.origin),
					expr_const(0xffffffff)));
			break;
		case Iop_Shl64:
			dest->lo.v = arg1.lo.v << arg2.lo.v;
			ORIGIN(expr_shl(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Sar64:
			dest->lo.v = (long)arg1.lo.v >> arg2.lo.v;
			ORIGIN(expr_shra(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Shr64:
			dest->lo.v = arg1.lo.v >> arg2.lo.v;
			ORIGIN(expr_shrl(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Xor64:
		case Iop_Xor32:
			dest->lo.v = arg1.lo.v ^ arg2.lo.v;
			ORIGIN(expr_xor(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_CmpNE8:
			dest->lo.v = arg1.lo.v != arg2.lo.v;
			ORIGIN(expr_not(expr_eq(arg1.lo.origin, arg2.lo.origin)));
			break;
		case Iop_CmpEQ8:
		case Iop_CmpEQ16:
		case Iop_CmpEQ32:
		case Iop_CmpEQ64:
			dest->lo.v = arg1.lo.v == arg2.lo.v;
			ORIGIN(expr_eq(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_CmpNE32:
		case Iop_CasCmpNE32:
		case Iop_CmpNE64:
			dest->lo.v = arg1.lo.v != arg2.lo.v;
			ORIGIN(expr_not(expr_eq(arg1.lo.origin, arg2.lo.origin)));
			break;
		case Iop_CmpLE64U:
			dest->lo.v = arg1.lo.v <= arg2.lo.v;
			ORIGIN(expr_be(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_CmpLE64S:
			dest->lo.v = (long)arg1.lo.v <= (long)arg2.lo.v;
			ORIGIN(expr_le(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_CmpLT64S:
			dest->lo.v = (long)arg1.lo.v < (long)arg2.lo.v;
			ORIGIN(expr_and(expr_le(arg1.lo.origin, arg2.lo.origin),
					expr_not(expr_eq(arg1.lo.origin, arg2.lo.origin))));
			break;
		case Iop_CmpLT64U:
			dest->lo.v = arg1.lo.v < arg2.lo.v;
			ORIGIN(expr_b(arg1.lo.origin, arg2.lo.origin));
			break;
		case Iop_Mul64:
			dest->lo.v = arg1.lo.v * arg2.lo.v;
			ORIGIN(expr_mul(arg1.lo.origin, arg2.lo.origin));
			break;

		case Iop_MullU32: {
			dest->lo.v = arg1.lo.v * arg2.lo.v;
			break;
		}
		case Iop_MullS32: {
			dest->lo.v = (long)(int)arg1.lo.v * (long)(int)arg2.lo.v;
			break;
		}

		case Iop_MullU64: {
			unsigned long a1, a2, b1, b2;
			dest->lo.v = arg1.lo.v * arg2.lo.v;
			a1 = arg1.lo.v & 0xffffffff;
			a2 = arg1.lo.v >> 32;
			b1 = arg2.lo.v & 0xffffffff;
			b2 = arg2.lo.v >> 32;
			dest->hi.v = a2 * b2 +
				( (a1 * b2 + a2 * b1 +
				   ((a1 * b1) >> 32)) >> 32);
			break;
		}
		case Iop_32HLto64:
			dest->lo.v = (arg1.lo.v << 32) | arg2.lo.v;
			ORIGIN(expr_or(expr_shl(arg1.lo.origin,
						expr_const(32)),
				       arg2.lo.origin));
			break;

		case Iop_64HLtoV128:
		case Iop_64HLto128:
			dest->lo.v = arg2.lo.v;
			dest->hi.v = arg1.lo.v;
			break;

		case Iop_DivModU64to32:
			dest->lo.v = (arg1.lo.v / arg2.lo.v) |
				((arg1.lo.v % arg2.lo.v) << 32);
			break;

		case Iop_DivModU128to64:
			/* arg1 is a I128, arg2 is an I64, result is
			   128 bits and has the dividend in its low 64
			   bits and the modulus in its high 64
			   bits. */
			asm ("div %4\n"
			     : "=a" (dest->lo.v), "=d" (dest->hi.v)
			     : "0" (arg1.lo.v), "1" (arg1.hi.v), "r" (arg2.lo.v));
			break;

		case Iop_DivModS128to64:
			asm ("idiv %4\n"
			     : "=a" (dest->lo.v), "=d" (dest->hi.v)
			     : "0" (arg1.lo.v), "1" (arg1.hi.v), "r" (arg2.lo.v));
			break;

		case Iop_Add32x4:
			dest->lo.v = ((arg1.lo.v + arg2.lo.v) & 0xffffffff) +
				((arg1.lo.v & ~0xfffffffful) + (arg2.lo.v & ~0xfffffffful));
			dest->hi.v = ((arg1.hi.v + arg2.hi.v) & 0xffffffff) +
				((arg1.hi.v & ~0xfffffffful) + (arg2.hi.v & ~0xfffffffful));
			break;

		case Iop_InterleaveLO64x2:
			dest->lo.v = arg2.lo.v;
			dest->hi.v = arg1.lo.v;
			break;

		case Iop_InterleaveHI64x2:
			dest->lo.v = arg2.hi.v;
			dest->hi.v = arg1.hi.v;
			break;

		case Iop_InterleaveLO32x4:
			dest->lo.v = (arg2.lo.v & 0xffffffff) | (arg1.lo.v << 32);
			dest->hi.v = (arg2.lo.v >> 32) | (arg1.lo.v & 0xffffffff00000000ul);
			break;

		case Iop_InterleaveHI32x4:
			dest->lo.v = (arg2.hi.v & 0xffffffff) | (arg1.hi.v << 32);
			dest->hi.v = (arg2.hi.v >> 32) | (arg1.hi.v & 0xffffffff00000000ul);
			break;

		case Iop_ShrN64x2:
			dest->lo.v = arg1.lo.v >> arg2.lo.v;
			dest->hi.v = arg1.hi.v >> arg2.lo.v;
			break;

		case Iop_ShlN64x2:
			dest->lo.v = arg1.lo.v << arg2.lo.v;
			dest->hi.v = arg1.hi.v << arg2.lo.v;
			break;

		case Iop_CmpGT32Sx4:
			dest->lo.v = 0;
			dest->hi.v = 0;
			if ( (int)arg1.lo.v > (int)arg2.lo.v )
				dest->lo.v |= 0xffffffff;
			if ( (int)(arg1.lo.v >> 32) > (int)(arg2.lo.v >> 32) )
				dest->lo.v |= 0xffffffff00000000;
			if ( (int)arg1.hi.v > (int)arg2.hi.v )
				dest->hi.v |= 0xffffffff;
			if ( (int)(arg1.hi.v >> 32) > (int)(arg2.hi.v >> 32) )
				dest->hi.v |= 0xffffffff00000000;
			break;

		default:
			abort();
		}
		break;
	}

	case Iex_Unop: {
		struct expression_result arg;
		eval_expression(temporaries, thr, &arg, expr->Iex.Unop.arg);
		switch (expr->Iex.Unop.op) {
		case Iop_64HIto32:
			dest->lo.v = arg.lo.v >> 32;
			ORIGIN(expr_shrl(arg.lo.origin, expr_const(32)));
			break;
		case Iop_64to32:
			dest->lo.v = arg.lo.v & 0xffffffff;
			ORIGIN(expr_and(arg.lo.origin, expr_const(0xfffffffful)));
			break;
		case Iop_64to16:
			dest->lo.v = arg.lo.v & 0xffff;
			ORIGIN(expr_and(arg.lo.origin, expr_const(0xffff)));
			break;
		case Iop_64to8:
			dest->lo.v = arg.lo.v & 0xff;
			ORIGIN(expr_and(arg.lo.origin, expr_const(0xff)));
			break;
		case Iop_128to64:
		case Iop_V128to64:
			dest->lo.v = arg.lo.v;
			ORIGIN(arg.lo.origin);
			break;
		case Iop_64to1:
			dest->lo.v = arg.lo.v & 1;
			ORIGIN(expr_and(arg.lo.origin, expr_const(1)));
			break;
		case Iop_32Uto64:
		case Iop_16Uto64:
		case Iop_16Uto32:
		case Iop_1Uto64:
		case Iop_1Uto8:
		case Iop_8Uto32:
		case Iop_8Uto64:
			*dest = arg;
			break;
		case Iop_32Sto64:
			dest->lo.v = (long)(int)arg.lo.v;
			ORIGIN(expr_shra(expr_shl(arg.lo.origin,
						  expr_const(32)),
					 expr_const(32)));
			break;
		case Iop_8Sto64:
			dest->lo.v = (long)(signed char)arg.lo.v;
			ORIGIN(expr_shra(expr_shl(arg.lo.origin,
						  expr_const(56)),
					 expr_const(56)));
			break;
		case Iop_8Sto32:
			dest->lo.v = (int)(signed char)arg.lo.v;
			ORIGIN(expr_and(expr_shra(expr_shl(arg.lo.origin,
							   expr_const(56)),
						  expr_const(56)),
					expr_const(0xffffffff)));
			break;
		case Iop_16Sto64:
			dest->lo.v = (long)(short)arg.lo.v;
			ORIGIN(expr_shra(expr_shl(arg.lo.origin,
						  expr_const(48)),
					 expr_const(48)));
			break;
		case Iop_128HIto64:
		case Iop_V128HIto64:
			dest->lo.v = arg.hi.v;
			tl_assert(arg.hi.origin != NULL);
			ORIGIN(arg.hi.origin);
			break;

		case Iop_Not1:
			dest->lo.v = !arg.lo.v;
			ORIGIN(expr_and(expr_not(arg.lo.origin),
					expr_const(1)));
			break;

		case Iop_Not32:
			dest->lo.v = ~arg.lo.v & 0xffffffff;
			ORIGIN(expr_and(expr_not(arg.lo.origin),
					expr_const(0xffffffff)));
			break;

		case Iop_Not64:
			dest->lo.v = ~arg.lo.v;
			ORIGIN(expr_not(arg.lo.origin));
			break;

		default:
			abort();
		}
		break;
	}

	case Iex_Mux0X: {
		struct expression_result cond;
		struct expression_result res0;
		struct expression_result resX;
		struct expression_result *choice;
		eval_expression(temporaries, thr, &cond, expr->Iex.Mux0X.cond);
		tl_assert(!cond.hi.origin);
		eval_expression(temporaries, thr, &res0, expr->Iex.Mux0X.expr0);
		eval_expression(temporaries, thr, &resX, expr->Iex.Mux0X.exprX);
		if (cond.lo.v == 0) {
			choice = &res0;
		} else {
			choice = &resX;
		}
		*dest = *choice;
		break;
	}

	case Iex_CCall: {
//		do_ccall(state, dest, expr->Iex.CCall.cee,
//			 expr->Iex.CCall.retty, expr->Iex.CCall.args);
		break;
	}

	default:
		printf("Bad expression tag %x\n", expr->tag);
		abort();
	}
#undef ORIGIN
}

void Interpreter::replayFootstep(const LogRecordFootstep &lrf)
{
	Thread *thr = currentState->findThread(lrf.thread());

	if (thr->regs.rip() != lrf.rip)
		throw ReplayFailedBadRip(thr->regs.rip(), lrf.rip);

	const void *code = currentState->addressSpace->getRawPointerUnsafe(thr->regs.rip());

	VexArchInfo archinfo_guest;
	VexAbiInfo abiinfo_both;
	VexGuestExtents vge;
	LibVEX_default_VexArchInfo(&archinfo_guest);
	LibVEX_default_VexAbiInfo(&abiinfo_both);
	abiinfo_both.guest_stack_redzone_size = 128;
	IRSB *irsb = bb_to_IR(&vge,
			      NULL, /* Context for chase_into_ok */
			      disInstr_AMD64,
			      (UChar *)code,
			      (Addr64)thr->regs.rip(),
			      chase_into_ok,
			      False, /* host bigendian */
			      VexArchAMD64,
			      &archinfo_guest,
			      &abiinfo_both,
			      Ity_I64, /* guest word type */
			      False, /* do_self_check */
			      NULL, /* preamble */
			      0, /* self check start */
			      0); /* self check len */
	if (!irsb)
		throw InstructionDecodeFailedException();

	ppIRSB(irsb);

	struct expression_result *temporaries = new expression_result[irsb->tyenv->types_used];
	memset(temporaries,
	       0,
	       sizeof(temporaries[0]) * irsb->tyenv->types_used);
	PointerKeeperArr<expression_result> pkt(temporaries);

	for (int stmt_nr = 0; stmt_nr < irsb->stmts_used; stmt_nr++) {
		IRStmt *stmt = irsb->stmts[stmt_nr];
		switch (stmt->tag) {
		case Ist_NoOp:
			break;
		case Ist_IMark:
			break;
		case Ist_AbiHint:
			break;
		case Ist_MBE:
			break;
		case Ist_WrTmp:
			eval_expression(temporaries,
					thr,
					&temporaries[stmt->Ist.WrTmp.tmp],
					stmt->Ist.WrTmp.data);
			break;

		case Ist_Store: {
			assert(stmt->Ist.Store.end == Iend_LE);
			assert(stmt->Ist.Store.resSC == IRTemp_INVALID);
			struct expression_result data;
			struct expression_result addr;
			eval_expression(temporaries, thr, &data, stmt->Ist.Store.data);
			eval_expression(temporaries, thr, &addr, stmt->Ist.Store.addr);
			unsigned size = sizeofIRType(typeOfIRExpr(irsb->tyenv,
								  stmt->Ist.Store.data));
			if (size <= 8) {
				currentState->addressSpace->writeMemory(addr.lo.v,
									size,
									&data.lo.v);
			} else if (size == 16) {
				currentState->addressSpace->writeMemory(addr.lo.v,
									8,
									&data.lo.v);
				currentState->addressSpace->writeMemory(addr.lo.v + 8,
									8,
									&data.hi.v);
			} else {
				abort();
			}
			break;
		}

		case Ist_Put: {
			unsigned byte_offset = stmt->Ist.Put.offset & 7;
			unsigned long *dest =
				get_reg(thr,
					stmt->Ist.Put.offset - byte_offset);
			struct expression_result data;

			eval_expression(temporaries, thr, &data, stmt->Ist.Put.data);
			switch (typeOfIRExpr(irsb->tyenv, stmt->Ist.Put.data)) {
			case Ity_I8:
				*dest &= ~(0xFF << (byte_offset * 8));
				*dest |= data.lo.v << (byte_offset * 8);
				break;

			case Ity_I16:
				tl_assert(!(byte_offset % 2));
				*dest &= ~(0xFFFF << (byte_offset * 8));
				*dest |= data.lo.v << (byte_offset * 8);
				break;

			case Ity_I64:
				tl_assert(byte_offset == 0);
				*dest = data.lo.v;
				break;

			case Ity_I128:
			case Ity_V128:
				tl_assert(byte_offset == 0);
				*dest = data.lo.v;
				*get_reg(thr,
					 stmt->Ist.Put.offset + 8) =
					data.hi.v;
				break;
			default:
				abort();
			}
			break;
		}

		case Ist_Exit: {
			struct expression_result guard;
			if (stmt->Ist.Exit.guard) {
				eval_expression(temporaries, thr, &guard, stmt->Ist.Exit.guard);
				if (!guard.lo.v)
					break;
			}
			tl_assert(stmt->Ist.Exit.jk == Ijk_Boring);
			tl_assert(stmt->Ist.Exit.dst->tag == Ico_U64);
			thr->regs.regs.guest_RIP = stmt->Ist.Exit.dst->Ico.U64;
			goto finished_block;
		}

		default:
			printf("Don't know how to interpret statement ");
			ppIRStmt(stmt);
			abort();
			break;
		}
	}

	assert(irsb->jumpkind == Ijk_Boring ||
	       irsb->jumpkind == Ijk_Call ||
	       irsb->jumpkind == Ijk_Ret);

	{
		struct expression_result next_addr;
		eval_expression(temporaries, thr, &next_addr, irsb->next);
		tl_assert(next_addr.hi.origin == NULL);
		thr->regs.regs.guest_RIP = next_addr.lo.v;
	}

finished_block:
	return;
}

void Interpreter::replayLogfile(LogReader const *lf, LogReader::ptr ptr)
{
	LogRecord *lr;

	while (1) {
		lr = lf->read(ptr, &ptr);
		if (!lr)
			break;
		PointerKeeper<LogRecord> k(lr);
		if (LogRecordFootstep *lrf = dynamic_cast<LogRecordFootstep *>(lr))
			replayFootstep(*lrf);
		else
			abort();
	}
}

Thread::Thread(LogRecordInitialRegisters const&lrir)
	: regs(lrir.regs)
{
}
