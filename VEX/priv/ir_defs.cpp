
/*---------------------------------------------------------------*/
/*---                                                         ---*/
/*--- This file (ir_defs.c) is                                ---*/
/*--- Copyright (C) OpenWorks LLP.  All rights reserved.      ---*/
/*---                                                         ---*/
/*---------------------------------------------------------------*/

/*
   This file is part of LibVEX, a library for dynamic binary
   instrumentation and translation.

   Copyright (C) 2004-2009 OpenWorks LLP.  All rights reserved.

   This library is made available under a dual licensing scheme.

   If you link LibVEX against other code all of which is itself
   licensed under the GNU General Public License, version 2 dated June
   1991 ("GPL v2"), then you may use LibVEX under the terms of the GPL
   v2, as appearing in the file LICENSE.GPL.  If the file LICENSE.GPL
   is missing, you can obtain a copy of the GPL v2 from the Free
   Software Foundation Inc., 51 Franklin St, Fifth Floor, Boston, MA
   02110-1301, USA.

   For any other uses of LibVEX, you must first obtain a commercial
   license from OpenWorks LLP.  Please contact info@open-works.co.uk
   for information about commercial licensing.

   This software is provided by OpenWorks LLP "as is" and any express
   or implied warranties, including, but not limited to, the implied
   warranties of merchantability and fitness for a particular purpose
   are disclaimed.  In no event shall OpenWorks LLP be liable for any
   direct, indirect, incidental, special, exemplary, or consequential
   damages (including, but not limited to, procurement of substitute
   goods or services; loss of use, data, or profits; or business
   interruption) however caused and on any theory of liability,
   whether in contract, strict liability, or tort (including
   negligence or otherwise) arising in any way out of the use of this
   software, even if advised of the possibility of such damage.

   Neither the names of the U.S. Department of Energy nor the
   University of California nor the names of its contributors may be
   used to endorse or promote products derived from this software
   without prior written permission.
*/
#include <ctype.h>
#include <stdarg.h>

#include <algorithm>
#include <vector>

#include "libvex_basictypes.h"
#include "libvex_ir.h"
#include "libvex_parse.h"
#include "libvex.h"

#include "libvex_guest_offsets.h"

#include "main_util.h"

Heap ir_heap;

#include "libvex_prof.hpp"

IRStmtNoOp IRStmtNoOp::singleton;
IRStmtStartAtomic IRStmtStartAtomic::singleton;
IRStmtEndAtomic IRStmtEndAtomic::singleton;

const IRExpr *IRExpr::no_tag_expr;

/* Returns true if the operation definitely associates in the sense
 * that (a op b) op c == a op (b op c), or false if we're not sure. */
bool
operationAssociates(IROp op)
{
	return (op >= Iop_Add8 && op <= Iop_Add64) || (op == Iop_And1) ||
		(op >= Iop_And8 && op <= Iop_And64) || (op >= Iop_Xor8 && op <= Iop_Xor64) ||
		(op >= Iop_Or8 && op <= Iop_Or64) || (op == Iop_Or1);
}

/*---------------------------------------------------------------*/
/*--- Printing the IR                                         ---*/
/*---------------------------------------------------------------*/
const char *nameIRType(IRType ty)
{
   switch (ty) {
      case Ity_INVALID: return "Ity_INVALID";
      case Ity_I1:      return "I1";
      case Ity_I8:      return "I8";
      case Ity_I16:     return "I16";
      case Ity_I32:     return "I32";
      case Ity_I64:     return "I64";
      case Ity_I128:    return "I128";
   }
   return vex_asprintf("ty(0x%x)", ty);
}

void ppIRType ( IRType ty, FILE *f )
{
  fprintf(f, "%s", nameIRType(ty));
}

bool parseIRType(IRType *out, const char *str, const char **suffix)
{
#define do_type(n)					\
  if (parseThisString( #n , str, suffix)) {		\
    *out = Ity_ ## n;					\
    return true;					\
  }
  if (parseThisString( "Ity_INVALID" , str, suffix)) { 
    *out = Ity_INVALID;
    return true;
  }

  do_type(I8);
  do_type(I16);
  do_type(I32);
  do_type(I64);
  do_type(I128);
  do_type(I1);
#undef do_type
  return false;
}

static void ppIRConst ( const IRExprConst *con, FILE* f )
{
   vassert(sizeof(ULong) == sizeof(Double));
   switch (con->ty) {
      case Ity_I1:   fprintf(f,  "%d:I1",        con->Ico.U1 ? 1 : 0); return;
      case Ity_I8:   fprintf(f,  "0x%x:I8",      (UInt)(con->Ico.U8)); return;
      case Ity_I16:  fprintf(f,  "0x%x:I16",     (UInt)(con->Ico.U16)); return;
      case Ity_I32:  fprintf(f,  "0x%x:I32",     (UInt)(con->Ico.U32)); return;
      case Ity_I64:  fprintf(f,  "0x%llx:I64",   (ULong)(con->Ico.U64)); return;
      case Ity_I128: fprintf(f,  "U128{0x%llx, 0x%llx}", con->Ico.U128.hi, con->Ico.U128.lo); return;
      case Ity_INVALID:
	break;
   }
   abort();
}

static bool parseIRConst(IRExprConst **out, const char *str, const char **suffix)
{
  int val1;
  unsigned long val2;
  const char *str2;

  if (parseDecimalInt(&val1, str, &str2) &&
      parseThisString(":I1", str2, suffix)) {
    *out = IRExpr_Const_U1(val1);
    return true;
  }
  if (parseThisString("0x", str, &str2) &&
      parseHexUlong(&val2, str2, &str)) {
    *out = NULL;
    if (parseThisString(":I8", str, suffix))
      *out = IRExpr_Const_U8(val2);
    else if (parseThisString(":I16", str, suffix))
      *out = IRExpr_Const_U16(val2);
    else if (parseThisString(":I32", str, suffix))
      *out = IRExpr_Const_U32(val2);
    else if (parseThisString(":I64", str, suffix))
      *out = IRExpr_Const_U64(val2);
    if (*out)
      return true;
  }
  if (parseThisString("F64{0x", str, &str) &&
      parseHexUlong(&val2, str, &str) &&
      parseThisChar('}', str, suffix)) {
    union { ULong x; Double y; } u;
    u.x = val2;
    *out = IRExpr_Const_F64(u.y);
    return true;
  }
  if (parseThisString("F64i{0x", str, &str) &&
      parseHexUlong(&val2, str, &str) &&
      parseThisChar('}', str, suffix)) {
    *out = IRExpr_Const_F64i(val2);
    return true;
  }
  if (parseThisString("V128{0x", str, &str) &&
      parseHexUlong(&val2, str, &str) &&
      parseThisChar('}', str, suffix)) {
    *out = IRExpr_Const_V128(val2);
    return true;
  }
  unsigned long val3;
  if (parseThisString("U128{0x", str, &str) &&
      parseHexUlong(&val2, str, &str) &&
      parseThisString(", 0x", str, &str) &&
      parseHexUlong(&val3, str, &str) &&
      parseThisString("}", str, suffix)) {
    *out = IRExpr_Const_U128(val2, val3);
    return true;
  }
  return false;
}

void ppIRCallee ( IRCallee* ce, FILE* f )
{
   fprintf(f, "%s", ce->name);
   if (ce->regparms > 0)
      fprintf(f, "[rp=%d]", ce->regparms);
   if (ce->mcx_mask > 0)
      fprintf(f, "[mcx=0x%x]", ce->mcx_mask);
   fprintf(f, "{%p}", (void*)ce->addr);
}

static bool parseFuncName(char **res, const char *str, const char **suffix)
{
  const char *cursor;
  for (cursor = str;
       isalnum(cursor[0]) || cursor[0] == '_';
       cursor++)
    ;
  if (cursor == str)
    return false;
  /* XXX this gets leaked! */
  *res = (char *)malloc(cursor - str + 1);
  memcpy(*res, str, cursor - str);
  (*res)[cursor - str] = 0;
  *suffix = cursor;
  return true;
}

static bool parseIRCallee(IRCallee **out, const char *str, const char **suffix)
{
  char *name;
  int regparms;
  unsigned long mcx_mask;
  unsigned long addr;
  if (!parseFuncName(&name, str, &str))
    return false;
  regparms = 0;
  parseThisString("[rp=", str, &str) &&
    parseDecimalInt(&regparms, str, &str) &&
    parseThisChar(']', str, &str);
  mcx_mask = 0;
  parseThisString("[mcx=0x", str, &str) &&
    parseHexUlong(&mcx_mask, str, &str) &&
    parseThisChar(']', str, &str);
  if (!parseThisChar('{', str, &str))
    return false;
  if (parseThisString("(nil)", str, &str)) {
    addr = 0;
  } else if (!parseThisString("0x", str, &str) ||
	     !parseHexUlong(&addr, str, &str))
    return false;
  if (!parseThisChar('}', str, suffix))
    return false;
  *out = new IRCallee(regparms, name, (void *)addr, mcx_mask);
  return true;      
}

void ppIRRegArray ( IRRegArray* arr, FILE* f )
{
   fprintf(f, "(%d:%dx", arr->base, arr->nElems);
   ppIRType(arr->elemTy, f);
   fprintf(f, ")");
}

static bool parseIRRegArray(IRRegArray **res, const char *str, const char **suffix)
{
  int base, nElems;
  IRType ty;
  if (!parseThisChar('(', str, &str) ||
      !parseDecimalInt(&base, str, &str) ||
      !parseThisChar(':', str, &str) ||
      !parseDecimalInt(&nElems, str, &str) ||
      !parseThisChar('x', str, &str) ||
      !parseIRType(&ty, str, &str) ||
      !parseThisChar(')', str, suffix))
    return false;
  *res = mkIRRegArray(base, ty, nElems);
  return true;
}

void ppIRTemp ( IRTemp tmp, FILE* f )
{
   if (tmp == IRTemp_INVALID)
      fprintf(f, "IRTemp_INVALID");
   else
      fprintf(f,  "t%d", (Int)tmp);
}

#define foreach_op_sized(iter)			\
  iter(Add)					\
  iter(Sub)					\
  iter(Mul)					\
  iter(Or)					\
  iter(And)					\
  iter(Xor)					\
  iter(Shl)					\
  iter(Shr)					\
  iter(Sar)					\
  iter(CmpEQ)					\
  iter(CmpNE)					\
  iter(CasCmpEQ)				\
  iter(CasCmpNE)				\
  iter(Not)					\
  iter(Neg)					\
  iter(Noop)

#define foreach_op_unsized(iter)		\
	   iter(8Uto16)				\
	     iter(8Uto32)			\
	     iter(16Uto32)			\
	     iter(8Sto16)			\
	     iter(8Sto32)			\
	     iter(16Sto32)			\
	     iter(32Sto64)			\
	     iter(32Uto64)			\
	     iter(32to8)			\
	     iter(16Uto64)			\
	     iter(16Sto64)			\
	     iter(8Uto64)			\
	     iter(8Sto64)			\
	     iter(64to16)			\
	     iter(64to8)			\
						\
	     iter(1Uto8)			\
	     iter(1Uto32)			\
	     iter(1Uto64)			\
	     iter(1Sto8)			\
	     iter(1Sto16)			\
	     iter(1Sto32)			\
	     iter(1Sto64)			\
	     iter(BadPtr)			\
	     iter(CmpEQ1)			\
	     iter(CmpEQF32)			\
	     iter(CmpEQF64)			\
	     iter(CmpEQI128)			\
	     iter(CmpEQV128)			\
						\
	     iter(MullS8)			\
	     iter(MullS16)			\
	     iter(MullS32)			\
	     iter(MullS64)			\
	     iter(MullU8)			\
	     iter(MullU16)			\
	     iter(MullU32)			\
	     iter(MullU64)			\
						\
	     iter(Clz64)			\
	     iter(Clz32)			\
	     iter(Ctz64)			\
	     iter(Ctz32)			\
						\
	     iter(CmpLT8S)			\
	     iter(CmpLT8U)			\
						\
	     iter(CmpLT16U)			\
	     iter(CmpLT16S)			\
						\
	     iter(CmpLT32S)			\
	     iter(CmpLE32S)			\
	     iter(CmpLT32U)			\
	     iter(CmpLE32U)			\
						\
	     iter(CmpLT64S)			\
	     iter(CmpLE64S)			\
	     iter(CmpLT64U)			\
	     iter(CmpLE64U)			\
						\
	     iter(CmpNEZ8)			\
	     iter(CmpNEZ16)			\
	     iter(CmpNEZ32)			\
	     iter(CmpNEZ64)			\
						\
	     iter(CmpwNEZ32)			\
	     iter(CmpwNEZ64)			\
						\
	     iter(Left8)			\
	     iter(Left16)			\
	     iter(Left32)			\
	     iter(Left64)			\
	     iter(Max32U)			\
						\
	     iter(CmpORD32U)			\
	     iter(CmpORD32S)			\
						\
	     iter(CmpORD64U)			\
	     iter(CmpORD64S)			\
						\
	     iter(DivU32)			\
	     iter(DivS32)			\
	     iter(DivU64)			\
	     iter(DivS64)			\
						\
	     iter(DivModU64to32)		\
	     iter(DivModS64to32)		\
						\
	     iter(DivModU128to64)		\
	     iter(DivModS128to64)		\
						\
	     iter(16HIto8)			\
	     iter(16to8)			\
	     iter(8HLto16)			\
						\
	     iter(32HIto16)			\
	     iter(32to16)			\
	     iter(16HLto32)			\
						\
	     iter(64HIto32)			\
	     iter(64to32)			\
	     iter(32HLto64)			\
						\
	     iter(128HIto64)			\
	     iter(128to64)			\
	     iter(64HLto128)			\
						\
	     iter(AddF64)			\
	     iter(SubF64)			\
	     iter(MulF64)			\
	     iter(DivF64)			\
	     iter(AddF64r32)			\
	     iter(SubF64r32)			\
	     iter(MulF64r32)			\
	     iter(DivF64r32)			\
						\
	     iter(ScaleF64)			\
	     iter(AtanF64)			\
	     iter(Yl2xF64)			\
	     iter(Yl2xp1F64)			\
	     iter(PRemF64)			\
	     iter(PRemC3210F64)			\
	     iter(PRem1F64)			\
	     iter(PRem1C3210F64)		\
	     iter(NegF64)			\
	     iter(SqrtF64)			\
						\
	     iter(AbsF64)			\
	     iter(SinF64)			\
	     iter(CosF64)			\
	     iter(TanF64)			\
	     iter(2xm1F64)			\
						\
	     iter(MAddF64)			\
	     iter(MSubF64)			\
	     iter(MAddF64r32)			\
	     iter(MSubF64r32)			\
						\
	     iter(Est5FRSqrt)			\
	     iter(RoundF64toF64_NEAREST)	\
	     iter(RoundF64toF64_NegINF)		\
	     iter(RoundF64toF64_PosINF)		\
	     iter(RoundF64toF64_ZERO)		\
						\
	     iter(TruncF64asF32)		\
	     iter(CalcFPRF)			\
						\
	     iter(CmpF32)			\
	     iter(CmpF64)			\
						\
	     iter(F64toI16)			\
	     iter(F64toI32)			\
	     iter(F64toI64)			\
						\
	     iter(I16toF64)			\
	     iter(I32toF64)			\
	     iter(I64toF64)			\
						\
	     iter(F32toF64)			\
	     iter(F64toF32)			\
						\
	     iter(RoundF64toInt)		\
	     iter(RoundF64toF32)		\
						\
	     iter(ReinterpF64asI64)		\
	     iter(ReinterpI64asF64)		\
	     iter(ReinterpF32asI32)		\
	     iter(ReinterpI32asF32)		\
						\
	     iter(I32UtoFx4)			\
	     iter(I32StoFx4)			\
						\
	     iter(QFtoI32Ux4_RZ)		\
	     iter(QFtoI32Sx4_RZ)		\
						\
	     iter(RoundF32x4_RM)		\
	     iter(RoundF32x4_RP)		\
	     iter(RoundF32x4_RN)		\
	     iter(RoundF32x4_RZ)		\
						\
	     iter(Add8x8)			\
	     iter(Add16x4)			\
	     iter(Add32x2)			\
	     iter(QAdd8Ux8)			\
	     iter(QAdd16Ux4)			\
	     iter(QAdd8Sx8)			\
	     iter(QAdd16Sx4)			\
	     iter(Sub8x8)			\
	     iter(Sub16x4)			\
	     iter(Sub32x2)			\
	     iter(QSub8Ux8)			\
	     iter(QSub16Ux4)			\
	     iter(QSub8Sx8)			\
	     iter(QSub16Sx4)			\
	     iter(Mul16x4)			\
	     iter(Mul32x2)			\
	     iter(MulHi16Ux4)			\
	     iter(MulHi16Sx4)			\
	     iter(Avg8Ux8)			\
	     iter(Avg16Ux4)			\
	     iter(Max16Sx4)			\
	     iter(Max8Ux8)			\
	     iter(Min16Sx4)			\
	     iter(Min8Ux8)			\
	     iter(CmpEQ8x8)			\
	     iter(CmpEQ16x4)			\
	     iter(CmpEQ32x2)			\
	     iter(CmpGT8Sx8)			\
	     iter(CmpGT16Sx4)			\
	     iter(CmpGT32Sx2)			\
	     iter(ShlN8x8)			\
	     iter(ShlN16x4)			\
	     iter(ShlN32x2)			\
	     iter(ShrN16x4)			\
	     iter(ShrN32x2)			\
	     iter(SarN8x8)			\
	     iter(SarN16x4)			\
	     iter(SarN32x2)			\
	     iter(QNarrow16Ux4)			\
	     iter(QNarrow16Sx4)			\
	     iter(QNarrow32Sx2)			\
	     iter(InterleaveHI8x8)		\
	     iter(InterleaveHI16x4)		\
	     iter(InterleaveHI32x2)		\
	     iter(InterleaveLO8x8)		\
	     iter(InterleaveLO16x4)		\
	     iter(InterleaveLO32x2)		\
	     iter(CatOddLanes16x4)		\
	     iter(CatEvenLanes16x4)		\
	     iter(Perm8x8)			\
						\
	     iter(CmpNEZ32x2)			\
	     iter(CmpNEZ16x4)			\
	     iter(CmpNEZ8x8)			\
						\
	     iter(Add32Fx4)			\
	     iter(Add32F0x4)			\
	     iter(Add64Fx2)			\
	     iter(Add64F0x2)			\
						\
	     iter(Div32Fx4)			\
	     iter(Div32F0x4)			\
	     iter(Div64Fx2)			\
	     iter(Div64F0x2)			\
						\
	     iter(Max32Fx4)			\
	     iter(Max32F0x4)			\
	     iter(Max64Fx2)			\
	     iter(Max64F0x2)			\
						\
	     iter(Min32Fx4)			\
	     iter(Min32F0x4)			\
	     iter(Min64Fx2)			\
	     iter(Min64F0x2)			\
						\
	     iter(Mul32Fx4)			\
	     iter(Mul32F0x4)			\
	     iter(Mul64Fx2)			\
	     iter(Mul64F0x2)			\
						\
	     iter(Recip32Fx4)			\
	     iter(Recip32F0x4)			\
	     iter(Recip64Fx2)			\
	     iter(Recip64F0x2)			\
						\
	     iter(RSqrt32Fx4)			\
	     iter(RSqrt32F0x4)			\
	     iter(RSqrt64Fx2)			\
	     iter(RSqrt64F0x2)			\
						\
	     iter(Sqrt32Fx4)			\
	     iter(Sqrt32F0x4)			\
	     iter(Sqrt64Fx2)			\
	     iter(Sqrt64F0x2)			\
						\
	     iter(Sub32Fx4)			\
	     iter(Sub32F0x4)			\
	     iter(Sub64Fx2)			\
	     iter(Sub64F0x2)			\
						\
	     iter(CmpEQ32Fx4)			\
	     iter(CmpLT32Fx4)			\
	     iter(CmpLE32Fx4)			\
	     iter(CmpGT32Fx4)			\
	     iter(CmpGE32Fx4)			\
	     iter(CmpUN32Fx4)			\
	     iter(CmpEQ64Fx2)			\
	     iter(CmpLT64Fx2)			\
	     iter(CmpLE64Fx2)			\
	     iter(CmpUN64Fx2)			\
						\
	     iter(CmpEQ32F0x4)			\
	     iter(CmpLT32F0x4)			\
	     iter(CmpLE32F0x4)			\
	     iter(CmpUN32F0x4)			\
	     iter(CmpEQ64F0x2)			\
	     iter(CmpLT64F0x2)			\
	     iter(CmpLE64F0x2)			\
	     iter(CmpUN64F0x2)			\
						\
	     iter(V128to64)			\
	     iter(V128HIto64)			\
	     iter(64HLtoV128)			\
						\
	     iter(64UtoV128)			\
	     iter(SetV128lo64)			\
						\
	     iter(32UtoV128)			\
	     iter(V128to32)			\
	     iter(SetV128lo32)			\
						\
	     iter(Dup8x16)			\
	     iter(Dup16x8)			\
	     iter(Dup32x4)			\
						\
	     iter(NotV128)			\
	     iter(AndV128)			\
	     iter(OrV128)			\
	     iter(XorV128)			\
						\
	     iter(CmpNEZ8x16)			\
	     iter(CmpNEZ16x8)			\
	     iter(CmpNEZ32x4)			\
	     iter(CmpNEZ64x2)			\
						\
	     iter(Add8x16)			\
	     iter(Add16x8)			\
	     iter(Add32x4)			\
	     iter(Add64x2)			\
	     iter(QAdd8Ux16)			\
	     iter(QAdd16Ux8)			\
	     iter(QAdd32Ux4)			\
	     iter(QAdd8Sx16)			\
	     iter(QAdd16Sx8)			\
	     iter(QAdd32Sx4)			\
						\
	     iter(Sub8x16)			\
	     iter(Sub16x8)			\
	     iter(Sub32x4)			\
	     iter(Sub64x2)			\
	     iter(QSub8Ux16)			\
	     iter(QSub16Ux8)			\
	     iter(QSub32Ux4)			\
	     iter(QSub8Sx16)			\
	     iter(QSub16Sx8)			\
	     iter(QSub32Sx4)			\
						\
	     iter(Mul16x8)			\
	     iter(MulHi16Ux8)			\
	     iter(MulHi32Ux4)			\
	     iter(MulHi16Sx8)			\
	     iter(MulHi32Sx4)			\
						\
	     iter(MullEven8Ux16)		\
	     iter(MullEven16Ux8)		\
	     iter(MullEven8Sx16)		\
	     iter(MullEven16Sx8)		\
						\
	     iter(Avg8Ux16)			\
	     iter(Avg16Ux8)			\
	     iter(Avg32Ux4)			\
	     iter(Avg8Sx16)			\
	     iter(Avg16Sx8)			\
	     iter(Avg32Sx4)			\
						\
	     iter(Max8Sx16)			\
	     iter(Max16Sx8)			\
	     iter(Max32Sx4)			\
	     iter(Max8Ux16)			\
	     iter(Max16Ux8)			\
	     iter(Max32Ux4)			\
						\
	     iter(Min8Sx16)			\
	     iter(Min16Sx8)			\
	     iter(Min32Sx4)			\
	     iter(Min8Ux16)			\
	     iter(Min16Ux8)			\
	     iter(Min32Ux4)			\
						\
	     iter(CmpEQ8x16)			\
	     iter(CmpEQ16x8)			\
	     iter(CmpEQ32x4)			\
	     iter(CmpGT8Sx16)			\
	     iter(CmpGT16Sx8)			\
	     iter(CmpGT32Sx4)			\
	     iter(CmpGT8Ux16)			\
	     iter(CmpGT16Ux8)			\
	     iter(CmpGT32Ux4)			\
						\
	     iter(ShlV128)			\
	     iter(ShrV128)			\
						\
	     iter(ShlN8x16)			\
	     iter(ShlN16x8)			\
	     iter(ShlN32x4)			\
	     iter(ShlN64x2)			\
	     iter(ShrN8x16)			\
	     iter(ShrN16x8)			\
	     iter(ShrN32x4)			\
	     iter(ShrN64x2)			\
	     iter(SarN8x16)			\
	     iter(SarN16x8)			\
	     iter(SarN32x4)			\
						\
	     iter(Shl8x16)			\
	     iter(Shl16x8)			\
	     iter(Shl32x4)			\
	     iter(Shr8x16)			\
	     iter(Shr16x8)			\
	     iter(Shr32x4)			\
	     iter(Sar8x16)			\
	     iter(Sar16x8)			\
	     iter(Sar32x4)			\
	     iter(Rol8x16)			\
	     iter(Rol16x8)			\
	     iter(Rol32x4)			\
						\
	     iter(Narrow16x8)			\
	     iter(Narrow32x4)			\
	     iter(QNarrow16Ux8)			\
	     iter(QNarrow32Ux4)			\
	     iter(QNarrow16Sx8)			\
	     iter(QNarrow32Sx4)			\
						\
	     iter(InterleaveHI8x16)		\
	     iter(InterleaveHI16x8)		\
	     iter(InterleaveHI32x4)		\
	     iter(InterleaveHI64x2)		\
	     iter(InterleaveLO8x16)		\
	     iter(InterleaveLO16x8)		\
	     iter(InterleaveLO32x4)		\
	     iter(InterleaveLO64x2)		\
						\
 	     iter(Perm8x16)			\
	   /* Things which end in 1 should be */\
	   /* at the end of the list, to avoid*/\
	   /* confusion with things which end*/	\
	   /* in 16 */				\
	     iter(Not1)				\
	     iter(8to1)				\
	     iter(16to1)			\
	     iter(32to1)			\
	     iter(64to1)			\
	     iter(And1)				\
	     iter(Or1)				\
	     iter(Noop128)

void ppIROp ( IROp op, FILE* f )
{
   const char* str = NULL; 
   IROp   base;
   switch (op) {
#define do_op(name)					\
     case Iop_ ## name ## 8 ... Iop_ ## name ## 64 :	\
       str = #name;					\
     base = Iop_ ## name ## 8;				\
     break;
     foreach_op_sized(do_op);
#undef do_op

      /* other cases must explicitly "return;" */
#define do_op(name) case Iop_ ## name: fprintf(f, #name); return;
     foreach_op_unsized(do_op)
#undef do_op

      default: vpanic("ppIROp(1)");
   }

   vassert(str);  
   switch (op - base) {
      case 0: fprintf(f, "%s",str); fprintf(f, "8"); break;
      case 1: fprintf(f, "%s",str); fprintf(f, "16"); break;
      case 2: fprintf(f, "%s",str); fprintf(f, "32"); break;
      case 3: fprintf(f, "%s",str); fprintf(f, "64"); break;
      default: vpanic("ppIROp(2)");
   }
}

struct irop_parser_successor;
typedef std::vector<irop_parser_successor> irop_parser_state;
struct irop_parser_successor {
  char c;
  IROp res;
  irop_parser_state *next_state;
  bool operator<(const irop_parser_successor &o) const {
    return c < o.c;
  }
};

static void add_entry_to_irop_table(irop_parser_state **acc,
				    const char *str,
				    IROp res)
{
  assert(str[0] != '\0');
  if (!*acc)
    *acc = new irop_parser_state();
  struct irop_parser_successor *succ = NULL;
  for (auto it = (*acc)->begin(); !succ && it != (*acc)->end(); it++) {
    if (it->c == str[0])
      succ = &*it;
  }
  if (!succ) {
    irop_parser_successor _succ;
    _succ.c = str[0];
    _succ.res = Iop_INVALID;
    _succ.next_state = NULL;
    (*acc)->push_back(_succ);
    succ = &(*acc)->back();
  }
  if (str[1] == '\0') {
    assert(succ->res == Iop_INVALID);
    succ->res = res;
  } else {
    add_entry_to_irop_table(&succ->next_state, str + 1, res);
  }
}

static void sort_irop_table(irop_parser_state *table)
{
  if (!table)
    return;
  std::sort(table->begin(), table->end());
  for (auto it = table->begin(); it != table->end(); it++)
    sort_irop_table(it->next_state);
}

static irop_parser_state *build_irop_parser(void)
{
  irop_parser_state *acc = NULL;
#define do_op(name)						       \
  add_entry_to_irop_table(&acc, #name, Iop_ ## name);
  foreach_op_unsized(do_op)

#define do_op2(name, sz)			\
    do_op(name ## sz)
#define do_op3(name) do {                       \
      do_op2(name, 8);				\
      do_op2(name, 16);				\
      do_op2(name, 32);				\
      do_op2(name, 64);				\
    } while (0);
    foreach_op_sized(do_op3)
#undef do_op
#undef do_op2
#undef do_op3

  sort_irop_table(acc);
  return acc;
}

static bool parseIropTable(const irop_parser_state *current_state,
			   IROp *res,
			   const char *str,
			   const char **successor)
{
  unsigned idx1, idx2;
  if (!current_state)
    return false;

  /* Loop invariant: the slot we're looking for is definitely in the
     range [idx1, idx2) */
  idx1 = 0;
  idx2 = current_state->size();
  const struct irop_parser_successor *succ;
  while (1) {
    assert(idx1 < idx2);
    /* Ignore overflow: these tables are small. */
    unsigned probe = (idx1 + idx2) / 2;
    assert(probe != idx2);
    if (probe == idx1)
      break;
    succ = &(*current_state)[probe];
    if ( succ->c < str[0] ) {
      idx1 = probe;
    } else if ( succ->c == str[0] ) {
      goto found_succ;
    } else {
      idx2 = probe;
    }
  }

  succ = &(*current_state)[idx1];
  if (succ->c == str[0])
    goto found_succ;
  return false;

 found_succ:
  if ( succ->res != Iop_INVALID &&
       (str[1] == '\0' || str[1] == ':' || str[1] == '(' || isspace(str[1])) ) {
    *successor = str + 1;
    *res = succ->res;
    return true;
  }
  return parseIropTable(succ->next_state, res, str + 1, successor);
}

static bool parseIROp(IROp *out, const char *str, const char **suffix)
{
  static irop_parser_state *parser;
  if (!parser)
    parser = build_irop_parser();
  return parseIropTable(parser, out, str, suffix);
}

static const char *irOpSimpleChar(IROp op)
{
  switch (op) {
  case Iop_Add8 ... Iop_Add64:
    return "+";
  case Iop_And8 ... Iop_And64:
    return "&";
  case Iop_Or8 ... Iop_Or64:
    return "|";
  case Iop_And1:
    return "&&";
  case Iop_Or1:
    return "||";
  case Iop_CmpEQ8 ... Iop_CmpEQ64:
    return "==";
  case Iop_Not1:
    return "!";
  case Iop_BadPtr:
    return "BadPtr";
  default:
    return 0;
  }
}

static bool parseIROpSimple(IROp *out, IRType ty, const char *str, const char **suffix)
{
  int delta;
  switch (ty) {
  case Ity_I8:
    delta = 0;
    break;
  case Ity_I16:
    delta = 1;
    break;
  case Ity_I32:
    delta = 2;
    break;
  case Ity_I64:
    delta = 3;
    break;
  case Ity_I1:
    delta = -1;
    break;
  default:
    return false;
  }
  if (parseThisChar('+', str, suffix)) {
    if (delta == -1) return false;
    *out = (IROp)(Iop_Add8 + delta);
    return true;
  }
  if (parseThisString("&&", str, suffix)) {
    if (delta != -1) return false;
    *out = Iop_And1;
    return true;
  }
  if (parseThisString("||", str, suffix)) {
    if (delta != -1) return false;
    *out = Iop_Or1;
    return true;
  }
  if (parseThisChar('&', str, suffix)) {
    if (delta == -1) return false;
    *out = (IROp)(Iop_And8 + delta);
    return true;
  }
  if (parseThisChar('|', str, suffix)) {
    if (delta == -1) return false;
    *out = (IROp)(Iop_Or8 + delta);
    return true;
  }
  if (parseThisString("==", str, suffix)) {
    if (delta == -1) return false;
    *out = (IROp)(Iop_CmpEQ8 + delta);
    return true;
  }
  if (parseThisChar('!', str, suffix)) {
    if (delta != -1) return false;
    *out = Iop_Not1;
    return true;
  }
  if (parseThisString("BadPtr", str, suffix)) {
    if (delta != -1) return false;
    *out = Iop_BadPtr;
    return true;
  }
  return false;
}

bool
parseThreadAndRegister(threadAndRegister *out, const char *str, const char **suffix)
{
	if (parseThisString("invalid", str, suffix)) {
		*out = threadAndRegister::invalid();
		return true;
	}
	int thread;
	int offset;
	int gen;
	if (parseThisString("tmp", str, &str) &&
	    parseDecimalInt(&thread, str, &str) &&
	    parseThisChar(':', str, &str) &&
	    parseDecimalInt(&offset, str, &str) &&
	    parseThisChar(':', str, &str) &&
	    parseDecimalInt(&gen, str, suffix)) {
	        *out = threadAndRegister::temp(thread, offset, gen);
		return true;
	}
	if (parseThisString("reg", str, &str) &&
	    parseDecimalInt(&thread, str, &str) &&
	    parseThisChar(':', str, &str) &&
	    parseDecimalInt(&offset, str, &str) &&
	    parseThisChar(':', str, &str) &&
	    parseDecimalInt(&gen, str, suffix)) {
		*out = threadAndRegister::reg(thread, offset, gen);
		return true;
	}
	return false;
}

static bool opHasFourArguments(IROp op)
{
  IRType dst, arg1, arg2, arg3, arg4;
  typeOfPrimop(op, &dst, &arg1, &arg2, &arg3, &arg4);
  return arg4 != Ity_INVALID;
}

static bool opHasThreeArguments(IROp op)
{
  IRType dst, arg1, arg2, arg3, arg4;
  typeOfPrimop(op, &dst, &arg1, &arg2, &arg3, &arg4);
  return arg3 != Ity_INVALID && arg4 == Ity_INVALID;
}

static bool opHasTwoArguments(IROp op)
{
  IRType dst, arg1, arg2, arg3, arg4;
  typeOfPrimop(op, &dst, &arg1, &arg2, &arg3, &arg4);
  return arg2 != Ity_INVALID && arg3 == Ity_INVALID && arg4 == Ity_INVALID;
}

/* Parse an IRExpr.  This ends up being a surprisingly important hot
   spot in some tests. */
bool parseIRExpr(IRExpr **out, const char *str, const char **suffix)
{
  /* Forms which start with a fixed letter: GET, GETI, LD, Mux0X, free variables. */
  if (str[0] == 'G') {
    if (parseThisString("GET:", str, &str)) {
      threadAndRegister reg(threadAndRegister::invalid());
      IRType ty;
      if (parseIRType(&ty, str, &str) &&
	  parseThisChar('(', str, &str) &&
	  parseThreadAndRegister(&reg, str, &str) &&
	  parseThisChar(')', str, suffix)) {
	*out = IRExpr_Get(reg, ty);
	return true;
      }
    } else if (parseThisString("GETI", str, &str)) {
      IRRegArray *arr;
      IRExpr *ix;
      int bias;
      int tid;

      if (parseIRRegArray(&arr, str, &str) &&
	  parseThisChar('[', str, &str) &&
	  parseIRExpr(&ix, str, &str) &&
	  parseThisChar(',', str, &str) &&
	  parseDecimalInt(&bias, str, &str) &&
	  parseThisString("](", str, &str) &&
	  parseDecimalInt(&tid, str, &str) &&
	  parseThisChar(')', str, suffix)) {
	*out = IRExpr_GetI(arr, ix, bias, tid);
	return true;
      }
    }
  } else if (str[0] == 'L') {
    IRType ty;
    IRExpr *addr;
    MemoryAccessIdentifier rip(MemoryAccessIdentifier::uninitialised());
    if (parseThisString("LD:", str, &str) &&
	parseIRType(&ty, str, &str) &&
	parseThisChar('(', str, &str) &&
	parseIRExpr(&addr, str, &str) &&
	parseThisString(")", str, suffix)) {
      *out = IRExpr_Load(ty, addr);
      return true;
    }
  } else if (str[0] == 'M') {
    IRExpr *cond, *expr0, *exprX;
    if (parseThisString("Mux0X(", str, &str) &&
	parseIRExpr(&cond, str, &str) &&
	parseThisChar(',', str, &str) &&
	parseIRExpr(&expr0, str, &str) &&
	parseThisChar(',', str, &str) &&
	parseIRExpr(&exprX, str, &str) &&
	parseThisChar(')', str, suffix)) {
      *out = IRExpr_Mux0X(cond, expr0, exprX);
      return true;
    }
  } else if (str[0] == 'E') {
    if (parseThisString("Entry(", str, &str)) {
      unsigned thread;
      CfgLabel label(CfgLabel::uninitialised());
      if (!parseDecimalUInt(&thread, str, &str) ||
	  !parseThisChar(':', str, &str) ||
	  !label.parse(str, &str) ||
	  !parseThisChar(')', str, suffix))
	return false;
      *out = new IRExprEntryPoint(thread, label);
      return true;
    }
  } else if (str[0] == 'F') {
    /* Could be a float const */
    IRExprConst *c;
    if (parseIRConst(&c, str, suffix)) {
      *out = c;
      return true;
    }

    /* Might be a free variable. */
    if (parseThisString("Free", str, &str)) {
      MemoryAccessIdentifier ma(MemoryAccessIdentifier::uninitialised());
      IRType ty;
      bool isUnique;
      if (!ma.parse(str, &str) ||
	  !parseThisChar(':', str, &str) ||
	  !parseIRType(&ty, str, &str) ||
	  !parseThisChar(':', str, &str))
	return false;
      if (parseThisString("UNIQUE", str, suffix))
	isUnique = true;
      else if (parseThisString("NONUNIQUE", str, suffix))
	isUnique = false;
      else
	return false;
      *out = IRExpr_FreeVariable(ma, ty, isUnique);
      return true;
    }

    /* Fall through and try to parse as a prefix irop. */
  } else if ((str[0] >= '0' && str[0] <= '9') || str[0] == 'V' || str[0] == '-') {
    /* Constant of some sort. */
    IRExprConst *c;
    if (parseIRConst(&c, str, suffix)) {
      *out = c;
      return true;
    }

    /* Let it fall through, because it might be an unop which starts
       with a number e.g. 64to1. */
  } else if (str[0] == '(') {
    /* This is either assoc or binop with a simple irop, or it's
       happens-before */
    {
      MemoryAccessIdentifier before(MemoryAccessIdentifier::uninitialised());
      if (before.parse(str + 1, &str)) {
	MemoryAccessIdentifier after(MemoryAccessIdentifier::uninitialised());
	/* It must be happens-before */
	if (!parseThisString(" <-< ", str, &str) ||
	    !after.parse(str, &str) ||
	    !parseThisChar(')', str, suffix))
	  return false;
	*out = IRExpr_HappensBefore(before, after);
	return true;
      }
    }

    IRExpr *arg1, *arg2;
    IROp op;
    if (!parseIRExpr(&arg1, str + 1, &str) ||
	!parseThisChar(' ', str, &str) ||
	!parseIROpSimple(&op, arg1->type(), str, &str) ||
	!parseThisChar(' ', str, &str) ||
	!parseIRExpr(&arg2, str, &str))
      return false;
    if (parseThisChar(')', str, suffix)) {
      *out = IRExpr_Binop(op, arg1, arg2);
      return true;
    }

    /* Must be a simple associative. */
    if (!operationAssociates(op))
      return false;
    IROp op2;
    std::vector<IRExpr *> args;
    args.push_back(arg1);
    args.push_back(arg2);
    IRExpr *arg;
    while (!parseThisChar(')', str, suffix)) {
      if (!parseThisChar(' ', str, &str) ||
	  !parseIROpSimple(&op2, arg1->type(), str, &str) ||
	  op != op2 ||
	  !parseThisChar(' ', str, &str) ||
	  !parseIRExpr(&arg, str, &str))
	return false;
      args.push_back(arg);
    }
    IRExprAssociative *r = IRExpr_Associative(args.size(), op);
    r->nr_arguments = args.size();
    for (unsigned i = 0; i < args.size(); i++)
      r->contents[i] = args[i];
    *out = r;
    return true;
  } else if (str[0] == 'C') {
    if (parseThisString("Control(", str, &str)) {
      unsigned thread;
      CfgLabel cfg1(CfgLabel::uninitialised());
      CfgLabel cfg2(CfgLabel::uninitialised());
      if (!parseDecimalUInt(&thread, str, &str) ||
	  !parseThisChar(':', str, &str) ||
	  !cfg1.parse(str, &str) ||
	  !parseThisString("->", str, &str) ||
	  !cfg2.parse(str, &str) ||
	  !parseThisChar(')', str, suffix))
	return false;
      *out = new IRExprControlFlow(thread, cfg1, cfg2);
      return true;
    }
  }

  /* Short names for registers */
  {
    int offset = -1;
#define do_reg(name)						\
    if (offset == -1 && parseThisString( #name ":", str, &str))	\
      offset = OFFSET_amd64_ ## name;
    foreach_reg(do_reg);
#undef do_reg

    if (offset != -1) {
      int tid;
      int generation;
      if (!parseDecimalInt(&tid, str, &str) ||
	  !parseThisChar(':', str, &str) ||
	  !parseDecimalInt(&generation, str, suffix))
	return false;
      *out = IRExpr_Get(offset, Ity_I64, tid, generation);
      return true;
    }
  }

  /* Now do the forms which start <IROp> ( <IRExpr> */
  {
    IROp op;
    if (parseIROp(&op, str, &str)) {
      IRExpr *arg1;
      if (!parseThisChar('(', str, &str) ||
	  !parseIRExpr(&arg1, str, &str))
	return false;
      if (opHasFourArguments(op)) {
	IRExpr *arg2, *arg3, *arg4;
	if (!parseThisChar(',', str, &str) ||
	    !parseIRExpr(&arg2, str, &str) ||
	    !parseThisChar(',', str, &str) ||
	    !parseIRExpr(&arg3, str, &str) ||
	    !parseThisChar(',', str, &str) ||
	    !parseIRExpr(&arg4, str, &str) ||
	    !parseThisChar(')', str, suffix))
	  return false;
	*out = IRExpr_Qop(op, arg1, arg2, arg3, arg4);
	return true;
      } else if (opHasThreeArguments(op)) {
	IRExpr *arg2, *arg3;
	if (!parseThisChar(',', str, &str) ||
	    !parseIRExpr(&arg2, str, &str) ||
	    !parseThisChar(',', str, &str) ||
	    !parseIRExpr(&arg3, str, &str) ||
	    !parseThisChar(')', str, suffix))
	  return false;
	*out = IRExpr_Triop(op, arg1, arg2, arg3);
	return true;
      } else if (opHasTwoArguments(op)) {
	IRExpr *arg2;
	if (!parseThisChar(',', str, &str) ||
	    !parseIRExpr(&arg2, str, &str) ||
	    !parseThisChar(')', str, suffix))
	  return false;
	*out = IRExpr_Binop(op, arg1, arg2);
	return true;
      } else {
	if (!parseThisChar(')', str, suffix))
	  return false;
	*out = IRExpr_Unop(op, arg1);
	return true;
      }
    }
  }

  /* A bit of a special case for unops with start with a simple
     irop. */
  {
    IROp op;

    if (parseIROpSimple(&op, Ity_I1, str, &str)) {
      IRExpr *arg;
      if (!parseThisChar('(', str, &str) ||
	  !parseIRExpr(&arg, str, &str) ||
	  !parseThisChar(')', str, suffix))
	return false;
      *out = IRExpr_Unop(op, arg);
      return true;
    }
  }

  /* And now various other cases which are too rare to be worth trying
     to optimise. */
  if (parseThisChar('[', str, &str)) {
    IROp op;
    if (parseIROp(&op, str, &str) &&
	operationAssociates(op) &&
	parseThisChar(']', str, suffix)) {
      *out = IRExpr_Associative(op, NULL);
      return true;
    }
    return false;
  }

  if (parseThisString("Assoc(", str, &str)) {
    IROp op = Iop_INVALID;
    IRExpr *arg;
    std::vector<IRExpr *> args;

    if (!parseIROp(&op, str, &str) ||
	!operationAssociates(op) ||
	!parseThisChar(':', str, &str) ||
	!parseIRExpr(&arg, str, &str))
      return false;
    args.push_back(arg);
    while (!parseThisChar(')', str, suffix)) {
      if (!parseThisString(", ", str, &str) ||
	  !parseIRExpr(&arg, str, &str))
	return false;
      args.push_back(arg);
    }
    IRExprAssociative *e = IRExpr_Associative(args.size(), op);
    e->nr_arguments = args.size();
    for (unsigned i = 0; i < args.size(); i++)
      e->contents[i] = args[i];
    *out = e;
    return true;
  }

  IRCallee *cee;
  std::vector<IRExpr *> args;
  IRExpr *arg;
  IRType ty;
  IRExpr **argsA;

  if (!parseIRCallee(&cee, str, &str) ||
      !parseThisChar('(', str, &str))
    return false;
  while (1) {
    if (parseThisString("):", str, &str))
      break;
    if (args.size() != 0 && !parseThisChar(',', str, &str))
      return false;
    if (!parseIRExpr(&arg, str, &str))
      return false;
    args.push_back(arg);
  }
  if (!parseIRType(&ty, str, suffix))
    return false;
  argsA = alloc_irexpr_array(args.size() + 1);
  for (unsigned i = 0; i < args.size(); i++)
    argsA[i] = args[i];
  argsA[args.size()] = NULL;
  *out = IRExpr_CCall(cee, ty, argsA);
  return true;
}

void
IRExprBinop::_prettyPrint(FILE *f, std::map<IRExpr *, unsigned> &tags) const
{
  if (irOpSimpleChar(op)) {
    fprintf(f, "(");
    arg1->prettyPrint(f, tags);
    fprintf(f,  " %s ", irOpSimpleChar(op) );
    arg2->prettyPrint(f, tags);
    fprintf(f,  ")" );
  } else {
    ppIROp(op, f);
    fprintf(f,  "(" );
    arg1->prettyPrint(f, tags);
    fprintf(f,  "," );
    arg2->prettyPrint(f, tags);
    fprintf(f,  ")" );
  }
}

void
IRExprUnop::_prettyPrint(FILE *f, std::map<IRExpr *, unsigned> &tags) const
{
  if (irOpSimpleChar(op))
    {
      fprintf(f, "%s(", irOpSimpleChar(op));
      arg->prettyPrint(f, tags);
      fprintf(f, ")");
    }
  else
    {
      ppIROp(op, f);
      fprintf(f,  "(" );
      arg->prettyPrint(f, tags);
      fprintf(f,  ")" );
    }
}

void
IRExprLoad::_prettyPrint(FILE *f, std::map<IRExpr *, unsigned> &tags) const
{
      fprintf(f,  "LD:");
      ppIRType(ty, f);
      fprintf(f,  "(" );
      addr->prettyPrint(f, tags);
      fprintf(f,  ")" );
}
void
IRExprConst::_prettyPrint(FILE *f, std::map<IRExpr *, unsigned> &) const
{
  ppIRConst(this, f);
}
void
IRExprCCall::_prettyPrint(FILE *f, std::map<IRExpr *, unsigned> &tags) const
{
      ppIRCallee(cee, f);
      fprintf(f, "(");
      for (int i = 0; args[i] != NULL; i++) {
	args[i]->prettyPrint(f, tags);
        if (args[i+1] != NULL)
          fprintf(f, ",");
      }
      fprintf(f, "):");
      ppIRType(retty, f);
}
void
IRExprMux0X::_prettyPrint(FILE *f, std::map<IRExpr *, unsigned> &tags) const
{
      fprintf(f, "Mux0X(");
      cond->prettyPrint(f, tags);
      fprintf(f, ",");
      expr0->prettyPrint(f, tags);
      fprintf(f, ",");
      exprX->prettyPrint(f, tags);
      fprintf(f, ")");
}
void
IRExprAssociative::_prettyPrint(FILE *f, std::map<IRExpr *, unsigned> &tags) const
{
      /* Bit of a hack: our parser can't handle expressions with
	 redundant brackets, which is what you get if print an assoc
	 with a single argument.  The ``fix'' (if that's the right
	 word) is to just avoid printing such things, by just printing
	 the single assoc argument instead. */
      if (nr_arguments == 1) {
	contents[0]->prettyPrint(f, tags);
	return;
      }

      if (nr_arguments == 0) {
	fprintf(f, "[");
	ppIROp(op, f);
	fprintf(f, "]");
	return;
      }

      if (irOpSimpleChar(op))
      {
	fprintf(f, "(");
	for (int x = 0; x < nr_arguments; x++) {
	  if (x != 0)
	    fprintf(f, " %s ", irOpSimpleChar(op));
	  contents[x]->prettyPrint(f, tags);
	}
	fprintf(f, ")");
      }
      else
      {
	fprintf(f, "Assoc(");
	ppIROp(op, f);
	fprintf(f, ":");
	for (int x = 0; x < nr_arguments; x++) {
	  if (x != 0)
	    fprintf(f, ", ");
	  contents[x]->prettyPrint(f, tags);
	}
	fprintf(f, ")");
      }
}
void
IRExprHappensBefore::_prettyPrint(FILE *f, std::map<IRExpr *, unsigned> &) const
{
      fprintf(f, "(%s <-< %s)", before.name(), after.name());
}

void ppIREffect ( IREffect fx, FILE* f )
{
   switch (fx) {
      case Ifx_None:   fprintf(f, "noFX"); return;
      case Ifx_Read:   fprintf(f, "RdFX"); return;
      case Ifx_Write:  fprintf(f, "WrFX"); return;
      case Ifx_Modify: fprintf(f, "MoFX"); return;
      default: vpanic("ppIREffect");
   }
}

void ppIRDirty ( IRDirty* d, FILE *f )
{
   Int i;
   if (d->tmp.isValid()) {
      d->tmp.prettyPrint(f);
      fprintf(f, " = ");
   }
   fprintf(f, "DIRTY ");
   ppIRExpr(d->guard, f);
   if (d->needsBBP)
      fprintf(f, " NeedsBBP");
   if (d->mFx != Ifx_None) {
      fprintf(f, " ");
      ppIREffect(d->mFx, f);
      fprintf(f, "-mem(");
      ppIRExpr(d->mAddr, f);
      fprintf(f, ",%d)", d->mSize);
   }
   for (i = 0; i < d->nFxState; i++) {
      fprintf(f, " ");
      ppIREffect(d->fxState[i].fx, f);
      fprintf(f, "-gst(%d,%d)", d->fxState[i].offset, d->fxState[i].size);
   }
   fprintf(f, " ::: ");
   ppIRCallee(d->cee, f);
   fprintf(f, "(");
   for (i = 0; d->args[i] != NULL; i++) {
      ppIRExpr(d->args[i], f);
      if (d->args[i+1] != NULL) {
         fprintf(f, ",");
      }
   }
   fprintf(f, ")");
}

void ppIRCAS ( IRCAS* cas, FILE* f )
{
   /* Print even structurally invalid constructions, as an aid to
      debugging. */
   if (cas->oldHi.isValid()) {
      cas->oldHi.prettyPrint(f);
      fprintf(f, ",");
   }
   cas->oldLo.prettyPrint(f);
   fprintf(f, " = CAS(");
   ppIRExpr(cas->addr, f);
   fprintf(f, "::");
   if (cas->expdHi) {
      ppIRExpr(cas->expdHi, f);
      fprintf(f, ",");
   }
   ppIRExpr(cas->expdLo, f);
   fprintf(f, "->");
   if (cas->dataHi) {
      ppIRExpr(cas->dataHi, f);
      fprintf(f, ",");
   }
   ppIRExpr(cas->dataLo, f);
   fprintf(f, ")");
}

void ppIRJumpKind ( IRJumpKind kind, FILE* f )
{
   switch (kind) {
      case Ijk_Boring:       fprintf(f, "Boring"); break;
      case Ijk_Call:         fprintf(f, "Call"); break;
      case Ijk_Ret:          fprintf(f, "Return"); break;
      case Ijk_ClientReq:    fprintf(f, "ClientReq"); break;
      case Ijk_Yield:        fprintf(f, "Yield"); break;
      case Ijk_EmWarn:       fprintf(f, "EmWarn"); break;
      case Ijk_EmFail:       fprintf(f, "EmFail"); break;
      case Ijk_NoDecode:     fprintf(f, "NoDecode"); break;
      case Ijk_MapFail:      fprintf(f, "MapFail"); break;
      case Ijk_TInval:       fprintf(f, "Invalidate"); break;
      case Ijk_NoRedir:      fprintf(f, "NoRedir"); break;
      case Ijk_SigTRAP:      fprintf(f, "SigTRAP"); break;
      case Ijk_SigSEGV:      fprintf(f, "SigSEGV"); break;
      case Ijk_SigBUS:       fprintf(f, "SigBUS"); break;
      case Ijk_Sys_syscall:  fprintf(f, "Sys_syscall"); break;
      case Ijk_Sys_int32:    fprintf(f, "Sys_int32"); break;
      case Ijk_Sys_int128:   fprintf(f, "Sys_int128"); break;
      case Ijk_Sys_int129:   fprintf(f, "Sys_int129"); break;
      case Ijk_Sys_int130:   fprintf(f, "Sys_int130"); break;
      case Ijk_Sys_sysenter: fprintf(f, "Sys_sysenter"); break;
      default:               vpanic("ppIRJumpKind");
   }
}

void ppIRMBusEvent ( IRMBusEvent event, FILE* f )
{
   switch (event) {
      case Imbe_Fence: fprintf(f, "Fence"); break;
      default:         vpanic("ppIRMBusEvent");
   }
}

void ppIRStmt ( IRStmt* s, FILE* f )
{
   if (!s) {
      fprintf(f, "!!! IRStmt* which is NULL !!!");
      return;
   }
   s->prettyPrint(f);
}

void ppIRTypeEnv ( IRTypeEnv* env, FILE* f ) {
   fprintf(f, "    %d temps used\n", env->types_used);
}

void ppIRSB ( IRSB* bb, FILE* f )
{
   Int i;
   fprintf(f, "IRSB {\n");
   ppIRTypeEnv(bb->tyenv, f);
   fprintf(f, "\n");
   for (i = 0; i < bb->stmts_used; i++) {
      fprintf(f,  "%d:   ", i);
      ppIRStmt(bb->stmts[i], f);
      fprintf(f,  "\n");
   }
   fprintf(f,  "   goto {");
   ppIRJumpKind(bb->jumpkind, f);
   fprintf(f,  "} ");
   if ( bb->next_is_const ) {
     fprintf(f, "const %s\n}\n", bb->next_const.name());
   } else if ( bb->next_nonconst ) {
     ppIRExpr( bb->next_nonconst, f );
     fprintf(f,  "\n}\n");
   } else {
     fprintf(f, "<null>\n}\n");
   }
}


/*---------------------------------------------------------------*/
/*--- Constructors                                            ---*/
/*---------------------------------------------------------------*/


/* Constructors -- IRConst */

IRExprConst* IRExpr_Const_U1 ( bool bit )
{
   vassert(bit == False || bit == True);
   IRExprConst::_Ico c;
   c.U1 = bit;
   return new IRExprConst(Ity_I1, c);
}
IRExprConst* IRExpr_Const_U8 ( unsigned char u8)
{
   IRExprConst::_Ico c;
   c.U8 = u8;
   return new IRExprConst(Ity_I8, c);
}
IRExprConst* IRExpr_Const_U16 ( unsigned short u16 )
{
   IRExprConst::_Ico c;
   c.U16 = u16;
   return new IRExprConst(Ity_I16, c);
}
IRExprConst* IRExpr_Const_U32 ( unsigned u32 )
{
   IRExprConst::_Ico c;
   c.U32 = u32;
   return new IRExprConst(Ity_I32, c);
}
static VexPtr<IRExprConst, &ir_heap> magicConstant0;
IRExprConst* IRExpr_Const_U64 ( unsigned long u64 )
{
   IRExprConst::_Ico c;
   c.U64 = u64;
   if (u64 == 0) {
     if (!magicConstant0)
       magicConstant0 = new IRExprConst(Ity_I64, c);
     return magicConstant0;
   }

   return new IRExprConst(Ity_I64, c);
}
IRExprConst* IRExpr_Const_F64 ( Double f64 )
{
   IRExprConst::_Ico c;
   *(double *)&c.U64 = f64;
   return new IRExprConst(Ity_I64, c);
}
IRExprConst* IRExpr_Const_F64i ( unsigned long f64i )
{
   return IRExpr_Const_U64(f64i);
}
IRExprConst* IRExpr_Const_V128 ( unsigned short con )
{
   unsigned long a = con;
   a <<= 16;
   a |= con;
   a = a | (a << 32);
   IRExprConst::_Ico c;
   c.U128.lo = a;
   c.U128.hi = a;
   return new IRExprConst(Ity_I128, c);
}
IRExprConst* IRExpr_Const_U128 ( unsigned long hi, unsigned long lo )
{
   IRExprConst::_Ico c;
   c.U128.lo = lo;
   c.U128.hi = hi;
   return new IRExprConst(Ity_I128, c);
}

/* Constructors -- IRCallee */

IRCallee* mkIRCallee ( Int regparms, const char* name, void* addr, UInt mcx_mask )
{
   vassert(regparms >= 0 && regparms <= 3);
   vassert(name != NULL);
   return new IRCallee(regparms, name, addr, mcx_mask);
}


/* Constructors -- IRRegArray */

IRRegArray* mkIRRegArray ( Int base, IRType elemTy, Int nElems )
{
   vassert(!(base < 0 || base > 10000 /* somewhat arbitrary */));
   vassert(!(elemTy == Ity_I1));
   vassert(!(nElems <= 0 || nElems > 500 /* somewhat arbitrary */));
   return new IRRegArray(base, elemTy, nElems);
}


/* Constructors -- IRExpr */

IRExprGet* IRExpr_Get ( threadAndRegister reg, IRType ty) {
   return new IRExprGet(reg, ty);
}
IRExprGet* IRExpr_Get ( Int off, IRType ty, unsigned tid, unsigned generation ) {
   return IRExpr_Get(threadAndRegister::reg(tid, off, generation), ty);
}
IRExpr* IRExpr_GetI ( IRRegArray* descr, IRExpr* ix, Int bias, unsigned tid ) {
   return new IRExprGetI(descr, ix, bias, tid);
}
IRExpr* IRExpr_RdTmp ( IRTemp tmp, IRType ty, unsigned tid, unsigned generation ) {
   return IRExpr_Get(-tmp - 1, ty, tid, generation);
}
IRExpr* IRExpr_Qop ( IROp op, IRExpr* arg1, IRExpr* arg2, 
                              IRExpr* arg3, IRExpr* arg4 ) {
   return new IRExprQop(op, arg1, arg2, arg3, arg4);
}
IRExpr* IRExpr_Triop  ( IROp op, IRExpr* arg1, 
                                 IRExpr* arg2, IRExpr* arg3 ) {
   return new IRExprTriop(op, arg1, arg2, arg3);
}
IRExpr* IRExpr_Binop ( IROp op, IRExpr* arg1, IRExpr* arg2 ) {
   assert(arg1);
   assert(arg2);

   /* Turn cas cmp operations into ordinary cmps. */
   if (op >= Iop_CasCmpEQ8 && op <= Iop_CasCmpNE64)
     op = (IROp)(Iop_CmpEQ8 + (op - Iop_CasCmpEQ8));

   /* Turn x != y into !(x == y) */
   if (op >= Iop_CmpNE8 && op <= Iop_CmpNE64)
     return IRExpr_Unop(Iop_Not1,
			IRExpr_Binop((IROp)(op - Iop_CmpNE8 + Iop_CmpEQ8),
				     arg1,
				     arg2));

   if (operationAssociates(op))
     return IRExpr_Associative(op, arg1, arg2, NULL);

   if (op == Iop_CmpEQ64) {
     if (arg2->tag == Iex_Const && arg1->tag != Iex_Const) {
       IRExpr *t = arg1;
       arg1 = arg2;
       arg2 = t;
     }
   }

   IRExprBinop* e         = new IRExprBinop(op);
   e->arg1 = arg1;
   e->arg2 = arg2;
   return e;
}

/* Check whether a(b(X)) can be converted to a single operator c(X).
   If it can, set @c appropriately and return true, otherwise return
   false. */
bool shortCircuitableUnops(IROp a, IROp b, IROp *c)
{
#define rule(_a, _b, _c)			\
  if (a == _a && b == _b) {			\
    *c = _c;					\
    return true;				\
  }

  /* For some reason, VEX doesn't have a 1Uto16 operation, although it
     does have 1Uto8 and 1Uto32.  That makes this a bit less
     symmetrical than it would otherwise be. */
  rule(Iop_32Uto64, Iop_16Uto32, Iop_16Uto64);
  rule(Iop_32Uto64, Iop_8Uto32, Iop_8Uto64);
  rule(Iop_32Uto64, Iop_1Uto32, Iop_1Uto64);
  rule(Iop_16Uto64, Iop_8Uto16, Iop_8Uto64);
  rule(Iop_8Uto64, Iop_1Uto8, Iop_1Uto64);

  rule(Iop_16Uto32, Iop_8Uto16, Iop_8Uto32);
  rule(Iop_8Uto32, Iop_1Uto8, Iop_1Uto32);

  /* An upcast immediately followed by a stronger downcast can be
     eliminated. */
  rule(Iop_64to1, Iop_32Uto64, Iop_32to1);
  rule(Iop_64to8, Iop_16Uto64, Iop_16to8);
  rule(Iop_64to8, Iop_32Uto64, Iop_32to8);
  rule(Iop_64to16, Iop_32Uto64, Iop_32to16);

  rule(Iop_64to16, Iop_8Uto64, Iop_8Uto16);
  rule(Iop_64to32, Iop_8Uto64, Iop_8Uto32);
  rule(Iop_64to32, Iop_16Uto64, Iop_16Uto32);

  rule(Iop_32to8, Iop_64to32, Iop_64to8);
  rule(Iop_32to16, Iop_64to32, Iop_64to16);
  rule(Iop_16to8, Iop_64to16, Iop_64to8);

#undef rule

  return false;
}

/* Return true if a(b(x)) == x */
bool inverseUnops(IROp a, IROp b)
{
#define rule(_a, _b)				\
  if (a == Iop_ ## _a && b == Iop_ ## _b)	\
    return true
  rule(64to1, 1Uto64);
  rule(64to8, 8Uto64);
  rule(64to16, 16Uto64);
  rule(64to32, 32Uto64);

  rule(32to1, 1Uto32);
  rule(32to8, 8Uto32);
  rule(32to16, 16Uto32);

  /* 1Uto16 doesn't exist */
  //rule(16to1, 1Uto16);
  rule(16to8, 8Uto16);

  rule(8to1, 1Uto8);

  rule(Not1, Not1);
  rule(Not8, Not8);
  rule(Not16, Not16);
  rule(Not32, Not32);
  rule(Not64, Not64);

  rule(Neg8, Neg8);
  rule(Neg16, Neg16);
  rule(Neg32, Neg32);
  rule(Neg64, Neg64);
#undef rule

  return false;
}

IRExpr* IRExpr_Unop ( IROp op, IRExpr* arg ) {
   if (op >= Iop_Noop8 && op <= Iop_Noop128)
     return arg;
   /* Short-circuit a bunch of redundant type conversions
      e.g. 64to1(1to64(x)) */
   if (arg->tag == Iex_Unop) {
     IRExprUnop *argu = (IRExprUnop *)arg;
     if (inverseUnops(op, argu->op))
       return argu->arg;
     IROp ss;
     if (shortCircuitableUnops(op, argu->op, &ss))
       return IRExpr_Unop(ss, argu->arg);
   }
   IRExprUnop* e       = new IRExprUnop(op);
   e->arg = arg;
   return e;
}
IRExpr* IRExpr_Load ( IRType ty, IRExpr* addr ) {
   return new IRExprLoad(ty, addr);
}
IRExpr* IRExpr_CCall ( IRCallee* cee, IRType retty, IRExpr** args ) {
   return new IRExprCCall(cee, retty, args);
}
IRExpr* IRExpr_Mux0X ( IRExpr* cond, IRExpr* expr0, IRExpr* exprX ) {
   return new IRExprMux0X(cond, expr0, exprX);
}
IRExpr* IRExpr_Associative(IROp op, ...)
{
   IRExprAssociative* e          = new IRExprAssociative();
   e->op = op;

   va_list args;
   int nr_args;
   IRExpr *arg;

   va_start(args, op);
   nr_args = 0;
   while (1) {
      arg = va_arg(args, IRExpr *);
      if (!arg)
	 break;
      nr_args++;
   }
   va_end(args);

   IRExpr *argsL[nr_args];
   int i;
   va_start(args, op);
   for (i = 0; i < nr_args; i++)
     argsL[i] = va_arg(args, IRExpr *);
   va_end(args);

   if (op == Iop_Add64) {
     /* Go through and find all the constant terms in the addition and
	reduce them to a single term right at the beginning (assuming
	that there's more than one) */
     int src, dest;
     unsigned long acc;
     IRExprConst *foundConstant;
     src = dest = nr_args - 1;
     acc = 0;
     foundConstant = NULL;
     while (src >= 0) {
       if (argsL[src]->tag == Iex_Const) {
	 IRExprConst *iec = (IRExprConst *)argsL[src];
	 foundConstant = iec;
	 acc += iec->Ico.U64;
       } else {
	 argsL[dest] = argsL[src];
	 dest--;
       }
       src--;
     }

     /* dest is now the number of constant terms found */
     if (dest == 0) {
       /* Found a single constant, just move it to the front */
       assert(foundConstant);
       argsL[0] = foundConstant;
     } else if (dest > 0) {
       /* Found multiple constants -> fold them together. */
       argsL[0] = IRExpr_Const_U64(acc);
       if (nr_args == dest + 1) {
	 /* Everything was a constant */
	 return argsL[0];
       }
       memmove(argsL + 1, argsL + dest + 1, sizeof(argsL[0]) * (nr_args - dest - 1));
       nr_args -= dest;
     } else {
       assert(dest == -1);
     }
   }

   e->nr_arguments_allocated = nr_args * 2;
   static libvex_allocation_site __las = {0, __FILE__, __LINE__};
   e->contents =
      (IRExpr **)__LibVEX_Alloc_Bytes(&ir_heap, sizeof(e->contents[0]) * nr_args * 2, &__las);
   e->nr_arguments = nr_args;
   memcpy(e->contents, argsL, sizeof(argsL[0]) * e->nr_arguments);
   va_end(args);
   return e;
}
IRExpr* IRExpr_Associative(IRExprAssociative *src)
{
   IRExprAssociative* e           = new IRExprAssociative();
   e->op = src->op;
   e->nr_arguments = src->nr_arguments;
   e->nr_arguments_allocated = src->nr_arguments * 2;
   static libvex_allocation_site __las = {0, __FILE__, __LINE__};
   e->contents = (IRExpr **)
      __LibVEX_Alloc_Bytes(&ir_heap,
			   sizeof(e->contents[0]) *
			   e->nr_arguments_allocated,
			   &__las);
   memcpy(e->contents,
	  src->contents,
	  sizeof(e->contents[0]) *
	  e->nr_arguments);
   return e;
}
IRExprAssociative* IRExpr_Associative(int nr_arguments, IROp op)
{
  IRExprAssociative *e = new IRExprAssociative();
  e->op = op;
  e->nr_arguments = 0;
  e->nr_arguments_allocated = nr_arguments;
  static libvex_allocation_site __las = {0, __FILE__, __LINE__};
  e->contents = (IRExpr **)
    __LibVEX_Alloc_Bytes(&ir_heap,
			 sizeof(e->contents[0]) *
			 e->nr_arguments_allocated,
			 &__las);
  return e;
}
IRExpr* IRExpr_HappensBefore ( const MemoryAccessIdentifier &before,
			       const MemoryAccessIdentifier &after )

{
  return new IRExprHappensBefore(before, after);
}

/* Constructors for NULL-terminated IRExpr expression vectors,
   suitable for use as arg lists in clean/dirty helper calls. */
IRExpr **alloc_irexpr_array(unsigned nr)
{
   return (IRExpr **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr);
}

IRExpr** mkIRExprVec_0 ( void ) {
   IRExpr** vec = alloc_irexpr_array(1);
   vec[0] = NULL;
   return vec;
}
IRExpr** mkIRExprVec_1 ( IRExpr* arg1 ) {
   IRExpr** vec = alloc_irexpr_array(2);
   vec[0] = arg1;
   vec[1] = NULL;
   return vec;
}
IRExpr** mkIRExprVec_2 ( IRExpr* arg1, IRExpr* arg2 ) {
   IRExpr** vec = alloc_irexpr_array(3);
   vec[0] = arg1;
   vec[1] = arg2;
   vec[2] = NULL;
   return vec;
}
IRExpr** mkIRExprVec_3 ( IRExpr* arg1, IRExpr* arg2, IRExpr* arg3 ) {
   IRExpr** vec = alloc_irexpr_array(4);
   vec[0] = arg1;
   vec[1] = arg2;
   vec[2] = arg3;
   vec[3] = NULL;
   return vec;
}
IRExpr** mkIRExprVec_4 ( IRExpr* arg1, IRExpr* arg2, IRExpr* arg3,
                         IRExpr* arg4 ) {
   IRExpr** vec = alloc_irexpr_array(5);
   vec[0] = arg1;
   vec[1] = arg2;
   vec[2] = arg3;
   vec[3] = arg4;
   vec[4] = NULL;
   return vec;
}
IRExpr** mkIRExprVec_5 ( IRExpr* arg1, IRExpr* arg2, IRExpr* arg3,
                         IRExpr* arg4, IRExpr* arg5 ) {
   IRExpr** vec = alloc_irexpr_array(6);
   vec[0] = arg1;
   vec[1] = arg2;
   vec[2] = arg3;
   vec[3] = arg4;
   vec[4] = arg5;
   vec[5] = NULL;
   return vec;
}
IRExpr** mkIRExprVec_6 ( IRExpr* arg1, IRExpr* arg2, IRExpr* arg3,
                         IRExpr* arg4, IRExpr* arg5, IRExpr* arg6 ) {
   IRExpr** vec = alloc_irexpr_array(7);
   vec[0] = arg1;
   vec[1] = arg2;
   vec[2] = arg3;
   vec[3] = arg4;
   vec[4] = arg5;
   vec[5] = arg6;
   vec[6] = NULL;
   return vec;
}
IRExpr** mkIRExprVec_7 ( IRExpr* arg1, IRExpr* arg2, IRExpr* arg3,
                         IRExpr* arg4, IRExpr* arg5, IRExpr* arg6,
                         IRExpr* arg7 ) {
   IRExpr** vec = alloc_irexpr_array(8);
   vec[0] = arg1;
   vec[1] = arg2;
   vec[2] = arg3;
   vec[3] = arg4;
   vec[4] = arg5;
   vec[5] = arg6;
   vec[6] = arg7;
   vec[7] = NULL;
   return vec;
}


/* Constructors -- IRDirty */

IRDirty* emptyIRDirty ( void ) {
   IRDirty* d = new IRDirty(threadAndRegister::invalid());
   d->cee      = NULL;
   d->guard    = NULL;
   d->args     = NULL;
   d->mFx      = Ifx_None;
   d->mAddr    = NULL;
   d->mSize    = 0;
   d->needsBBP = False;
   d->nFxState = 0;
   return d;
}


/* Constructors -- IRCAS */

IRCAS* mkIRCAS ( threadAndRegister oldHi,
		 threadAndRegister oldLo,
                 IRExpr* addr, 
                 IRExpr* expdHi, IRExpr* expdLo,
                 IRExpr* dataHi, IRExpr* dataLo ) {
   IRCAS* cas = new IRCAS(oldHi, oldLo);
   cas->addr   = addr;
   cas->expdHi = expdHi;
   cas->expdLo = expdLo;
   cas->dataHi = dataHi;
   cas->dataLo = dataLo;
   return cas;
}


/* Constructors -- IRStmt */

IRStmt* IRStmt_NoOp ( void )
{
   return &IRStmtNoOp::singleton;
}
IRStmt* IRStmt_StartAtomic ( void )
{
   return &IRStmtStartAtomic::singleton;
}
IRStmt* IRStmt_EndAtomic ( void )
{
   return &IRStmtEndAtomic::singleton;
}
IRStmt* IRStmt_IMark ( const ThreadRip &addr, Int len ) {
   return new IRStmtIMark(addr, len);
}
IRStmt* IRStmt_AbiHint ( IRExpr* base, Int len, IRExpr* nia ) {
   return new IRStmtAbiHint(base, len, nia);
}
IRStmt* IRStmt_Put ( threadAndRegister off, IRExpr* data ) {
   return new IRStmtPut(off, data);
}
IRStmt* IRStmt_PutI ( IRRegArray* descr, IRExpr* ix,
                      Int bias, IRExpr* data )
{
   return new IRStmtPutI(descr, ix, bias, data);
}
IRStmt* IRStmt_WrTmp ( threadAndRegister tmp, IRExpr* data )
{
   return new IRStmtPut(tmp, data);
}
IRStmt* IRStmt_Store ( IRExpr* addr, IRExpr* data )
{
   return new IRStmtStore(addr, data);
}
IRStmt* IRStmt_CAS ( IRCAS* cas )
{
   return new IRStmtCAS(cas);
}
IRStmt* IRStmt_Dirty ( IRDirty* d )
{
   return new IRStmtDirty(d);
}
IRStmt* IRStmt_MBE ( IRMBusEvent event )
{
   return new IRStmtMBE(event);
}
IRStmt* IRStmt_Exit ( IRExpr* guard, IRJumpKind jk, const ThreadRip &dst )
{
   return new IRStmtExit(guard, jk, dst);
}


/* Constructors -- IRTypeEnv */

IRTypeEnv* emptyIRTypeEnv ( void )
{
   IRTypeEnv* env   = new IRTypeEnv();
   env->types_used  = 0;
   return env;
}


/* Constructors -- IRSB */

IRSB* emptyIRSB ( void )
{
   IRSB* bb       = new IRSB();
   bb->tyenv      = emptyIRTypeEnv();
   bb->stmts_used = 0;
   bb->stmts_size = 8;
   bb->stmts      = (IRStmt **)__LibVEX_Alloc_Ptr_Array(&ir_heap, bb->stmts_size);
   bb->jumpkind   = Ijk_Boring;
   return bb;
}


/*---------------------------------------------------------------*/
/*--- (Deep) copy constructors.  These make complete copies   ---*/
/*--- the original, which can be modified without affecting   ---*/
/*--- the original.                                           ---*/
/*---------------------------------------------------------------*/

/* Copying IR Expr vectors (for call args). */

/* Shallow copy of an IRExpr vector */

IRExpr** shallowCopyIRExprVec ( IRExpr** vec )
{
   Int      i;
   IRExpr** newvec;
   for (i = 0; vec[i]; i++)
      ;
   newvec = alloc_irexpr_array(i+1);
   for (i = 0; vec[i]; i++)
      newvec[i] = vec[i];
   newvec[i] = NULL;
   return newvec;
}

/*---------------------------------------------------------------*/
/*--- Primop types                                            ---*/
/*---------------------------------------------------------------*/

void typeOfPrimop ( IROp op, 
                    /*OUTs*/
                    IRType* t_dst, 
                    IRType* t_arg1, IRType* t_arg2, 
                    IRType* t_arg3, IRType* t_arg4 )
{
#  define UNARY(_ta1,_td)                                      \
      *t_dst = (_td); *t_arg1 = (_ta1); return
#  define BINARY(_ta1,_ta2,_td)                                \
     *t_dst = (_td); *t_arg1 = (_ta1); *t_arg2 = (_ta2); return
#  define TERNARY(_ta1,_ta2,_ta3,_td)                          \
     *t_dst = (_td); *t_arg1 = (_ta1);                         \
     *t_arg2 = (_ta2); *t_arg3 = (_ta3); return
#  define QUATERNARY(_ta1,_ta2,_ta3,_ta4,_td)                  \
     *t_dst = (_td); *t_arg1 = (_ta1);                         \
     *t_arg2 = (_ta2); *t_arg3 = (_ta3);                       \
     *t_arg4 = (_ta4); return
#  define COMPARISON(_ta)                                      \
     *t_dst = Ity_I1; *t_arg1 = *t_arg2 = (_ta); return;
#  define UNARY_COMPARISON(_ta)                                \
     *t_dst = Ity_I1; *t_arg1 = (_ta); return;

   /* Rounding mode values are always Ity_I32, encoded as per
      IRRoundingMode */
   const IRType ity_RMode = Ity_I32;

   *t_dst  = Ity_INVALID;
   *t_arg1 = Ity_INVALID;
   *t_arg2 = Ity_INVALID;
   *t_arg3 = Ity_INVALID;
   *t_arg4 = Ity_INVALID;
   switch (op) {
      case Iop_INVALID:
         abort();
      case Iop_Add8: case Iop_Sub8: case Iop_Mul8: 
      case Iop_Or8:  case Iop_And8: case Iop_Xor8:
         BINARY(Ity_I8,Ity_I8, Ity_I8);

      case Iop_Add16: case Iop_Sub16: case Iop_Mul16:
      case Iop_Or16:  case Iop_And16: case Iop_Xor16:
         BINARY(Ity_I16,Ity_I16, Ity_I16);

      case Iop_CmpORD32U:
      case Iop_CmpORD32S:
      case Iop_Add32: case Iop_Sub32: case Iop_Mul32:
      case Iop_Or32:  case Iop_And32: case Iop_Xor32:
      case Iop_Max32U:
         BINARY(Ity_I32,Ity_I32, Ity_I32);

      case Iop_Add64: case Iop_Sub64: case Iop_Mul64:
      case Iop_Or64:  case Iop_And64: case Iop_Xor64:
      case Iop_CmpORD64U:
      case Iop_CmpORD64S:
      case Iop_Avg8Ux8: case Iop_Avg16Ux4:
      case Iop_Add8x8: case Iop_Add16x4: case Iop_Add32x2:
      case Iop_CmpEQ8x8: case Iop_CmpEQ16x4: case Iop_CmpEQ32x2:
      case Iop_CmpGT8Sx8: case Iop_CmpGT16Sx4: case Iop_CmpGT32Sx2:
      case Iop_InterleaveHI8x8: case Iop_InterleaveLO8x8:
      case Iop_InterleaveHI16x4: case Iop_InterleaveLO16x4:
      case Iop_InterleaveHI32x2: case Iop_InterleaveLO32x2:
      case Iop_CatOddLanes16x4: case Iop_CatEvenLanes16x4:
      case Iop_Perm8x8:
      case Iop_Max8Ux8: case Iop_Max16Sx4:
      case Iop_Min8Ux8: case Iop_Min16Sx4:
      case Iop_Mul16x4: case Iop_Mul32x2:
      case Iop_MulHi16Sx4: case Iop_MulHi16Ux4:
      case Iop_QAdd8Sx8: case Iop_QAdd16Sx4:
      case Iop_QAdd8Ux8: case Iop_QAdd16Ux4:
      case Iop_QNarrow32Sx2:
      case Iop_QNarrow16Sx4: case Iop_QNarrow16Ux4:
      case Iop_Sub8x8: case Iop_Sub16x4: case Iop_Sub32x2:
      case Iop_QSub8Sx8: case Iop_QSub16Sx4:
      case Iop_QSub8Ux8: case Iop_QSub16Ux4:
         BINARY(Ity_I64,Ity_I64, Ity_I64);

      case Iop_ShlN32x2: case Iop_ShlN16x4: case Iop_ShlN8x8:
      case Iop_ShrN32x2: case Iop_ShrN16x4:
      case Iop_SarN32x2: case Iop_SarN16x4: case Iop_SarN8x8:
         BINARY(Ity_I64,Ity_I8, Ity_I64);

      case Iop_Shl8: case Iop_Shr8: case Iop_Sar8:
         BINARY(Ity_I8,Ity_I8, Ity_I8);
      case Iop_Shl16: case Iop_Shr16: case Iop_Sar16:
         BINARY(Ity_I16,Ity_I8, Ity_I16);
      case Iop_Shl32: case Iop_Shr32: case Iop_Sar32:
         BINARY(Ity_I32,Ity_I8, Ity_I32);
      case Iop_Shl64: case Iop_Shr64: case Iop_Sar64:
         BINARY(Ity_I64,Ity_I8, Ity_I64);

      case Iop_Not8:
      case Iop_Neg8:
      case Iop_Noop8:
         UNARY(Ity_I8, Ity_I8);
      case Iop_Not16:
      case Iop_Neg16:
      case Iop_Noop16:
         UNARY(Ity_I16, Ity_I16);
      case Iop_Not32:
      case Iop_Neg32:
      case Iop_Noop32:
         UNARY(Ity_I32, Ity_I32);
      case Iop_Not64:
      case Iop_Neg64:
      case Iop_Noop64:
      case Iop_CmpNEZ32x2: case Iop_CmpNEZ16x4: case Iop_CmpNEZ8x8:
         UNARY(Ity_I64, Ity_I64);

      case Iop_CmpEQ8: case Iop_CmpNE8:
      case Iop_CasCmpEQ8: case Iop_CasCmpNE8:
      case Iop_CmpLT8S: case Iop_CmpLT8U:
         COMPARISON(Ity_I8);
      case Iop_CmpEQ16: case Iop_CmpNE16:
      case Iop_CasCmpEQ16: case Iop_CasCmpNE16:
      case Iop_CmpLT16S: case Iop_CmpLT16U:
         COMPARISON(Ity_I16);
      case Iop_CmpEQ32: case Iop_CmpNE32:
      case Iop_CasCmpEQ32: case Iop_CasCmpNE32:
      case Iop_CmpLT32S: case Iop_CmpLE32S:
      case Iop_CmpLT32U: case Iop_CmpLE32U:
         COMPARISON(Ity_I32);
      case Iop_CmpEQ64: case Iop_CmpNE64:
      case Iop_CasCmpEQ64: case Iop_CasCmpNE64:
      case Iop_CmpLT64S: case Iop_CmpLE64S:
      case Iop_CmpLT64U: case Iop_CmpLE64U:
         COMPARISON(Ity_I64);

      case Iop_CmpNEZ8:  UNARY_COMPARISON(Ity_I8);
      case Iop_CmpNEZ16: UNARY_COMPARISON(Ity_I16);
      case Iop_CmpNEZ32: UNARY_COMPARISON(Ity_I32);
      case Iop_CmpNEZ64: UNARY_COMPARISON(Ity_I64);

      case Iop_Left8:  UNARY(Ity_I8, Ity_I8);
      case Iop_Left16: UNARY(Ity_I16,Ity_I16);
      case Iop_CmpwNEZ32: case Iop_Left32: UNARY(Ity_I32,Ity_I32);
      case Iop_CmpwNEZ64: case Iop_Left64: UNARY(Ity_I64,Ity_I64);

      case Iop_MullU8: case Iop_MullS8:
         BINARY(Ity_I8,Ity_I8, Ity_I16);
      case Iop_MullU16: case Iop_MullS16:
         BINARY(Ity_I16,Ity_I16, Ity_I32);
      case Iop_MullU32: case Iop_MullS32:
         BINARY(Ity_I32,Ity_I32, Ity_I64);
      case Iop_MullU64: case Iop_MullS64:
         BINARY(Ity_I64,Ity_I64, Ity_I128);

      case Iop_Clz32: case Iop_Ctz32:
         UNARY(Ity_I32, Ity_I32);

      case Iop_Clz64: case Iop_Ctz64:
         UNARY(Ity_I64, Ity_I64);

      case Iop_DivU32: case Iop_DivS32:
         BINARY(Ity_I32,Ity_I32, Ity_I32);

      case Iop_DivU64: case Iop_DivS64:
         BINARY(Ity_I64,Ity_I64, Ity_I64);

      case Iop_DivModU64to32: case Iop_DivModS64to32:
         BINARY(Ity_I64,Ity_I32, Ity_I64);

      case Iop_DivModU128to64: case Iop_DivModS128to64:
         BINARY(Ity_I128,Ity_I64, Ity_I128);

      case Iop_16HIto8: case Iop_16to8:
         UNARY(Ity_I16, Ity_I8);
      case Iop_8HLto16:
         BINARY(Ity_I8,Ity_I8, Ity_I16);

      case Iop_32HIto16: case Iop_32to16:
         UNARY(Ity_I32, Ity_I16);
      case Iop_16HLto32:
         BINARY(Ity_I16,Ity_I16, Ity_I32);

      case Iop_64HIto32: case Iop_64to32:
         UNARY(Ity_I64, Ity_I32);
      case Iop_32HLto64:
         BINARY(Ity_I32,Ity_I32, Ity_I64);

      case Iop_128HIto64: case Iop_128to64:
         UNARY(Ity_I128, Ity_I64);
      case Iop_64HLto128:
         BINARY(Ity_I64,Ity_I64, Ity_I128);

      case Iop_Not1:   UNARY(Ity_I1, Ity_I1);
      case Iop_1Uto8:  UNARY(Ity_I1, Ity_I8);
      case Iop_1Sto8:  UNARY(Ity_I1, Ity_I8);
      case Iop_1Sto16: UNARY(Ity_I1, Ity_I16);
      case Iop_1Uto32: case Iop_1Sto32: UNARY(Ity_I1, Ity_I32);
      case Iop_1Sto64: case Iop_1Uto64: UNARY(Ity_I1, Ity_I64);
      case Iop_8to1:   UNARY(Ity_I8, Ity_I1);
      case Iop_16to1:  UNARY(Ity_I16, Ity_I1);
      case Iop_32to1:  UNARY(Ity_I32, Ity_I1);
      case Iop_64to1:  UNARY(Ity_I64, Ity_I1);
      case Iop_CmpEQ1: case Iop_And1: case Iop_Or1: BINARY(Ity_I1, Ity_I1, Ity_I1);
      case Iop_BadPtr: UNARY(Ity_I64, Ity_I1);

      case Iop_8Uto32: case Iop_8Sto32:
         UNARY(Ity_I8, Ity_I32);

      case Iop_8Uto16: case Iop_8Sto16:
         UNARY(Ity_I8, Ity_I16);

      case Iop_16Uto32: case Iop_16Sto32: 
         UNARY(Ity_I16, Ity_I32);

      case Iop_32Sto64: case Iop_32Uto64:
         UNARY(Ity_I32, Ity_I64);

      case Iop_8Uto64: case Iop_8Sto64:
         UNARY(Ity_I8, Ity_I64);

      case Iop_16Uto64: case Iop_16Sto64:
         UNARY(Ity_I16, Ity_I64);
      case Iop_64to16:
         UNARY(Ity_I64, Ity_I16);

      case Iop_32to8: UNARY(Ity_I32, Ity_I8);
      case Iop_64to8: UNARY(Ity_I64, Ity_I8);

      case Iop_AddF64:    case Iop_SubF64: 
      case Iop_MulF64:    case Iop_DivF64:
      case Iop_AddF64r32: case Iop_SubF64r32: 
      case Iop_MulF64r32: case Iop_DivF64r32:
         TERNARY(ity_RMode,Ity_I64,Ity_I64, Ity_I64);

      case Iop_NegF64: case Iop_AbsF64: 
         UNARY(Ity_I64, Ity_I64);

      case Iop_SqrtF64:
      case Iop_SqrtF64r32:
         BINARY(ity_RMode,Ity_I64, Ity_I64);

      case Iop_CmpF64:
         BINARY(Ity_I64,Ity_I64, Ity_I32);
      case Iop_CmpF32:
         BINARY(Ity_I32,Ity_I32, Ity_I32);

      case Iop_F64toI16: BINARY(ity_RMode,Ity_I64, Ity_I16);
      case Iop_F64toI32: BINARY(ity_RMode,Ity_I64, Ity_I32);
      case Iop_F64toI64: BINARY(ity_RMode,Ity_I64, Ity_I64);

      case Iop_I16toF64: UNARY(Ity_I16, Ity_I64);
      case Iop_I32toF64: UNARY(Ity_I32, Ity_I64);
      case Iop_I64toF64: BINARY(ity_RMode,Ity_I64, Ity_I64);

      case Iop_F32toF64: UNARY(Ity_I32, Ity_I64);
      case Iop_F64toF32: BINARY(ity_RMode,Ity_I64, Ity_I32);

      case Iop_ReinterpI64asF64: UNARY(Ity_I64, Ity_I64);
      case Iop_ReinterpF64asI64: UNARY(Ity_I64, Ity_I64);
      case Iop_ReinterpI32asF32: UNARY(Ity_I32, Ity_I32);
      case Iop_ReinterpF32asI32: UNARY(Ity_I32, Ity_I32);

      case Iop_AtanF64: case Iop_Yl2xF64:  case Iop_Yl2xp1F64: 
      case Iop_ScaleF64: case Iop_PRemF64: case Iop_PRem1F64:
         TERNARY(ity_RMode,Ity_I64,Ity_I64, Ity_I64);

      case Iop_PRemC3210F64: case Iop_PRem1C3210F64:
         TERNARY(ity_RMode,Ity_I64,Ity_I64, Ity_I32);

      case Iop_SinF64: case Iop_CosF64: case Iop_TanF64: 
      case Iop_2xm1F64:
      case Iop_RoundF64toInt: BINARY(ity_RMode,Ity_I64, Ity_I64);

      case Iop_MAddF64: case Iop_MSubF64:
      case Iop_MAddF64r32: case Iop_MSubF64r32:
         QUATERNARY(ity_RMode,Ity_I64,Ity_I64,Ity_I64, Ity_I64);

      case Iop_Est5FRSqrt:
      case Iop_RoundF64toF64_NEAREST: case Iop_RoundF64toF64_NegINF:
      case Iop_RoundF64toF64_PosINF: case Iop_RoundF64toF64_ZERO:
         UNARY(Ity_I64, Ity_I64);
      case Iop_RoundF64toF32:
         BINARY(ity_RMode,Ity_I64, Ity_I64);
      case Iop_CalcFPRF:
         UNARY(Ity_I64, Ity_I32);
      case Iop_TruncF64asF32:
         UNARY(Ity_I64, Ity_I32);

      case Iop_I32UtoFx4:
      case Iop_I32StoFx4:
      case Iop_QFtoI32Ux4_RZ:
      case Iop_QFtoI32Sx4_RZ:
      case Iop_RoundF32x4_RM:
      case Iop_RoundF32x4_RP:
      case Iop_RoundF32x4_RN:
      case Iop_RoundF32x4_RZ:
      case Iop_Noop128:
         UNARY(Ity_I128, Ity_I128);

      case Iop_64HLtoV128: BINARY(Ity_I64,Ity_I64, Ity_I128);
      case Iop_V128to64: case Iop_V128HIto64: 
         UNARY(Ity_I128, Ity_I64);

      case Iop_V128to32:    UNARY(Ity_I128, Ity_I32);
      case Iop_32UtoV128:   UNARY(Ity_I32, Ity_I128);
      case Iop_64UtoV128:   UNARY(Ity_I64, Ity_I128);
      case Iop_SetV128lo32: BINARY(Ity_I128,Ity_I32, Ity_I128);
      case Iop_SetV128lo64: BINARY(Ity_I128,Ity_I64, Ity_I128);

      case Iop_Dup8x16: UNARY(Ity_I8, Ity_I128);
      case Iop_Dup16x8: UNARY(Ity_I16, Ity_I128);
      case Iop_Dup32x4: UNARY(Ity_I32, Ity_I128);

      case Iop_CmpEQ32Fx4: case Iop_CmpLT32Fx4:
      case Iop_CmpEQ64Fx2: case Iop_CmpLT64Fx2:
      case Iop_CmpLE32Fx4: case Iop_CmpUN32Fx4:
      case Iop_CmpLE64Fx2: case Iop_CmpUN64Fx2:
      case Iop_CmpGT32Fx4: case Iop_CmpGE32Fx4:
      case Iop_CmpEQ32F0x4: case Iop_CmpLT32F0x4:
      case Iop_CmpEQ64F0x2: case Iop_CmpLT64F0x2:
      case Iop_CmpLE32F0x4: case Iop_CmpUN32F0x4:
      case Iop_CmpLE64F0x2: case Iop_CmpUN64F0x2:
      case Iop_Add32Fx4: case Iop_Add32F0x4:
      case Iop_Add64Fx2: case Iop_Add64F0x2:
      case Iop_Div32Fx4: case Iop_Div32F0x4:
      case Iop_Div64Fx2: case Iop_Div64F0x2:
      case Iop_Max32Fx4: case Iop_Max32F0x4:
      case Iop_Max64Fx2: case Iop_Max64F0x2:
      case Iop_Min32Fx4: case Iop_Min32F0x4:
      case Iop_Min64Fx2: case Iop_Min64F0x2:
      case Iop_Mul32Fx4: case Iop_Mul32F0x4:
      case Iop_Mul64Fx2: case Iop_Mul64F0x2:
      case Iop_Sub32Fx4: case Iop_Sub32F0x4:
      case Iop_Sub64Fx2: case Iop_Sub64F0x2:
      case Iop_AndV128: case Iop_OrV128: case Iop_XorV128:
      case Iop_Add8x16:   case Iop_Add16x8:   
      case Iop_Add32x4:   case Iop_Add64x2:
      case Iop_QAdd8Ux16: case Iop_QAdd16Ux8: case Iop_QAdd32Ux4:
      case Iop_QAdd8Sx16: case Iop_QAdd16Sx8: case Iop_QAdd32Sx4:
      case Iop_Sub8x16:   case Iop_Sub16x8:
      case Iop_Sub32x4:   case Iop_Sub64x2:
      case Iop_QSub8Ux16: case Iop_QSub16Ux8: case Iop_QSub32Ux4:
      case Iop_QSub8Sx16: case Iop_QSub16Sx8: case Iop_QSub32Sx4:
      case Iop_Mul16x8:
      case Iop_MulHi16Ux8: case Iop_MulHi32Ux4: 
      case Iop_MulHi16Sx8: case Iop_MulHi32Sx4: 
      case Iop_MullEven8Ux16: case Iop_MullEven16Ux8:
      case Iop_MullEven8Sx16: case Iop_MullEven16Sx8:
      case Iop_Avg8Ux16: case Iop_Avg16Ux8: case Iop_Avg32Ux4:
      case Iop_Avg8Sx16: case Iop_Avg16Sx8: case Iop_Avg32Sx4:
      case Iop_Max8Sx16: case Iop_Max16Sx8: case Iop_Max32Sx4:
      case Iop_Max8Ux16: case Iop_Max16Ux8: case Iop_Max32Ux4:
      case Iop_Min8Sx16: case Iop_Min16Sx8: case Iop_Min32Sx4:
      case Iop_Min8Ux16: case Iop_Min16Ux8: case Iop_Min32Ux4:
      case Iop_CmpEQ8x16:  case Iop_CmpEQ16x8:  case Iop_CmpEQ32x4:
      case Iop_CmpGT8Sx16: case Iop_CmpGT16Sx8: case Iop_CmpGT32Sx4:
      case Iop_CmpGT8Ux16: case Iop_CmpGT16Ux8: case Iop_CmpGT32Ux4:
      case Iop_Shl8x16: case Iop_Shl16x8: case Iop_Shl32x4:
      case Iop_Shr8x16: case Iop_Shr16x8: case Iop_Shr32x4:
      case Iop_Sar8x16: case Iop_Sar16x8: case Iop_Sar32x4:
      case Iop_Rol8x16: case Iop_Rol16x8: case Iop_Rol32x4:
      case Iop_QNarrow16Ux8: case Iop_QNarrow32Ux4:
      case Iop_QNarrow16Sx8: case Iop_QNarrow32Sx4:
      case Iop_Narrow16x8:   case Iop_Narrow32x4:
      case Iop_InterleaveHI8x16: case Iop_InterleaveHI16x8:
      case Iop_InterleaveHI32x4: case Iop_InterleaveHI64x2:
      case Iop_InterleaveLO8x16: case Iop_InterleaveLO16x8: 
      case Iop_InterleaveLO32x4: case Iop_InterleaveLO64x2:
      case Iop_Perm8x16:
         BINARY(Ity_I128,Ity_I128, Ity_I128);

      case Iop_NotV128:
      case Iop_Recip32Fx4: case Iop_Recip32F0x4:
      case Iop_Recip64Fx2: case Iop_Recip64F0x2:
      case Iop_RSqrt32Fx4: case Iop_RSqrt32F0x4:
      case Iop_RSqrt64Fx2: case Iop_RSqrt64F0x2:
      case Iop_Sqrt32Fx4:  case Iop_Sqrt32F0x4:
      case Iop_Sqrt64Fx2:  case Iop_Sqrt64F0x2:
      case Iop_CmpNEZ8x16: case Iop_CmpNEZ16x8:
      case Iop_CmpNEZ32x4: case Iop_CmpNEZ64x2:
         UNARY(Ity_I128, Ity_I128);

      case Iop_ShlV128: case Iop_ShrV128:
      case Iop_ShlN8x16: case Iop_ShlN16x8: 
      case Iop_ShlN32x4: case Iop_ShlN64x2:
      case Iop_ShrN8x16: case Iop_ShrN16x8: 
      case Iop_ShrN32x4: case Iop_ShrN64x2:
      case Iop_SarN8x16: case Iop_SarN16x8: case Iop_SarN32x4:
         BINARY(Ity_I128,Ity_I8, Ity_I128);

      case Iop_CmpEQF32:
	  BINARY(Ity_I32, Ity_I32, Ity_I1);
      case Iop_CmpEQF64:
	  BINARY(Ity_I64, Ity_I64, Ity_I1);
      case Iop_CmpEQI128:
	  BINARY(Ity_I128, Ity_I128, Ity_I1);
      case Iop_CmpEQV128:
	  BINARY(Ity_I128, Ity_I128, Ity_I1);
   }
#  undef UNARY
#  undef BINARY
#  undef TERNARY
#  undef COMPARISON
#  undef UNARY_COMPARISON

   ppIROp(op, stderr);
   vpanic("typeOfPrimop");
}


/*---------------------------------------------------------------*/
/*--- Helper functions for the IR -- IR Basic Blocks          ---*/
/*---------------------------------------------------------------*/

void addStmtToIRSB ( IRSB* bb, IRStmt* st )
{
   Int i;
   if (bb->stmts_used == bb->stmts_size) {
     IRStmt** stmts2 = (IRStmt **)__LibVEX_Alloc_Ptr_Array(&ir_heap, 2 * bb->stmts_size + 8);
      for (i = 0; i < bb->stmts_size; i++)
         stmts2[i] = bb->stmts[i];
      bb->stmts = stmts2;
      bb->stmts_size = bb->stmts_size * 2 + 8;
   }
   vassert(bb->stmts_used < bb->stmts_size);
   bb->stmts[bb->stmts_used] = st;
   bb->stmts_used++;
}


/*---------------------------------------------------------------*/
/*--- Helper functions for the IR -- IR Type Environments     ---*/
/*---------------------------------------------------------------*/

/* Allocate a new IRTemp, given its type. */

IRTemp newIRTemp ( IRTypeEnv* env )
{
   vassert(env);
   vassert(env->types_used >= 0);
   return env->types_used++;
}


/*---------------------------------------------------------------*/
/*--- Helper functions for the IR -- finding types of exprs   ---*/
/*---------------------------------------------------------------*/

IRType typeOfIRExprConst ( IRExprConst* con )
{
   switch (con->ty) {
      case Ity_I1:    return Ity_I1;
      case Ity_I8:    return Ity_I8;
      case Ity_I16:   return Ity_I16;
      case Ity_I32:   return Ity_I32;
      case Ity_I64:   return Ity_I64;
      case Ity_I128:  return Ity_I128;
      case Ity_INVALID:
	break;
   }
   abort();
}

/* Is this any value actually in the enumeration 'IRType' ? */
Bool isPlausibleIRType ( IRType ty )
{
   switch (ty) {
      case Ity_INVALID: case Ity_I1:
      case Ity_I8: case Ity_I16: case Ity_I32: 
      case Ity_I64: case Ity_I128:
         return True;
      default: 
         return False;
   }
}


#ifndef NDEBUG
/*---------------------------------------------------------------*/
/*--- Sanity checking                                         ---*/
/*---------------------------------------------------------------*/

/* Checks:

   Everything is type-consistent.  No ill-typed anything.
   The target address at the end of the BB is a 32- or 64-
   bit expression, depending on the guest's word size.

   Each temp is assigned only once, before its uses.
*/

static inline Int countArgs ( IRExpr** args )
{
   Int i;
   for (i = 0; args[i]; i++)
      ;
   return i;
}

static
__attribute((noreturn))
void sanityCheckFail ( IRSB* bb, IRStmt* stmt, const char* what )
{
   fprintf(stderr, "\nIR SANITY CHECK FAILURE\n\n");
   ppIRSB(bb, stderr);
   if (stmt) {
      fprintf(stderr, "\nIN STATEMENT:\n\n");
      ppIRStmt(stmt, stderr);
   }
   fprintf(stderr, "\n\nERROR = %s\n\n", what );
   vpanic("sanityCheckFail: exiting due to bad IR");
}

#endif

/*---------------------------------------------------------------*/
/*--- Misc helper functions                                   ---*/
/*---------------------------------------------------------------*/

Bool eqIRExprConst ( const IRExprConst* c1, const IRExprConst* c2 )
{
   if (c1->ty != c2->ty)
      return False;

   switch (c1->ty) {
      case Ity_I1:  return toBool( (1 & c1->Ico.U1) == (1 & c2->Ico.U1) );
      case Ity_I8:  return toBool( c1->Ico.U8  == c2->Ico.U8 );
      case Ity_I16: return toBool( c1->Ico.U16 == c2->Ico.U16 );
      case Ity_I32: return toBool( c1->Ico.U32 == c2->Ico.U32 );
      case Ity_I64: return toBool( c1->Ico.U64 == c2->Ico.U64 );
      case Ity_I128:
	return toBool( c1->Ico.U128.hi == c2->Ico.U128.hi &&
		       c1->Ico.U128.lo == c2->Ico.U128.lo );
      case Ity_INVALID: break;
   }
  vpanic("eqIRExprConst");
}

Int sizeofIRType ( IRType ty )
{
   switch (ty) {
      case Ity_I8:   return 1;
      case Ity_I16:  return 2;
      case Ity_I32:  return 4;
      case Ity_I64:  return 8;
      case Ity_I128: return 16;
      case Ity_I1:
      case Ity_INVALID:
	break;
   }
   fprintf(stderr, "\n"); ppIRType(ty, stderr); fprintf(stderr, "\n");
   vpanic("sizeofIRType");
}

IRExpr* mkIRExpr_HWord ( HWord hw )
{
   vassert(sizeof(void*) == sizeof(HWord));
   if (sizeof(HWord) == 4)
      return IRExpr_Const_U32((UInt)hw);
   if (sizeof(HWord) == 8)
      return IRExpr_Const_U64((ULong)hw);
   vpanic("mkIRExpr_HWord");
}

IRDirty* unsafeIRDirty_0_N ( Int regparms, const char* name, void* addr, 
                             IRExpr** args ) 
{
   IRDirty* d = emptyIRDirty();
   d->cee   = mkIRCallee ( regparms, name, addr, 0 );
   d->guard = IRExpr_Const_U1(True);
   d->args  = args;
   return d;
}

IRDirty* unsafeIRDirty_1_N ( threadAndRegister dst,
                             Int regparms, const char* name, void* addr, 
                             IRExpr** args ) 
{
   IRDirty* d = emptyIRDirty();
   d->cee   = mkIRCallee ( regparms, name, addr, 0 );
   d->guard = IRExpr_Const_U1(True);
   d->args  = args;
   d->tmp   = dst;
   return d;
}

IRExpr* mkIRExprCCall ( IRType retty,
                        Int regparms, const char* name, void* addr, 
                        IRExpr** args,
			UInt mcx_mask)
{
  return IRExpr_CCall ( mkIRCallee ( regparms, name, addr, mcx_mask ), 
                         retty, args );
}

CfgLabel
CfgLabelAllocator::operator()()
{
	return CfgLabel(++cntr);
}

void
CfgLabelAllocator::reset()
{
	cntr = 1;
}

/*---------------------------------------------------------------*/
/*--- end                                           ir_defs.c ---*/
/*---------------------------------------------------------------*/
