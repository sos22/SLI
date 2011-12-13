
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

/*---------------------------------------------------------------*/
/*--- Printing the IR                                         ---*/
/*---------------------------------------------------------------*/

void ppIRType ( IRType ty, FILE *f )
{
   switch (ty) {
      case Ity_INVALID: fprintf(f, "Ity_INVALID"); break;
      case Ity_I1:      fprintf(f,  "I1");   break;
      case Ity_I8:      fprintf(f,  "I8");   break;
      case Ity_I16:     fprintf(f,  "I16");  break;
      case Ity_I32:     fprintf(f,  "I32");  break;
      case Ity_I64:     fprintf(f,  "I64");  break;
      case Ity_I128:    fprintf(f,  "I128"); break;
      case Ity_F32:     fprintf(f,  "F32");  break;
      case Ity_F64:     fprintf(f,  "F64");  break;
      case Ity_V128:    fprintf(f,  "V128"); break;
      default: fprintf(f, "ty = 0x%x\n", (Int)ty);
               vpanic("ppIRType");
   }
}

static bool parseIRType(IRType *out, const char *str, const char **suffix)
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
  do_type(F32);
  do_type(F64);
  do_type(V128);
  do_type(I1);
#undef do_type
  return false;
}

void ppIRConst ( IRConst* con, FILE* f )
{
   union { ULong i64; Double f64; } u;
   vassert(sizeof(ULong) == sizeof(Double));
   switch (con->tag) {
      case Ico_U1:   fprintf(f,  "%d:I1",        con->Ico.U1 ? 1 : 0); break;
      case Ico_U8:   fprintf(f,  "0x%x:I8",      (UInt)(con->Ico.U8)); break;
      case Ico_U16:  fprintf(f,  "0x%x:I16",     (UInt)(con->Ico.U16)); break;
      case Ico_U32:  fprintf(f,  "0x%x:I32",     (UInt)(con->Ico.U32)); break;
      case Ico_U64:  fprintf(f,  "0x%llx:I64",   (ULong)(con->Ico.U64)); break;
      case Ico_F64:  u.f64 = con->Ico.F64;
                     fprintf(f,  "F64{0x%llx}",  u.i64);
                     break;
      case Ico_F64i: fprintf(f,  "F64i{0x%llx}", con->Ico.F64i); break;
      case Ico_V128: fprintf(f,  "V128{0x%04x}", (UInt)(con->Ico.V128)); break;
      default: vpanic("ppIRConst");
   }
}

static bool parseIRConst(IRConst **out, const char *str, const char **suffix)
{
  int val1;
  unsigned long val2;
  const char *str2;

  if (parseDecimalInt(&val1, str, &str2) &&
      parseThisString(":I1", str2, suffix)) {
    *out = IRConst_U1(val1);
    return true;
  }
  if (parseThisString("0x", str, &str2) &&
      parseHexUlong(&val2, str2, &str)) {
    *out = NULL;
    if (parseThisString(":I8", str, suffix))
      *out = IRConst_U8(val2);
    else if (parseThisString(":I16", str, suffix))
      *out = IRConst_U16(val2);
    else if (parseThisString(":I32", str, suffix))
      *out = IRConst_U32(val2);
    else if (parseThisString(":I64", str, suffix))
      *out = IRConst_U64(val2);
    if (*out)
      return true;
  }
  if (parseThisString("F64{0x", str, &str) &&
      parseHexUlong(&val2, str, &str) &&
      parseThisChar('}', str, suffix)) {
    union { ULong x; Double y; } u;
    u.x = val2;
    *out = IRConst_F64(u.y);
    return true;
  }
  if (parseThisString("F64i{0x", str, &str) &&
      parseHexUlong(&val2, str, &str) &&
      parseThisChar('}', str, suffix)) {
    *out = IRConst_F64i(val2);
    return true;
  }
  if (parseThisString("V128{0x", str, &str) &&
      parseHexUlong(&val2, str, &str) &&
      parseThisChar('}', str, suffix)) {
    *out = IRConst_V128(val2);
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
  *out = mkIRCallee(regparms, name, (void *)addr);
  (*out)->mcx_mask = mcx_mask;
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
  iter(Neg)

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
	     iter(Not1)				\
	     iter(32to1)			\
	     iter(64to1)			\
	     iter(1Uto8)			\
	     iter(1Uto32)			\
	     iter(1Uto64)			\
	     iter(1Sto8)			\
	     iter(1Sto16)			\
	     iter(1Sto32)			\
	     iter(1Sto64)			\
	     iter(And1)				\
	     iter(Or1)				\
	     iter(Xor1)				\
	     iter(BadPtr)			\
	     iter(CC_OverflowSub)		\
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
	     iter(Perm8x16)

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

static bool parseIROp(IROp *out, const char *str, const char **suffix)
{
  const char *str2;
#define __do_op2(name, sz)			\
  if (parseThisString( # sz , str2, suffix)) {	\
    *out = Iop_ ## name ## sz ;			\
    return true;				\
  }
#define do_op(name)				\
  if (parseThisString( #name, str, &str2)) {	\
    __do_op2(name, 8);				\
    __do_op2(name, 16);				\
    __do_op2(name, 32);				\
    __do_op2(name, 64);				\
  }
  foreach_op_sized(do_op)
#undef do_op
#undef __do_op2

#define do_op(name)					\
    if (parseThisString( #name, str, suffix) ) {	\
      *out = Iop_ ## name ;				\
      return true;					\
    }
    foreach_op_unsized(do_op)
#undef do_op

  return false;
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
  case Iop_Xor1:
    return "^^";
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

static bool parseIROpSimple(IROp *out, const char *str, const char **suffix)
{
  if (parseThisChar('+', str, suffix)) {
    *out = Iop_Add64;
    return true;
  }
  if (parseThisString("&&", str, suffix)) {
    *out = Iop_And1;
    return true;
  }
  if (parseThisString("||", str, suffix)) {
    *out = Iop_Or1;
    return true;
  }
  if (parseThisString("^^", str, suffix)) {
    *out = Iop_Xor1;
    return true;
  }
  if (parseThisChar('&', str, suffix)) {
    *out = Iop_And64;
    return true;
  }
  if (parseThisChar('|', str, suffix)) {
    *out = Iop_Or64;
    return true;
  }
  if (parseThisString("==", str, suffix)) {
    *out = Iop_CmpEQ64;
    return true;
  }
  if (parseThisChar('!', str, suffix)) {
    *out = Iop_Not1;
    return true;
  }
  if (parseThisString("BadPtr", str, suffix)) {
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

static bool parseIRExprGet(IRExpr **res, const char *str, const char **suffix)
{
  threadAndRegister reg(threadAndRegister::invalid());
  int offset;
  int tid;
  IRType ty;

#define do_reg(name)					\
  if (parseThisString( #name ":", str, &str)) {	\
    offset = OFFSET_amd64_ ## name;			\
    goto canned_register;				\
  }
  foreach_reg(do_reg);
#undef do_reg
  if (!parseThisString("GET:", str, &str) ||
      !parseIRType(&ty, str, &str) ||
      !parseThisChar('(', str, &str) ||
      !parseThreadAndRegister(&reg, str, &str) ||
      !parseThisChar(')', str, suffix))
    return false;
  *res = IRExpr_Get(reg, ty);
  return true;

 canned_register:
  int generation;
  if (!parseDecimalInt(&tid, str, &str) ||
      !parseThisChar(':', str, &str) ||
      !parseDecimalInt(&generation, str, suffix))
    return false;
  *res = IRExpr_Get(offset, Ity_I64, tid, generation);
  return true;
}

static bool parseIRExprGetI(IRExpr **res, const char *str, const char **suffix)
{
  IRRegArray *arr;
  IRExpr *ix;
  int bias;
  int tid;

  if (!parseThisString("GETI", str, &str) ||
      !parseIRRegArray(&arr, str, &str) ||
      !parseThisChar('[', str, &str) ||
      !parseIRExpr(&ix, str, &str) ||
      !parseThisChar(',', str, &str) ||
      !parseDecimalInt(&bias, str, &str) ||
      !parseThisString("](", str, &str) ||
      !parseDecimalInt(&tid, str, &str) ||
      !parseThisChar(')', str, suffix))
    return false;
  *res = IRExpr_GetI(arr, ix, bias, tid);
  return true;
}

static bool parseIRExprQop(IRExpr **res, const char *str, const char **suffix)
{
  IROp op;
  IRExpr *arg1, *arg2, *arg3, *arg4;
  if (!parseIROp(&op, str, &str) ||
      !parseThisChar('(', str, &str) ||
      !parseIRExpr(&arg1, str, &str) ||
      !parseThisChar(',', str, &str) ||
      !parseIRExpr(&arg2, str, &str) ||
      !parseThisChar(',', str, &str) ||
      !parseIRExpr(&arg3, str, &str) ||
      !parseThisChar(',', str, &str) ||
      !parseIRExpr(&arg4, str, &str) ||
      !parseThisChar(')', str, suffix))
    return false;
  *res = IRExpr_Qop(op, arg1, arg2, arg3, arg4);
  return true;
}

static bool parseIRExprTriop(IRExpr **res, const char *str, const char **suffix)
{
  IROp op;
  IRExpr *arg1, *arg2, *arg3;
  if (!parseIROp(&op, str, &str) ||
      !parseThisChar('(', str, &str) ||
      !parseIRExpr(&arg1, str, &str) ||
      !parseThisChar(',', str, &str) ||
      !parseIRExpr(&arg2, str, &str) ||
      !parseThisChar(',', str, &str) ||
      !parseIRExpr(&arg3, str, &str) ||
      !parseThisChar(')', str, suffix))
    return false;
  *res = IRExpr_Triop(op, arg1, arg2, arg3);
  return true;
}

static bool parseIRExprBinop(IRExpr **res, const char *str, const char **suffix)
{
  IRExpr *arg1, *arg2;
  IROp op;

  if (parseThisChar('(', str, &str)) {
    if (!parseIRExpr(&arg1, str, &str) ||
	!parseThisChar(' ', str, &str) ||
	!parseIROpSimple(&op, str, &str) ||
	!parseThisChar(' ', str, &str) ||
	!parseIRExpr(&arg2, str, &str) ||
	!parseThisChar(')', str, suffix))
      return false;
  } else {
    if (!parseIROp(&op, str, &str) ||
	!parseThisChar('(', str, &str) ||
	!parseIRExpr(&arg1, str, &str) ||
	!parseThisChar(',', str, &str) ||
	!parseIRExpr(&arg2, str, &str) ||
	!parseThisChar(')', str, suffix))
      return false;
  }
  *res = IRExpr_Binop(op, arg1, arg2);
  return true;
}

static bool parseIRExprUnop(IRExpr **res, const char *str, const char **suffix)
{
  IROp op;
  IRExpr *arg;

  if (!parseIROpSimple(&op, str, &str) &&
      !parseIROp(&op, str, &str))
    return false;
  if (!parseThisChar('(', str, &str) ||
      !parseIRExpr(&arg, str, &str) ||
      !parseThisChar(')', str, suffix))
    return false;
  *res = IRExpr_Unop(op, arg);
  return true;
}

static bool parseIRExprLoad(IRExpr **res, const char *str, const char **suffix)
{
  IRType ty;
  IRExpr *addr;
  ThreadRip rip;
  if (!parseThisString("LD:", str, &str) ||
      !parseIRType(&ty, str, &str) ||
      !parseThisChar('(', str, &str) ||
      !parseIRExpr(&addr, str, &str) ||
      !parseThisString(")@", str, &str) ||
      !parseThreadRip(&rip, str, suffix))
    return false;
  *res = IRExpr_Load(ty, addr, rip);
  return true;
}

static bool parseIRExprConst(IRExpr **res, const char *str, const char **suffix)
{
  IRConst *c;
  if (!parseIRConst(&c, str, suffix))
    return false;
  *res = IRExpr_Const(c);
  return true;
}

static bool parseIRExprCCall(IRExpr **res, const char *str, const char **suffix)
{
  IRCallee *cee;
  std::vector<IRExpr *> args;
  IRExpr *arg;
  IRType ty;
  IRExpr **argsA;

  if (!parseIRCallee(&cee, str, &str) ||
      !parseThisChar('(', str, &str))
    return false;
  while (1) {
    if (!parseIRExpr(&arg, str, &str))
      return false;
    args.push_back(arg);
    if (parseThisString("):", str, &str))
      break;
    if (!parseThisChar(',', str, &str))
      return false;
  }
  if (!parseIRType(&ty, str, suffix))
    return false;
  argsA = alloc_irexpr_array(args.size() + 1);
  for (unsigned i = 0; i < args.size(); i++)
    argsA[i] = args[i];
  argsA[args.size()] = NULL;
  *res = IRExpr_CCall(cee, ty, argsA);
  return true;
}

static bool parseIRExprMux0X(IRExpr **res, const char *str, const char **suffix)
{
  IRExpr *cond, *expr0, *exprX;
  if (!parseThisString("Mux0X(", str, &str) ||
      !parseIRExpr(&cond, str, &str) ||
      !parseThisChar(',', str, &str) ||
      !parseIRExpr(&expr0, str, &str) ||
      !parseThisChar(',', str, &str) ||
      !parseIRExpr(&exprX, str, &str) ||
      !parseThisChar(')', str, suffix))
    return false;
  *res = IRExpr_Mux0X(cond, expr0, exprX);
  return true;
}

static bool parseIRExprAssociative(IRExpr **res, const char *str, const char **suffix)
{
  IROp op = (IROp)-1;
  IROp op2;
  std::vector<IRExpr *> args;
  IRExpr *arg;

  if (parseThisChar('(', str, &str)) {
    while (1) {
      if (!parseIRExpr(&arg, str, &str))
	return false;
      args.push_back(arg);
      if (parseThisChar(')', str, &str))
	break;
      if (!parseThisChar(' ', str, &str))
	return false;
      if (!parseIROpSimple(&op2, str, &str))
	return false;
      if (op != (IROp)-1 && op != op2)
	return false;
      op = op2;
      if (!parseThisChar(' ', str, &str))
	return false;
    }
  } else {
    if (!parseThisString("Assoc(", str, &str) ||
	!parseIROp(&op, str, &str) ||
	!parseThisChar(':', str, &str))
      return false;
    while (1) {
      if (!parseIRExpr(&arg, str, &str))
	return false;
      args.push_back(arg);
      if (parseThisChar(')', str, &str))
	break;
      if (!parseThisString(", ", str, &str))
	return false;
    }
  }
  if (op == (IROp)-1) {
    assert(args.size() == 1);
    return false;
  }
  IRExprAssociative *e          = new IRExprAssociative();
  e->op = op;
  e->nr_arguments_allocated = args.size();
  e->nr_arguments = args.size();
  static libvex_allocation_site __las = {0, __FILE__, __LINE__};
  e->contents =
    (IRExpr **)__LibVEX_Alloc_Bytes(&ir_heap, sizeof(e->contents[0]) * args.size(), &__las);
  for (unsigned i = 0; i < args.size(); i++)
    e->contents[i] = args[i];
  *suffix = str;
  *res = e;
  return true;
}

static bool parseIRExprFreeVariable(IRExpr **res, const char *str, const char **suffix)
{
  FreeVariableKey key;
  if (!parseThisString("free", str, &str) ||
      !parseDecimalInt(&key.val, str, suffix))
    return false;
  *res = IRExpr_FreeVariable(key);
  return true;
}

static bool parseIRExprClientCall(IRExpr **res, const char *str, const char **suffix)
{
  unsigned long addr;
  ThreadRip site;
  if (!parseThisString("call0x", str, &str) ||
      !parseHexUlong(&addr, str, &str) ||
      !parseThisChar('@', str, &str) ||
      !parseThreadRip(&site, str, &str) ||
      !parseThisChar('(', str, &str))
    return false;
  std::vector<IRExpr *> args;
  while (1) {
    if (parseThisChar(')', str, suffix))
      break;
    if (args.size() != 0 &&
	!parseThisString(", ", str, &str))
      return false;
    IRExpr *arg;
    if (!parseIRExpr(&arg, str, &str))
      return false;
    args.push_back(arg);
  }
  IRExpr **a = alloc_irexpr_array(args.size() + 1);
  for (unsigned x = 0; x < args.size(); x++)
    a[x] = args[x];
  a[args.size()] = NULL;
  *res = IRExpr_ClientCall(addr, site, a);
  return true;
}

static bool parseIRExprFailedCall(IRExpr **res, const char *str, const char **suffix)
{
  IRExpr *target;
  if (!parseThisString("failedCall(", str, &str) ||
      !parseIRExpr(&target, str, &str) ||
      !parseThisChar(')', str, suffix))
    return false;
  *res = IRExpr_ClientCallFailed(target);
  return true;
}

static bool parseIRExprHappensBefore(IRExpr **res, const char *str, const char **suffix)
{
  ThreadRip before;
  ThreadRip after;
  if (!parseThisChar('(', str, &str) ||
      !parseThreadRip(&before, str, &str) ||
      !parseThisString(" <-< ", str, &str) ||
      !parseThreadRip(&after, str, &str) ||
      !parseThisChar(')', str, suffix))
    return false;
  *res = IRExpr_HappensBefore(before, after);
  return true;
}

bool parseIRExpr(IRExpr **out, const char *str, const char **suffix)
{
#define do_form(name)					\
  if (parseIRExpr ## name (out, str, suffix))		\
    return true;
  do_form(Get);
  do_form(GetI);
  do_form(Qop);
  do_form(Triop);
  do_form(Binop);
  do_form(Unop);
  do_form(Load);
  do_form(Const);
  do_form(CCall);
  do_form(Mux0X);
  do_form(Associative);
  do_form(FreeVariable);
  do_form(ClientCall);
  do_form(FailedCall);
  do_form(HappensBefore);
#undef do_form
  return false;
}

void
IRExprBinop::prettyPrint(FILE *f) const
{
  if (irOpSimpleChar(op)) {
    fprintf(f, "(");
    arg1->prettyPrint(f);
    fprintf(f,  " %s ", irOpSimpleChar(op) );
    arg2->prettyPrint(f);
    fprintf(f,  ")" );
  } else {
    ppIROp(op, f);
    fprintf(f,  "(" );
    arg1->prettyPrint(f);
    fprintf(f,  "," );
    arg2->prettyPrint(f);
    fprintf(f,  ")" );
  }
}

void
IRExprUnop::prettyPrint(FILE *f) const
{
  if (irOpSimpleChar(op))
    {
      fprintf(f, "%s(", irOpSimpleChar(op));
      ppIRExpr(arg, f);
      fprintf(f, ")");
    }
  else
    {
      ppIROp(op, f);
      fprintf(f,  "(" );
      ppIRExpr(arg, f);
      fprintf(f,  ")" );
    }
}

void
IRExprLoad::prettyPrint(FILE *f) const
{
      fprintf(f,  "LD:");
      ppIRType(ty, f);
      fprintf(f,  "(" );
      ppIRExpr(addr, f);
      fprintf(f,  ")@%s", rip.name() );
}
void
IRExprConst::prettyPrint(FILE *f) const
{
      ppIRConst(con, f);
}
void
IRExprCCall::prettyPrint(FILE *f) const
{
      ppIRCallee(cee, f);
      fprintf(f, "(");
      for (int i = 0; args[i] != NULL; i++) {
        ppIRExpr(args[i], f);
        if (args[i+1] != NULL)
          fprintf(f, ",");
      }
      fprintf(f, "):");
      ppIRType(retty, f);
}
void
IRExprMux0X::prettyPrint(FILE *f) const
{
      fprintf(f, "Mux0X(");
      ppIRExpr(cond, f);
      fprintf(f, ",");
      ppIRExpr(expr0, f);
      fprintf(f, ",");
      ppIRExpr(exprX, f);
      fprintf(f, ")");
}
void
IRExprAssociative::prettyPrint(FILE *f) const
{
      if (irOpSimpleChar(op))
      {
	fprintf(f, "(");
	for (int x = 0; x < nr_arguments; x++) {
	  if (x != 0)
	    fprintf(f, " %s ", irOpSimpleChar(op));
	  ppIRExpr(contents[x], f);
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
	  ppIRExpr(contents[x], f);
	}
	fprintf(f, ")");
      }
}
void
IRExprFreeVariable::prettyPrint(FILE *f) const
{
      fprintf(f, "free%d", key.val);
}
void
IRExprClientCall::prettyPrint(FILE *f) const
{
      fprintf(f, "call0x%lx@%s(", calledRip, callSite.name());
      for (int x = 0; args[x]; x++) {
	if (x != 0)
	  fprintf(f, ", ");
	ppIRExpr(args[x], f);
      }
      fprintf(f, ")");
}
void
IRExprClientCallFailed::prettyPrint(FILE *f) const
{
      fprintf(f, "failedCall(");
      ppIRExpr(target, f);
      fprintf(f, ")");
}
void
IRExprHappensBefore::prettyPrint(FILE *f) const
{
      fprintf(f, "(%s <-< %s)",
	      before.name(),
	      after.name());
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
   Int i;
   for (i = 0; i < env->types_used; i++) {
      if (i % 8 == 0)
         fprintf(f,  "   ");
      ppIRTemp(i, f);
      fprintf(f,  ":");
      ppIRType(env->types[i], f);
      if (i % 8 == 7) 
         fprintf(f,  "\n"); 
      else 
         fprintf(f,  "   ");
   }
   if (env->types_used > 0 && env->types_used % 8 != 7) 
      fprintf(f,  "\n"); 
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
   ppIRExpr( bb->next, f );
   fprintf(f,  "\n}\n");
}


/*---------------------------------------------------------------*/
/*--- Constructors                                            ---*/
/*---------------------------------------------------------------*/


/* Constructors -- IRConst */

IRConst* IRConst_U1 ( Bool bit )
{
   IRConst* c = new IRConst();
   c->tag     = Ico_U1;
   c->Ico.U1  = bit;
   /* call me paranoid; I don't care :-) */
   vassert(bit == False || bit == True);
   return c;
}
IRConst* IRConst_U8 ( UChar u8 )
{
   IRConst* c = new IRConst();
   c->tag     = Ico_U8;
   c->Ico.U8  = u8;
   return c;
}
IRConst* IRConst_U16 ( UShort u16 )
{
   IRConst* c = new IRConst();
   c->tag     = Ico_U16;
   c->Ico.U16 = u16;
   return c;
}
IRConst* IRConst_U32 ( UInt u32 )
{
   IRConst* c = new IRConst();
   c->tag     = Ico_U32;
   c->Ico.U32 = u32;
   return c;
}
IRConst* IRConst_U64 ( ULong u64 )
{
   IRConst* c = new IRConst();
   c->tag     = Ico_U64;
   c->Ico.U64 = u64;
   return c;
}
IRConst* IRConst_F64 ( Double f64 )
{
   IRConst* c = new IRConst();
   c->tag     = Ico_F64;
   c->Ico.F64 = f64;
   return c;
}
IRConst* IRConst_F64i ( ULong f64i )
{
   IRConst* c = new IRConst();
   c->tag      = Ico_F64i;
   c->Ico.F64i = f64i;
   return c;
}
IRConst* IRConst_V128 ( UShort con )
{
   IRConst* c = new IRConst();
   c->tag      = Ico_V128;
   c->Ico.V128 = con;
   return c;
}

/* Constructors -- IRCallee */

IRCallee* mkIRCallee ( Int regparms, const char* name, void* addr )
{
   IRCallee* ce = new IRCallee();
   ce->regparms = regparms;
   ce->name     = name;
   ce->addr     = addr;
   ce->mcx_mask = 0;
   vassert(regparms >= 0 && regparms <= 3);
   vassert(name != NULL);
   return ce;
}


/* Constructors -- IRRegArray */

IRRegArray* mkIRRegArray ( Int base, IRType elemTy, Int nElems )
{
   IRRegArray* arr = new IRRegArray();
   arr->base       = base;
   arr->elemTy     = elemTy;
   arr->nElems     = nElems;
   vassert(!(arr->base < 0 || arr->base > 10000 /* somewhat arbitrary */));
   vassert(!(arr->elemTy == Ity_I1));
   vassert(!(arr->nElems <= 0 || arr->nElems > 500 /* somewhat arbitrary */));
   return arr;
}


/* Constructors -- IRExpr */

IRExpr* IRExpr_Get ( threadAndRegister reg, IRType ty) {
   return new IRExprGet(reg, ty);
}
IRExpr* IRExpr_Get ( Int off, IRType ty, unsigned tid, unsigned generation ) {
   return IRExpr_Get(threadAndRegister::reg(tid, off, generation), ty);
}
IRExpr* IRExpr_GetI ( IRRegArray* descr, IRExpr* ix, Int bias, unsigned tid ) {
   IRExprGetI* e         = new IRExprGetI();
   e->descr = descr;
   e->ix    = ix;
   e->bias  = bias;
   e->tid   = tid;
   return e;
}
IRExpr* IRExpr_RdTmp ( IRTemp tmp, unsigned tid, unsigned generation ) {
   return IRExpr_Get(-tmp - 1, Ity_INVALID, tid, generation);
}
IRExpr* IRExpr_Qop ( IROp op, IRExpr* arg1, IRExpr* arg2, 
                              IRExpr* arg3, IRExpr* arg4 ) {
   IRExprQop* e       = new IRExprQop();
   e->op   = op;
   e->arg1 = arg1;
   e->arg2 = arg2;
   e->arg3 = arg3;
   e->arg4 = arg4;
   return e;
}
IRExpr* IRExpr_Triop  ( IROp op, IRExpr* arg1, 
                                 IRExpr* arg2, IRExpr* arg3 ) {
   IRExprTriop* e         = new IRExprTriop();
   e->op   = op;
   e->arg1 = arg1;
   e->arg2 = arg2;
   e->arg3 = arg3;
   return e;
}
IRExpr* IRExpr_Binop ( IROp op, IRExpr* arg1, IRExpr* arg2 ) {
   IRExprBinop* e         = new IRExprBinop();
   e->op   = op;
   e->arg1 = arg1;
   e->arg2 = arg2;
   return e;
}
IRExpr* IRExpr_Unop ( IROp op, IRExpr* arg ) {
   IRExprUnop* e       = new IRExprUnop();
   e->op  = op;
   e->arg = arg;
   return e;
}
IRExpr* IRExpr_Load ( IRType ty, IRExpr* addr, ThreadRip rip ) {
   IRExprLoad* e        = new IRExprLoad();
   e->ty   = ty;
   e->addr = addr;
   e->rip  = rip;
   return e;
}
IRExpr* IRExpr_Const ( IRConst* con ) {
   IRExprConst* e        = new IRExprConst();
   e->con = con;
   return e;
}
IRExpr* IRExpr_CCall ( IRCallee* cee, IRType retty, IRExpr** args ) {
   IRExprCCall* e          = new IRExprCCall();
   e->cee   = cee;
   e->retty = retty;
   e->args  = args;
   return e;
}
IRExpr* IRExpr_Mux0X ( IRExpr* cond, IRExpr* expr0, IRExpr* exprX ) {
   IRExprMux0X* e          = new IRExprMux0X();
   e->cond  = cond;
   e->expr0 = expr0;
   e->exprX = exprX;
   return e;
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

   e->nr_arguments_allocated = nr_args * 2;
   static libvex_allocation_site __las = {0, __FILE__, __LINE__};
   e->contents =
      (IRExpr **)__LibVEX_Alloc_Bytes(&ir_heap, sizeof(e->contents[0]) * nr_args * 2, &__las);
   va_start(args, op);
   while (e->nr_arguments < nr_args) {
      arg = va_arg(args, IRExpr *);
      e->contents[e->nr_arguments] =
	 arg;
      e->nr_arguments++;
   }
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
IRExpr* IRExpr_FreeVariable ( FreeVariableKey key )
{
   IRExprFreeVariable *e = new IRExprFreeVariable();
   e->key = key;
   return e;
}
IRExpr* IRExpr_FreeVariable ( )
{
   static FreeVariableKey next_key;
   IRExpr *res = IRExpr_FreeVariable(next_key);
   next_key.val++;
   return res;
}
IRExpr* IRExpr_ClientCall ( unsigned long r, ThreadRip site, IRExpr **args )
{
   IRExprClientCall *e = new IRExprClientCall();
   e->calledRip = r;
   e->callSite = site;
   e->args = args;
   return e;
}
IRExpr* IRExpr_ClientCallFailed ( IRExpr *t )
{
   IRExprClientCallFailed *e = new IRExprClientCallFailed();
   e->target = t;
   return e;
}
IRExpr* IRExpr_HappensBefore ( ThreadRip before, ThreadRip after )
{
   IRExprHappensBefore *e = new IRExprHappensBefore();
   e->before = before;
   e->after = after;
   return e;
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
IRStmt* IRStmt_IMark ( Addr64 addr, Int len ) {
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
IRStmt* IRStmt_Exit ( IRExpr* guard, IRJumpKind jk, IRConst* dst )
{
   return new IRStmtExit(guard, jk, dst);
}


/* Constructors -- IRTypeEnv */

IRTypeEnv* emptyIRTypeEnv ( void )
{
   IRTypeEnv* env   = new IRTypeEnv();
   env->types       = (IRType *)__LibVEX_Alloc_Bytes(&ir_heap, 8 * sizeof(IRType), NULL);
   env->types_size  = 8;
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
   bb->next       = NULL;
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
      *t_dst = (_td); *t_arg1 = (_ta1); break
#  define BINARY(_ta1,_ta2,_td)                                \
     *t_dst = (_td); *t_arg1 = (_ta1); *t_arg2 = (_ta2); break
#  define TERNARY(_ta1,_ta2,_ta3,_td)                          \
     *t_dst = (_td); *t_arg1 = (_ta1);                         \
     *t_arg2 = (_ta2); *t_arg3 = (_ta3); break
#  define QUATERNARY(_ta1,_ta2,_ta3,_ta4,_td)                  \
     *t_dst = (_td); *t_arg1 = (_ta1);                         \
     *t_arg2 = (_ta2); *t_arg3 = (_ta3);                       \
     *t_arg4 = (_ta4); break
#  define COMPARISON(_ta)                                      \
     *t_dst = Ity_I1; *t_arg1 = *t_arg2 = (_ta); break;
#  define UNARY_COMPARISON(_ta)                                \
     *t_dst = Ity_I1; *t_arg1 = (_ta); break;

   /* Rounding mode values are always Ity_I32, encoded as per
      IRRoundingMode */
   const IRType ity_RMode = Ity_I32;

   *t_dst  = Ity_INVALID;
   *t_arg1 = Ity_INVALID;
   *t_arg2 = Ity_INVALID;
   *t_arg3 = Ity_INVALID;
   *t_arg4 = Ity_INVALID;
   switch (op) {
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
         UNARY(Ity_I8, Ity_I8);
      case Iop_Not16:
         UNARY(Ity_I16, Ity_I16);
      case Iop_Not32:
         UNARY(Ity_I32, Ity_I32);

      case Iop_Not64:
      case Iop_CmpNEZ32x2: case Iop_CmpNEZ16x4: case Iop_CmpNEZ8x8:
         UNARY(Ity_I64, Ity_I64);

      case Iop_CmpEQ8: case Iop_CmpNE8:
      case Iop_CasCmpEQ8: case Iop_CasCmpNE8:
         COMPARISON(Ity_I8);
      case Iop_CmpEQ16: case Iop_CmpNE16:
      case Iop_CasCmpEQ16: case Iop_CasCmpNE16:
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
      case Iop_32to1:  UNARY(Ity_I32, Ity_I1);
      case Iop_64to1:  UNARY(Ity_I64, Ity_I1);
      case Iop_And1: case Iop_Or1: case Iop_Xor1: BINARY(Ity_I1, Ity_I1, Ity_I1);
      case Iop_BadPtr: UNARY(Ity_I1, Ity_I64);

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
         TERNARY(ity_RMode,Ity_F64,Ity_F64, Ity_F64);

      case Iop_NegF64: case Iop_AbsF64: 
         UNARY(Ity_F64, Ity_F64);

      case Iop_SqrtF64:
      case Iop_SqrtF64r32:
         BINARY(ity_RMode,Ity_F64, Ity_F64);

      case Iop_CmpF64:
         BINARY(Ity_F64,Ity_F64, Ity_I32);

      case Iop_F64toI16: BINARY(ity_RMode,Ity_F64, Ity_I16);
      case Iop_F64toI32: BINARY(ity_RMode,Ity_F64, Ity_I32);
      case Iop_F64toI64: BINARY(ity_RMode,Ity_F64, Ity_I64);

      case Iop_I16toF64: UNARY(Ity_I16, Ity_F64);
      case Iop_I32toF64: UNARY(Ity_I32, Ity_F64);
      case Iop_I64toF64: BINARY(ity_RMode,Ity_I64, Ity_F64);

      case Iop_F32toF64: UNARY(Ity_F32, Ity_F64);
      case Iop_F64toF32: BINARY(ity_RMode,Ity_F64, Ity_F32);

      case Iop_ReinterpI64asF64: UNARY(Ity_I64, Ity_F64);
      case Iop_ReinterpF64asI64: UNARY(Ity_F64, Ity_I64);
      case Iop_ReinterpI32asF32: UNARY(Ity_I32, Ity_F32);
      case Iop_ReinterpF32asI32: UNARY(Ity_F32, Ity_I32);

      case Iop_AtanF64: case Iop_Yl2xF64:  case Iop_Yl2xp1F64: 
      case Iop_ScaleF64: case Iop_PRemF64: case Iop_PRem1F64:
         TERNARY(ity_RMode,Ity_F64,Ity_F64, Ity_F64);

      case Iop_PRemC3210F64: case Iop_PRem1C3210F64:
         TERNARY(ity_RMode,Ity_F64,Ity_F64, Ity_I32);

      case Iop_SinF64: case Iop_CosF64: case Iop_TanF64: 
      case Iop_2xm1F64:
      case Iop_RoundF64toInt: BINARY(ity_RMode,Ity_F64, Ity_F64);

      case Iop_MAddF64: case Iop_MSubF64:
      case Iop_MAddF64r32: case Iop_MSubF64r32:
         QUATERNARY(ity_RMode,Ity_F64,Ity_F64,Ity_F64, Ity_F64);

      case Iop_Est5FRSqrt:
      case Iop_RoundF64toF64_NEAREST: case Iop_RoundF64toF64_NegINF:
      case Iop_RoundF64toF64_PosINF: case Iop_RoundF64toF64_ZERO:
         UNARY(Ity_F64, Ity_F64);
      case Iop_RoundF64toF32:
         BINARY(ity_RMode,Ity_F64, Ity_F64);
      case Iop_CalcFPRF:
         UNARY(Ity_F64, Ity_I32);
      case Iop_TruncF64asF32:
         UNARY(Ity_F64, Ity_F32);

      case Iop_I32UtoFx4:
      case Iop_I32StoFx4:
      case Iop_QFtoI32Ux4_RZ:
      case Iop_QFtoI32Sx4_RZ:
      case Iop_RoundF32x4_RM:
      case Iop_RoundF32x4_RP:
      case Iop_RoundF32x4_RN:
      case Iop_RoundF32x4_RZ:
         UNARY(Ity_V128, Ity_V128);

      case Iop_64HLtoV128: BINARY(Ity_I64,Ity_I64, Ity_V128);
      case Iop_V128to64: case Iop_V128HIto64: 
         UNARY(Ity_V128, Ity_I64);

      case Iop_V128to32:    UNARY(Ity_V128, Ity_I32);
      case Iop_32UtoV128:   UNARY(Ity_I32, Ity_V128);
      case Iop_64UtoV128:   UNARY(Ity_I64, Ity_V128);
      case Iop_SetV128lo32: BINARY(Ity_V128,Ity_I32, Ity_V128);
      case Iop_SetV128lo64: BINARY(Ity_V128,Ity_I64, Ity_V128);

      case Iop_Dup8x16: UNARY(Ity_I8, Ity_V128);
      case Iop_Dup16x8: UNARY(Ity_I16, Ity_V128);
      case Iop_Dup32x4: UNARY(Ity_I32, Ity_V128);

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
         BINARY(Ity_V128,Ity_V128, Ity_V128);

      case Iop_NotV128:
      case Iop_Recip32Fx4: case Iop_Recip32F0x4:
      case Iop_Recip64Fx2: case Iop_Recip64F0x2:
      case Iop_RSqrt32Fx4: case Iop_RSqrt32F0x4:
      case Iop_RSqrt64Fx2: case Iop_RSqrt64F0x2:
      case Iop_Sqrt32Fx4:  case Iop_Sqrt32F0x4:
      case Iop_Sqrt64Fx2:  case Iop_Sqrt64F0x2:
      case Iop_CmpNEZ8x16: case Iop_CmpNEZ16x8:
      case Iop_CmpNEZ32x4: case Iop_CmpNEZ64x2:
         UNARY(Ity_V128, Ity_V128);

      case Iop_ShlV128: case Iop_ShrV128:
      case Iop_ShlN8x16: case Iop_ShlN16x8: 
      case Iop_ShlN32x4: case Iop_ShlN64x2:
      case Iop_ShrN8x16: case Iop_ShrN16x8: 
      case Iop_ShrN32x4: case Iop_ShrN64x2:
      case Iop_SarN8x16: case Iop_SarN16x8: case Iop_SarN32x4:
         BINARY(Ity_V128,Ity_I8, Ity_V128);

      default:
	 ppIROp(op, stderr);
         vpanic("typeOfPrimop");
   }
#  undef UNARY
#  undef BINARY
#  undef TERNARY
#  undef COMPARISON
#  undef UNARY_COMPARISON
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

IRTemp newIRTemp ( IRTypeEnv* env, IRType ty )
{
   vassert(env);
   vassert(env->types_used >= 0);
   vassert(env->types_size >= 0);
   vassert(env->types_used <= env->types_size);
   if (env->types_used < env->types_size) {
      env->types[env->types_used] = ty;
      return env->types_used++;
   } else {
      Int i;
      Int new_size = env->types_size==0 ? 8 : 2*env->types_size;
      IRType* new_types 
	= (IRType *)__LibVEX_Alloc_Bytes(&ir_heap, new_size * sizeof(IRType), NULL);
      for (i = 0; i < env->types_used; i++)
         new_types[i] = env->types[i];
      env->types      = new_types;
      env->types_size = new_size;
      return newIRTemp(env, ty);
   }
}


/*---------------------------------------------------------------*/
/*--- Helper functions for the IR -- finding types of exprs   ---*/
/*---------------------------------------------------------------*/

IRType typeOfIRTemp ( IRTypeEnv* env, IRTemp tmp )
{
   vassert(tmp >= 0);
   //   vassert(tmp < env->types_used);
   return env->types[tmp];
}


IRType typeOfIRConst ( IRConst* con )
{
   switch (con->tag) {
      case Ico_U1:    return Ity_I1;
      case Ico_U8:    return Ity_I8;
      case Ico_U16:   return Ity_I16;
      case Ico_U32:   return Ity_I32;
      case Ico_U64:   return Ity_I64;
      case Ico_F64:   return Ity_F64;
      case Ico_F64i:  return Ity_F64;
      case Ico_V128:  return Ity_V128;
      default: vpanic("typeOfIRConst");
   }
}

/* Is this any value actually in the enumeration 'IRType' ? */
Bool isPlausibleIRType ( IRType ty )
{
   switch (ty) {
      case Ity_INVALID: case Ity_I1:
      case Ity_I8: case Ity_I16: case Ity_I32: 
      case Ity_I64: case Ity_I128:
      case Ity_F32: case Ity_F64:
      case Ity_V128:
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

Bool eqIRConst ( IRConst* c1, IRConst* c2 )
{
   if (c1->tag != c2->tag)
      return False;

   switch (c1->tag) {
      case Ico_U1:  return toBool( (1 & c1->Ico.U1) == (1 & c2->Ico.U1) );
      case Ico_U8:  return toBool( c1->Ico.U8  == c2->Ico.U8 );
      case Ico_U16: return toBool( c1->Ico.U16 == c2->Ico.U16 );
      case Ico_U32: return toBool( c1->Ico.U32 == c2->Ico.U32 );
      case Ico_U64: return toBool( c1->Ico.U64 == c2->Ico.U64 );
      case Ico_F64: return toBool( c1->Ico.F64 == c2->Ico.F64 );
      case Ico_F64i: return toBool( c1->Ico.F64i == c2->Ico.F64i );
      case Ico_V128: return toBool( c1->Ico.V128 == c2->Ico.V128 );
      default: vpanic("eqIRConst");
   }
}

Int sizeofIRType ( IRType ty )
{
   switch (ty) {
      case Ity_I8:   return 1;
      case Ity_I16:  return 2;
      case Ity_I32:  return 4;
      case Ity_I64:  return 8;
      case Ity_F32:  return 4;
      case Ity_F64:  return 8;
      case Ity_V128: return 16;
      default: fprintf(stderr, "\n"); ppIRType(ty, stderr); fprintf(stderr, "\n");
               vpanic("sizeofIRType");
   }
}

IRExpr* mkIRExpr_HWord ( HWord hw )
{
   vassert(sizeof(void*) == sizeof(HWord));
   if (sizeof(HWord) == 4)
      return IRExpr_Const(IRConst_U32((UInt)hw));
   if (sizeof(HWord) == 8)
      return IRExpr_Const(IRConst_U64((ULong)hw));
   vpanic("mkIRExpr_HWord");
}

IRDirty* unsafeIRDirty_0_N ( Int regparms, const char* name, void* addr, 
                             IRExpr** args ) 
{
   IRDirty* d = emptyIRDirty();
   d->cee   = mkIRCallee ( regparms, name, addr );
   d->guard = IRExpr_Const(IRConst_U1(True));
   d->args  = args;
   return d;
}

IRDirty* unsafeIRDirty_1_N ( threadAndRegister dst,
                             Int regparms, const char* name, void* addr, 
                             IRExpr** args ) 
{
   IRDirty* d = emptyIRDirty();
   d->cee   = mkIRCallee ( regparms, name, addr );
   d->guard = IRExpr_Const(IRConst_U1(True));
   d->args  = args;
   d->tmp   = dst;
   return d;
}

IRExpr* mkIRExprCCall ( IRType retty,
                        Int regparms, const char* name, void* addr, 
                        IRExpr** args )
{
   return IRExpr_CCall ( mkIRCallee ( regparms, name, addr ), 
                         retty, args );
}

/*---------------------------------------------------------------*/
/*--- end                                           ir_defs.c ---*/
/*---------------------------------------------------------------*/
