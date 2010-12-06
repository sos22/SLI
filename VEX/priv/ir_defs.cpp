
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

#include "libvex_basictypes.h"
#include "libvex_ir.h"
#include "libvex.h"

#include "main_util.h"

Heap ir_heap;

void
IRExpr::visit(HeapVisitor &visit)
{
   switch (tag) {
   case Iex_Binder:
   case Iex_Get:
   case Iex_RdTmp:
     break;
   case Iex_GetI:
     visit(Iex.GetI.descr);
     visit(Iex.GetI.ix);
     break;
   case Iex_Qop:
     visit(Iex.Qop.arg1);
     visit(Iex.Qop.arg2);
     visit(Iex.Qop.arg3);
     visit(Iex.Qop.arg4);
     break;
   case Iex_Triop:
     visit(Iex.Triop.arg1);
     visit(Iex.Triop.arg2);
     visit(Iex.Triop.arg3);
     break;
   case Iex_Binop:
     visit(Iex.Binop.arg1);
     visit(Iex.Binop.arg2);
     break;
   case Iex_Unop:
     visit(Iex.Unop.arg);
     break;
   case Iex_Load:
     visit(Iex.Load.addr);
     break;
   case Iex_Const:
     visit(Iex.Const.con);
     break;
   case Iex_CCall:
     visit(Iex.CCall.cee);
     visit(Iex.CCall.args);
     break;
   case Iex_Mux0X:
     visit(Iex.Mux0X.cond);
     visit(Iex.Mux0X.expr0);
     visit(Iex.Mux0X.exprX);
     break;
   }
}

void
_IRStmt::visit(HeapVisitor &visit)
{
   switch (tag) {
   case Ist_NoOp:
   case Ist_IMark:
     break;
   case Ist_AbiHint:
     visit(Ist.AbiHint.base);
     visit(Ist.AbiHint.nia);
     break;
   case Ist_Put:
     visit(Ist.Put.data);
     break;
   case Ist_PutI:
     visit(Ist.PutI.descr);
     visit(Ist.PutI.ix);
     visit(Ist.PutI.data);
     break;
   case Ist_WrTmp:
     visit(Ist.WrTmp.data);
     break;
   case Ist_Store:
     visit(Ist.Store.addr);
     visit(Ist.Store.data);
     break;
   case Ist_CAS:
     visit(Ist.CAS.details);
     break;
   case Ist_Dirty:
     visit(Ist.Dirty.details);
     break;
   case Ist_MBE:
     break;
   case Ist_Exit:
     visit(Ist.Exit.guard);
     visit(Ist.Exit.dst);
     break;
   }
}

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

void ppIRCallee ( IRCallee* ce, FILE* f )
{
   fprintf(f, "%s", ce->name);
   if (ce->regparms > 0)
      fprintf(f, "[rp=%d]", ce->regparms);
   if (ce->mcx_mask > 0)
      fprintf(f, "[mcx=0x%x]", ce->mcx_mask);
   fprintf(f, "{%p}", (void*)ce->addr);
}

void ppIRRegArray ( IRRegArray* arr, FILE* f )
{
   fprintf(f, "(%d:%dx", arr->base, arr->nElems);
   ppIRType(arr->elemTy, f);
   fprintf(f, ")");
}

void ppIRTemp ( IRTemp tmp, FILE* f )
{
   if (tmp == IRTemp_INVALID)
      fprintf(f, "IRTemp_INVALID");
   else
      fprintf(f,  "t%d", (Int)tmp);
}

void ppIROp ( IROp op, FILE* f )
{
   const char* str = NULL; 
   IROp   base;
   switch (op) {
      case Iop_Add8 ... Iop_Add64:
         str = "Add"; base = Iop_Add8; break;
      case Iop_Sub8 ... Iop_Sub64:
         str = "Sub"; base = Iop_Sub8; break;
      case Iop_Mul8 ... Iop_Mul64:
         str = "Mul"; base = Iop_Mul8; break;
      case Iop_Or8 ... Iop_Or64:
         str = "Or"; base = Iop_Or8; break;
      case Iop_And8 ... Iop_And64:
         str = "And"; base = Iop_And8; break;
      case Iop_Xor8 ... Iop_Xor64:
         str = "Xor"; base = Iop_Xor8; break;
      case Iop_Shl8 ... Iop_Shl64:
         str = "Shl"; base = Iop_Shl8; break;
      case Iop_Shr8 ... Iop_Shr64:
         str = "Shr"; base = Iop_Shr8; break;
      case Iop_Sar8 ... Iop_Sar64:
         str = "Sar"; base = Iop_Sar8; break;
      case Iop_CmpEQ8 ... Iop_CmpEQ64:
         str = "CmpEQ"; base = Iop_CmpEQ8; break;
      case Iop_CmpNE8 ... Iop_CmpNE64:
         str = "CmpNE"; base = Iop_CmpNE8; break;
      case Iop_CasCmpEQ8 ... Iop_CasCmpEQ64:
         str = "CasCmpEQ"; base = Iop_CasCmpEQ8; break;
      case Iop_CasCmpNE8 ... Iop_CasCmpNE64:
         str = "CasCmpNE"; base = Iop_CasCmpNE8; break;
      case Iop_Not8 ... Iop_Not64:
         str = "Not"; base = Iop_Not8; break;
      case Iop_Neg8 ... Iop_Neg64:
         str = "Neg"; base = Iop_Neg8; break;
      /* other cases must explicitly "return;" */
      case Iop_8Uto16:   fprintf(f, "8Uto16");  return;
      case Iop_8Uto32:   fprintf(f, "8Uto32");  return;
      case Iop_16Uto32:  fprintf(f, "16Uto32"); return;
      case Iop_8Sto16:   fprintf(f, "8Sto16");  return;
      case Iop_8Sto32:   fprintf(f, "8Sto32");  return;
      case Iop_16Sto32:  fprintf(f, "16Sto32"); return;
      case Iop_32Sto64:  fprintf(f, "32Sto64"); return;
      case Iop_32Uto64:  fprintf(f, "32Uto64"); return;
      case Iop_32to8:    fprintf(f, "32to8");   return;
      case Iop_16Uto64:  fprintf(f, "16Uto64"); return;
      case Iop_16Sto64:  fprintf(f, "16Sto64"); return;
      case Iop_8Uto64:   fprintf(f, "8Uto64"); return;
      case Iop_8Sto64:   fprintf(f, "8Sto64"); return;
      case Iop_64to16:   fprintf(f, "64to16"); return;
      case Iop_64to8:    fprintf(f, "64to8");  return;

      case Iop_Not1:     fprintf(f, "Not1");    return;
      case Iop_32to1:    fprintf(f, "32to1");   return;
      case Iop_64to1:    fprintf(f, "64to1");   return;
      case Iop_1Uto8:    fprintf(f, "1Uto8");   return;
      case Iop_1Uto32:   fprintf(f, "1Uto32");  return;
      case Iop_1Uto64:   fprintf(f, "1Uto64");  return;
      case Iop_1Sto8:    fprintf(f, "1Sto8");  return;
      case Iop_1Sto16:   fprintf(f, "1Sto16");  return;
      case Iop_1Sto32:   fprintf(f, "1Sto32");  return;
      case Iop_1Sto64:   fprintf(f, "1Sto64");  return;
      case Iop_And1:     fprintf(f, "And1");    return;

      case Iop_MullS8:   fprintf(f, "MullS8");  return;
      case Iop_MullS16:  fprintf(f, "MullS16"); return;
      case Iop_MullS32:  fprintf(f, "MullS32"); return;
      case Iop_MullS64:  fprintf(f, "MullS64"); return;
      case Iop_MullU8:   fprintf(f, "MullU8");  return;
      case Iop_MullU16:  fprintf(f, "MullU16"); return;
      case Iop_MullU32:  fprintf(f, "MullU32"); return;
      case Iop_MullU64:  fprintf(f, "MullU64"); return;

      case Iop_Clz64:    fprintf(f, "Clz64"); return;
      case Iop_Clz32:    fprintf(f, "Clz32"); return;
      case Iop_Ctz64:    fprintf(f, "Ctz64"); return;
      case Iop_Ctz32:    fprintf(f, "Ctz32"); return;

      case Iop_CmpLT32S: fprintf(f, "CmpLT32S"); return;
      case Iop_CmpLE32S: fprintf(f, "CmpLE32S"); return;
      case Iop_CmpLT32U: fprintf(f, "CmpLT32U"); return;
      case Iop_CmpLE32U: fprintf(f, "CmpLE32U"); return;

      case Iop_CmpLT64S: fprintf(f, "CmpLT64S"); return;
      case Iop_CmpLE64S: fprintf(f, "CmpLE64S"); return;
      case Iop_CmpLT64U: fprintf(f, "CmpLT64U"); return;
      case Iop_CmpLE64U: fprintf(f, "CmpLE64U"); return;

      case Iop_CmpNEZ8:  fprintf(f, "CmpNEZ8"); return;
      case Iop_CmpNEZ16: fprintf(f, "CmpNEZ16"); return;
      case Iop_CmpNEZ32: fprintf(f, "CmpNEZ32"); return;
      case Iop_CmpNEZ64: fprintf(f, "CmpNEZ64"); return;

      case Iop_CmpwNEZ32: fprintf(f, "CmpwNEZ32"); return;
      case Iop_CmpwNEZ64: fprintf(f, "CmpwNEZ64"); return;

      case Iop_Left8:  fprintf(f, "Left8"); return;
      case Iop_Left16: fprintf(f, "Left16"); return;
      case Iop_Left32: fprintf(f, "Left32"); return;
      case Iop_Left64: fprintf(f, "Left64"); return;
      case Iop_Max32U: fprintf(f, "Max32U"); return;

      case Iop_CmpORD32U: fprintf(f, "CmpORD32U"); return;
      case Iop_CmpORD32S: fprintf(f, "CmpORD32S"); return;

      case Iop_CmpORD64U: fprintf(f, "CmpORD64U"); return;
      case Iop_CmpORD64S: fprintf(f, "CmpORD64S"); return;

      case Iop_DivU32: fprintf(f, "DivU32"); return;
      case Iop_DivS32: fprintf(f, "DivS32"); return;
      case Iop_DivU64: fprintf(f, "DivU64"); return;
      case Iop_DivS64: fprintf(f, "DivS64"); return;

      case Iop_DivModU64to32: fprintf(f, "DivModU64to32"); return;
      case Iop_DivModS64to32: fprintf(f, "DivModS64to32"); return;

      case Iop_DivModU128to64: fprintf(f, "DivModU128to64"); return;
      case Iop_DivModS128to64: fprintf(f, "DivModS128to64"); return;

      case Iop_16HIto8:  fprintf(f, "16HIto8"); return;
      case Iop_16to8:    fprintf(f, "16to8");   return;
      case Iop_8HLto16:  fprintf(f, "8HLto16"); return;

      case Iop_32HIto16: fprintf(f, "32HIto16"); return;
      case Iop_32to16:   fprintf(f, "32to16");   return;
      case Iop_16HLto32: fprintf(f, "16HLto32"); return;

      case Iop_64HIto32: fprintf(f, "64HIto32"); return;
      case Iop_64to32:   fprintf(f, "64to32");   return;
      case Iop_32HLto64: fprintf(f, "32HLto64"); return;

      case Iop_128HIto64: fprintf(f, "128HIto64"); return;
      case Iop_128to64:   fprintf(f, "128to64");   return;
      case Iop_64HLto128: fprintf(f, "64HLto128"); return;

      case Iop_AddF64:    fprintf(f, "AddF64"); return;
      case Iop_SubF64:    fprintf(f, "SubF64"); return;
      case Iop_MulF64:    fprintf(f, "MulF64"); return;
      case Iop_DivF64:    fprintf(f, "DivF64"); return;
      case Iop_AddF64r32: fprintf(f, "AddF64r32"); return;
      case Iop_SubF64r32: fprintf(f, "SubF64r32"); return;
      case Iop_MulF64r32: fprintf(f, "MulF64r32"); return;
      case Iop_DivF64r32: fprintf(f, "DivF64r32"); return;

      case Iop_ScaleF64:      fprintf(f, "ScaleF64"); return;
      case Iop_AtanF64:       fprintf(f, "AtanF64"); return;
      case Iop_Yl2xF64:       fprintf(f, "Yl2xF64"); return;
      case Iop_Yl2xp1F64:     fprintf(f, "Yl2xp1F64"); return;
      case Iop_PRemF64:       fprintf(f, "PRemF64"); return;
      case Iop_PRemC3210F64:  fprintf(f, "PRemC3210F64"); return;
      case Iop_PRem1F64:      fprintf(f, "PRem1F64"); return;
      case Iop_PRem1C3210F64: fprintf(f, "PRem1C3210F64"); return;
      case Iop_NegF64:        fprintf(f, "NegF64"); return;
      case Iop_SqrtF64:       fprintf(f, "SqrtF64"); return;

      case Iop_AbsF64:    fprintf(f, "AbsF64"); return;
      case Iop_SinF64:    fprintf(f, "SinF64"); return;
      case Iop_CosF64:    fprintf(f, "CosF64"); return;
      case Iop_TanF64:    fprintf(f, "TanF64"); return;
      case Iop_2xm1F64:   fprintf(f, "2xm1F64"); return;

      case Iop_MAddF64:    fprintf(f, "MAddF64"); return;
      case Iop_MSubF64:    fprintf(f, "MSubF64"); return;
      case Iop_MAddF64r32: fprintf(f, "MAddF64r32"); return;
      case Iop_MSubF64r32: fprintf(f, "MSubF64r32"); return;

      case Iop_Est5FRSqrt:    fprintf(f, "Est5FRSqrt"); return;
      case Iop_RoundF64toF64_NEAREST: fprintf(f, "RoundF64toF64_NEAREST"); return;
      case Iop_RoundF64toF64_NegINF: fprintf(f, "RoundF64toF64_NegINF"); return;
      case Iop_RoundF64toF64_PosINF: fprintf(f, "RoundF64toF64_PosINF"); return;
      case Iop_RoundF64toF64_ZERO: fprintf(f, "RoundF64toF64_ZERO"); return;

      case Iop_TruncF64asF32: fprintf(f, "TruncF64asF32"); return;
      case Iop_CalcFPRF:      fprintf(f, "CalcFPRF"); return;

      case Iop_CmpF64:    fprintf(f, "CmpF64"); return;

      case Iop_F64toI16: fprintf(f, "F64toI16"); return;
      case Iop_F64toI32: fprintf(f, "F64toI32"); return;
      case Iop_F64toI64: fprintf(f, "F64toI64"); return;

      case Iop_I16toF64: fprintf(f, "I16toF64"); return;
      case Iop_I32toF64: fprintf(f, "I32toF64"); return;
      case Iop_I64toF64: fprintf(f, "I64toF64"); return;

      case Iop_F32toF64: fprintf(f, "F32toF64"); return;
      case Iop_F64toF32: fprintf(f, "F64toF32"); return;

      case Iop_RoundF64toInt: fprintf(f, "RoundF64toInt"); return;
      case Iop_RoundF64toF32: fprintf(f, "RoundF64toF32"); return;

      case Iop_ReinterpF64asI64: fprintf(f, "ReinterpF64asI64"); return;
      case Iop_ReinterpI64asF64: fprintf(f, "ReinterpI64asF64"); return;
      case Iop_ReinterpF32asI32: fprintf(f, "ReinterpF32asI32"); return;
      case Iop_ReinterpI32asF32: fprintf(f, "ReinterpI32asF32"); return;

      case Iop_I32UtoFx4: fprintf(f, "I32UtoFx4"); return;
      case Iop_I32StoFx4: fprintf(f, "I32StoFx4"); return;

      case Iop_QFtoI32Ux4_RZ: fprintf(f, "QFtoI32Ux4_RZ"); return;
      case Iop_QFtoI32Sx4_RZ: fprintf(f, "QFtoI32Sx4_RZ"); return;

      case Iop_RoundF32x4_RM: fprintf(f, "RoundF32x4_RM"); return;
      case Iop_RoundF32x4_RP: fprintf(f, "RoundF32x4_RP"); return;
      case Iop_RoundF32x4_RN: fprintf(f, "RoundF32x4_RN"); return;
      case Iop_RoundF32x4_RZ: fprintf(f, "RoundF32x4_RZ"); return;

      case Iop_Add8x8: fprintf(f, "Add8x8"); return;
      case Iop_Add16x4: fprintf(f, "Add16x4"); return;
      case Iop_Add32x2: fprintf(f, "Add32x2"); return;
      case Iop_QAdd8Ux8: fprintf(f, "QAdd8Ux8"); return;
      case Iop_QAdd16Ux4: fprintf(f, "QAdd16Ux4"); return;
      case Iop_QAdd8Sx8: fprintf(f, "QAdd8Sx8"); return;
      case Iop_QAdd16Sx4: fprintf(f, "QAdd16Sx4"); return;
      case Iop_Sub8x8: fprintf(f, "Sub8x8"); return;
      case Iop_Sub16x4: fprintf(f, "Sub16x4"); return;
      case Iop_Sub32x2: fprintf(f, "Sub32x2"); return;
      case Iop_QSub8Ux8: fprintf(f, "QSub8Ux8"); return;
      case Iop_QSub16Ux4: fprintf(f, "QSub16Ux4"); return;
      case Iop_QSub8Sx8: fprintf(f, "QSub8Sx8"); return;
      case Iop_QSub16Sx4: fprintf(f, "QSub16Sx4"); return;
      case Iop_Mul16x4: fprintf(f, "Mul16x4"); return;
      case Iop_Mul32x2: fprintf(f, "Mul32x2"); return;
      case Iop_MulHi16Ux4: fprintf(f, "MulHi16Ux4"); return;
      case Iop_MulHi16Sx4: fprintf(f, "MulHi16Sx4"); return;
      case Iop_Avg8Ux8: fprintf(f, "Avg8Ux8"); return;
      case Iop_Avg16Ux4: fprintf(f, "Avg16Ux4"); return;
      case Iop_Max16Sx4: fprintf(f, "Max16Sx4"); return;
      case Iop_Max8Ux8: fprintf(f, "Max8Ux8"); return;
      case Iop_Min16Sx4: fprintf(f, "Min16Sx4"); return;
      case Iop_Min8Ux8: fprintf(f, "Min8Ux8"); return;
      case Iop_CmpEQ8x8: fprintf(f, "CmpEQ8x8"); return;
      case Iop_CmpEQ16x4: fprintf(f, "CmpEQ16x4"); return;
      case Iop_CmpEQ32x2: fprintf(f, "CmpEQ32x2"); return;
      case Iop_CmpGT8Sx8: fprintf(f, "CmpGT8Sx8"); return;
      case Iop_CmpGT16Sx4: fprintf(f, "CmpGT16Sx4"); return;
      case Iop_CmpGT32Sx2: fprintf(f, "CmpGT32Sx2"); return;
      case Iop_ShlN8x8: fprintf(f, "ShlN8x8"); return;
      case Iop_ShlN16x4: fprintf(f, "ShlN16x4"); return;
      case Iop_ShlN32x2: fprintf(f, "ShlN32x2"); return;
      case Iop_ShrN16x4: fprintf(f, "ShrN16x4"); return;
      case Iop_ShrN32x2: fprintf(f, "ShrN32x2"); return;
      case Iop_SarN8x8: fprintf(f, "SarN8x8"); return;
      case Iop_SarN16x4: fprintf(f, "SarN16x4"); return;
      case Iop_SarN32x2: fprintf(f, "SarN32x2"); return;
      case Iop_QNarrow16Ux4: fprintf(f, "QNarrow16Ux4"); return;
      case Iop_QNarrow16Sx4: fprintf(f, "QNarrow16Sx4"); return;
      case Iop_QNarrow32Sx2: fprintf(f, "QNarrow32Sx2"); return;
      case Iop_InterleaveHI8x8: fprintf(f, "InterleaveHI8x8"); return;
      case Iop_InterleaveHI16x4: fprintf(f, "InterleaveHI16x4"); return;
      case Iop_InterleaveHI32x2: fprintf(f, "InterleaveHI32x2"); return;
      case Iop_InterleaveLO8x8: fprintf(f, "InterleaveLO8x8"); return;
      case Iop_InterleaveLO16x4: fprintf(f, "InterleaveLO16x4"); return;
      case Iop_InterleaveLO32x2: fprintf(f, "InterleaveLO32x2"); return;
      case Iop_CatOddLanes16x4: fprintf(f, "CatOddLanes16x4"); return;
      case Iop_CatEvenLanes16x4: fprintf(f, "CatEvenLanes16x4"); return;
      case Iop_Perm8x8: fprintf(f, "Perm8x8"); return;

      case Iop_CmpNEZ32x2: fprintf(f, "CmpNEZ32x2"); return;
      case Iop_CmpNEZ16x4: fprintf(f, "CmpNEZ16x4"); return;
      case Iop_CmpNEZ8x8:  fprintf(f, "CmpNEZ8x8"); return;

      case Iop_Add32Fx4:  fprintf(f, "Add32Fx4"); return;
      case Iop_Add32F0x4: fprintf(f, "Add32F0x4"); return;
      case Iop_Add64Fx2:  fprintf(f, "Add64Fx2"); return;
      case Iop_Add64F0x2: fprintf(f, "Add64F0x2"); return;

      case Iop_Div32Fx4:  fprintf(f, "Div32Fx4"); return;
      case Iop_Div32F0x4: fprintf(f, "Div32F0x4"); return;
      case Iop_Div64Fx2:  fprintf(f, "Div64Fx2"); return;
      case Iop_Div64F0x2: fprintf(f, "Div64F0x2"); return;

      case Iop_Max32Fx4:  fprintf(f, "Max32Fx4"); return;
      case Iop_Max32F0x4: fprintf(f, "Max32F0x4"); return;
      case Iop_Max64Fx2:  fprintf(f, "Max64Fx2"); return;
      case Iop_Max64F0x2: fprintf(f, "Max64F0x2"); return;

      case Iop_Min32Fx4:  fprintf(f, "Min32Fx4"); return;
      case Iop_Min32F0x4: fprintf(f, "Min32F0x4"); return;
      case Iop_Min64Fx2:  fprintf(f, "Min64Fx2"); return;
      case Iop_Min64F0x2: fprintf(f, "Min64F0x2"); return;

      case Iop_Mul32Fx4:  fprintf(f, "Mul32Fx4"); return;
      case Iop_Mul32F0x4: fprintf(f, "Mul32F0x4"); return;
      case Iop_Mul64Fx2:  fprintf(f, "Mul64Fx2"); return;
      case Iop_Mul64F0x2: fprintf(f, "Mul64F0x2"); return;

      case Iop_Recip32Fx4:  fprintf(f, "Recip32Fx4"); return;
      case Iop_Recip32F0x4: fprintf(f, "Recip32F0x4"); return;
      case Iop_Recip64Fx2:  fprintf(f, "Recip64Fx2"); return;
      case Iop_Recip64F0x2: fprintf(f, "Recip64F0x2"); return;

      case Iop_RSqrt32Fx4:  fprintf(f, "RSqrt32Fx4"); return;
      case Iop_RSqrt32F0x4: fprintf(f, "RSqrt32F0x4"); return;
      case Iop_RSqrt64Fx2:  fprintf(f, "RSqrt64Fx2"); return;
      case Iop_RSqrt64F0x2: fprintf(f, "RSqrt64F0x2"); return;

      case Iop_Sqrt32Fx4:  fprintf(f, "Sqrt32Fx4"); return;
      case Iop_Sqrt32F0x4: fprintf(f, "Sqrt32F0x4"); return;
      case Iop_Sqrt64Fx2:  fprintf(f, "Sqrt64Fx2"); return;
      case Iop_Sqrt64F0x2: fprintf(f, "Sqrt64F0x2"); return;

      case Iop_Sub32Fx4:  fprintf(f, "Sub32Fx4"); return;
      case Iop_Sub32F0x4: fprintf(f, "Sub32F0x4"); return;
      case Iop_Sub64Fx2:  fprintf(f, "Sub64Fx2"); return;
      case Iop_Sub64F0x2: fprintf(f, "Sub64F0x2"); return;

      case Iop_CmpEQ32Fx4: fprintf(f, "CmpEQ32Fx4"); return;
      case Iop_CmpLT32Fx4: fprintf(f, "CmpLT32Fx4"); return;
      case Iop_CmpLE32Fx4: fprintf(f, "CmpLE32Fx4"); return;
      case Iop_CmpGT32Fx4: fprintf(f, "CmpGT32Fx4"); return;
      case Iop_CmpGE32Fx4: fprintf(f, "CmpGE32Fx4"); return;
      case Iop_CmpUN32Fx4: fprintf(f, "CmpUN32Fx4"); return;
      case Iop_CmpEQ64Fx2: fprintf(f, "CmpEQ64Fx2"); return;
      case Iop_CmpLT64Fx2: fprintf(f, "CmpLT64Fx2"); return;
      case Iop_CmpLE64Fx2: fprintf(f, "CmpLE64Fx2"); return;
      case Iop_CmpUN64Fx2: fprintf(f, "CmpUN64Fx2"); return;

      case Iop_CmpEQ32F0x4: fprintf(f, "CmpEQ32F0x4"); return;
      case Iop_CmpLT32F0x4: fprintf(f, "CmpLT32F0x4"); return;
      case Iop_CmpLE32F0x4: fprintf(f, "CmpLE32F0x4"); return;
      case Iop_CmpUN32F0x4: fprintf(f, "CmpUN32F0x4"); return;
      case Iop_CmpEQ64F0x2: fprintf(f, "CmpEQ64F0x2"); return;
      case Iop_CmpLT64F0x2: fprintf(f, "CmpLT64F0x2"); return;
      case Iop_CmpLE64F0x2: fprintf(f, "CmpLE64F0x2"); return;
      case Iop_CmpUN64F0x2: fprintf(f, "CmpUN64F0x2"); return;

      case Iop_V128to64:   fprintf(f, "V128to64");   return;
      case Iop_V128HIto64: fprintf(f, "V128HIto64"); return;
      case Iop_64HLtoV128: fprintf(f, "64HLtoV128"); return;

      case Iop_64UtoV128:   fprintf(f, "64UtoV128"); return;
      case Iop_SetV128lo64: fprintf(f, "SetV128lo64"); return;

      case Iop_32UtoV128:   fprintf(f, "32UtoV128"); return;
      case Iop_V128to32:    fprintf(f, "V128to32"); return;
      case Iop_SetV128lo32: fprintf(f, "SetV128lo32"); return;

      case Iop_Dup8x16: fprintf(f, "Dup8x16"); return;
      case Iop_Dup16x8: fprintf(f, "Dup16x8"); return;
      case Iop_Dup32x4: fprintf(f, "Dup32x4"); return;

      case Iop_NotV128:    fprintf(f, "NotV128"); return;
      case Iop_AndV128:    fprintf(f, "AndV128"); return;
      case Iop_OrV128:     fprintf(f, "OrV128");  return;
      case Iop_XorV128:    fprintf(f, "XorV128"); return;

      case Iop_CmpNEZ8x16: fprintf(f, "CmpNEZ8x16"); return;
      case Iop_CmpNEZ16x8: fprintf(f, "CmpNEZ16x8"); return;
      case Iop_CmpNEZ32x4: fprintf(f, "CmpNEZ32x4"); return;
      case Iop_CmpNEZ64x2: fprintf(f, "CmpNEZ64x2"); return;

      case Iop_Add8x16:   fprintf(f, "Add8x16"); return;
      case Iop_Add16x8:   fprintf(f, "Add16x8"); return;
      case Iop_Add32x4:   fprintf(f, "Add32x4"); return;
      case Iop_Add64x2:   fprintf(f, "Add64x2"); return;
      case Iop_QAdd8Ux16: fprintf(f, "QAdd8Ux16"); return;
      case Iop_QAdd16Ux8: fprintf(f, "QAdd16Ux8"); return;
      case Iop_QAdd32Ux4: fprintf(f, "QAdd32Ux4"); return;
      case Iop_QAdd8Sx16: fprintf(f, "QAdd8Sx16"); return;
      case Iop_QAdd16Sx8: fprintf(f, "QAdd16Sx8"); return;
      case Iop_QAdd32Sx4: fprintf(f, "QAdd32Sx4"); return;

      case Iop_Sub8x16:   fprintf(f, "Sub8x16"); return;
      case Iop_Sub16x8:   fprintf(f, "Sub16x8"); return;
      case Iop_Sub32x4:   fprintf(f, "Sub32x4"); return;
      case Iop_Sub64x2:   fprintf(f, "Sub64x2"); return;
      case Iop_QSub8Ux16: fprintf(f, "QSub8Ux16"); return;
      case Iop_QSub16Ux8: fprintf(f, "QSub16Ux8"); return;
      case Iop_QSub32Ux4: fprintf(f, "QSub32Ux4"); return;
      case Iop_QSub8Sx16: fprintf(f, "QSub8Sx16"); return;
      case Iop_QSub16Sx8: fprintf(f, "QSub16Sx8"); return;
      case Iop_QSub32Sx4: fprintf(f, "QSub32Sx4"); return;

      case Iop_Mul16x8:    fprintf(f, "Mul16x8"); return;
      case Iop_MulHi16Ux8: fprintf(f, "MulHi16Ux8"); return;
      case Iop_MulHi32Ux4: fprintf(f, "MulHi32Ux4"); return;
      case Iop_MulHi16Sx8: fprintf(f, "MulHi16Sx8"); return;
      case Iop_MulHi32Sx4: fprintf(f, "MulHi32Sx4"); return;

      case Iop_MullEven8Ux16: fprintf(f, "MullEven8Ux16"); return;
      case Iop_MullEven16Ux8: fprintf(f, "MullEven16Ux8"); return;
      case Iop_MullEven8Sx16: fprintf(f, "MullEven8Sx16"); return;
      case Iop_MullEven16Sx8: fprintf(f, "MullEven16Sx8"); return;

      case Iop_Avg8Ux16: fprintf(f, "Avg8Ux16"); return;
      case Iop_Avg16Ux8: fprintf(f, "Avg16Ux8"); return;
      case Iop_Avg32Ux4: fprintf(f, "Avg32Ux4"); return;
      case Iop_Avg8Sx16: fprintf(f, "Avg8Sx16"); return;
      case Iop_Avg16Sx8: fprintf(f, "Avg16Sx8"); return;
      case Iop_Avg32Sx4: fprintf(f, "Avg32Sx4"); return;

      case Iop_Max8Sx16: fprintf(f, "Max8Sx16"); return;
      case Iop_Max16Sx8: fprintf(f, "Max16Sx8"); return;
      case Iop_Max32Sx4: fprintf(f, "Max32Sx4"); return;
      case Iop_Max8Ux16: fprintf(f, "Max8Ux16"); return;
      case Iop_Max16Ux8: fprintf(f, "Max16Ux8"); return;
      case Iop_Max32Ux4: fprintf(f, "Max32Ux4"); return;

      case Iop_Min8Sx16: fprintf(f, "Min8Sx16"); return;
      case Iop_Min16Sx8: fprintf(f, "Min16Sx8"); return;
      case Iop_Min32Sx4: fprintf(f, "Min32Sx4"); return;
      case Iop_Min8Ux16: fprintf(f, "Min8Ux16"); return;
      case Iop_Min16Ux8: fprintf(f, "Min16Ux8"); return;
      case Iop_Min32Ux4: fprintf(f, "Min32Ux4"); return;

      case Iop_CmpEQ8x16:  fprintf(f, "CmpEQ8x16"); return;
      case Iop_CmpEQ16x8:  fprintf(f, "CmpEQ16x8"); return;
      case Iop_CmpEQ32x4:  fprintf(f, "CmpEQ32x4"); return;
      case Iop_CmpGT8Sx16: fprintf(f, "CmpGT8Sx16"); return;
      case Iop_CmpGT16Sx8: fprintf(f, "CmpGT16Sx8"); return;
      case Iop_CmpGT32Sx4: fprintf(f, "CmpGT32Sx4"); return;
      case Iop_CmpGT8Ux16: fprintf(f, "CmpGT8Ux16"); return;
      case Iop_CmpGT16Ux8: fprintf(f, "CmpGT16Ux8"); return;
      case Iop_CmpGT32Ux4: fprintf(f, "CmpGT32Ux4"); return;

      case Iop_ShlV128: fprintf(f, "ShlV128"); return;
      case Iop_ShrV128: fprintf(f, "ShrV128"); return;

      case Iop_ShlN8x16: fprintf(f, "ShlN8x16"); return;
      case Iop_ShlN16x8: fprintf(f, "ShlN16x8"); return;
      case Iop_ShlN32x4: fprintf(f, "ShlN32x4"); return;
      case Iop_ShlN64x2: fprintf(f, "ShlN64x2"); return;
      case Iop_ShrN8x16: fprintf(f, "ShrN8x16"); return;
      case Iop_ShrN16x8: fprintf(f, "ShrN16x8"); return;
      case Iop_ShrN32x4: fprintf(f, "ShrN32x4"); return;
      case Iop_ShrN64x2: fprintf(f, "ShrN64x2"); return;
      case Iop_SarN8x16: fprintf(f, "SarN8x16"); return;
      case Iop_SarN16x8: fprintf(f, "SarN16x8"); return;
      case Iop_SarN32x4: fprintf(f, "SarN32x4"); return;

      case Iop_Shl8x16: fprintf(f, "Shl8x16"); return;
      case Iop_Shl16x8: fprintf(f, "Shl16x8"); return;
      case Iop_Shl32x4: fprintf(f, "Shl32x4"); return;
      case Iop_Shr8x16: fprintf(f, "Shr8x16"); return;
      case Iop_Shr16x8: fprintf(f, "Shr16x8"); return;
      case Iop_Shr32x4: fprintf(f, "Shr32x4"); return;
      case Iop_Sar8x16: fprintf(f, "Sar8x16"); return;
      case Iop_Sar16x8: fprintf(f, "Sar16x8"); return;
      case Iop_Sar32x4: fprintf(f, "Sar32x4"); return;
      case Iop_Rol8x16: fprintf(f, "Rol8x16"); return;
      case Iop_Rol16x8: fprintf(f, "Rol16x8"); return;
      case Iop_Rol32x4: fprintf(f, "Rol32x4"); return;

      case Iop_Narrow16x8:   fprintf(f, "Narrow16x8"); return;
      case Iop_Narrow32x4:   fprintf(f, "Narrow32x4"); return;
      case Iop_QNarrow16Ux8: fprintf(f, "QNarrow16Ux8"); return;
      case Iop_QNarrow32Ux4: fprintf(f, "QNarrow32Ux4"); return;
      case Iop_QNarrow16Sx8: fprintf(f, "QNarrow16Sx8"); return;
      case Iop_QNarrow32Sx4: fprintf(f, "QNarrow32Sx4"); return;

      case Iop_InterleaveHI8x16: fprintf(f, "InterleaveHI8x16"); return;
      case Iop_InterleaveHI16x8: fprintf(f, "InterleaveHI16x8"); return;
      case Iop_InterleaveHI32x4: fprintf(f, "InterleaveHI32x4"); return;
      case Iop_InterleaveHI64x2: fprintf(f, "InterleaveHI64x2"); return;
      case Iop_InterleaveLO8x16: fprintf(f, "InterleaveLO8x16"); return;
      case Iop_InterleaveLO16x8: fprintf(f, "InterleaveLO16x8"); return;
      case Iop_InterleaveLO32x4: fprintf(f, "InterleaveLO32x4"); return;
      case Iop_InterleaveLO64x2: fprintf(f, "InterleaveLO64x2"); return;

      case Iop_Perm8x16: fprintf(f, "Perm8x16"); return;

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

void ppIRExpr ( IRExpr* e, FILE *f )
{
  Int i;
  switch (e->tag) {
    case Iex_Binder:
      fprintf(f, "BIND-%d", e->Iex.Binder.binder);
      break;
    case Iex_Get:
      fprintf(f,  "GET:" );
      ppIRType(e->Iex.Get.ty, f);
      fprintf(f, "(%d)", e->Iex.Get.offset);
      break;
    case Iex_GetI:
      fprintf(f,  "GETI" );
      ppIRRegArray(e->Iex.GetI.descr, f);
      fprintf(f, "[");
      ppIRExpr(e->Iex.GetI.ix, f);
      fprintf(f, ",%d]", e->Iex.GetI.bias);
      break;
    case Iex_RdTmp:
      ppIRTemp(e->Iex.RdTmp.tmp, f);
      break;
    case Iex_Qop:
      ppIROp(e->Iex.Qop.op, f);
      fprintf(f,  "(" );
      ppIRExpr(e->Iex.Qop.arg1, f);
      fprintf(f,  "," );
      ppIRExpr(e->Iex.Qop.arg2, f);
      fprintf(f,  "," );
      ppIRExpr(e->Iex.Qop.arg3, f);
      fprintf(f,  "," );
      ppIRExpr(e->Iex.Qop.arg4, f);
      fprintf(f,  ")" );
      break;
    case Iex_Triop:
      ppIROp(e->Iex.Triop.op, f);
      fprintf(f,  "(" );
      ppIRExpr(e->Iex.Triop.arg1, f);
      fprintf(f,  "," );
      ppIRExpr(e->Iex.Triop.arg2, f);
      fprintf(f,  "," );
      ppIRExpr(e->Iex.Triop.arg3, f);
      fprintf(f,  ")" );
      break;
    case Iex_Binop:
      ppIROp(e->Iex.Binop.op, f);
      fprintf(f,  "(" );
      ppIRExpr(e->Iex.Binop.arg1, f);
      fprintf(f,  "," );
      ppIRExpr(e->Iex.Binop.arg2, f);
      fprintf(f,  ")" );
      break;
    case Iex_Unop:
      ppIROp(e->Iex.Unop.op, f);
      fprintf(f,  "(" );
      ppIRExpr(e->Iex.Unop.arg, f);
      fprintf(f,  ")" );
      break;
    case Iex_Load:
      fprintf(f,  "LD%s%s:", e->Iex.Load.end==Iend_LE ? "le" : "be",
                             e->Iex.Load.isLL ? "-LL" : "" );
      ppIRType(e->Iex.Load.ty, f);
      fprintf(f,  "(" );
      ppIRExpr(e->Iex.Load.addr, f);
      fprintf(f,  ")" );
      break;
    case Iex_Const:
      ppIRConst(e->Iex.Const.con, f);
      break;
    case Iex_CCall:
      ppIRCallee(e->Iex.CCall.cee, f);
      fprintf(f, "(");
      for (i = 0; e->Iex.CCall.args[i] != NULL; i++) {
        ppIRExpr(e->Iex.CCall.args[i], f);
        if (e->Iex.CCall.args[i+1] != NULL)
          fprintf(f, ",");
      }
      fprintf(f, "):");
      ppIRType(e->Iex.CCall.retty, f);
      break;
    case Iex_Mux0X:
      fprintf(f, "Mux0X(");
      ppIRExpr(e->Iex.Mux0X.cond, f);
      fprintf(f, ",");
      ppIRExpr(e->Iex.Mux0X.expr0, f);
      fprintf(f, ",");
      ppIRExpr(e->Iex.Mux0X.exprX, f);
      fprintf(f, ")");
      break;
    default:
      vpanic("ppIRExpr");
  }
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
   if (d->tmp != IRTemp_INVALID) {
      ppIRTemp(d->tmp, f);
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
   if (cas->oldHi != IRTemp_INVALID) {
      ppIRTemp(cas->oldHi, f);
      fprintf(f, ",");
   }
   ppIRTemp(cas->oldLo, f);
   fprintf(f, " = CAS%s(", cas->end==Iend_LE ? "le" : "be" );
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
   switch (s->tag) {
      case Ist_NoOp:
         fprintf(f, "IR-NoOp");
         break;
      case Ist_IMark:
         fprintf(f,  "------ IMark(0x%llx, %d) ------", 
                     s->Ist.IMark.addr, s->Ist.IMark.len);
         break;
      case Ist_AbiHint:
         fprintf(f, "====== AbiHint(");
         ppIRExpr(s->Ist.AbiHint.base, f);
         fprintf(f, ", %d, ", s->Ist.AbiHint.len);
         ppIRExpr(s->Ist.AbiHint.nia, f);
         fprintf(f, ") ======");
         break;
      case Ist_Put:
         fprintf(f,  "PUT(%d) = ", s->Ist.Put.offset);
         ppIRExpr(s->Ist.Put.data, f);
         break;
      case Ist_PutI:
         fprintf(f,  "PUTI" );
         ppIRRegArray(s->Ist.PutI.descr, f);
         fprintf(f, "[");
         ppIRExpr(s->Ist.PutI.ix, f);
         fprintf(f, ",%d] = ", s->Ist.PutI.bias);
         ppIRExpr(s->Ist.PutI.data, f);
         break;
      case Ist_WrTmp:
         ppIRTemp(s->Ist.WrTmp.tmp, f);
         fprintf(f,  " = " );
         ppIRExpr(s->Ist.WrTmp.data, f);
         break;
      case Ist_Store:
         if (s->Ist.Store.resSC != IRTemp_INVALID) {
            ppIRTemp(s->Ist.Store.resSC, f);
            fprintf(f,  " = SC( " );
         }
         fprintf(f,  "ST%s(", s->Ist.Store.end==Iend_LE ? "le" : "be" );
         ppIRExpr(s->Ist.Store.addr, f);
         fprintf(f,  ") = ");
         ppIRExpr(s->Ist.Store.data, f);
         if (s->Ist.Store.resSC != IRTemp_INVALID)
            fprintf(f,  " )" );
         break;
      case Ist_CAS:
         ppIRCAS(s->Ist.CAS.details, f);
         break;
      case Ist_Dirty:
         ppIRDirty(s->Ist.Dirty.details, f);
         break;
      case Ist_MBE:
         fprintf(f, "IR-");
         ppIRMBusEvent(s->Ist.MBE.event, f);
         break;
      case Ist_Exit:
         fprintf(f,  "if (" );
         ppIRExpr(s->Ist.Exit.guard, f);
         fprintf(f,  ") goto {");
         ppIRJumpKind(s->Ist.Exit.jk, f);
         fprintf(f, "} ");
         ppIRConst(s->Ist.Exit.dst, f);
         break;
      default: 
         vpanic("ppIRStmt");
   }
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
   vassert(addr != 0);
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

IRExpr* IRExpr_Binder ( Int binder ) {
   IRExpr* e            = new IRExpr();
   e->tag               = Iex_Binder;
   e->Iex.Binder.binder = binder;
   return e;
}
IRExpr* IRExpr_Get ( Int off, IRType ty ) {
   IRExpr* e         = new IRExpr();
   e->tag            = Iex_Get;
   e->Iex.Get.offset = off;
   e->Iex.Get.ty     = ty;
   return e;
}
IRExpr* IRExpr_GetI ( IRRegArray* descr, IRExpr* ix, Int bias ) {
   IRExpr* e         = new IRExpr();
   e->tag            = Iex_GetI;
   e->Iex.GetI.descr = descr;
   e->Iex.GetI.ix    = ix;
   e->Iex.GetI.bias  = bias;
   return e;
}
IRExpr* IRExpr_RdTmp ( IRTemp tmp ) {
   IRExpr* e        = new IRExpr();
   e->tag           = Iex_RdTmp;
   e->Iex.RdTmp.tmp = tmp;
   return e;
}
IRExpr* IRExpr_Qop ( IROp op, IRExpr* arg1, IRExpr* arg2, 
                              IRExpr* arg3, IRExpr* arg4 ) {
   IRExpr* e       = new IRExpr();
   e->tag          = Iex_Qop;
   e->Iex.Qop.op   = op;
   e->Iex.Qop.arg1 = arg1;
   e->Iex.Qop.arg2 = arg2;
   e->Iex.Qop.arg3 = arg3;
   e->Iex.Qop.arg4 = arg4;
   return e;
}
IRExpr* IRExpr_Triop  ( IROp op, IRExpr* arg1, 
                                 IRExpr* arg2, IRExpr* arg3 ) {
   IRExpr* e         = new IRExpr();
   e->tag            = Iex_Triop;
   e->Iex.Triop.op   = op;
   e->Iex.Triop.arg1 = arg1;
   e->Iex.Triop.arg2 = arg2;
   e->Iex.Triop.arg3 = arg3;
   return e;
}
IRExpr* IRExpr_Binop ( IROp op, IRExpr* arg1, IRExpr* arg2 ) {
   IRExpr* e         = new IRExpr();
   e->tag            = Iex_Binop;
   e->Iex.Binop.op   = op;
   e->Iex.Binop.arg1 = arg1;
   e->Iex.Binop.arg2 = arg2;
   return e;
}
IRExpr* IRExpr_Unop ( IROp op, IRExpr* arg ) {
   IRExpr* e       = new IRExpr();
   e->tag          = Iex_Unop;
   e->Iex.Unop.op  = op;
   e->Iex.Unop.arg = arg;
   return e;
}
IRExpr* IRExpr_Load ( Bool isLL, IREndness end, IRType ty, IRExpr* addr ) {
   IRExpr* e        = new IRExpr();
   e->tag           = Iex_Load;
   e->Iex.Load.isLL = isLL;
   e->Iex.Load.end  = end;
   e->Iex.Load.ty   = ty;
   e->Iex.Load.addr = addr;
   vassert(end == Iend_LE || end == Iend_BE);
   return e;
}
IRExpr* IRExpr_Const ( IRConst* con ) {
   IRExpr* e        = new IRExpr();
   e->tag           = Iex_Const;
   e->Iex.Const.con = con;
   return e;
}
IRExpr* IRExpr_CCall ( IRCallee* cee, IRType retty, IRExpr** args ) {
   IRExpr* e          = new IRExpr();
   e->tag             = Iex_CCall;
   e->Iex.CCall.cee   = cee;
   e->Iex.CCall.retty = retty;
   e->Iex.CCall.args  = args;
   return e;
}
IRExpr* IRExpr_Mux0X ( IRExpr* cond, IRExpr* expr0, IRExpr* exprX ) {
   IRExpr* e          = new IRExpr();
   e->tag             = Iex_Mux0X;
   e->Iex.Mux0X.cond  = cond;
   e->Iex.Mux0X.expr0 = expr0;
   e->Iex.Mux0X.exprX = exprX;
   return e;
}


/* Constructors for NULL-terminated IRExpr expression vectors,
   suitable for use as arg lists in clean/dirty helper calls. */
static IRExpr **alloc_irexpr_array(unsigned nr)
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
   IRDirty* d = new IRDirty();
   d->cee      = NULL;
   d->guard    = NULL;
   d->args     = NULL;
   d->tmp      = IRTemp_INVALID;
   d->mFx      = Ifx_None;
   d->mAddr    = NULL;
   d->mSize    = 0;
   d->needsBBP = False;
   d->nFxState = 0;
   return d;
}


/* Constructors -- IRCAS */

IRCAS* mkIRCAS ( IRTemp oldHi, IRTemp oldLo,
                 IREndness end, IRExpr* addr, 
                 IRExpr* expdHi, IRExpr* expdLo,
                 IRExpr* dataHi, IRExpr* dataLo ) {
   IRCAS* cas = new IRCAS();
   cas->oldHi  = oldHi;
   cas->oldLo  = oldLo;
   cas->end    = end;
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
   /* Just use a single static closure. */
   static IRStmt static_closure;
   static_closure.tag = Ist_NoOp;
   return &static_closure;
}
IRStmt* IRStmt_IMark ( Addr64 addr, Int len ) {
   IRStmt* s         = new IRStmt();
   s->tag            = Ist_IMark;
   s->Ist.IMark.addr = addr;
   s->Ist.IMark.len  = len;
   return s;
}
IRStmt* IRStmt_AbiHint ( IRExpr* base, Int len, IRExpr* nia ) {
   IRStmt* s           = new IRStmt();
   s->tag              = Ist_AbiHint;
   s->Ist.AbiHint.base = base;
   s->Ist.AbiHint.len  = len;
   s->Ist.AbiHint.nia  = nia;
   return s;
}
IRStmt* IRStmt_Put ( Int off, IRExpr* data ) {
   IRStmt* s         = new IRStmt();
   s->tag            = Ist_Put;
   s->Ist.Put.offset = off;
   s->Ist.Put.data   = data;
   return s;
}
IRStmt* IRStmt_PutI ( IRRegArray* descr, IRExpr* ix,
                      Int bias, IRExpr* data ) {
   IRStmt* s         = new IRStmt();
   s->tag            = Ist_PutI;
   s->Ist.PutI.descr = descr;
   s->Ist.PutI.ix    = ix;
   s->Ist.PutI.bias  = bias;
   s->Ist.PutI.data  = data;
   return s;
}
IRStmt* IRStmt_WrTmp ( IRTemp tmp, IRExpr* data ) {
   IRStmt* s         = new IRStmt();
   s->tag            = Ist_WrTmp;
   s->Ist.WrTmp.tmp  = tmp;
   s->Ist.WrTmp.data = data;
   return s;
}
IRStmt* IRStmt_Store ( IREndness end,
                       IRTemp resSC, IRExpr* addr, IRExpr* data ) {
   IRStmt* s          = new IRStmt();
   s->tag             = Ist_Store;
   s->Ist.Store.end   = end;
   s->Ist.Store.resSC = resSC;
   s->Ist.Store.addr  = addr;
   s->Ist.Store.data  = data;
   vassert(end == Iend_LE || end == Iend_BE);
   return s;
}
IRStmt* IRStmt_CAS ( IRCAS* cas ) {
   IRStmt* s          = new IRStmt();
   s->tag             = Ist_CAS;
   s->Ist.CAS.details = cas;
   return s;
}
IRStmt* IRStmt_Dirty ( IRDirty* d )
{
   IRStmt* s            = new IRStmt();
   s->tag               = Ist_Dirty;
   s->Ist.Dirty.details = d;
   return s;
}
IRStmt* IRStmt_MBE ( IRMBusEvent event )
{
   IRStmt* s        = new IRStmt();
   s->tag           = Ist_MBE;
   s->Ist.MBE.event = event;
   return s;
}
IRStmt* IRStmt_Exit ( IRExpr* guard, IRJumpKind jk, IRConst* dst ) {
   IRStmt* s         = new IRStmt();
   s->tag            = Ist_Exit;
   s->Ist.Exit.guard = guard;
   s->Ist.Exit.jk    = jk;
   s->Ist.Exit.dst   = dst;
   return s;
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

/* Deep copy of an IRExpr vector */

IRExpr** deepCopyIRExprVec ( IRExpr** vec )
{
   Int      i;
   IRExpr** newvec = shallowCopyIRExprVec( vec );
   for (i = 0; newvec[i]; i++)
      newvec[i] = deepCopyIRExpr(newvec[i]);
   return newvec;
}

/* Deep copy constructors for all heap-allocated IR types follow. */

IRConst* deepCopyIRConst ( IRConst* c )
{
   switch (c->tag) {
      case Ico_U1:   return IRConst_U1(c->Ico.U1);
      case Ico_U8:   return IRConst_U8(c->Ico.U8);
      case Ico_U16:  return IRConst_U16(c->Ico.U16);
      case Ico_U32:  return IRConst_U32(c->Ico.U32);
      case Ico_U64:  return IRConst_U64(c->Ico.U64);
      case Ico_F64:  return IRConst_F64(c->Ico.F64);
      case Ico_F64i: return IRConst_F64i(c->Ico.F64i);
      case Ico_V128: return IRConst_V128(c->Ico.V128);
      default: vpanic("deepCopyIRConst");
   }
}

IRCallee* deepCopyIRCallee ( IRCallee* ce )
{
   IRCallee* ce2 = mkIRCallee(ce->regparms, ce->name, ce->addr);
   ce2->mcx_mask = ce->mcx_mask;
   return ce2;
}

IRRegArray* deepCopyIRRegArray ( IRRegArray* d )
{
   return mkIRRegArray(d->base, d->elemTy, d->nElems);
}

IRExpr* deepCopyIRExpr ( IRExpr* e )
{
   switch (e->tag) {
      case Iex_Get: 
         return IRExpr_Get(e->Iex.Get.offset, e->Iex.Get.ty);
      case Iex_GetI: 
         return IRExpr_GetI(deepCopyIRRegArray(e->Iex.GetI.descr), 
                            deepCopyIRExpr(e->Iex.GetI.ix),
                            e->Iex.GetI.bias);
      case Iex_RdTmp: 
         return IRExpr_RdTmp(e->Iex.RdTmp.tmp);
      case Iex_Qop: 
         return IRExpr_Qop(e->Iex.Qop.op,
                           deepCopyIRExpr(e->Iex.Qop.arg1),
                           deepCopyIRExpr(e->Iex.Qop.arg2),
                           deepCopyIRExpr(e->Iex.Qop.arg3),
                           deepCopyIRExpr(e->Iex.Qop.arg4));
      case Iex_Triop: 
         return IRExpr_Triop(e->Iex.Triop.op,
                             deepCopyIRExpr(e->Iex.Triop.arg1),
                             deepCopyIRExpr(e->Iex.Triop.arg2),
                             deepCopyIRExpr(e->Iex.Triop.arg3));
      case Iex_Binop: 
         return IRExpr_Binop(e->Iex.Binop.op,
                             deepCopyIRExpr(e->Iex.Binop.arg1),
                             deepCopyIRExpr(e->Iex.Binop.arg2));
      case Iex_Unop: 
         return IRExpr_Unop(e->Iex.Unop.op,
                            deepCopyIRExpr(e->Iex.Unop.arg));
      case Iex_Load: 
         return IRExpr_Load(e->Iex.Load.isLL,
                            e->Iex.Load.end,
                            e->Iex.Load.ty,
                            deepCopyIRExpr(e->Iex.Load.addr));
      case Iex_Const: 
         return IRExpr_Const(deepCopyIRConst(e->Iex.Const.con));
      case Iex_CCall:
         return IRExpr_CCall(deepCopyIRCallee(e->Iex.CCall.cee),
                             e->Iex.CCall.retty,
                             deepCopyIRExprVec(e->Iex.CCall.args));

      case Iex_Mux0X: 
         return IRExpr_Mux0X(deepCopyIRExpr(e->Iex.Mux0X.cond),
                             deepCopyIRExpr(e->Iex.Mux0X.expr0),
                             deepCopyIRExpr(e->Iex.Mux0X.exprX));
      default:
         vpanic("deepCopyIRExpr");
   }
}

IRDirty* deepCopyIRDirty ( IRDirty* d )
{
   Int      i;
   IRDirty* d2 = emptyIRDirty();
   d2->cee   = deepCopyIRCallee(d->cee);
   d2->guard = deepCopyIRExpr(d->guard);
   d2->args  = deepCopyIRExprVec(d->args);
   d2->tmp   = d->tmp;
   d2->mFx   = d->mFx;
   d2->mAddr = d->mAddr==NULL ? NULL : deepCopyIRExpr(d->mAddr);
   d2->mSize = d->mSize;
   d2->needsBBP = d->needsBBP;
   d2->nFxState = d->nFxState;
   for (i = 0; i < d2->nFxState; i++)
      d2->fxState[i] = d->fxState[i];
   return d2;
}

IRCAS* deepCopyIRCAS ( IRCAS* cas )
{
   return mkIRCAS( cas->oldHi, cas->oldLo, cas->end,
                   deepCopyIRExpr(cas->addr),
                   cas->expdHi==NULL ? NULL : deepCopyIRExpr(cas->expdHi),
                   deepCopyIRExpr(cas->expdLo),
                   cas->dataHi==NULL ? NULL : deepCopyIRExpr(cas->dataHi),
                   deepCopyIRExpr(cas->dataLo) );
}

IRStmt* deepCopyIRStmt ( IRStmt* s )
{
   switch (s->tag) {
      case Ist_NoOp:
         return IRStmt_NoOp();
      case Ist_AbiHint:
         return IRStmt_AbiHint(deepCopyIRExpr(s->Ist.AbiHint.base),
                               s->Ist.AbiHint.len,
                               deepCopyIRExpr(s->Ist.AbiHint.nia));
      case Ist_IMark:
         return IRStmt_IMark(s->Ist.IMark.addr, s->Ist.IMark.len);
      case Ist_Put: 
         return IRStmt_Put(s->Ist.Put.offset, 
                           deepCopyIRExpr(s->Ist.Put.data));
      case Ist_PutI: 
         return IRStmt_PutI(deepCopyIRRegArray(s->Ist.PutI.descr),
                            deepCopyIRExpr(s->Ist.PutI.ix),
                            s->Ist.PutI.bias, 
                            deepCopyIRExpr(s->Ist.PutI.data));
      case Ist_WrTmp:
         return IRStmt_WrTmp(s->Ist.WrTmp.tmp,
                             deepCopyIRExpr(s->Ist.WrTmp.data));
      case Ist_Store: 
         return IRStmt_Store(s->Ist.Store.end,
                             s->Ist.Store.resSC,
                             deepCopyIRExpr(s->Ist.Store.addr),
                             deepCopyIRExpr(s->Ist.Store.data));
      case Ist_CAS:
         return IRStmt_CAS(deepCopyIRCAS(s->Ist.CAS.details));
      case Ist_Dirty: 
         return IRStmt_Dirty(deepCopyIRDirty(s->Ist.Dirty.details));
      case Ist_MBE:
         return IRStmt_MBE(s->Ist.MBE.event);
      case Ist_Exit: 
         return IRStmt_Exit(deepCopyIRExpr(s->Ist.Exit.guard),
                            s->Ist.Exit.jk,
                            deepCopyIRConst(s->Ist.Exit.dst));
      default: 
         vpanic("deepCopyIRStmt");
   }
}

IRTypeEnv* deepCopyIRTypeEnv ( IRTypeEnv* src )
{
   Int        i;
   IRTypeEnv* dst = new IRTypeEnv();
   dst->types_size = src->types_size;
   dst->types_used = src->types_used;
   dst->types = (IRType *)__LibVEX_Alloc_Bytes(&ir_heap, dst->types_size * sizeof(IRType), NULL);
   for (i = 0; i < src->types_used; i++)
      dst->types[i] = src->types[i];
   return dst;
}

IRSB* deepCopyIRSB ( IRSB* bb )
{
   Int      i;
   IRStmt** sts2;
   IRSB* bb2 = deepCopyIRSBExceptStmts(bb);
   bb2->stmts_used = bb2->stmts_size = bb->stmts_used;
   sts2 = (IRStmt **)__LibVEX_Alloc_Ptr_Array(&ir_heap, bb2->stmts_used);
   for (i = 0; i < bb2->stmts_used; i++)
      sts2[i] = deepCopyIRStmt(bb->stmts[i]);
   bb2->stmts    = sts2;
   return bb2;
}

IRSB* deepCopyIRSBExceptStmts ( IRSB* bb )
{
   IRSB* bb2     = emptyIRSB();
   bb2->tyenv    = deepCopyIRTypeEnv(bb->tyenv);
   bb2->next     = deepCopyIRExpr(bb->next);
   bb2->jumpkind = bb->jumpkind;
   return bb2;
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
     IRStmt** stmts2 = (IRStmt **)__LibVEX_Alloc_Ptr_Array(&ir_heap, 2 * bb->stmts_size);
      for (i = 0; i < bb->stmts_size; i++)
         stmts2[i] = bb->stmts[i];
      bb->stmts = stmts2;
      bb->stmts_size *= 2;
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

IRType typeOfIRExpr ( IRTypeEnv* tyenv, IRExpr* e )
{
   IRType t_dst, t_arg1, t_arg2, t_arg3, t_arg4;
 start:
   switch (e->tag) {
      case Iex_Load:
         return e->Iex.Load.ty;
      case Iex_Get:
         return e->Iex.Get.ty;
      case Iex_GetI:
         return e->Iex.GetI.descr->elemTy;
      case Iex_RdTmp:
         return typeOfIRTemp(tyenv, e->Iex.RdTmp.tmp);
      case Iex_Const:
         return typeOfIRConst(e->Iex.Const.con);
      case Iex_Qop:
         typeOfPrimop(e->Iex.Qop.op, 
                      &t_dst, &t_arg1, &t_arg2, &t_arg3, &t_arg4);
         return t_dst;
      case Iex_Triop:
         typeOfPrimop(e->Iex.Triop.op, 
                      &t_dst, &t_arg1, &t_arg2, &t_arg3, &t_arg4);
         return t_dst;
      case Iex_Binop:
         typeOfPrimop(e->Iex.Binop.op, 
                      &t_dst, &t_arg1, &t_arg2, &t_arg3, &t_arg4);
         return t_dst;
      case Iex_Unop:
         typeOfPrimop(e->Iex.Unop.op, 
                      &t_dst, &t_arg1, &t_arg2, &t_arg3, &t_arg4);
         return t_dst;
      case Iex_CCall:
         return e->Iex.CCall.retty;
      case Iex_Mux0X:
         e = e->Iex.Mux0X.expr0;
         goto start;
         /* return typeOfIRExpr(tyenv, e->Iex.Mux0X.expr0); */
      case Iex_Binder:
         vpanic("typeOfIRExpr: Binder is not a valid expression");
      default:
	 ppIRExpr(e, stderr);
         vpanic("typeOfIRExpr");
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
/*--- Sanity checking -- FLATNESS                             ---*/
/*---------------------------------------------------------------*/

/* Check that the canonical flatness constraints hold on an
   IRStmt. The only place where any expression is allowed to be
   non-atomic is the RHS of IRStmt_Tmp. */

/* Relies on:
   inline static Bool isAtom ( IRExpr* e ) {
      return e->tag == Iex_RdTmp || e->tag == Iex_Const;
   }
*/

Bool isFlatIRStmt ( IRStmt* st )
{
   Int      i;
   IRExpr*  e;
   IRDirty* di;
   IRCAS*   cas;

   switch (st->tag) {
      case Ist_AbiHint:
         return isIRAtom(st->Ist.AbiHint.base)
                && isIRAtom(st->Ist.AbiHint.nia);
      case Ist_Put:
         return isIRAtom(st->Ist.Put.data);
      case Ist_PutI:
         return toBool( isIRAtom(st->Ist.PutI.ix) 
                        && isIRAtom(st->Ist.PutI.data) );
      case Ist_WrTmp:
         /* This is the only interesting case.  The RHS can be any
            expression, *but* all its subexpressions *must* be
            atoms. */
         e = st->Ist.WrTmp.data;
         switch (e->tag) {
            case Iex_Binder: return True;
            case Iex_Get:    return True;
            case Iex_GetI:   return isIRAtom(e->Iex.GetI.ix);
            case Iex_RdTmp:  return True;
            case Iex_Qop:    return toBool(
                                    isIRAtom(e->Iex.Qop.arg1) 
                                    && isIRAtom(e->Iex.Qop.arg2)
                                    && isIRAtom(e->Iex.Qop.arg3)
                                    && isIRAtom(e->Iex.Qop.arg4));
            case Iex_Triop:  return toBool(
                                    isIRAtom(e->Iex.Triop.arg1) 
                                    && isIRAtom(e->Iex.Triop.arg2)
                                    && isIRAtom(e->Iex.Triop.arg3));
            case Iex_Binop:  return toBool(
                                    isIRAtom(e->Iex.Binop.arg1) 
                                    && isIRAtom(e->Iex.Binop.arg2));
            case Iex_Unop:   return isIRAtom(e->Iex.Unop.arg);
            case Iex_Load:   return isIRAtom(e->Iex.Load.addr);
            case Iex_Const:  return True;
            case Iex_CCall:  for (i = 0; e->Iex.CCall.args[i]; i++)
                                if (!isIRAtom(e->Iex.CCall.args[i])) 
                                   return False;
                             return True;
            case Iex_Mux0X:  return toBool (
                                    isIRAtom(e->Iex.Mux0X.cond) 
                                    && isIRAtom(e->Iex.Mux0X.expr0) 
                                    && isIRAtom(e->Iex.Mux0X.exprX));
            default:         vpanic("isFlatIRStmt(e)");
         }
         /*notreached*/
         vassert(0);
      case Ist_Store:
         return toBool( isIRAtom(st->Ist.Store.addr) 
                        && isIRAtom(st->Ist.Store.data) );
      case Ist_CAS:
         cas = st->Ist.CAS.details;
         return toBool( isIRAtom(cas->addr)
                        && (cas->expdHi ? isIRAtom(cas->expdHi) : True)
                        && isIRAtom(cas->expdLo)
                        && (cas->dataHi ? isIRAtom(cas->dataHi) : True)
                        && isIRAtom(cas->dataLo) );
      case Ist_Dirty:
         di = st->Ist.Dirty.details;
         if (!isIRAtom(di->guard)) 
            return False;
         for (i = 0; di->args[i]; i++)
            if (!isIRAtom(di->args[i])) 
               return False;
         if (di->mAddr && !isIRAtom(di->mAddr)) 
            return False;
         return True;
      case Ist_NoOp:
      case Ist_IMark:
      case Ist_MBE:
         return True;
      case Ist_Exit:
         return isIRAtom(st->Ist.Exit.guard);
      default: 
         vpanic("isFlatIRStmt(st)");
   }
}


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

static Bool saneIRRegArray ( IRRegArray* arr )
{
   if (arr->base < 0 || arr->base > 10000 /* somewhat arbitrary */)
      return False;
   if (arr->elemTy == Ity_I1)
      return False;
   if (arr->nElems <= 0 || arr->nElems > 500 /* somewhat arbitrary */)
      return False;
   return True;
}

static Bool saneIRCallee ( IRCallee* cee )
{
   if (cee->name == NULL)
      return False;
   if (cee->addr == 0)
      return False;
   if (cee->regparms < 0 || cee->regparms > 3)
      return False;
   return True;
}

static Bool saneIRConst ( IRConst* con )
{
   switch (con->tag) {
      case Ico_U1: 
         return toBool( con->Ico.U1 == True || con->Ico.U1 == False );
      default: 
         /* Is there anything we can meaningfully check?  I don't
            think so. */
         return True;
   }
}

/* Traverse a Stmt/Expr, inspecting IRTemp uses.  Report any out of
   range ones.  Report any which are read and for which the current
   def_count is zero. */

static
void useBeforeDef_Temp ( IRSB* bb, IRStmt* stmt, IRTemp tmp, Int* def_counts )
{
   if (def_counts[tmp] < 1)
      sanityCheckFail(bb,stmt, "IRTemp use before def in IRExpr");
}

static
void useBeforeDef_Expr ( IRSB* bb, IRStmt* stmt, IRExpr* expr, Int* def_counts )
{
   Int i;
   switch (expr->tag) {
      case Iex_Get: 
         break;
      case Iex_GetI:
         useBeforeDef_Expr(bb,stmt,expr->Iex.GetI.ix,def_counts);
         break;
      case Iex_RdTmp:
         useBeforeDef_Temp(bb,stmt,expr->Iex.RdTmp.tmp,def_counts);
         break;
      case Iex_Qop:
         useBeforeDef_Expr(bb,stmt,expr->Iex.Qop.arg1,def_counts);
         useBeforeDef_Expr(bb,stmt,expr->Iex.Qop.arg2,def_counts);
         useBeforeDef_Expr(bb,stmt,expr->Iex.Qop.arg3,def_counts);
         useBeforeDef_Expr(bb,stmt,expr->Iex.Qop.arg4,def_counts);
         break;
      case Iex_Triop:
         useBeforeDef_Expr(bb,stmt,expr->Iex.Triop.arg1,def_counts);
         useBeforeDef_Expr(bb,stmt,expr->Iex.Triop.arg2,def_counts);
         useBeforeDef_Expr(bb,stmt,expr->Iex.Triop.arg3,def_counts);
         break;
      case Iex_Binop:
         useBeforeDef_Expr(bb,stmt,expr->Iex.Binop.arg1,def_counts);
         useBeforeDef_Expr(bb,stmt,expr->Iex.Binop.arg2,def_counts);
         break;
      case Iex_Unop:
         useBeforeDef_Expr(bb,stmt,expr->Iex.Unop.arg,def_counts);
         break;
      case Iex_Load:
         useBeforeDef_Expr(bb,stmt,expr->Iex.Load.addr,def_counts);
         break;
      case Iex_Const:
         break;
      case Iex_CCall:
         for (i = 0; expr->Iex.CCall.args[i]; i++)
            useBeforeDef_Expr(bb,stmt,expr->Iex.CCall.args[i],def_counts);
         break;
      case Iex_Mux0X:
         useBeforeDef_Expr(bb,stmt,expr->Iex.Mux0X.cond,def_counts);
         useBeforeDef_Expr(bb,stmt,expr->Iex.Mux0X.expr0,def_counts);
         useBeforeDef_Expr(bb,stmt,expr->Iex.Mux0X.exprX,def_counts);
         break;
      default:
         vpanic("useBeforeDef_Expr");
   }
}

static
void useBeforeDef_Stmt ( IRSB* bb, IRStmt* stmt, Int* def_counts )
{
   Int      i;
   IRDirty* d;
   IRCAS*   cas;
   switch (stmt->tag) {
      case Ist_IMark:
         break;
      case Ist_AbiHint:
         useBeforeDef_Expr(bb,stmt,stmt->Ist.AbiHint.base,def_counts);
         useBeforeDef_Expr(bb,stmt,stmt->Ist.AbiHint.nia,def_counts);
         break;
      case Ist_Put:
         useBeforeDef_Expr(bb,stmt,stmt->Ist.Put.data,def_counts);
         break;
      case Ist_PutI:
         useBeforeDef_Expr(bb,stmt,stmt->Ist.PutI.ix,def_counts);
         useBeforeDef_Expr(bb,stmt,stmt->Ist.PutI.data,def_counts);
         break;
      case Ist_WrTmp:
         useBeforeDef_Expr(bb,stmt,stmt->Ist.WrTmp.data,def_counts);
         break;
      case Ist_Store:
         useBeforeDef_Expr(bb,stmt,stmt->Ist.Store.addr,def_counts);
         useBeforeDef_Expr(bb,stmt,stmt->Ist.Store.data,def_counts);
         break;
      case Ist_CAS:
         cas = stmt->Ist.CAS.details;
         useBeforeDef_Expr(bb,stmt,cas->addr,def_counts);
         if (cas->expdHi)
            useBeforeDef_Expr(bb,stmt,cas->expdHi,def_counts);
         useBeforeDef_Expr(bb,stmt,cas->expdLo,def_counts);
         if (cas->dataHi)
            useBeforeDef_Expr(bb,stmt,cas->dataHi,def_counts);
         useBeforeDef_Expr(bb,stmt,cas->dataLo,def_counts);
         break;
      case Ist_Dirty:
         d = stmt->Ist.Dirty.details;
         for (i = 0; d->args[i] != NULL; i++)
            useBeforeDef_Expr(bb,stmt,d->args[i],def_counts);
         if (d->mFx != Ifx_None)
            useBeforeDef_Expr(bb,stmt,d->mAddr,def_counts);
         break;
      case Ist_NoOp:
      case Ist_MBE:
         break;
      case Ist_Exit:
         useBeforeDef_Expr(bb,stmt,stmt->Ist.Exit.guard,def_counts);
         break;
      default: 
         vpanic("useBeforeDef_Stmt");
   }
}

static
void tcExpr ( IRSB* bb, IRStmt* stmt, IRExpr* expr, IRType gWordTy )
{
   Int        i;
   IRType     t_dst, t_arg1, t_arg2, t_arg3, t_arg4;
   IRTypeEnv* tyenv = bb->tyenv;
   switch (expr->tag) {
      case Iex_Get:
      case Iex_RdTmp:
         break;
      case Iex_GetI:
         tcExpr(bb,stmt, expr->Iex.GetI.ix, gWordTy );
         if (typeOfIRExpr(tyenv,expr->Iex.GetI.ix) != Ity_I32)
            sanityCheckFail(bb,stmt,"IRExpr.GetI.ix: not :: Ity_I32");
         if (!saneIRRegArray(expr->Iex.GetI.descr))
            sanityCheckFail(bb,stmt,"IRExpr.GetI.descr: invalid descr");
         break;
      case Iex_Qop: {
         IRType ttarg1, ttarg2, ttarg3, ttarg4;
         tcExpr(bb,stmt, expr->Iex.Qop.arg1, gWordTy );
         tcExpr(bb,stmt, expr->Iex.Qop.arg2, gWordTy );
         tcExpr(bb,stmt, expr->Iex.Qop.arg3, gWordTy );
         tcExpr(bb,stmt, expr->Iex.Qop.arg4, gWordTy );
         typeOfPrimop(expr->Iex.Qop.op, 
                      &t_dst, &t_arg1, &t_arg2, &t_arg3, &t_arg4);
         if (t_arg1 == Ity_INVALID || t_arg2 == Ity_INVALID 
             || t_arg3 == Ity_INVALID || t_arg4 == Ity_INVALID) {
            fprintf(stderr, " op name: " );
            ppIROp(expr->Iex.Qop.op, stderr);
            fprintf(stderr, "\n");
            sanityCheckFail(bb,stmt,
               "Iex.Qop: wrong arity op\n"
               "... name of op precedes BB printout\n");
         }
         ttarg1 = typeOfIRExpr(tyenv, expr->Iex.Qop.arg1);
         ttarg2 = typeOfIRExpr(tyenv, expr->Iex.Qop.arg2);
         ttarg3 = typeOfIRExpr(tyenv, expr->Iex.Qop.arg3);
         ttarg4 = typeOfIRExpr(tyenv, expr->Iex.Qop.arg4);
         if (t_arg1 != ttarg1 || t_arg2 != ttarg2 
             || t_arg3 != ttarg3 || t_arg4 != ttarg4) {
            fprintf(stderr, " op name: ");
            ppIROp(expr->Iex.Qop.op, stderr);
            fprintf(stderr, "\n");
            fprintf(stderr, " op type is (");
            ppIRType(t_arg1, stderr);
            fprintf(stderr, ",");
            ppIRType(t_arg2, stderr);
            fprintf(stderr, ",");
            ppIRType(t_arg3, stderr);
            fprintf(stderr, ",");
            ppIRType(t_arg4, stderr);
            fprintf(stderr, ") -> ");
            ppIRType (t_dst, stderr);
            fprintf(stderr, "\narg tys are (");
            ppIRType(ttarg1, stderr);
            fprintf(stderr, ",");
            ppIRType(ttarg2, stderr);
            fprintf(stderr, ",");
            ppIRType(ttarg3, stderr);
            fprintf(stderr, ",");
            ppIRType(ttarg4, stderr);
            fprintf(stderr, ")\n");
            sanityCheckFail(bb,stmt,
               "Iex.Qop: arg tys don't match op tys\n"
               "... additional details precede BB printout\n");
         }
         break;
      }
      case Iex_Triop: {
         IRType ttarg1, ttarg2, ttarg3;
         tcExpr(bb,stmt, expr->Iex.Triop.arg1, gWordTy );
         tcExpr(bb,stmt, expr->Iex.Triop.arg2, gWordTy );
         tcExpr(bb,stmt, expr->Iex.Triop.arg3, gWordTy );
         typeOfPrimop(expr->Iex.Triop.op, 
                      &t_dst, &t_arg1, &t_arg2, &t_arg3, &t_arg4);
         if (t_arg1 == Ity_INVALID || t_arg2 == Ity_INVALID 
             || t_arg3 == Ity_INVALID || t_arg4 != Ity_INVALID) {
            fprintf(stderr, " op name: " );
            ppIROp(expr->Iex.Triop.op, stderr);
            fprintf(stderr, "\n");
            sanityCheckFail(bb,stmt,
               "Iex.Triop: wrong arity op\n"
               "... name of op precedes BB printout\n");
         }
         ttarg1 = typeOfIRExpr(tyenv, expr->Iex.Triop.arg1);
         ttarg2 = typeOfIRExpr(tyenv, expr->Iex.Triop.arg2);
         ttarg3 = typeOfIRExpr(tyenv, expr->Iex.Triop.arg3);
         if (t_arg1 != ttarg1 || t_arg2 != ttarg2 || t_arg3 != ttarg3) {
            fprintf(stderr, " op name: ");
            ppIROp(expr->Iex.Triop.op, stderr);
            fprintf(stderr, "\n");
            fprintf(stderr, " op type is (");
            ppIRType(t_arg1, stderr);
            fprintf(stderr, ",");
            ppIRType(t_arg2, stderr);
            fprintf(stderr, ",");
            ppIRType(t_arg3, stderr);
            fprintf(stderr, ") -> ");
            ppIRType (t_dst, stderr);
            fprintf(stderr, "\narg tys are (");
            ppIRType(ttarg1, stderr);
            fprintf(stderr, ",");
            ppIRType(ttarg2, stderr);
            fprintf(stderr, ",");
            ppIRType(ttarg3, stderr);
            fprintf(stderr, ")\n");
            sanityCheckFail(bb,stmt,
               "Iex.Triop: arg tys don't match op tys\n"
               "... additional details precede BB printout\n");
         }
         break;
      }
      case Iex_Binop: {
         IRType ttarg1, ttarg2;
         tcExpr(bb,stmt, expr->Iex.Binop.arg1, gWordTy );
         tcExpr(bb,stmt, expr->Iex.Binop.arg2, gWordTy );
         typeOfPrimop(expr->Iex.Binop.op, 
                      &t_dst, &t_arg1, &t_arg2, &t_arg3, &t_arg4);
         if (t_arg1 == Ity_INVALID || t_arg2 == Ity_INVALID 
             || t_arg3 != Ity_INVALID || t_arg4 != Ity_INVALID) {
            fprintf(stderr, " op name: " );
            ppIROp(expr->Iex.Binop.op, stderr);
            fprintf(stderr, "\n");
            sanityCheckFail(bb,stmt,
               "Iex.Binop: wrong arity op\n"
               "... name of op precedes BB printout\n");
         }
         ttarg1 = typeOfIRExpr(tyenv, expr->Iex.Binop.arg1);
         ttarg2 = typeOfIRExpr(tyenv, expr->Iex.Binop.arg2);
         if (t_arg1 != ttarg1 || t_arg2 != ttarg2) {
            fprintf(stderr, " op name: ");
            ppIROp(expr->Iex.Binop.op, stderr);
            fprintf(stderr, "\n");
            fprintf(stderr, " op type is (");
            ppIRType(t_arg1, stderr);
            fprintf(stderr, ",");
            ppIRType(t_arg2, stderr);
            fprintf(stderr, ") -> ");
            ppIRType (t_dst, stderr);
            fprintf(stderr, "\narg tys are (");
            ppIRType(ttarg1, stderr);
            fprintf(stderr, ",");
            ppIRType(ttarg2, stderr);
            fprintf(stderr, ")\n");
            sanityCheckFail(bb,stmt,
               "Iex.Binop: arg tys don't match op tys\n"
               "... additional details precede BB printout\n");
         }
         break;
      }
      case Iex_Unop:
         tcExpr(bb,stmt, expr->Iex.Unop.arg, gWordTy );
         typeOfPrimop(expr->Iex.Binop.op, 
                      &t_dst, &t_arg1, &t_arg2, &t_arg3, &t_arg4);
         if (t_arg1 == Ity_INVALID || t_arg2 != Ity_INVALID
             || t_arg3 != Ity_INVALID || t_arg4 != Ity_INVALID)
            sanityCheckFail(bb,stmt,"Iex.Unop: wrong arity op");
         if (t_arg1 != typeOfIRExpr(tyenv, expr->Iex.Unop.arg))
            sanityCheckFail(bb,stmt,"Iex.Unop: arg ty doesn't match op ty");
         break;
      case Iex_Load:
         tcExpr(bb,stmt, expr->Iex.Load.addr, gWordTy);
         if (typeOfIRExpr(tyenv, expr->Iex.Load.addr) != gWordTy)
            sanityCheckFail(bb,stmt,"Iex.Load.addr: not :: guest word type");
         if (expr->Iex.Load.end != Iend_LE && expr->Iex.Load.end != Iend_BE)
            sanityCheckFail(bb,stmt,"Iex.Load.end: bogus endianness");
         break;
      case Iex_CCall:
         if (!saneIRCallee(expr->Iex.CCall.cee))
            sanityCheckFail(bb,stmt,"Iex.CCall.cee: bad IRCallee");
         if (expr->Iex.CCall.cee->regparms > countArgs(expr->Iex.CCall.args)) 
            sanityCheckFail(bb,stmt,"Iex.CCall.cee: #regparms > #args");
         for (i = 0; expr->Iex.CCall.args[i]; i++) {
            if (i >= 32)
               sanityCheckFail(bb,stmt,"Iex.CCall: > 32 args");
            tcExpr(bb,stmt, expr->Iex.CCall.args[i], gWordTy);
         }
         if (expr->Iex.CCall.retty == Ity_I1)
            sanityCheckFail(bb,stmt,"Iex.CCall.retty: cannot return :: Ity_I1");
         for (i = 0; expr->Iex.CCall.args[i]; i++)
            if (typeOfIRExpr(tyenv, expr->Iex.CCall.args[i]) == Ity_I1)
               sanityCheckFail(bb,stmt,"Iex.CCall.arg: arg :: Ity_I1");
         break;
      case Iex_Const:
         if (!saneIRConst(expr->Iex.Const.con))
            sanityCheckFail(bb,stmt,"Iex.Const.con: invalid const");
         break;
      case Iex_Mux0X:
         tcExpr(bb,stmt, expr->Iex.Mux0X.cond, gWordTy);
         tcExpr(bb,stmt, expr->Iex.Mux0X.expr0, gWordTy);
         tcExpr(bb,stmt, expr->Iex.Mux0X.exprX, gWordTy);
         if (typeOfIRExpr(tyenv, expr->Iex.Mux0X.cond) != Ity_I8)
            sanityCheckFail(bb,stmt,"Iex.Mux0X.cond: cond :: Ity_I8");
         if (typeOfIRExpr(tyenv, expr->Iex.Mux0X.expr0)
             != typeOfIRExpr(tyenv, expr->Iex.Mux0X.exprX))
            sanityCheckFail(bb,stmt,"Iex.Mux0X: expr0/exprX mismatch");
         break;
       default: 
         vpanic("tcExpr");
   }
}


static
void tcStmt ( IRSB* bb, IRStmt* stmt, IRType gWordTy )
{
   Int        i;
   IRDirty*   d;
   IRCAS*     cas;
   IRType     tyExpd, tyData;
   IRTypeEnv* tyenv = bb->tyenv;
   switch (stmt->tag) {
      case Ist_IMark:
         /* Somewhat heuristic, but rule out totally implausible
            instruction sizes. */
         if (stmt->Ist.IMark.len < 0 || stmt->Ist.IMark.len > 20)
            sanityCheckFail(bb,stmt,"IRStmt.IMark.len: implausible");
         break;
      case Ist_AbiHint:
         if (typeOfIRExpr(tyenv, stmt->Ist.AbiHint.base) != gWordTy)
            sanityCheckFail(bb,stmt,"IRStmt.AbiHint.base: "
                                    "not :: guest word type");
         if (typeOfIRExpr(tyenv, stmt->Ist.AbiHint.nia) != gWordTy)
            sanityCheckFail(bb,stmt,"IRStmt.AbiHint.nia: "
                                    "not :: guest word type");
         break;
      case Ist_Put:
         tcExpr( bb, stmt, stmt->Ist.Put.data, gWordTy );
         if (typeOfIRExpr(tyenv,stmt->Ist.Put.data) == Ity_I1)
            sanityCheckFail(bb,stmt,"IRStmt.Put.data: cannot Put :: Ity_I1");
         break;
      case Ist_PutI:
         tcExpr( bb, stmt, stmt->Ist.PutI.data, gWordTy );
         tcExpr( bb, stmt, stmt->Ist.PutI.ix, gWordTy );
         if (typeOfIRExpr(tyenv,stmt->Ist.PutI.data) == Ity_I1)
            sanityCheckFail(bb,stmt,"IRStmt.PutI.data: cannot PutI :: Ity_I1");
         if (typeOfIRExpr(tyenv,stmt->Ist.PutI.data) 
             != stmt->Ist.PutI.descr->elemTy)
            sanityCheckFail(bb,stmt,"IRStmt.PutI.data: data ty != elem ty");
         if (typeOfIRExpr(tyenv,stmt->Ist.PutI.ix) != Ity_I32)
            sanityCheckFail(bb,stmt,"IRStmt.PutI.ix: not :: Ity_I32");
         if (!saneIRRegArray(stmt->Ist.PutI.descr))
            sanityCheckFail(bb,stmt,"IRStmt.PutI.descr: invalid descr");
         break;
      case Ist_WrTmp:
         tcExpr( bb, stmt, stmt->Ist.WrTmp.data, gWordTy );
         if (typeOfIRTemp(tyenv, stmt->Ist.WrTmp.tmp)
             != typeOfIRExpr(tyenv, stmt->Ist.WrTmp.data))
            sanityCheckFail(bb,stmt,"IRStmt.Put.Tmp: tmp and expr do not match");
         break;
      case Ist_Store:
         tcExpr( bb, stmt, stmt->Ist.Store.addr, gWordTy );
         tcExpr( bb, stmt, stmt->Ist.Store.data, gWordTy );
         if (typeOfIRExpr(tyenv, stmt->Ist.Store.addr) != gWordTy)
            sanityCheckFail(bb,stmt,"IRStmt.Store.addr: not :: guest word type");
         if (typeOfIRExpr(tyenv, stmt->Ist.Store.data) == Ity_I1)
            sanityCheckFail(bb,stmt,"IRStmt.Store.data: cannot Store :: Ity_I1");
         if (stmt->Ist.Store.end != Iend_LE && stmt->Ist.Store.end != Iend_BE)
            sanityCheckFail(bb,stmt,"Ist.Store.end: bogus endianness");
         if (stmt->Ist.Store.resSC != IRTemp_INVALID
             && typeOfIRTemp(tyenv, stmt->Ist.Store.resSC) != Ity_I1)
            sanityCheckFail(bb,stmt,"Ist.Store.resSC: not :: Ity_I1");
         break;
      case Ist_CAS:
         cas = stmt->Ist.CAS.details;
         /* make sure it's definitely either a CAS or a DCAS */
         if (cas->oldHi == IRTemp_INVALID 
             && cas->expdHi == NULL && cas->dataHi == NULL) {
            /* fine; it's a single cas */
         }
         else
         if (cas->oldHi != IRTemp_INVALID 
             && cas->expdHi != NULL && cas->dataHi != NULL) {
            /* fine; it's a double cas */
         }
         else {
            /* it's some el-mutanto hybrid */
            goto bad_cas;
         }
         /* check the address type */
         tcExpr( bb, stmt, cas->addr, gWordTy );
         if (typeOfIRExpr(tyenv, cas->addr) != gWordTy) goto bad_cas;
         /* check types on the {old,expd,data}Lo components agree */
         tyExpd = typeOfIRExpr(tyenv, cas->expdLo);
         tyData = typeOfIRExpr(tyenv, cas->dataLo);
         if (tyExpd != tyData) goto bad_cas;
         if (tyExpd != typeOfIRTemp(tyenv, cas->oldLo))
            goto bad_cas;
         /* check the base element type is sane */
         if (tyExpd == Ity_I8 || tyExpd == Ity_I16 || tyExpd == Ity_I32
             || (gWordTy == Ity_I64 && tyExpd == Ity_I64)) {
            /* fine */
         } else {
            goto bad_cas;
         }
         /* If it's a DCAS, check types on the {old,expd,data}Hi
            components too */
         if (cas->oldHi != IRTemp_INVALID) {
            tyExpd = typeOfIRExpr(tyenv, cas->expdHi);
            tyData = typeOfIRExpr(tyenv, cas->dataHi);
            if (tyExpd != tyData) goto bad_cas;
            if (tyExpd != typeOfIRTemp(tyenv, cas->oldHi))
               goto bad_cas;
            /* and finally check that oldLo and oldHi have the same
               type.  This forces equivalence amongst all 6 types. */
            if (typeOfIRTemp(tyenv, cas->oldHi)
                != typeOfIRTemp(tyenv, cas->oldLo))
               goto bad_cas;
         }
         break;
         bad_cas:
         sanityCheckFail(bb,stmt,"IRStmt.CAS: ill-formed");
         break;
      case Ist_Dirty:
         /* Mostly check for various kinds of ill-formed dirty calls. */
         d = stmt->Ist.Dirty.details;
         if (d->cee == NULL) goto bad_dirty;
         if (!saneIRCallee(d->cee)) goto bad_dirty;
         if (d->cee->regparms > countArgs(d->args)) goto bad_dirty;
         if (d->mFx == Ifx_None) {
            if (d->mAddr != NULL || d->mSize != 0)
               goto bad_dirty;
         } else {
            if (d->mAddr == NULL || d->mSize == 0)
               goto bad_dirty;
         }
         if (d->nFxState < 0 || d->nFxState > VEX_N_FXSTATE)
            goto bad_dirty;
         if (d->nFxState == 0 && d->needsBBP)
            goto bad_dirty;
         for (i = 0; i < d->nFxState; i++) {
            if (d->fxState[i].fx == Ifx_None) goto bad_dirty;
            if (d->fxState[i].size <= 0) goto bad_dirty;
         }
         /* check types, minimally */
         if (d->guard == NULL) goto bad_dirty;
         tcExpr( bb, stmt, d->guard, gWordTy );
         if (typeOfIRExpr(tyenv, d->guard) != Ity_I1)
            sanityCheckFail(bb,stmt,"IRStmt.Dirty.guard not :: Ity_I1");
         if (d->tmp != IRTemp_INVALID
             && typeOfIRTemp(tyenv, d->tmp) == Ity_I1)
            sanityCheckFail(bb,stmt,"IRStmt.Dirty.dst :: Ity_I1");
         for (i = 0; d->args[i] != NULL; i++) {
            if (i >= 32)
               sanityCheckFail(bb,stmt,"IRStmt.Dirty: > 32 args");
            if (typeOfIRExpr(tyenv, d->args[i]) == Ity_I1)
               sanityCheckFail(bb,stmt,"IRStmt.Dirty.arg[i] :: Ity_I1");
         }
         break;
         bad_dirty:
         sanityCheckFail(bb,stmt,"IRStmt.Dirty: ill-formed");
         break;
      case Ist_NoOp:
         break;
      case Ist_MBE:
         switch (stmt->Ist.MBE.event) {
            case Imbe_Fence:
               break;
            default: sanityCheckFail(bb,stmt,"IRStmt.MBE.event: unknown");
               break;
         }
         break;
      case Ist_Exit:
         tcExpr( bb, stmt, stmt->Ist.Exit.guard, gWordTy );
         if (typeOfIRExpr(tyenv,stmt->Ist.Exit.guard) != Ity_I1)
            sanityCheckFail(bb,stmt,"IRStmt.Exit.guard: not :: Ity_I1");
         if (!saneIRConst(stmt->Ist.Exit.dst))
            sanityCheckFail(bb,stmt,"IRStmt.Exit.dst: bad dst");
         if (typeOfIRConst(stmt->Ist.Exit.dst) != gWordTy)
            sanityCheckFail(bb,stmt,"IRStmt.Exit.dst: not :: guest word type");
         break;
      default:
         vpanic("tcStmt");
   }
}

void sanityCheckIRSB ( IRSB* bb,          const char* caller,
                       Bool require_flat, IRType guest_word_size )
{
   Int     i;
   IRStmt* stmt;
   Int     n_temps    = bb->tyenv->types_used;
   Int*    def_counts = (Int *)LibVEX_Alloc_Bytes(n_temps * sizeof(Int));

   if (0)
      fprintf(stderr, "sanityCheck: %s\n", caller);

   vassert(guest_word_size == Ity_I32
           || guest_word_size == Ity_I64);

   if (bb->stmts_used < 0 || bb->stmts_size < 8
       || bb->stmts_used > bb->stmts_size)
      /* this BB is so strange we can't even print it */
      vpanic("sanityCheckIRSB: stmts array limits wierd");

   /* Ensure each temp has a plausible type. */
   for (i = 0; i < n_temps; i++) {
      IRType ty = typeOfIRTemp(bb->tyenv,(IRTemp)i);
      if (!isPlausibleIRType(ty)) {
         fprintf(stderr, "Temp t%d declared with implausible type 0x%x\n",
                    i, (UInt)ty);
         sanityCheckFail(bb,NULL,"Temp declared with implausible type");
      }
   }

   /* Check for flatness, if required. */
   if (require_flat) {
      for (i = 0; i < bb->stmts_used; i++) {
         stmt = bb->stmts[i];
         if (!stmt)
            sanityCheckFail(bb, stmt, "IRStmt: is NULL");
         if (!isFlatIRStmt(stmt))
            sanityCheckFail(bb, stmt, "IRStmt: is not flat");
      }
      if (!isIRAtom(bb->next))
         sanityCheckFail(bb, NULL, "bb->next is not an atom");
   }

   /* Count the defs of each temp.  Only one def is allowed.
      Also, check that each used temp has already been defd. */

   for (i = 0; i < n_temps; i++)
      def_counts[i] = 0;

   for (i = 0; i < bb->stmts_used; i++) {
      IRDirty* d;
      IRCAS*   cas;
      stmt = bb->stmts[i];
      /* Check any temps used by this statement. */
      useBeforeDef_Stmt(bb,stmt,def_counts);

      /* Now make note of any temps defd by this statement. */
      switch (stmt->tag) {
      case Ist_WrTmp:
         def_counts[stmt->Ist.WrTmp.tmp]++;
         if (def_counts[stmt->Ist.WrTmp.tmp] > 1)
            sanityCheckFail(bb, stmt, 
               "IRStmt.Tmp: destination tmp is assigned more than once");
         break;
      case Ist_Store:
         if (stmt->Ist.Store.resSC != IRTemp_INVALID) {
            IRTemp resSC = stmt->Ist.Store.resSC;
            def_counts[resSC]++;
            if (def_counts[resSC] > 1)
               sanityCheckFail(bb, stmt, 
                  "IRStmt.Store.resSC: destination tmp "
                   "is assigned more than once");
         }
         break;
      case Ist_Dirty:
         if (stmt->Ist.Dirty.details->tmp != IRTemp_INVALID) {
            d = stmt->Ist.Dirty.details;
            def_counts[d->tmp]++;
            if (def_counts[d->tmp] > 1)
               sanityCheckFail(bb, stmt, 
                  "IRStmt.Dirty: destination tmp is assigned more than once");
         }
         break;
      case Ist_CAS:
         cas = stmt->Ist.CAS.details;

         if (cas->oldHi != IRTemp_INVALID) {
             def_counts[cas->oldHi]++;
             if (def_counts[cas->oldHi] > 1)
                sanityCheckFail(bb, stmt, 
                   "IRStmt.CAS: destination tmpHi is assigned more than once");
         }
          def_counts[cas->oldLo]++;
          if (def_counts[cas->oldLo] > 1)
             sanityCheckFail(bb, stmt, 
                "IRStmt.CAS: destination tmpLo is assigned more than once");
          break;
      default:
          /* explicitly handle the rest, so as to keep gcc quiet */
          break;
      }
   }

   /* Typecheck everything. */
   for (i = 0; i < bb->stmts_used; i++)
      if (bb->stmts[i])
         tcStmt( bb, bb->stmts[i], guest_word_size );
   if (typeOfIRExpr(bb->tyenv,bb->next) != guest_word_size)
      sanityCheckFail(bb, NULL, "bb->next field has wrong type");
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

Bool eqIRRegArray ( IRRegArray* descr1, IRRegArray* descr2 )
{
   return toBool( descr1->base == descr2->base 
                  && descr1->elemTy == descr2->elemTy
                  && descr1->nElems == descr2->nElems );
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

IRDirty* unsafeIRDirty_1_N ( IRTemp dst, 
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

Bool eqIRAtom ( IRExpr* a1, IRExpr* a2 )
{
   vassert(isIRAtom(a1));
   vassert(isIRAtom(a2));
   if (a1->tag == Iex_RdTmp && a2->tag == Iex_RdTmp)
      return toBool(a1->Iex.RdTmp.tmp == a2->Iex.RdTmp.tmp);
   if (a1->tag == Iex_Const && a2->tag == Iex_Const)
      return eqIRConst(a1->Iex.Const.con, a2->Iex.Const.con);
   return False;
}

/*---------------------------------------------------------------*/
/*--- end                                           ir_defs.c ---*/
/*---------------------------------------------------------------*/
