
/*---------------------------------------------------------------*/
/*---                                                         ---*/
/*--- This file (main_main.c) is                              ---*/
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

#include "libvex.h"
#include "libvex_emwarn.h"
#include "libvex_guest_amd64.h"

#include "main_globals.h"
#include "main_util.h"
#include "ir_opt.h"

#include "guest_generic_bb_to_IR.h"
#include "guest_amd64_defs.h"


/* This file contains the top level interface to the library. */

/* --------- fwds ... --------- */

static const char* show_hwcaps ( VexArch arch, UInt hwcaps );


/* --------- Initialise the library. --------- */

/* Exported to library client. */

void LibVEX_default_VexControl ( /*OUT*/ VexControl* vcon )
{
   vcon->iropt_verbosity            = 0;
   vcon->iropt_level                = 2;
   vcon->iropt_precise_memory_exns  = False;
   vcon->iropt_unroll_thresh        = 120;
   vcon->guest_max_insns            = 60;
   vcon->guest_chase_thresh         = 10;
}


/* Exported to library client. */

void LibVEX_Init (
   /* failure exit function */
   __attribute__ ((noreturn))
   void (*failure_exit) ( void ),
   /* logging output function */
   void (*log_bytes) ( const char*, Int nbytes ),
   /* debug paranoia level */
   Int debuglevel,
   /* Are we supporting valgrind checking? */
   Bool valgrind_support,
   /* Control ... */
   /*READONLY*/VexControl* vcon
)
{
   /* First off, do enough minimal setup so that the following
      assertions can fail in a sane fashion, if need be. */
   vex_failure_exit = failure_exit;
   vex_log_bytes    = log_bytes;

   /* Now it's safe to check parameters for sanity. */
   vassert(!vex_initdone);
   vassert(failure_exit);
   vassert(log_bytes);
   vassert(debuglevel >= 0);

   vassert(vcon->iropt_verbosity >= 0);
   vassert(vcon->iropt_level >= 0);
   vassert(vcon->iropt_level <= 2);
   vassert(vcon->iropt_unroll_thresh >= 0);
   vassert(vcon->iropt_unroll_thresh <= 400);
   vassert(vcon->guest_max_insns >= 1);
   vassert(vcon->guest_max_insns <= 100);
   vassert(vcon->guest_chase_thresh >= 0);
   vassert(vcon->guest_chase_thresh < vcon->guest_max_insns);

   /* Check that Vex has been built with sizes of basic types as
      stated in priv/libvex_basictypes.h.  Failure of any of these is
      a serious configuration error and should be corrected
      immediately.  If any of these assertions fail you can fully
      expect Vex not to work properly, if at all. */

   vassert(1 == sizeof(UChar));
   vassert(1 == sizeof(Char));
   vassert(2 == sizeof(UShort));
   vassert(2 == sizeof(Short));
   vassert(4 == sizeof(UInt));
   vassert(4 == sizeof(Int));
   vassert(8 == sizeof(ULong));
   vassert(8 == sizeof(Long));
   vassert(4 == sizeof(Float));
   vassert(8 == sizeof(Double));
   vassert(1 == sizeof(Bool));
   vassert(4 == sizeof(Addr32));
   vassert(8 == sizeof(Addr64));
   vassert(16 == sizeof(U128));

   vassert(sizeof(void*) == 4 || sizeof(void*) == 8);
   vassert(sizeof(void*) == sizeof(int*));
   vassert(sizeof(void*) == sizeof(HWord));

   vassert(VEX_HOST_WORDSIZE == sizeof(void*));
   vassert(VEX_HOST_WORDSIZE == sizeof(HWord));

   /* Really start up .. */
   vex_debuglevel         = debuglevel;
   vex_valgrind_support   = valgrind_support;
   vex_control            = *vcon;
   vex_initdone           = True;
   vexSetAllocMode ( VexAllocModeTEMP );
}


/* --------- Emulation warnings. --------- */

const char* LibVEX_EmWarn_string ( VexEmWarn ew )
{
   switch (ew) {
     case EmWarn_NONE: 
        return "none";
     case EmWarn_X86_x87exns:
        return "Unmasking x87 FP exceptions";
     case EmWarn_X86_x87precision:
        return "Selection of non-80-bit x87 FP precision";
     case EmWarn_X86_sseExns:
        return "Unmasking SSE FP exceptions";
     case EmWarn_X86_fz:
        return "Setting %mxcsr.fz (SSE flush-underflows-to-zero mode)";
     case EmWarn_X86_daz:
        return "Setting %mxcsr.daz (SSE treat-denormals-as-zero mode)";
     case EmWarn_X86_acFlag:
        return "Setting %eflags.ac (setting noted but ignored)";
     case EmWarn_PPCexns:
        return "Unmasking PPC32/64 FP exceptions";
     case EmWarn_PPC64_redir_overflow:
        return "PPC64 function redirection stack overflow";
     case EmWarn_PPC64_redir_underflow:
        return "PPC64 function redirection stack underflow";
     default: 
        vpanic("LibVEX_EmWarn_string: unknown warning");
   }
}

/* ------------------ Arch/HwCaps stuff. ------------------ */

const char* LibVEX_ppVexArch ( VexArch arch )
{
   switch (arch) {
      case VexArch_INVALID: return "INVALID";
      case VexArchX86:      return "X86";
      case VexArchAMD64:    return "AMD64";
      case VexArchARM:      return "ARM";
      case VexArchPPC32:    return "PPC32";
      case VexArchPPC64:    return "PPC64";
      default:              return "VexArch???";
   }
}

const char* LibVEX_ppVexHwCaps ( VexArch arch, UInt hwcaps )
{
   const char* str = show_hwcaps(arch,hwcaps);
   return str ? str : "INVALID";
}


/* Write default settings info *vai. */
void LibVEX_default_VexArchInfo ( /*OUT*/VexArchInfo* vai )
{
   vai->hwcaps             = 0;
   vai->ppc_cache_line_szB = 0;
}

/* Write default settings info *vbi. */
void LibVEX_default_VexAbiInfo ( /*OUT*/VexAbiInfo* vbi )
{
   vbi->guest_stack_redzone_size       = 0;
   vbi->guest_amd64_assume_fs_is_zero  = False;
   vbi->guest_amd64_assume_gs_is_0x60  = False;
   vbi->guest_ppc_zap_RZ_at_blr        = False;
   vbi->guest_ppc_zap_RZ_at_bl         = NULL;
   vbi->guest_ppc_sc_continues_at_LR   = False;
   vbi->host_ppc_calls_use_fndescrs    = False;
   vbi->host_ppc32_regalign_int64_args = False;
}


/* Return a string showing the hwcaps in a nice way.  The string will
   be NULL for invalid combinations of flags, so these functions also
   serve as a way to validate hwcaps values. */

static const char* show_hwcaps_x86 ( UInt hwcaps ) 
{
   /* Monotonic, SSE3 > SSE2 > SSE1 > baseline. */
   if (hwcaps == 0)
      return "x86-sse0";
   if (hwcaps == VEX_HWCAPS_X86_SSE1)
      return "x86-sse1";
   if (hwcaps == (VEX_HWCAPS_X86_SSE1 | VEX_HWCAPS_X86_SSE2))
      return "x86-sse1-sse2";
   if (hwcaps == (VEX_HWCAPS_X86_SSE1 
                  | VEX_HWCAPS_X86_SSE2 | VEX_HWCAPS_X86_SSE3))
      return "x86-sse1-sse2-sse3";

   return NULL;
}

static const char* show_hwcaps_amd64 ( UInt hwcaps )
{
   /* SSE3 and CX16 are orthogonal and > baseline, although we really
      don't expect to come across anything which can do SSE3 but can't
      do CX16.  Still, we can handle that case. */
   const UInt SSE3 = VEX_HWCAPS_AMD64_SSE3;
   const UInt CX16 = VEX_HWCAPS_AMD64_CX16;
         UInt c    = hwcaps;
   if (c == 0)           return "amd64-sse2";
   if (c == SSE3)        return "amd64-sse3";
   if (c == CX16)        return "amd64-sse2-cx16";
   if (c == (SSE3|CX16)) return "amd64-sse3-cx16";
   return NULL;
}

static const char* show_hwcaps_ppc32 ( UInt hwcaps )
{
   /* Monotonic with complications.  Basically V > F > baseline,
      but once you have F then you can have FX or GX too. */
   const UInt F  = VEX_HWCAPS_PPC32_F;
   const UInt V  = VEX_HWCAPS_PPC32_V;
   const UInt FX = VEX_HWCAPS_PPC32_FX;
   const UInt GX = VEX_HWCAPS_PPC32_GX;
         UInt c  = hwcaps;
   if (c == 0)           return "ppc32-int";
   if (c == F)           return "ppc32-int-flt";
   if (c == (F|FX))      return "ppc32-int-flt-FX";
   if (c == (F|GX))      return "ppc32-int-flt-GX";
   if (c == (F|FX|GX))   return "ppc32-int-flt-FX-GX";
   if (c == (F|V))       return "ppc32-int-flt-vmx";
   if (c == (F|V|FX))    return "ppc32-int-flt-vmx-FX";
   if (c == (F|V|GX))    return "ppc32-int-flt-vmx-GX";
   if (c == (F|V|FX|GX)) return "ppc32-int-flt-vmx-FX-GX";
   return NULL;
}

static const char* show_hwcaps_ppc64 ( UInt hwcaps )
{
   /* Monotonic with complications.  Basically V > baseline(==F),
      but once you have F then you can have FX or GX too. */
   const UInt V  = VEX_HWCAPS_PPC64_V;
   const UInt FX = VEX_HWCAPS_PPC64_FX;
   const UInt GX = VEX_HWCAPS_PPC64_GX;
         UInt c  = hwcaps;
   if (c == 0)         return "ppc64-int-flt";
   if (c == FX)        return "ppc64-int-flt-FX";
   if (c == GX)        return "ppc64-int-flt-GX";
   if (c == (FX|GX))   return "ppc64-int-flt-FX-GX";
   if (c == V)         return "ppc64-int-flt-vmx";
   if (c == (V|FX))    return "ppc64-int-flt-vmx-FX";
   if (c == (V|GX))    return "ppc64-int-flt-vmx-GX";
   if (c == (V|FX|GX)) return "ppc64-int-flt-vmx-FX-GX";
   return NULL;
}

static const char* show_hwcaps_arm ( UInt hwcaps )
{
   if (hwcaps == 0) return "arm-baseline";
   return NULL;
}

/* ---- */
static const char* show_hwcaps ( VexArch arch, UInt hwcaps )
{
   switch (arch) {
      case VexArchX86:   return show_hwcaps_x86(hwcaps);
      case VexArchAMD64: return show_hwcaps_amd64(hwcaps);
      case VexArchPPC32: return show_hwcaps_ppc32(hwcaps);
      case VexArchPPC64: return show_hwcaps_ppc64(hwcaps);
      case VexArchARM:   return show_hwcaps_arm(hwcaps);
      default: return NULL;
   }
}

/*---------------------------------------------------------------*/
/*--- end                                         main_main.c ---*/
/*---------------------------------------------------------------*/
