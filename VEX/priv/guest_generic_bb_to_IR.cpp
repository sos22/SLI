
/*--------------------------------------------------------------------*/
/*---                                                              ---*/
/*--- This file (guest_generic_bb_to_IR.c) is                      ---*/
/*--- Copyright (C) OpenWorks LLP.  All rights reserved.           ---*/
/*---                                                              ---*/
/*--------------------------------------------------------------------*/

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
#include "libvex_prof.hpp"
#include "main_util.h"
#include "main_globals.h"
#include "guest_generic_bb_to_IR.h"


/* Small helpers */
static Bool const_False ( void*, Addr64 ) { 
   return False; 
}

/* Disassemble a complete basic block, starting at guest_IP_start, 
   returning a new IRSB.  The disassembler may chase across basic
   block boundaries if it wishes and if chase_into_ok allows it.
   The precise guest address ranges from which code has been taken
   are written into vge.  guest_IP_bbstart is taken to be the IP in
   the guest's address space corresponding to the instruction at
   &guest_code[0].  

   dis_instr_fn is the arch-specific fn to disassemble on function; it
   is this that does the real work.

   do_self_check indicates that the caller needs a self-checking
   translation.

   preamble_function is a callback which allows the caller to add
   its own IR preamble (following the self-check, if any).  May be
   NULL.  If non-NULL, the IRSB under construction is handed to 
   this function, which presumably adds IR statements to it.  The
   callback may optionally complete the block and direct bb_to_IR
   not to disassemble any instructions into it; this is indicated
   by the callback returning True.

   offB_TIADDR and offB_TILEN are the offsets of guest_TIADDR and
   guest_TILEN.  Since this routine has to work for any guest state,
   without knowing what it is, those offsets have to passed in.

   callback_opaque is a caller-supplied pointer to data which the
   callbacks may want to see.  Vex has no idea what it is.
   (In fact it's a VgInstrumentClosure.)
*/

IRSB* bb_to_IR ( unsigned tid,
                 /*IN*/ void*            callback_opaque,
                 /*IN*/ DisOneInstrFn    dis_instr_fn,
                 /*IN*/ GuestMemoryFetcher &guest_code,
                 /*IN*/ const ThreadRip &guest_IP_bbstart,
                 /*IN*/ Bool             (*chase_into_ok)(void*,Addr64),
                 /*IN*/ Bool             host_bigendian,
                 /*IN*/ VexArchInfo*     archinfo_guest,
                 /*IN*/ VexAbiInfo*      abiinfo_both,
                 /*IN*/ Bool             do_self_check,
                 /*IN*/ Bool             (*preamble_function)(void*,IRSB*),
		 bool singleInstr)
{
   Long       delta;
   Int        n_instrs, first_stmt_idx;
   Bool       resteerOK, need_to_put_IP, debug_print;
   DisResult  dres;
   IRStmt*    imark;
   static Int n_resteers = 0;
   Int        d_resteers = 0;
   Int        selfcheck_idx = 0;
   IRSB*      irsb;
   ThreadRip  guest_IP_curr_instr(guest_IP_bbstart);

   Bool (*resteerOKfn)(void*,Addr64) = NULL;

   __set_profiling(libvex_decode);

   debug_print = toBool(vex_traceflags & VEX_TRACE_FE);

   /* Note: for adler32 to work without % operation for the self
      check, need to limit length of stuff it scans to 5552 bytes.
      Therefore limiting the max bb len to 100 insns seems generously
      conservative. */

   /* check sanity .. */
   vassert(sizeof(HWord) == sizeof(void*));
   vassert(vex_control.guest_max_insns >= 1);
   vassert(vex_control.guest_max_insns < 100);
   vassert(vex_control.guest_chase_thresh >= 0);
   vassert(vex_control.guest_chase_thresh < vex_control.guest_max_insns);

   /* And a new IR superblock to dump the result into. */
   irsb = emptyIRSB();

   /* Delta keeps track of how far along the guest_code array we have
      so far gone. */
   delta    = 0;
   n_instrs = 0;

   /* If asked to make a self-checking translation, leave 5 spaces
      in which to put the check statements.  We'll fill them in later
      when we know the length and adler32 of the area to check. */
   if (do_self_check) {
      selfcheck_idx = irsb->stmts_used;
      addStmtToIRSB( irsb, IRStmt_NoOp() );
      addStmtToIRSB( irsb, IRStmt_NoOp() );
      addStmtToIRSB( irsb, IRStmt_NoOp() );
      addStmtToIRSB( irsb, IRStmt_NoOp() );
      addStmtToIRSB( irsb, IRStmt_NoOp() );
   }

   /* If the caller supplied a function to add its own preamble, use
      it now. */
   if (preamble_function) {
      Bool stopNow = preamble_function( callback_opaque, irsb );
      if (stopNow) {
         /* The callback has completed the IR block without any guest
            insns being disassembled into it, so just return it at
            this point, even if a self-check was requested - as there
            is nothing to self-check.  The five self-check no-ops will
            still be in place, but they are harmless. */
         return irsb;
      }
   }

   /* Process instructions. */
   while (True) {
      vassert(n_instrs < vex_control.guest_max_insns);

      /* Regardless of what chase_into_ok says, is chasing permissible
         at all right now?  Set resteerOKfn accordingly. */
      resteerOK 
         = toBool(
              n_instrs < vex_control.guest_chase_thresh
              /* If making self-checking translations, don't chase
                 .. it makes the checks too complicated.  We only want
                 to scan just one sequence of bytes in the check, not
                 a whole bunch. */
              && !do_self_check
           );

      resteerOKfn
         = resteerOK ? chase_into_ok : const_False;

      /* This is the irsb statement array index of the first stmt in
         this insn.  That will always be the instruction-mark
         descriptor. */
      first_stmt_idx = irsb->stmts_used;

      /* Add an instruction-mark statement.  We won't know until after
         disassembling the instruction how long it instruction is, so
         just put in a zero length and we'll fix it up later. */
      addStmtToIRSB( irsb, IRStmt_IMark( guest_IP_curr_instr, 0 ));

      /* for the first insn, the dispatch loop will have set
         %IP, but for all the others we have to do it ourselves. */
      need_to_put_IP = toBool(n_instrs > 0);

      /* Finally, actually disassemble an instruction. */
      dres = dis_instr_fn ( tid,
			    irsb,
                            need_to_put_IP,
                            resteerOKfn,
                            callback_opaque,
                            guest_code,
                            delta,
                            guest_IP_curr_instr,
                            archinfo_guest,
                            abiinfo_both,
                            host_bigendian );

      /* stay sane ... */
      vassert(dres.whatNext == DisResult::Dis_StopHere
              || dres.whatNext == DisResult::Dis_Continue
              || dres.whatNext == DisResult::Dis_Resteer);
      vassert(dres.len >= 0 && dres.len <= 20);
      if (dres.whatNext != DisResult::Dis_Resteer)
	 vassert(!dres.continueAt.rip.isValid());

      /* Fill in the insn-mark length field. */
      vassert(first_stmt_idx >= 0 && first_stmt_idx < irsb->stmts_used);
      imark = irsb->stmts[first_stmt_idx];
      vassert(imark);
      vassert(imark->tag == Ist_IMark);
      vassert(((IRStmtIMark *)imark)->len == 0);
      ((IRStmtIMark *)imark)->len = toUInt(dres.len);

      n_instrs++;
      if (debug_print) 
	 printf("\n");

      /* Advance delta (inconspicuous but very important :-) */
      delta += (Long)dres.len;

      if (singleInstr)
	goto done;

      switch (dres.whatNext) {
         case DisResult::Dis_Continue:
	    /* This is the IP of the instruction we're just about to deal
	       with. */
	   guest_IP_curr_instr = guest_IP_curr_instr + (long)dres.len;

            if (n_instrs < vex_control.guest_max_insns) {
               /* keep going */
            } else {
               /* We have to stop. */
	       irsb->next_is_const = true;
	       irsb->next_const = guest_IP_bbstart + (long)delta;
               goto done;
            }
            break;
         case DisResult::Dis_StopHere:
            goto done;
         case DisResult::Dis_Resteer:
            /* Check that we actually allowed a resteer .. */
            vassert(resteerOK);
            /* figure out a new delta to continue at. */
            delta = dres.continueAt.rip.unwrap_vexrip() - guest_IP_bbstart.rip.unwrap_vexrip();
            n_resteers++;
            d_resteers++;

	    /* This is the IP of the instruction we're just about to deal
	       with. */
	    guest_IP_curr_instr = dres.continueAt;

            break;
         default:
            vpanic("bb_to_IR");
      }
   }
   /*NOTREACHED*/
   vassert(0);

  done:
   return irsb;
}


/*--------------------------------------------------------------------*/
/*--- end                                 guest_generic_bb_to_IR.c ---*/
/*--------------------------------------------------------------------*/
