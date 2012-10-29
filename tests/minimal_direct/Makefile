all: bug1.so bug2.so bug3.so

%.so: ../../ced_to_patch %.exe %.ced ../../sli/enforce_crash/patch_core.c
	../../ced_to_patch $*.exe $*.ced ../../ $@

%.cep.o: %.cep.c ../../sli/enforce_crash/cep_interpreter.h
	gcc -g -I ../../sli/enforce_crash -c -fPIC -Wall -Werror $< -o $@

%.cep.c: %.ced ../../ced_to_cep %.bcg %.types.canon %.exe
	../../ced_to_cep $*.exe $< $*.types.canon $*.bcg $@
%.interp.so: %.cep.o ../../cep_interpreter.o
	gcc -shared $^ -o $@

%.fix.c: ../../summary_to_fix %.exe %.types.canon %.bcg %.summary.canon4
	../../summary_to_fix $*.exe $*.types.canon $*.bcg $@ $*.summary.canon4
%.fix.so: %.fix.c ../../sli/patch_head.h ../../sli/patch_skeleton_jump.c ../../sli/patch_skeleton_common.c
	gcc -Wall -g -shared -fPIC -I../../sli $< -o $@

%.ced: %.summary.canon4  ../../enforce_crash %.exe %.types.canon %.bcg
	../../enforce_crash $*.exe $*.types.canon $*.bcg $@ $<

%.summary.canon4: ../../canonicalise_crash_summary0 %.summary.canon3
	$^ $@

%.summary.canon3: ../../canonicalise_crash_summary3 %.summary.canon2 %.exe %.types.canon
	$< $*.summary.canon2 $*.exe $*.types.canon $@

%.summary.canon2: ../../canonicalise_crash_summary2 %.summary.canon0
	$^ $@

%.summary.canon1: ../../canonicalise_crash_summary %.summary.canon0
	$^ $@

%.summary.canon0: ../../canonicalise_crash_summary0 %.summary 
	$^ $@

%.summary: %.summaries
	! [ -e $</1 ] && [ -e $</0 ] && cp $</0 $@

bug9a.summary: bug9.summaries
	cp $</0 $@
bug9b.summary: bug9.summaries
	cp $</1 $@
bug9a.summary.canon3: ../../canonicalise_crash_summary3 bug9a.summary.canon2 bug9.exe bug9.types.canon
	$< bug9a.summary.canon2 bug9.exe bug9.types.canon $@
bug9b.summary.canon3: ../../canonicalise_crash_summary3 bug9b.summary.canon2 bug9.exe bug9.types.canon
	$< bug9b.summary.canon2 bug9.exe bug9.types.canon $@
bug9a.ced: bug9a.summary.canon4  ../../enforce_crash bug9.exe bug9.types.canon bug9.bcg
	../../enforce_crash bug9.exe bug9.types.canon bug9.bcg $@ $<
bug9b.ced: bug9b.summary.canon4  ../../enforce_crash bug9.exe bug9.types.canon bug9.bcg
	../../enforce_crash bug9.exe bug9.types.canon bug9.bcg $@ $<
bug9a.cep.c: bug9a.ced ../../ced_to_cep bug9.bcg bug9.types.canon bug9.exe
	../../ced_to_cep bug9.exe $< bug9.types.canon bug9.bcg $@
bug9b.cep.c: bug9b.ced ../../ced_to_cep bug9.bcg bug9.types.canon bug9.exe
	../../ced_to_cep bug9.exe $< bug9.types.canon bug9.bcg $@
bug9ab.ced: bug9a.summary.canon4 bug9b.summary.canon4  ../../enforce_crash bug9.exe bug9.types.canon bug9.bcg
	../../enforce_crash bug9.exe bug9.types.canon bug9.bcg $@ bug9a.summary.canon4 bug9b.summary.canon4
bug9ab.cep.c: bug9ab.ced ../../ced_to_cep bug9.bcg bug9.types.canon bug9.exe
	../../ced_to_cep bug9.exe $< bug9.types.canon bug9.bcg $@

%.summaries: ../../minimal_direct %.exe %.types.canon %.bcg
	rm -rf $@ crash_summaries induction.log logs generated_patch.c static.db && \
	mkdir logs && \
	mkdir crash_summaries && \
	../../minimal_direct $*.exe $*.types.canon $*.bcg && \
	mv crash_summaries $*.summaries

%.types: %.exe ./build_types_table.sh
	./build_types_table.sh ./$<

%.bcg: %.exe ./build_call_graph.sh
	./build_call_graph.sh ./$<

%.types.canon: %.exe %.types ../../canonicalise_types_table
	../../canonicalise_types_table ./$< $*.types $@

.PRECIOUS: bug1.types bug1.bcg bug2.types bug2.bcg bug1.ced bug2.ced bug3.types bug3.bcg bug3.ced bug4.types bug4.bcg bug4.ced bug5.types bug5.bcg bug5.ced bug6.types bug6.bcg bug6.ced bug8.types bug8.bcg bug9.types bug9.bcg

%.exe: %.c
	gcc -O -pthread -Wall -g $< -o $@

clean:
	rm -f *.exe *.idx *.canon *.types *.bcg *~ static.db timings.txt generated_patch.c \
	      *.ced *.cep *.cep.c *.so *.summary* core enforce_crash_* static.db timings.txt; \
	rm -rf *.summaries logs
