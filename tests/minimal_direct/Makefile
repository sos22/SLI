all: bug1.so

%.so: ../../ced_to_patch % %.ced ../../sli/enforce_crash/patch_core.c
	../../ced_to_patch $* $*.ced ../../ $@

%.ced: %.summary.canon4  ../../enforce_crash % %.types.canon %.types.canon.idx %.bcg
	../../enforce_crash $* $*.types.canon $*.bcg $@ $<

%.summary.canon4: ../../canonicalise_crash_summary0 %.summary.canon3
	$^ $@

%.summary.canon3: ../../canonicalise_crash_summary3 %.summary.canon2
	$^ $@

%.summary.canon2: ../../canonicalise_crash_summary2 %.summary.canon0
	$^ $@

%.summary.canon1: ../../canonicalise_crash_summary %.summary.canon0
	$^ $@

%.summary.canon0: ../../canonicalise_crash_summary0 %.summary 
	$^ $@

%.summary: %.summaries
	! [ -e $</1 ] && [ -e $</0 ] && cp $</0 $@

%.summaries: ../../minimal_direct % %.types.canon %.types.canon.idx %.bcg
	rm -rf $@ crash_summaries induction.log logs generated_patch.c static.db && \
	mkdir logs && \
	mkdir crash_summaries && \
	../../minimal_direct $* $*.types.canon $*.bcg && \
	mv crash_summaries $*.summaries

%.types: % ./build_types_table.sh
	./build_types_table.sh ./$<

%.bcg: % ./build_call_graph.sh
	./build_call_graph.sh ./$<

%.types.canon: % %.types ../../canonicalise_types_table
	../../canonicalise_types_table ./$< $<.types $@

%.types.canon.idx: % %.types.canon ../../build_types_db
	rm -f $@ ; \
	../../build_types_db ./$< $<.types.canon $@

bug1: bug1.c
	gcc -pthread -Wall -g bug1.c -o bug1

clean:
	rm -f bug1 *.idx *.canon *.types *.bcg *~ static.db timings.txt generated_patch.c \
	      *.ced *.so *.summary* core enforce_crash_*; \
	rm -rf *.summaries logs
