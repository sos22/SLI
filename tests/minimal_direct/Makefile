all: bug1.so

bug1.so: ../../ced_to_patch ./bug1 ./bug1.ced ../../sli/enforce_crash/patch_core.c
	../../ced_to_patch ./bug1 ./bug1.ced ../../ $@

bug1.ced: bug1.summary.canon4  ../../enforce_crash ./bug1 bug1.types.canon bug1.types.canon.idx bug1.bcg
	../../enforce_crash ./bug1 bug1.types.canon bug1.bcg $@ $<

bug1.summary.canon4: ../../canonicalise_crash_summary0 bug1.summary.canon3
	$^ $@

bug1.summary.canon3: ../../canonicalise_crash_summary3 bug1.summary.canon2
	$^ $@

bug1.summary.canon2: ../../canonicalise_crash_summary2 bug1.summary.canon0
	$^ $@

bug1.summary.canon1: ../../canonicalise_crash_summary bug1.summary.canon0
	$^ $@

bug1.summary.canon0: ../../canonicalise_crash_summary0 bug1.summary 
	$^ $@

bug1.summary: bug1.summaries
	! [ -e bug1.summaries/1 ] && [ -e bug1.summaries/0 ] && cp bug1.summaries/0 bug1.summary

bug1.summaries: ../../minimal_direct ./bug1 ./bug1.types.canon ./bug1.types.canon.idx bug1.bcg
	rm -rf bug1.summaries crash_summaries induction.log logs generated_patch.c static.db && \
	mkdir logs && \
	mkdir crash_summaries && \
	../../minimal_direct ./bug1 ./bug1.types.canon ./bug1.bcg && \
	mv crash_summaries bug1.summaries

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
	      bug1.ced *.so bug1.summary* core enforce_crash_*; \
	rm -rf bug1.summaries logs
