all: bug1.so bug2.so bug3.so

%.so: ../../ced_to_patch %.exe %.ced ../../sli/enforce_crash/patch_core.c
	../../ced_to_patch $*.exe $*.ced ../../ $@

%.cep.o: %.cep.c ../../sli/enforce_crash/cep_interpreter.h
	gcc -g -I ../../sli/enforce_crash -c -fPIC -Wall -Werror $< -o $@

%.cep.c: %.ced ../../ced_to_cep
	../../ced_to_cep $*.exe $< > $@
%.interp.so: %.cep.o ../../cep_interpreter.o
	gcc -shared $^ -o $@

%.ced: %.summary.canon4  ../../enforce_crash %.exe %.types.canon %.types.canon.idx %.bcg
	../../enforce_crash $*.exe $*.types.canon $*.bcg $@ $<

%.summary.canon4: ../../canonicalise_crash_summary0 %.summary.canon3
	$^ $@

%.summary.canon3: ../../canonicalise_crash_summary3 %.summary.canon2 %.exe %.types.canon %.types.canon.idx
	$< $*.summary.canon2 $*.exe $*.types.canon $@

%.summary.canon2: ../../canonicalise_crash_summary2 %.summary.canon0
	$^ $@

%.summary.canon1: ../../canonicalise_crash_summary %.summary.canon0
	$^ $@

%.summary.canon0: ../../canonicalise_crash_summary0 %.summary 
	$^ $@

%.summary: %.summaries
	! [ -e $</1 ] && [ -e $</0 ] && cp $</0 $@

%.summaries: ../../minimal_direct %.exe %.types.canon %.types.canon.idx %.bcg
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

.PRECIOUS: bug1.types bug1.bcg bug2.types bug2.bcg bug1.ced bug2.ced bug3.types bug3.bcg bug3.ced bug4.types bug4.bcg bug4.ced bug5.types bug5.bcg bug5.ced
%.types.canon.idx: %.exe %.types.canon ../../build_types_db
	rm -f $@ ; \
	../../build_types_db ./$< $*.types.canon $@

%.exe: %.c
	gcc -pthread -Wall -g $< -o $@

clean:
	rm -f *.exe *.idx *.canon *.types *.bcg *~ static.db timings.txt generated_patch.c \
	      *.ced *.cep *.cep.c *.so *.summary* core enforce_crash_* static.db timings.txt; \
	rm -rf *.summaries logs
