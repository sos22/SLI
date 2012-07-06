all: bug1.summaries

bug1.summaries: ./bug1 ./bug1.types.canon ./bug1.types.canon.idx bug1.bcg
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
	rm -f bug1 *.idx *.canon *.types *.bcg *~ static.db timings.txt generated_patch.c ;\
	rm -rf bug1.summaries logs
