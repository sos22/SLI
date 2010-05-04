all: real_all

TARGETS=
CPPFLAGS=-DSLI
CFLAGS=-Wall -g $(CPPFLAGS)
CXXFLAGS=-Wall -g $(CPPFLAGS)

include Makefile.mk

%.mk: %.mk.in build_makefile.sh
	./build_makefile.sh $< > $@.tmp && mv -f $@.tmp $@

clean:
	find . -name '*.mk' -o -name '*.o' | xargs rm ; \
	rm -f $(TARGETS)

real_all: $(TARGETS)
