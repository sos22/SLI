all: real_all

TARGETS=
CPPFLAGS=-DSLI
CFLAGS=-Wall -g $(CPPFLAGS) -O3 -fno-strict-aliasing
CXXFLAGS=-Wall -g $(CPPFLAGS) -O3 -fno-strict-aliasing

include Makefile.mk

%.mk: %.mk.in build_makefile.sh
	./build_makefile.sh $< > $@.tmp && mv -f $@.tmp $@

clean:
	find . -name '*.mk' -o -name '*.o' | xargs rm ; \
	rm -f $(TARGETS)

real_all: $(TARGETS)
