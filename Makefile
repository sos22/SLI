all: real_all

OPTIMIZE=y
TARGETS=
CPPFLAGS=-DSLI
CFLAGS=-Wall -g $(CPPFLAGS) -fno-strict-aliasing
CXXFLAGS=$(CFLAGS)

ifeq ($(OPTIMIZE),y)
CFLAGS+=-O3 -DNDEBUG
endif

include Makefile.mk

%.mk: %.mk.in build_makefile.sh
	./build_makefile.sh $< > $@.tmp && mv -f $@.tmp $@

clean:
	find . -name '*.mk' -o -name '*.o' | xargs rm ; \
	rm -f $(TARGETS)

real_all: $(TARGETS)
