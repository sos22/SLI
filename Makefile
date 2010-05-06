all: real_all

OPTIMIZE=n
PROFILE_FLAGS=
TARGETS=
CPPFLAGS=-DSLI
CFLAGS=-Wall -g $(CPPFLAGS) $(PROFILE_FLAGS) -fno-strict-aliasing
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
