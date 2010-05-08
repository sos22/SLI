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
include .depends

.depends:
	for x in $(all_sources);\
	do\
		echo "include $${x}.d" ;\
	done > $@.t &&\
	mv -f $@.t $@

%.mk: %.mk.in build_makefile.sh
	./build_makefile.sh $< > $@.tmp && mv -f $@.tmp $@

%.cpp.d: %.cpp
	g++ $(CPPFLAGS) -MG -M -MD -o $@ $<

clean:
	find . -name '*.mk' -o -name '*.[od]' | xargs rm ; \
	rm -f $(TARGETS) ; \
	rm -f .depends

real_all: $(TARGETS)
