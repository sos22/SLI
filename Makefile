all: real_all

OPTIMIZE=y
#PROFILE_FLAGS=-DMANUAL_PROFILING=1
PROFILE_FLAGS=
TARGETS=
CPPFLAGS=-DSLI -include config.h
CFLAGS=-Wall -g $(PROFILE_FLAGS) $(OPTIMIZE_FLAGS) -fno-strict-aliasing
CXXFLAGS=$(CFLAGS)
clean_files=$(TARGETS) .depends
all_makefiles=Makefile Makefile.mk

CXXFLAGS+=-std=gnu++0x
ifeq ($(OPTIMIZE),y)
OPTIMIZE_FLAGS=-O1 -DNDEBUG
else
OPTIMIZE_FLAGS=-D_GLIBCXX_DEBUG
endif

include Makefile.mk

Makefile.mk: Makefile.mk.in build_makefile.sh
	./build_makefile.sh $< $@ > $@.tmp && mv -f $@.tmp $@

%.cpp.d: %.cpp
	g++ $(CPPFLAGS) -MG -M -MD -MT $(patsubst %.cpp,%.o,$<) -o $@ $<

clean:
	find . -name '*.mk' -o -name '*.[od]' | xargs rm ; \
	rm -f $(clean_files)

real_all: $(TARGETS)

.depends: $(all_makefiles)
	make -f Makefile.mk mk_depends

extra_config.h:
	touch extra_config.h

include .depends
