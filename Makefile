all: real_all

OPTIMIZE?=y
SELECTIVE_PROFILING=n
#PROFILE_FLAGS=-DMANUAL_PROFILING=1
PROFILE_FLAGS=
TARGETS=
CPPFLAGS=-DSLI -include config.h
CFLAGS=-Wall -g $(PROFILE_FLAGS) $(OPTIMIZE_FLAGS) -fno-strict-aliasing -Wimplicit -Wredundant-decls -Wunused-parameter
CXXFLAGS=$(CFLAGS)
clean_files=$(TARGETS) .depends
all_makefiles=Makefile Makefile.mk

CXXFLAGS+=-std=gnu++0x
ifeq ($(OPTIMIZE),y)
OPTIMIZE_FLAGS=-O1 -DNDEBUG
else
OPTIMIZE_FLAGS=-D_GLIBCXX_DEBUG
endif
ifeq ($(SELECTIVE_PROFILING),y)
CFLAGS+=-fno-omit-frame-pointer
CPPFLAGS+=-DSELECTIVE_PROFILING=1
else
CPPFLAGS+=-DSELECTIVE_PROFILING=0
endif

ifeq ($(VERBOSE),y)
%.o: %.cpp
	g++ $(CXXFLAGS) $(CPPFLAGS) -c -o $@ $<
else
%.o: %.cpp
	@printf "Compile [%-40s]\\n" $@ ; \
	g++ $(CXXFLAGS) $(CPPFLAGS) -c -o $@ $<
endif

include Makefile.mk

Makefile.mk: Makefile.mk.in build_makefile.sh
	./build_makefile.sh $< $@ > $@.tmp && mv -f $@.tmp $@

ifeq ($(VERBOSE),y)
%.cpp.d: %.cpp
	g++ $(CPPFLAGS) -MG -M -MD -MT $(patsubst %.cpp,%.o,$<) -o $@ $<
else
%.cpp.d: %.cpp
	@printf "Depend [%-40s]\n" $@ ; \
	g++ $(CPPFLAGS) -MG -M -MD -MT $(patsubst %.cpp,%.o,$<) -o $@ $<
endif

clean:
	find . -name '*.mk' -o -name '*.[od]' | xargs rm ; \
	rm -f $(clean_files)
	rm -rf ${clean_dirs}

real_all: $(TARGETS)

.depends: $(all_makefiles)
	make -f Makefile.mk mk_depends

extra_config.h:
	touch extra_config.h

include .depends
