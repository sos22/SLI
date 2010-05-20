#include "sli.h"

#define for_each_event(x)						\
	x(RdtscEvent)							\
	x(LoadEvent)							\
	x(StoreEvent)							\
	x(CasEvent)							\
	x(SignalEvent)							\
	x(SyscallEvent)							\
	x(InstructionEvent)

#define mk_template(evt)			\
	template <typename ait> VexAllocTypeWrapper<evt<ait> > evt<ait>::allocator;

for_each_event(mk_template)

#define mk_allocator(e, t)						\
	template VexAllocTypeWrapper<e<t> > e<t>::allocator;

#define instantiate(e) mk_allocator(e, unsigned long) mk_allocator(e, abstract_interpret_value)

for_each_event(instantiate)
