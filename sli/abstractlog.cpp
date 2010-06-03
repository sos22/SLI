#include "sli.h"

template <typename outtype, typename intype>
class AbstractLogReader : public LogReader<outtype> {
	const LogReader<intype> *inp;
	static VexAllocTypeWrapper<AbstractLogReader> allocator;
public:
	static void *operator new(size_t s) { return LibVEX_Alloc_Sized(&allocator.type, s); }
	LogRecord<outtype> *read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const;
	AbstractLogReader(const LogReader<intype> *_inp) :
		LogReader<outtype>(),
		inp(_inp) {}
	void visit(HeapVisitor &hv) const {}
	void destruct() {}
};

template <typename outtype, typename intype> VexAllocTypeWrapper<AbstractLogReader<outtype, intype> > AbstractLogReader<outtype,intype>::allocator;

/* Templates turn out to be much more limited than you would expect,
   so have to unroll this by hand (in particular, you can't call a
   member template function from another multi-parameter template
   function, at least not with gcc 4.3.3).  Grr. */

static LogRecord<abstract_interpret_value> *
abstractLogRecord(const LogRecord<unsigned long> *inp)
{
#define DO_TYPE(typ)							\
	if (const LogRecord ## typ <unsigned long> *ll =		\
	    dynamic_cast<const LogRecord ## typ <unsigned long> *>(inp)) \
		return ll->abstract<abstract_interpret_value>()
	DO_TYPE(InitialSighandlers);
	DO_TYPE(Load);
	DO_TYPE(Store);
	DO_TYPE(Footstep);
	DO_TYPE(Syscall);
	DO_TYPE(Memory);
	DO_TYPE(Rdtsc);
	DO_TYPE(Signal);
	DO_TYPE(AllocateMemory);
	DO_TYPE(InitialRegisters);
	DO_TYPE(InitialBrk);
	DO_TYPE(VexThreadState);
#undef DO_TYPE
	abort();
}

template <>
LogRecord<abstract_interpret_value> *
AbstractLogReader<abstract_interpret_value,unsigned long>::read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const
{
	LogRecord<unsigned long> *inr = inp->read(startPtr, outPtr);
	if (!inr)
		return NULL;
	return abstractLogRecord(inr);
}

template <typename ait> template <typename new_type>
LogReader<new_type> *LogReader<ait>::abstract() const
{
	return new AbstractLogReader<new_type, ait>(this);
}

template LogReader<abstract_interpret_value> *LogReader<unsigned long>::abstract<abstract_interpret_value>() const;

