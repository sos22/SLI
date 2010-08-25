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
	NAMED_CLASS
};

template <typename outtype, typename intype> VexAllocTypeWrapper<AbstractLogReader<outtype, intype> > AbstractLogReader<outtype,intype>::allocator;

template <typename rtype>
LogRecord<rtype> *
abstractLogRecord(const LogRecord<unsigned long> *inp)
{
#define DO_TYPE(typ)							\
	if (const LogRecord ## typ <unsigned long> *ll =		\
	    dynamic_cast<const LogRecord ## typ <unsigned long> *>(inp)) \
		return ll->abstract<rtype>()
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

template <typename outtype, typename intype>
LogRecord<outtype> *
AbstractLogReader<outtype,intype>::read(LogReaderPtr startPtr, LogReaderPtr *outPtr) const
{
	LogRecord<intype> *inr = inp->read(startPtr, outPtr);
	if (!inr)
		return NULL;
	return abstractLogRecord<outtype>(inr);
}

template <typename ait> template <typename new_type>
LogReader<new_type> *LogReader<ait>::abstract() const
{
	return new AbstractLogReader<new_type, ait>(this);
}

template LogReader<abstract_interpret_value> *LogReader<unsigned long>::abstract<abstract_interpret_value>() const;
template LogReader<racetrack_value> *LogReader<unsigned long>::abstract<racetrack_value>() const;

