#ifndef EXCEPTIONS_H__
#define EXCEPTIONS_H__

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <exception>

class SliException : public std::exception {
	char *msg;
protected:
	void setMessage(va_list args, const char *fmt)
	{
		free(msg);
		int r = vasprintf(&msg, fmt, args);
		(void)r;
	}
	void setMessage(const char *fmt, ...)  __attribute__((__format__ (__printf__,2,3)))
	{
		va_list args;
		va_start(args, fmt);
		setMessage(args, fmt);
		va_end(args);
	}
public:
	SliException(const SliException &b)
	{
		msg = strdup(b.msg);
	}
	SliException(const char *fmt, ...) __attribute__((__format__ (__printf__,2,3)))
	{
		va_list args;
		va_start(args, fmt);
		int r = vasprintf(&msg, fmt, args);
		(void)r;
		va_end(args);
	}
	SliException()
		: msg(strdup(""))
	{
	}
	~SliException() throw()
	{
		free(msg);
	}
	virtual const char *what() const throw() {
		return msg;
	}
};

class ReplayFailedException : public SliException {
public:
	ReplayFailedException(const char *fmt, ...) __attribute__((__format__ (__printf__,2,3)))
	{
		va_list args;
		va_start(args, fmt);
		setMessage(args, fmt);
		va_end(args);
	}
};

class ReplayFailedBadRegister : public ReplayFailedException {
public:
	const char *reg_name;
	unsigned long observed;
	unsigned long expected;
	ReplayFailedBadRegister(const char *_name,
				unsigned long _observed,
				unsigned long _expected) :
		ReplayFailedException(
			"replay failed due to bad register %s: wanted %lx, got %lx\n",
			_name,
			_expected,
			_observed),
		reg_name(_name),
		observed(_observed),
		expected(_expected)
	{
	}
};

class InstructionDecodeFailedException : public SliException {
};

class NotImplementedException : public SliException {
public:
	char *reason;
	NotImplementedException(const char *fmt, ...) __attribute__((__format__ (__printf__,2,3)))
	{
		va_list args;
		
		va_start(args, fmt);
		int r = vasprintf(&reason, fmt, args);
		(void)r;
		va_end(args);
		setMessage("not implemented: %s", reason);
	}
	NotImplementedException() :
		SliException("not implemented"),
		reason(NULL)
	{
	}

	~NotImplementedException() throw () {
		free(reason);
	}
};

class BadMemoryException : public SliException {
public:
	bool isWrite;
	unsigned long ptr;
	unsigned size;
	BadMemoryException(bool _isWrite,
			   unsigned long _ptr,
			   unsigned _size) :
		SliException(
			"guest dereferenced a bad pointer: size %x, isWrite %d\n",
			_size,
			_isWrite),
		isWrite(_isWrite),
		ptr(_ptr),
		size(_size)
	{
	}
};

class ForceFailureException : public SliException {
public:
	unsigned long rip;
	ForceFailureException(unsigned long _rip)
		: SliException(
			"forced failure at %lx\n", _rip),
		  rip(_rip)
	{
	}
};

class UnknownSyscallException : public SliException {
public:
	unsigned nr;
	UnknownSyscallException(unsigned _nr) :
		SliException("unknown syscall %d\n", _nr),
		nr(_nr)
	{
	}
};

class AssertFailedException : public SliException {
public:
	const char *file;
	unsigned line;
	char *condition;
	AssertFailedException(const char *_file,
			      unsigned _line,
			      const char *_condition,
			      ...)  __attribute__((__format__ (__printf__,4,5)))
		: SliException(),
		  file(_file),
		  line(_line)
	{
		va_list args;
		va_start(args, _condition);
		int r = vasprintf(&condition, _condition, args);
		(void)r;
		va_end(args);
		setMessage("assertion failed at %s:%d: %s",
			   file, line, condition);
	}
	~AssertFailedException() throw () {
		free(condition);
	}
};

#undef assert
#ifndef NDEBUG
#define assert(x)							\
	do {								\
		if (!(x))						\
			throw AssertFailedException(__FILE__, __LINE__,	\
						    "%s", #x );		\
	} while (0)
#else
/* Moderate trickiness so that we check that @x has the right type and
   doesn't reference any bad variables, but we don't force any
   functions in @x to be evaluated in NDEBUG builds. */
#define assert(x)				\
	do {					\
		if (0) {			\
			int ___ignore = !(x);	\
			(void)___ignore;	\
		}				\
	} while (0)
#endif

#endif /* !EXCEPTIONS_H__ */
