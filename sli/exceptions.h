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
		vasprintf(&msg, fmt, args);
	}
	void setMessage(const char *fmt, ...)
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
	SliException(const char *fmt, ...)
	{
		va_list args;
		va_start(args, fmt);
		vasprintf(&msg, fmt, args);
		va_end(args);
	}
	SliException()
		: msg(strdup(""))
	{
	}
	~SliException() throw()
	{
		printf("Destroy sli exception\n");
		free(msg);
	}
	virtual const char *what() const throw() {
		return msg;
	}
};

class ReplayFailedException : public SliException {
public:
	ReplayFailedException(const char *fmt, ...)
	{
		va_list args;
		va_start(args, fmt);
		setMessage(fmt, args);
		va_end(args);
	}
};

class ReplayFailedBadRip : public ReplayFailedException {
public:
	unsigned long observed;
	unsigned long expected;
	ReplayFailedBadRip(unsigned long _observed,
			   unsigned long _expected) :
		ReplayFailedException(
			"replay failed due to bad RIP: wanted %lx, got %lx\n",
			_expected,
			_observed),
		observed(_observed),
		expected(_expected)
	{
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
			"guest dereferenced a bad pointer: address %lx, size %x, isWrite %d\n",
			_ptr,
			_size,
			_isWrite),
		isWrite(_isWrite),
		ptr(_ptr),
		size(_size)
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
			      ...) :
		SliException(),
		file(_file),
		line(_line)
	{
		va_list args;
		va_start(args, _condition);
		vasprintf(&condition, _condition, args);
		va_end(args);
		setMessage("assertion failed at %s:%d: %s",
			   file, line, condition);
	}
	~AssertFailedException() throw () {
		free(condition);
	}
};

#define assert(x)							\
	do {								\
	if (!(x))							\
		throw AssertFailedException(__FILE__, __LINE__,		\
					    "%s", #x );			\
	} while (0)

#endif /* !EXCEPTIONS_H__ */
