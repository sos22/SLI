#ifndef ORACLE_RIP_HPP__
#define ORACLE_RIP_HPP__

#include "libvex_rip.hpp"

class ThreadVexRip : public Named {
	char *mkName() const { return my_asprintf("%d:%s", thread, rip.name()); }
public:
	unsigned thread;
	VexRip rip;

	bool operator< (const ThreadVexRip &other) const {
		if (thread < other.thread)
			return true;
		else if (thread > other.thread)
			return false;
		else
			return rip < other.rip;
	}
	mk_ordering_operators(ThreadVexRip)

	ThreadVexRip(unsigned _thread, const VexRip &_rip)
		: thread(_thread), rip(_rip)
	{}

	ThreadVexRip() {}
	operator ThreadRip() const {
		return ThreadRip::mk(thread, rip.rip);
	}
};

bool parseThreadVexRip(ThreadVexRip *out, const char *str, const char **suffix);

#endif /* !ORACLE_RIP_HPP__ */

