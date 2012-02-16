#ifndef LIBVEX_RIP_HPP__
#define LIBVEX_RIP_HPP__

#include "libvex_alloc.h"

#include <vector>

#define mk_ordering_operators(type)				\
	bool operator==(const type &other) const {		\
		return !(*this < other ||			\
			 other < *this);			\
	}							\
	bool operator!=(const type &other) const {		\
		return !(*this == other);			\
	}							\
	bool operator>=(const type &other) const {		\
		return !(*this < other);			\
	}							\
	bool operator> (const type &other) const {		\
		return (*this) >= other && (*this) != other;	\
	}							\
	bool operator<=(const type &other) const {		\
		return !(*this > other);			\
	}

class VexRip : public Named {
	char *mkName() const {
		/* Each element of the stack needs 16 chars for the
		   value itself, plus two for the 0x.  All but the
		   first need an additional two bytes for the ", "
		   separator, so that's n * 20 - 2 bytes for the body.
		   We also have enclosing {} and a nul terminator, for
		   n * 20 + 1 bytes in total. */
		char *buf = (char *)malloc(stack.size() * 20 + 1);
		char *cursor;
		unsigned idx;
		buf[0] = '{';
		cursor = buf + 1;
		for (idx = 0; idx < stack.size(); idx++)
			cursor += sprintf(cursor,
					  "%s0x%lx",
					  idx != 0 ? ", " : "",
					  stack[idx]);
		cursor[0] = '}';
		cursor[1] = 0;
		assert(cursor - buf < stack.size() * 20);
		return buf;
	}
	std::vector<unsigned long> stack;
	friend bool parseVexRip(VexRip *out, const char *str, const char **suffix);
public:

	bool operator< (const VexRip &other) const {
		for (unsigned idx = 0;
		     idx < stack.size() && idx < other.stack.size();
		     idx++) {
			if (stack[stack.size() - idx - 1] <
			    other.stack[other.stack.size() - idx - 1])
				return true;
			else if (stack[stack.size() - idx - 1] >
				 other.stack[other.stack.size() - idx - 1])
				return false;
		}
		return stack.size() < other.stack.size();
	}

	mk_ordering_operators(VexRip)

	unsigned long hash() const {
		unsigned long acc = 0;
		for (auto it = stack.rend(); it != stack.rbegin(); it++)
			acc = acc * 943231 + *it;
		return acc;
	}

	unsigned long unwrap_vexrip() const {
		return stack.back();
	}

	bool isValid() const {
		return stack.size() != 0;
	}

	static VexRip invent_vex_rip(unsigned long rip) {
		VexRip res;
		res.stack.push_back(rip);
		return res;
	}

	VexRip() {}

	VexRip operator+(long delta) const {
		VexRip r(*this);
		r.stack.back() += delta;
		return r;
	}

	void call(unsigned long target) {
		stack.push_back(target);
	}
	void jump(unsigned long target) {
		stack.back() = target;
	}
};

bool parseVexRip(VexRip *out, const char *str, const char **suffix);

#endif /* !LIBVEX_RIP_HPP__ */
