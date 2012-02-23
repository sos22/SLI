#ifndef LIBVEX_RIP_HPP__
#define LIBVEX_RIP_HPP__

#include <err.h>

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

class VexRip;

bool parseVexRip(VexRip *out, const char *str, const char **suffix);

class VexRip : public Named {
	friend bool parseVexRip(VexRip *out, const char *str, const char **suffix);
	friend class __types_db_instr_iterator;

	char *mkName() const {
		/* Each element of the stack needs 16 chars for the
		   value itself, plus two for the 0x.  All but the
		   first need an additional two bytes for the ", "
		   separator, so that's n * 20 - 2 bytes for the body.
		   We also have enclosing {} and a nul terminator, for
		   n * 20 + 1 bytes in total.  An exception: if the
		   stack is empty, we don't get the two bytes for ",
		   ", so have to add it back on again.  Make things
		   easy by just always adding it in. */
		char *buf = (char *)malloc(stack.size() * 20 + 3);
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
		assert(cursor - buf < (int)stack.size() * 20 + 2);
		return buf;
	}
	std::vector<unsigned long> stack;
	void changed() { clearName(); }
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
		for (auto it = stack.begin(); it != stack.end(); it++)
			acc = acc * 943231 + *it;
		return acc;
	}

	unsigned long unwrap_vexrip() const {
		return stack.back();
	}

	bool isValid() const {
		return stack.size() != 0;
	}

	const std::vector<unsigned long> &getStack() const {
		return stack;
	}
	static VexRip invent_vex_rip(unsigned long rip) {
		VexRip res;
		res.stack.push_back(rip);
		return res;
	}

	static VexRip from_string(const char *str) {
		VexRip res;
		const char *succ;
		if (!parseVexRip(&res, str, &succ) ||
		    *succ)
			errx(1, "cannot parse %s as vex rip", str);
		return res;
	}
	VexRip() {}
	VexRip(const std::vector<unsigned long> &content)
		: stack(content)
	{}

	VexRip operator+(long delta) const {
		VexRip r(*this);
		r.stack.back() += delta;
		clearName();
		return r;
	}

	void call(unsigned long target) {
		stack.push_back(target);
		clearName();
	}
	void jump(unsigned long target) {
		stack.back() = target;
		clearName();
	}
	void rtrn() {
		stack.pop_back();
		clearName();
	}
	bool on_stack(unsigned long rip) const {
		for (auto it = stack.begin(); it != stack.end(); it++)
			if (*it == rip)
				return true;
		return false;
	}
};

#endif /* !LIBVEX_RIP_HPP__ */
