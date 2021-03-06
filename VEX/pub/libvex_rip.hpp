#ifndef LIBVEX_RIP_HPP__
#define LIBVEX_RIP_HPP__

#include <err.h>

#include "libvex_alloc.h"

#include <vector>

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
	void changed() { clearName(); }
public:
	std::vector<unsigned long> stack;
	bool fullCompareLt(const VexRip &other) const {
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
	bool fullCompareGt(const VexRip &other) const {
		return other.fullCompareLt(*this);
	}
	bool fullCompareGe(const VexRip &other) const {
		return !fullCompareLt(other);
	}
	bool fullCompareEq(const VexRip &other) const {
		return stack == other.stack;
	}
	bool fullCompareNe(const VexRip &other) const {
		return stack != other.stack;
	}

#define mk_wrapper(suffix)						\
	static bool FullCompare ## suffix (const VexRip &a,		\
					   const VexRip &b) {		\
		return a.fullCompare ## suffix (b);			\
	}
	mk_wrapper(Lt);
	mk_wrapper(Gt);
	mk_wrapper(Ge);
	mk_wrapper(Eq);
	mk_wrapper(Ne);
#undef mk_wrapper

	class FullCompare {
	public:
		bool operator()(const VexRip &a, const VexRip &b) const {
			return a.fullCompareLt(b);
		}
#define mk_wrapper(s1, s2)						\
		static bool s1(const VexRip &a, const VexRip &b) {	\
			return a.fullCompare ## s2(b);			\
		}
		mk_wrapper(lt, Lt);
		mk_wrapper(gt, Gt);
		mk_wrapper(ge, Ge);
		mk_wrapper(eq, Eq);
		mk_wrapper(ne, Ne);
#undef mk_wrapper
	};

#define mk_wrapper(op, suffix)				\
	bool operator op(const VexRip &o) const {	\
		return fullCompare ## suffix (o);	\
	}
	mk_wrapper(<, Lt)
	mk_wrapper(>, Gt)
	mk_wrapper(>=, Ge)
	mk_wrapper(==, Eq)
	mk_wrapper(!=, Ne)
#undef mk_wrapper
	unsigned long hash() const {
		unsigned long acc = 0;
		for (auto it = stack.begin(); it != stack.end(); it++)
			acc = acc * 943231 + *it;
		return acc;
	}

	void get_binrep(void **out, int *out_size) const {
		*out_size = sizeof(unsigned long) * stack.size();
		unsigned long *buf = (unsigned long *)malloc(*out_size);
		for (unsigned x = 0; x < stack.size(); x++)
			buf[x] = stack[x];
		*out = buf;
	}
	static VexRip from_binrep(const void *_inp, int inp_size) {
		const unsigned long *inp = (const unsigned long *)_inp;
		VexRip res;
		res.stack.resize(inp_size / sizeof(unsigned long));
		for (unsigned x = 0; x < res.stack.size(); x++)
			res.stack[x] = inp[x];
		return res;
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
	std::vector<unsigned long> &getStack() {
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
		r.clearName();
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

	void prepend(unsigned long what) {
		stack.insert(stack.begin(), what);
		clearName();
	}

	bool isPrefix(const VexRip &vr) const {
		if (stack.size() >= vr.stack.size())
			return false;
		for (unsigned x = 0; x < stack.size(); x++)
			if (stack[x] != vr.stack[x])
				return false;
		return true;
	}

	void sanity_check() const {
	}

	/* Check whether this is a strict truncation of @vr (i.e.  vr
	   with some elements removed from the top) */
	bool isTruncationOf(const VexRip &vr) const {
		if (stack.size() >= vr.stack.size())
			return false;
		for (unsigned x = 0; x < stack.size(); x++)
			if (stack[stack.size() - x - 1] !=
			    vr.stack[vr.stack.size() - x - 1])
				return false;
		return true;
	}
};

#endif /* !LIBVEX_RIP_HPP__ */
