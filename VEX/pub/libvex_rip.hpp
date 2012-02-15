#ifndef LIBVEX_RIP_HPP__
#define LIBVEX_RIP_HPP__

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
	char *mkName() const { return my_asprintf("%lx", rip); }
	explicit VexRip(unsigned long _rip)
		: rip(_rip), valid(true)
	{}
	unsigned long rip;
	bool valid;
	friend bool parseVexRip(VexRip *out, const char *str, const char **suffix);
public:

	bool operator< (const VexRip &other) const {
		return rip < other.rip;
	}

	mk_ordering_operators(VexRip)

	unsigned long hash() const {
		return rip;
	}

	unsigned long unwrap_vexrip() const {
		return rip;
	}

	bool isValid() const {
		return valid;
	}

	static VexRip invent_vex_rip(unsigned long rip) {
		return VexRip(rip);
	}

	VexRip() : valid(false) {}
};

bool parseVexRip(VexRip *out, const char *str, const char **suffix);

#endif /* !LIBVEX_RIP_HPP__ */
