#ifndef ORACLE_RIP_HPP__
#define ORACLE_RIP_HPP__

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

class OracleRip : public Named {
	char *mkName() const { return my_asprintf("%lx", rip); }
public:
	unsigned long rip;

	bool operator< (const OracleRip &other) const {
		return rip < other.rip;
	}

	mk_ordering_operators(OracleRip)

	unsigned long hash() const {
		return rip;
	}

	OracleRip(unsigned long _rip)
		: rip(_rip)
	{}
	OracleRip() {}
};

class ThreadOracleRip : public Named {
	char *mkName() const { return my_asprintf("%d:%s", thread, rip.name()); }
public:
	unsigned thread;
	OracleRip rip;

	bool operator< (const ThreadOracleRip &other) const {
		if (thread < other.thread)
			return true;
		else if (thread > other.thread)
			return false;
		else
			return rip < other.rip;
	}
	mk_ordering_operators(ThreadOracleRip)

	ThreadOracleRip(unsigned _thread, const OracleRip &_rip)
		: thread(_thread), rip(_rip)
	{}

	ThreadOracleRip() {}
	operator ThreadRip() const {
		return ThreadRip::mk(thread, rip.rip);
	}
};

bool parseThreadOracleRip(ThreadOracleRip *out, const char *str, const char **suffix);
bool parseOracleRip(OracleRip *out, const char *str, const char **suffix);

#endif /* !ORACLE_RIP_HPP__ */

