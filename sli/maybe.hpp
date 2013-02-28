/* Simple Maybe type. */
#ifndef MAYBE_HPP__
#define MAYBE_HPP__

template <typename t> class Maybe {
public:
	Maybe(const t &x)
		: valid(true), content(x)
	{}
	Maybe()
		: valid(false), content()
	{}
	bool valid;
	t content;
	static Maybe just(const t &x)
	{ return Maybe(x); }
	static Maybe nothing()
	{ return Maybe(); }	

	bool operator==(const Maybe<t> &o) const {
		if (!valid && !o.valid) {
			return true;
		}
		if (!valid || !o.valid) {
			return false;
		}
		return content == o.content;
	}
	bool operator!=(const Maybe<t> &o) const {
		return !(*this == o);
	}
	bool operator<(const Maybe<t> &o) const {
		if (valid && o.valid)
			return content < o.content;
		else
			return valid < o.valid;
	}

	/* Note that we do *not* lift &&, ||, and ?:, because there's
	   no way of getting the right short circuit and laziness
	   properties, and it just gets horribly confusing. */
#define lift_operator(op)					\
	Maybe<t> operator op (const Maybe<t> &o) const {	\
		if (!valid || !o.valid)				\
			return nothing();			\
		return just(content op o.content);		\
	}
	lift_operator(&)
	lift_operator(|)
	lift_operator(^)
	lift_operator(+)
	lift_operator(-)
	lift_operator(*)
	lift_operator(/)
	lift_operator(<<)
	lift_operator(>>)
#undef lift_operator
};

#endif /* !MAYBE_HPP__ */
