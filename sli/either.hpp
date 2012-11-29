#ifndef EITHER_HPP__
#define EITHER_HPP__

template <typename a, typename b> struct either {
	union {
		unsigned char _left[sizeof(a)];
		unsigned char _right[sizeof(b)];
	} content;
	either() {}
public:
	bool isLeft;
	either(const a &what)
		: isLeft(true)
	{
		new (&content) a(what);
	}
	either(const b &what)
		: isLeft(false)
	{
		new (&content) b(what);
	}
	static either<a, b> Left(const a &what)
	{
		either<a, b> res;
		res.isLeft = true;
		new (&res.content) a(what);
		return res;
	}
	static either<a, b> Right(const b &what)
	{
		either<a, b> res;
		res.isLeft = false;
		new (&res.content) b(what);
		return res;
	}
	either(const either<a, b> &o)
		: isLeft(o.isLeft)
	{
		if (isLeft)
			new (&content) a(o.left());
		else
			new (&content) b(o.right());
	}
	void operator=(const either<a, b> &o)
	{
		if (isLeft && o.isLeft) {
			left() = o.left();
		} else if (!isLeft && !o.isLeft) {
			right() = o.right();
		} else if (isLeft) {
			left().~a();
			isLeft = false;
			new (&content) b(o.right());
		} else {
			right().~b();
			isLeft = true;
			new (&content) a(o.left());
		}
	}
	const a &left() const
	{
		return *(const a *)&content;
	}
	a &left()
	{
		return *(a *)&content;
	}
	const b &right() const
	{
		return *(const b *)&content;
	}
	b &right()
	{
		return *(b *)&content;
	}
	~either()
	{
		if (isLeft)
			left().~a();
		else
			right().~b();
	}
};

#endif /* !EITHER_HPP__ */
