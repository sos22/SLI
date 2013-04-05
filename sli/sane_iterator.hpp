#ifndef SANE_ITERATOR_HPP__
#define SANE_ITERATOR_HPP__

template <typename t>
class _saneIterator {
	t cursor;
	t end;
public:
	typedef typename t::value_type value_type;
	_saneIterator(const t &begin, const t &_end)
		: cursor(begin), end(_end)
	{}
	bool finished() const {
		return cursor == end;
	}
	void operator++(int) {
		cursor++;
	}
	typename t::value_type &operator *() {
		return *cursor;
	}
};
template <typename t> _saneIterator<t>
saneIterator(const t &begin, const t &end)
{
	return _saneIterator<t>(begin, end);
}
template <typename k, typename v> _saneIterator<typename std::map<k, v>::iterator>
saneIterator(std::map<k, v> &m)
{
	return saneIterator(m.begin(), m.end());
}
template <typename k> _saneIterator<typename std::vector<k>::iterator>
saneIterator(std::vector<k> &m)
{
	return saneIterator(m.begin(), m.end());
}

template <typename underlying_it1, typename underlying_it2>
class concatIterator {
	enum { ph_1, ph_2, ph_finished } phase;
	underlying_it1 cursor1;
	underlying_it2 cursor2;
public:
	concatIterator(const underlying_it1 &_begin1,
		       const underlying_it2 &_begin2)
		: phase(ph_1),
		  cursor1(_begin1),
		  cursor2(_begin2)
	{
		if (cursor1.finished()) {
			phase = ph_2;
			if (cursor2.finished())
				phase = ph_finished;
		}
	}
	bool finished() const {
		return phase == ph_finished;
	}
	void operator++(int) {
		switch (phase) {
		case ph_1:
			cursor1++;
			if (cursor1.finished()) {
				phase = ph_2;
				if (cursor2.finished())
					phase = ph_finished;
			}
			break;
		case ph_2:
			cursor2++;
			if (cursor2.finished())
				phase = ph_finished;
			break;
		case ph_finished:
			abort();
		}
	}
	const typename underlying_it1::value_type &operator*() {
		switch (phase) {
		case ph_1:
			return *cursor1;
		case ph_2:
			return *cursor2;
		case ph_finished:
			abort();
		}
		abort();
	}
	const typename underlying_it1::value_type *operator->() {
		switch (phase) {
		case ph_1:
			return &*cursor1;
		case ph_2:
			return &*cursor2;
		case ph_finished:
			abort();
		}
		abort();
	}
};
template <typename a, typename b> concatIterator<a, b>
concatIterators(const a &a1, const b &b1)
{
	return concatIterator<a, b>(a1, b1);
}

template <typename t>
class ptrIterator {
	int nr_ptrs;
	int cursor;
	t **content;
public:
	ptrIterator(t *a, ...)
		: cursor(0), content(NULL)
	{
		if (a == NULL) {
			nr_ptrs = 0;
			return;
		}
		nr_ptrs = 1;
		va_list args;
		va_start(args, a);
		while (1) {
			t *b = va_arg(args, t *);
			if (!b)
				break;
			nr_ptrs++;
		}
		va_end(args);

		content = (t **)malloc(sizeof(t *) * nr_ptrs);
		content[0] = a;
		va_start(args, a);
		int i = 1;
		while (1) {
			t *b = va_arg(args, t*);
			if (!b)
				break;
			content[i] = b;
			i++;
		}
		assert(i == nr_ptrs);
	}
	~ptrIterator()
	{
		free(content);
	}
	ptrIterator(const ptrIterator &other)
		: nr_ptrs(other.nr_ptrs),
		  cursor(other.cursor)
	{
		content = (t **)malloc(sizeof(t *) * nr_ptrs);
		memcpy(content, other.content, sizeof(t *) * nr_ptrs);
	}
	void operator=(const ptrIterator &other)
	{
		nr_ptrs = other.nr_ptrs;
		cursor = other.cursor;
		if (content)
			free(content);
		content = (t **)malloc(sizeof(t *) * nr_ptrs);
		memcpy(content, other.content, sizeof(t *) * nr_ptrs);
	}
	bool finished() const {
		return cursor == nr_ptrs;
	}
	void operator++(int) {
		assert(!finished());
		cursor++;
	}
	t *&operator *() {
		return content[cursor];
	}
};

#endif /* !SANE_ITERATOR_HPP__ */
