/* Simple thing for building maps from ranges of unsigned longs to
 * <something>, where the something is GC-allocated and it's likely
 * that there will only be a small number of distinct ranges.  The
 * ranges cannot overlap (if you try to create two overlapping ranges
 * which map to the smae thing then we merge the ranges; if they map
 * to different things then we abort())
 */
#ifndef RANGE_TREE_H__
#define RANGE_TREE_H__

#include <vector>

template <typename key, Heap *heap, typename comparator>
class RawRangeTree : public GarbageCollected<RawRangeTree<key, heap, comparator>, heap> {
	bool performSearch(const key &, int &, int &);
	static bool key_lt(const key &a, const key &b) {
		return comparator::lt(a, b);
	}
	static bool key_ge(const key &a, const key &b) {
		return comparator::ge(a, b);
	}
	static bool key_eq(const key &a, const key &b) {
		return comparator::eq(a, b);
	}
	static bool key_gt(const key &a, const key &b) {
		return comparator::gt(a, b);
	}
public:
	struct entry {
		key start;
		key end1;
		void *value;
		entry(const key &s, const key &e, void *v)
			: start(s), end1(e), value(v)
		{
		}
		entry() : value(NULL) {}
	};
	std::vector<entry> content;
	class iterator {
	private:
		RawRangeTree<key, heap, comparator> *t;
		entry inner;
	public:
		int idx;
		entry *operator->() { return &inner; }
		void operator++(int) { idx++; updateInner(); }
		bool operator!=(const iterator &o) const { return idx != o.idx; }
		void updateInner();

		iterator(RawRangeTree<key, heap, comparator> *_t, int _idx)
			: t(_t), idx(_idx)
		{
			updateInner();
		}
	};

	/* Look up @v in the mapping, and either return the value
	   associated with it or return NULL. */
	void *get(const key &v);
	/* Set the mapping for [start,end1) (i.e. including start,
	   excluding end1) to value. */
	void set(const key &start, const key &end1, void *value);
	/* Purge all of the ranges which map to a particular value. */
	void purgeByValue(void *v);

	iterator begin() { return iterator(this, 0); }
	iterator end() { return iterator(this, content.size()); }
	iterator erase(iterator it) {
		content.erase(content.begin() + it.idx);
		it.updateInner();
		return it;
	}

	void visit(HeapVisitor &hv);
	NAMED_CLASS;
};

/* Simple facade around RawRangeTree to get better type checking. */
template <typename key, typename t, Heap *heap, typename comparator>
class RangeTree : public GarbageCollected<RangeTree<key, t, heap, comparator>, heap> {
	RangeTree(const RangeTree &); /* DNI */
public:
	RawRangeTree<key, heap, comparator> *content;

	class iterator {
		void updateUnderlying(void) {
			content.value = (t *)underlying->value;
			content.start = underlying->start;
			content.end1 = underlying->end1;
		}
	public:
		iterator(class RawRangeTree<key, heap, comparator>::iterator u)
			: underlying(u)
		{
			updateUnderlying();
		}
		class _inner {
		public:
			t *value;
			key start;
			key end1;
		};
		_inner content;
		class RawRangeTree<key, heap, comparator>::iterator underlying;
		bool operator!=(const iterator &o) { return underlying != o.underlying; }
		void operator++(int) {
			underlying++;
			updateUnderlying();
		}
		_inner *operator->() { return &content; }
	};

	RangeTree() : content(new RawRangeTree<key, heap, comparator>()) {}
	t *get(const key &k) { return (t *)content->get(k); }
	void set(const key &start, const key &end1, t *k) { content->set(start, end1, k); }

	void purgeByValue(t *x) { content->purgeByValue(x); }

	iterator begin() { return iterator(content->begin()); }
	iterator end() { return iterator(content->end()); }
	iterator erase(iterator &it) { return iterator(content->erase(it.underlying)); }

	void visit(HeapVisitor &hv) { hv(content); }
	NAMED_CLASS
};

/* Variant which provides a simple set of ranges, rather than a map
   from ranges to values.  Everything defaults to not present. */
template <typename key, Heap *heap, typename comparator>
class RangeSet : public GarbageCollected<RangeSet<key, heap, comparator>, heap> {
	RawRangeTree<key, heap, comparator> *content;
	class pe : public GarbageCollected<pe, heap> {
	public:
		void visit(HeapVisitor &hv) {}
		NAMED_CLASS
	};
	static VexPtr<pe, heap> presentEntry;
public:
	class iterator {
		void updateInner() {
			inner.start = it->start;
			inner.end1 = it->end1;
		}
	public:
		class _inner {
		public:
			key start;
			key end1;
		};
		_inner inner;
		class RawRangeTree<key, heap, comparator>::iterator it;
		_inner *operator->() { return &inner; }
		void operator++(int) { it++; updateInner(); }
		bool operator!=(const iterator &i) { return it != i.it; }
		iterator(class RawRangeTree<key, heap, comparator>::iterator _it)
			: it(_it)
		{ updateInner(); }
	};
	RangeSet() : content(new RawRangeTree<key, heap, comparator>()) {}
	void visit(HeapVisitor &hv) { hv(content); }
	bool test(const key &x) { return content->get(x) == presentEntry; }
	void set(const key &start, const key &end1) {
		content->set(start, end1, presentEntry);
	}

	iterator begin() { return iterator(content->begin()); }
	iterator end() { return iterator(content->end()); }

	NAMED_CLASS
};

template <typename key, Heap *heap, typename comparator> VexPtr<class RangeSet<key, heap, comparator>::pe, heap>
RangeSet<key, heap, comparator>::presentEntry(new RangeSet<key, heap, comparator>::pe);

template <typename key, Heap *heap, typename comparator> bool
RawRangeTree<key, heap, comparator>::performSearch(const key &v, int &low, int &high)
{
	low = 0;
	high = content.size() - 1;
	if (content.size() == 0 ||
	    key_lt(v, content[low].start) ||
	    key_ge(v, content[high].end1))
		return false;
	/* We now maintain the invariant that v >= content[low].start
	   and v < content[high].end1. */
	while (high > low + 1) {
		int probe = (high + low) / 2;
		if (key_ge(v, content[probe].start))
			low = probe;
		if (key_lt(v, content[probe].end1))
			high = probe;
		assert(key_ge(v, content[low].start) && key_lt(v, content[high].end1));
	}
	assert(key_ge(v, content[low].start) && key_lt(v, content[high].end1));
	return true;
}

template <typename key, Heap *heap, typename comparator> void *
RawRangeTree<key, heap, comparator>::get(const key &v)
{
	int low;
	int high;
	if (!performSearch(v, low, high))
		return NULL;
	assert(low == high || low + 1 == high);
	assert(key_ge(v, content[low].start) && key_lt(v, content[high].end1));
	if (low == high) {
		return content[low].value;
	} else {
		assert(high == low + 1);
		if (key_lt(v, content[low].end1))
			return content[low].value;
		if (key_ge(v, content[high].start))
			return content[high].value;
		return NULL;
	}
}

template <typename key, Heap *heap, typename comparator> void
RawRangeTree<key, heap, comparator>::set(const key &start, const key &end1, void *value)
{
	int low, high;
	assert(key_ge(end1, start));
	if (key_eq(end1, start))
		return;
	if (content.size() == 0) {
		content.push_back(entry(start, end1, value));
		return;
	}
	if (key_lt(end1, content[0].start) ||
	    (key_eq(end1, content[0].start) &&
	     value != content[0].value)) {
		content.insert(content.begin(),
			       entry(start, end1, value));
		return;
	}

	if (key_eq(end1, content[0].start)) {
		assert(value == content[0].value);
		content[0].start = start;
		return;
	}

	if (key_ge(start, content[content.size()-1].end1)) {
		if (key_eq(start, content[content.size()-1].end1) &&
		    value == content[content.size()-1].value) {
			content[content.size()-1].end1 = end1;
		} else {
			content.push_back(entry(start, end1, value));
		}
		return;
	}

	/* Find the starting point of the new range in the current
	 * list. */
	bool t = performSearch(start, low, high);
	assert(t);
	if (high == low + 1) {
		if (key_lt(start, content[low].end1))
			high = low;
		if (key_ge(start, content[high].start))
			low = high;
	}
	if (high == low) {
		/* Start is in the middle of this range.  Check for
		   compatibility with this range and then considering
		   splitting. */
		assert(value == content[low].value);
		if (key_gt(end1, content[low].end1))
			set(content[low].end1, end1, value);
		return;
	}
	assert(high == low + 1);

	/* The start of this range is in the gap between two other
	   ranges. */
	if (key_gt(end1, content[high].start)) {
		/* But the end isn't, so split the range and try
		 * again. */
		set(start, content[high].start, value);
		set(content[high].start, end1, value);
		return;
	}

	/* Do we want to merge with an existing range? */
	bool mergeDown =
		value == content[low].value &&
		key_eq(start, content[low].end1);
	bool mergeUp =
		value == content[high].value &&
		key_eq(end1, content[high].start);
	if (mergeDown && mergeUp) {
		/* Merge with both.  Extend low to subsume high, and
		   then nuke high. */
		content[low].end1 = content[high].end1;
		content.erase(content.begin() + high);
	} else if (mergeDown) {
		content[low].end1 = end1;
	} else if (mergeUp) {
		content[high].start = start;
	} else {
		/* No merge possible -> insert a completely new
		 * range. */
		content.insert(content.begin() + high,
			       entry(start, end1, value));
	}
}

template <typename key, Heap *heap, typename comparator> void
RawRangeTree<key, heap, comparator>::purgeByValue(void *v)
{
	for (auto it = content.begin();
	     it != content.end();
		) {
		if (it->value == v)
			it = content.erase(it);
		else
			it++;
	}
}

template <typename key, Heap *heap, typename comparator> void
RawRangeTree<key, heap, comparator>::iterator::updateInner()
{
	if (idx >= (int)t->content.size())
		return;
	else
		inner = t->content[idx];
}

template <typename key, Heap *heap, typename comparator> void
RawRangeTree<key, heap, comparator>::visit(HeapVisitor &hv)
{
	for (auto it = content.begin();
	     it != content.end();
	     it++)
		hv(it->value);
}

#endif /* !RANGE_TREE_H__ */
