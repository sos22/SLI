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

template <Heap *heap>
class RawRangeTree : public GarbageCollected<RawRangeTree<heap>, heap> {
	bool performSearch(unsigned long, int &, int &);
public:
	struct entry {
		unsigned long start;
		unsigned long end1;
		void *value;
		entry(unsigned long s, unsigned long e, void *v)
			: start(s), end1(e), value(v)
		{
		}
		entry() : start(0), end1(0), value(NULL) {}
	};
	std::vector<entry> content;
	class iterator {
	private:
		RawRangeTree<heap> *t;
		entry inner;
	public:
		int idx;
		entry *operator->() { return &inner; }
		void operator++(int) { idx++; updateInner(); }
		bool operator!=(const iterator &o) const { return idx != o.idx; }
		void updateInner();

		iterator(RawRangeTree<heap> *_t, int _idx)
			: t(_t), idx(_idx)
		{
			updateInner();
		}
	};

	/* Look up @v in the mapping, and either return the value
	   associated with it or return NULL. */
	void *get(unsigned long v);
	/* Set the mapping for [start,end1) (i.e. including start,
	   excluding end1) to value. */
	void set(unsigned long start, unsigned long end1, void *value);
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
template <typename t, Heap *heap>
class RangeTree : public GarbageCollected<RangeTree<t,heap>, heap> {
	RangeTree(const RangeTree &); /* DNI */
public:
	RawRangeTree<heap> *content;

	class iterator {
		void updateUnderlying(void) {
			content.value = (t *)underlying->value;
			content.start = underlying->start;
			content.end1 = underlying->end1;
		}
	public:
		iterator(class RawRangeTree<heap>::iterator u)
			: underlying(u)
		{
			updateUnderlying();
		}
		class _inner {
		public:
			t *value;
			unsigned long start;
			unsigned long end1;
		};
		_inner content;
		class RawRangeTree<heap>::iterator underlying;
		bool operator!=(const iterator &o) { return underlying != o.underlying; }
		void operator++(int) {
			underlying++;
			updateUnderlying();
		}
		_inner *operator->() { return &content; }
	};

	RangeTree() : content(new RawRangeTree<heap>()) {}
	t *get(unsigned long k) { return (t *)content->get(k); }
	void set(unsigned long start, unsigned long end1, t *k) { content->set(start, end1, k); }

	void purgeByValue(t *x) { content->purgeByValue(x); }

	iterator begin() { return iterator(content->begin()); }
	iterator end() { return iterator(content->end()); }
	iterator erase(iterator &it) { return iterator(content->erase(it.underlying)); }

	void visit(HeapVisitor &hv) { hv(content); }
	NAMED_CLASS
};

/* Variant which provides a simple set of ranges, rather than a map
   from ranges to values.  Everything defaults to not present. */
template <Heap *heap>
class RangeSet : public GarbageCollected<RangeSet<heap>, heap> {
	RawRangeTree<heap> *content;
	class pe : public GarbageCollected<pe, heap> {
	public:
		void visit(HeapVisitor &hv) {}
		NAMED_CLASS
	};
	static pe *const presentEntry;
public:
	class iterator {
		void updateInner() {
			inner.start = it->start;
			inner.end1 = it->end1;
		}
	public:
		class _inner {
		public:
			unsigned long start;
			unsigned long end1;
		};
		_inner inner;
		class RawRangeTree<heap>::iterator it;
		_inner *operator->() { return &inner; }
		void operator++(int) { it++; updateInner(); }
		bool operator!=(const iterator &i) { return it != i.it; }
		iterator(class RawRangeTree<heap>::iterator _it)
			: it(_it)
		{ updateInner(); }
	};
	RangeSet() : content(new RawRangeTree<heap>()) {}
	void visit(HeapVisitor &hv) { hv(content); }
	bool test(unsigned long x) { return content->get(x) == presentEntry; }
	void set(unsigned long start, unsigned long end1) {
		content->set(start, end1, presentEntry);
	}

	iterator begin() { return iterator(content->begin()); }
	iterator end() { return iterator(content->end()); }

	NAMED_CLASS
};

template <Heap *heap> class RangeSet<heap>::pe *const
RangeSet<heap>::presentEntry(new RangeSet<heap>::pe);

template <Heap *heap> bool
RawRangeTree<heap>::performSearch(unsigned long v, int &low, int &high)
{
	low = 0;
	high = content.size() - 1;
	if (content.size() == 0 ||
	    v < content[low].start ||
	    v >= content[high].end1)
		return false;
	/* We now maintain the invariant that v >= content[low].start
	   and v < content[high].end1. */
	while (high > low + 1) {
		int probe = (high + low) / 2;
		if (v >= content[probe].start)
			low = probe;
		if (v < content[probe].end1)
			high = probe;
		assert(v >= content[low].start && v < content[high].end1);
	}
	assert(v >= content[low].start && v < content[high].end1);
	return true;
}

template <Heap *heap> void *
RawRangeTree<heap>::get(unsigned long v)
{
	int low;
	int high;
	if (!performSearch(v, low, high))
		return NULL;
	assert(low == high || low + 1 == high);
	assert(v >= content[low].start && v < content[high].end1);
	if (low == high) {
		return content[low].value;
	} else {
		assert(high == low + 1);
		if (v < content[low].end1)
			return content[low].value;
		if (v >= content[high].start)
			return content[high].value;
		return NULL;
	}
}

template <Heap *heap> void
RawRangeTree<heap>::set(unsigned long start, unsigned long end1, void *value)
{
	int low, high;
	assert(end1 >= start);
	if (end1 == start)
		return;
	if (content.size() == 0) {
		content.push_back(entry(start, end1, value));
		return;
	}
	if (end1 < content[0].start ||
	    (end1 == content[0].start &&
	     value != content[0].value)) {
		content.insert(content.begin(),
			       entry(start, end1, value));
		return;
	}

	if (end1 == content[0].start) {
		assert(value == content[0].value);
		content[0].start = start;
		return;
	}

	if (start >= content[content.size()-1].end1) {
		if (start == content[content.size()-1].end1 &&
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
		if (start < content[low].end1)
			high = low;
		if (start >= content[high].start)
			low = high;
	}
	if (high == low) {
		/* Start is in the middle of this range.  Check for
		   compatibility with this range and then considering
		   splitting. */
		assert(value == content[low].value);
		if (end1 > content[low].end1)
			set(content[low].end1, end1, value);
		return;
	}
	assert(high == low + 1);

	/* The start of this range is in the gap between two other
	   ranges. */
	if (end1 > content[high].start) {
		/* But the end isn't, so split the range and try
		 * again. */
		set(start, content[high].start, value);
		set(content[high].start, end1, value);
		return;
	}

	/* Do we want to merge with an existing range? */
	bool mergeDown =
		value == content[low].value &&
		start == content[low].end1;
	bool mergeUp =
		value == content[high].value &&
		end1  == content[high].start;
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

template <Heap *heap> void
RawRangeTree<heap>::purgeByValue(void *v)
{
	for (class std::vector<entry>::iterator it = content.begin();
	     it != content.end();
		) {
		if (it->value == v)
			it = content.erase(it);
		else
			it++;
	}
}

template <Heap *heap> void
RawRangeTree<heap>::iterator::updateInner()
{
	if (idx >= (int)t->content.size())
		return;
	else
		inner = t->content[idx];
}

template <Heap *heap> void
RawRangeTree<heap>::visit(HeapVisitor &hv)
{
	for (class std::vector<entry>::iterator it = content.begin();
	     it != content.end();
	     it++)
		hv(it->value);
}

#endif /* !RANGE_TREE_H__ */
