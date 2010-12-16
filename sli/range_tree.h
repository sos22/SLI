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

class RawRangeTree : public GarbageCollected<RawRangeTree> {
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
		RawRangeTree *t;
		entry inner;
	public:
		int idx;
		entry *operator->() { return &inner; }
		void operator++(int) { idx++; updateInner(); }
		bool operator!=(const iterator &o) const { return idx != o.idx; }
		void updateInner();

		iterator(RawRangeTree *_t, int _idx)
			: t(_t), idx(_idx)
		{
			updateInner();
		}
	};

	RawRangeTree();

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
template <typename t>
class RangeTree : public GarbageCollected<RangeTree<t> > {
	RangeTree(const RangeTree &); /* DNI */
public:
	RawRangeTree *content;

	class iterator {
		void updateUnderlying(void) {
			content.value = (t *)underlying->value;
			content.start = underlying->start;
			content.end1 = underlying->end1;
		}
	public:
		iterator(RawRangeTree::iterator u)
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
		RawRangeTree::iterator underlying;
		bool operator!=(const iterator &o) { return underlying != o.underlying; }
		void operator++(int) {
			underlying++;
			updateUnderlying();
		}
		_inner *operator->() { return &content; }
	};

	RangeTree() : content(new RawRangeTree()) {}
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
class RangeSet : public GarbageCollected<RangeSet> {
	RawRangeTree *content;
	static void *const presentEntry;
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
		RawRangeTree::iterator it;
		_inner *operator->() { return &inner; }
		void operator++(int) { it++; updateInner(); }
		bool operator!=(const iterator &i) { return it != i.it; }
		iterator(RawRangeTree::iterator _it)
			: it(_it)
		{ updateInner(); }
	};
	RangeSet() : content(new RawRangeTree()) {}
	void visit(HeapVisitor &hv) { hv(content); }
	bool test(unsigned long x) { return content->get(x) == presentEntry; }
	void set(unsigned long start, unsigned long end1) {
		content->set(start, end1, presentEntry);
	}

	iterator begin() { return iterator(content->begin()); }
	iterator end() { return iterator(content->end()); }

	NAMED_CLASS
};

#endif /* !RANGE_TREE_H__ */
