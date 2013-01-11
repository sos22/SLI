/* Simple reimplementation of std::map (roughly) which can be put in
   the GC heap. */
#ifndef MAP_H__
#define MAP_H__

#include <libvex_alloc.h>

template <typename k> unsigned long
__default_hash_function(const k &key)
{
	return key.hash();
}

template <> unsigned long __default_hash_function(const unsigned long &key);

template <typename k> bool
__default_eq_function(const k &k1, const k &k2)
{
	return k1 == k2;
}

template <typename k, typename v> void
__default_visit_function(k &, v &, HeapVisitor &)
{
}

template <typename k, typename v> void
__visit_function_heap(k &, v &h, HeapVisitor &hv)
{
	hv(h);
}

template <typename keyt, typename valuet, unsigned long hashfn(const keyt &k) = __default_hash_function<keyt>,
	  bool equalfn(const keyt &k1, const keyt &k2) = __default_eq_function<keyt>,
	  void visitvalue(keyt &, valuet &, HeapVisitor &hv) = __default_visit_function<keyt, valuet>,
	  Heap *heap = &main_heap>
class gc_map : public GarbageCollected<gc_map<keyt, valuet, hashfn, equalfn, visitvalue, heap>, heap > {
	typedef gc_map<keyt, valuet, hashfn, equalfn, visitvalue, heap> self_t;

	struct hash_entry : public GarbageCollected<self_t::hash_entry, heap> {
		struct hash_entry *next;
		keyt key;
		valuet value;

		hash_entry(struct hash_entry *_next,
			   const keyt &_key)
			: next(_next), key(_key), value()
		{
		}
		void visit(HeapVisitor &hv) {
			visitvalue(key, value, hv);
			hv(next); /* Hope it tail calls correctly... */
		}
		NAMED_CLASS
	};

	/* Everything is mutable, because we want a const indexing
	   operation which can still create new unpopulated slots. */
	mutable struct hash_entry **heads;
	mutable unsigned nr_heads;
	mutable unsigned nr_items;

	unsigned long __hash(const keyt &k) const {
		unsigned long h = hashfn(k);
		while (h >= nr_heads)
			h = (h % nr_heads) + (h / nr_heads);
		return h;
	}
	hash_entry *lookup(const keyt &k, bool create) const {
		if (!heads) {
			if (!create)
				return NULL;
			nr_heads = 128;
			heads = (hash_entry **)LibVEX_Alloc_Bytes(heap, sizeof(heads[0]) * nr_heads);
		}

		unsigned long h = __hash(k);
		hash_entry *head;
		for (head = heads[h];
		     head && !equalfn(k, head->key);
		     head = head->next)
			;
		if (head || !create)
			return head;

		head = new hash_entry(heads[h], k);
		nr_items++;
		heads[h] = head;
		return head;
	}
public:
	gc_map() {}
	gc_map(const self_t &x) {
		for (iterator it = x.begin(); it != x.end(); it++)
			(*this)[it.key()] = it.value();
	}

	valuet &operator [](const keyt &idx) { return lookup(idx, true)->value; }
	const valuet &operator [](const keyt &idx) const { return lookup(idx, true)->value; }
	valuet &get(const keyt &idx) { return lookup(idx, true)->value; }
	void set(const keyt &idx, const valuet &v) { lookup(idx, true)->value = v; }

	bool hasKey(const keyt &k) { return lookup(k, false) != NULL; }
	class iterator {
		friend class gc_map<keyt, valuet, hashfn, equalfn, visitvalue, heap>;
		unsigned bucket_idx;
		VexPtr<struct hash_entry> cursor;
		VexPtr<self_t> htable;
	public:
		iterator(const iterator &it)
			: bucket_idx(it.bucket_idx),
			  cursor(it.cursor),
			  htable(it.htable)
		{
		}
		iterator(self_t *ht)
			: bucket_idx(0),
			  cursor(NULL),
			  htable(ht)
		{
		}
		void operator=(const iterator &it) {
			bucket_idx = it.bucket_idx;
			cursor = it.cursor;
			htable = it.htable;
		}
		void operator++() {
			if (!cursor)
				return;
			cursor = cursor->next;
			while (!cursor) {
				bucket_idx++;
				if (bucket_idx == htable->nr_heads)
					return;
				cursor = htable->heads[bucket_idx];
			}
		}

		void operator++(int ) { this->operator++(); }
		bool operator!=(const iterator &i) const {
			return cursor.get() != i.cursor.get();
		}
		const keyt &key() const { assert(cursor); return cursor->key; }
		valuet &value() const { assert(cursor); return cursor->value; }
		void set_value(valuet &v) { assert(cursor); cursor->value = v; }
		void set_value(valuet v) { assert(cursor); cursor->value = v; }
	};

	iterator begin() const {
		for (unsigned x = 0; x < nr_heads; x++) {
			if (heads[x]) {
				iterator r(const_cast<self_t *>(this));
				r.bucket_idx = x;
				r.cursor = heads[x];
				return r;
			}
		}
		return end();
	}
	iterator end() const {
		iterator r(const_cast<self_t *>(this));
		r.cursor = NULL;
		r.bucket_idx = nr_heads;
		return r;
	}
	iterator erase(const iterator &it) {
		iterator rv = it;
		rv++;
		assert(it.cursor);
		hash_entry *he;
		hash_entry **pprev;
		pprev = &heads[it.bucket_idx];
		while (1) {
			he = *pprev;
			assert(he != NULL);
			if (he == it.cursor)
				break;
			pprev = &he->next;
		}
		*pprev = he->next;
		nr_items--;
		return rv;
	}

	bool empty() {
		return nr_items == 0;
	}
	void clear() {
		heads = NULL;
		nr_heads = 0;
		nr_items = 0;
	}
	size_t size() const { return nr_items; }
	void visit(HeapVisitor &hv) {
		hv(heads);
		for (unsigned x = 0; x < nr_heads; x++)
			hv(heads[x]);
	}
	NAMED_CLASS
};

/* C++ was apparently designed by morons.  Why can't you have a
   template typedef?  Nobody seems to know.  Work around this glaring
   omission using a stupid stub class; ugly as sin, but slightly less
   hideous than the alternative. */
template <typename k, typename v, Heap *heap = &main_heap>
class gc_heap_map {
public:
	typedef gc_map<k, v *, __default_hash_function<k>,
		       __default_eq_function<k>, __visit_function_heap<k, v *>, heap > type;
};

#endif /* !MAP_H__ */
