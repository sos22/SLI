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

template <typename v> void
__default_visit_function(v &, HeapVisitor &)
{
}

template <typename v> void
__visit_function_heap(v &h, HeapVisitor &hv)
{
	hv(h);
}

template <typename keyt, typename valuet, unsigned long hashfn(const keyt &k) = __default_hash_function<keyt>,
	  bool equalfn(const keyt &k1, const keyt &k2) = __default_eq_function<keyt>,
	  void visitvalue(valuet &, HeapVisitor &hv) = __default_visit_function<valuet> >
class gc_map : public GarbageCollected<gc_map<keyt, valuet, hashfn, equalfn, visitvalue> > {
	typedef gc_map<keyt, valuet, hashfn, equalfn, visitvalue> self_t;

	struct hash_entry : public GarbageCollected<self_t::hash_entry> {
		struct hash_entry *next;
		keyt key;
		valuet value;

		void visit(HeapVisitor &hv) {
			visitvalue(value, hv);
			hv(next); /* Hope it tail calls correctly... */
		}
		void destruct() {
			this->~hash_entry();
		}
		NAMED_CLASS
	};

	/* Everything is mutable, because we want a const indexing
	   operation which can still create new unpopulated slots. */
	mutable struct hash_entry **heads;
	mutable unsigned nr_heads;
	mutable unsigned nr_items;

	hash_entry *lookup(const keyt &k, bool create) const {
		if (!heads) {
			if (!create)
				return NULL;
			nr_heads = 128;
			heads = (hash_entry **)LibVEX_Alloc_Bytes(sizeof(heads[0]) * nr_heads);
		}

		unsigned long h = hashfn(k);
		h %= nr_heads;
		hash_entry *head;
		for (head = heads[h];
		     head && !equalfn(k, head->key);
		     head = head->next)
			;
		if (head || !create)
			return head;

		head = new hash_entry();
		nr_items++;
		head->next = heads[h];
		head->key = k;
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
		friend class gc_map<keyt, valuet, hashfn, equalfn, visitvalue>;
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

		void operator++(int ign) { this->operator++(); }
		bool operator!=(const iterator &i) const {
			return cursor.get() != i.cursor.get();
		}
		const keyt &key() const { assert(cursor); return cursor->key; }
		valuet &value() const { assert(cursor); return cursor->value; }
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
		return rv;
	}

	void clear() {
		heads = NULL;
		nr_heads = 0;
		nr_items = 0;
	}
	void visit(HeapVisitor &hv) {
		hv(heads);
		for (unsigned x = 0; x < nr_heads; x++)
			hv(heads[x]);
	}
	void destruct() {}
	NAMED_CLASS
};

#endif /* !MAP_H__ */
