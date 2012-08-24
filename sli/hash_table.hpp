#ifndef HASH_TABLE_HPP__
#define HASH_TABLE_HPP__

#include "maybe.hpp"

template <typename member, int _nr_heads = 2053, int _nr_per_elem = 4> class HashTable {
public:
	static const int nr_heads = _nr_heads;
	static const int nr_per_elem = _nr_per_elem;
	size_t sz;

	struct elem {
		struct elem *next;
		unsigned long use_map;
		member content[nr_per_elem];
		elem()
			: next(NULL), use_map(0)
		{}
	};
	struct elem heads[nr_heads];

	HashTable() : sz(0) {}
	HashTable(const HashTable &o)
		: sz(0)
	{
		for (int i = 0; i < nr_heads; i++) {
			struct elem *dest_cursor = &heads[i];
			const struct elem *src_cursor = &o.heads[i];
			int dest_idx = 0;
			while (src_cursor) {
				for (int src_idx = 0; src_idx < nr_per_elem; src_idx++) {
					if (!(src_cursor->use_map & (1ul << src_idx)))
						continue;
					dest_cursor->content[dest_idx] = src_cursor->content[src_idx];
					dest_cursor->use_map |= 1ul << dest_idx;
					dest_idx++;
					sz++;
					if (dest_idx == nr_per_elem) {
						dest_idx = 0;
						dest_cursor->next = new elem();
						dest_cursor = dest_cursor->next;
					}
				}
				src_cursor = src_cursor->next;
			}
		}
		assert(sz == o.sz);
	}
	void operator=(const HashTable &o) {
		/* First go and scavenge all of the dynamically
		 * allocated elems. */
		struct elem *malloced_elems = NULL;
		for (int i = 0; i < nr_heads; i++) {
			heads[i].use_map = 0;
			if (!heads[i].next)
				continue;
			struct elem *end;
			for (end = heads[i].next; end->next; end = end->next)
				end->use_map = 0;
			end->next = malloced_elems;
			malloced_elems = heads[i].next;
			heads[i].next = NULL;
		}

		sz = 0;

		/* Now go and repack the other table's content into
		   this one. */
		for (int i = 0; i < nr_heads; i++) {
			struct elem *dest_elem = &heads[i];
			const struct elem *src_elem = &o.heads[i];
			int dest_idx = 0;
			while (src_elem) {
				for (int j = 0; j < nr_per_elem; j++) {
					if (src_elem->use_map & (1ul << j)) {
						dest_elem->content[dest_idx] = src_elem->content[j];
						dest_elem->use_map |= 1ul << dest_idx;
						dest_idx++;
						if (dest_idx == nr_per_elem) {
							if (malloced_elems) {
								dest_elem->next = malloced_elems;
								malloced_elems = malloced_elems->next;
								dest_elem = dest_elem->next;
								dest_elem->next = NULL;
								assert(dest_elem->use_map == 0);
							} else {
								dest_elem->next = new elem();
								dest_elem = dest_elem->next;
							}
							dest_idx = 0;
						}
						sz++;
					}
				}
				src_elem = src_elem->next;
			}
		}
		assert(sz == o.sz);

		/* Release any left-over scavenged heads */
		while (malloced_elems) {
			struct elem *n = malloced_elems->next;
			delete malloced_elems;
			malloced_elems = n;
		}
	}

	~HashTable() {
		for (int x = 0; x < nr_heads; x++) {
			struct elem *n;
			for (struct elem *e = heads[x].next; e; e = n) {
				n = e->next;
				delete e;
			}
		}
	}
	const struct elem *getHead(unsigned long h) const {
		while (h >= (unsigned long)nr_heads)
			h = (h % nr_heads) ^ (h / nr_heads);
		return &heads[h];
	}
	struct elem *getHead(unsigned long h) {
		while (h >= (unsigned long)nr_heads)
			h = (h % nr_heads) ^ (h / nr_heads);
		return &heads[h];
	}

	void clear() {
		for (int i = 0; i < nr_heads; i++) {
			while (heads[i].next) {
				struct elem *e = heads[i].next->next;
				delete heads[i].next;
				heads[i].next = e;
			}
			heads[i].use_map = 0;
		}
		sz = 0;
	}

	size_t size() const { return sz; }
	bool empty() const { return size() == 0; }

	class iterator {
		HashTable *owner;
		elem *elm;
		int idx1;
		int idx2;
	public:
		iterator(HashTable *_owner)
			: owner(_owner)
		{
			elm = NULL;
			idx1 = nr_per_elem;
			idx2 = -1;
			advance();
		}
		bool started() const {
			return idx2 != -1;
		}
		bool finished() const {
			return idx2 == nr_heads;
		}
		void advance() {
			idx1 = (idx1 + 1) % nr_per_elem;
			if (idx1 == 0) {
				if (elm) {
					elm = elm->next;
				} else {
					assert(idx2 < nr_heads);
					idx2++;
					elm = &owner->heads[idx2];
				}
			}
			while (idx2 < nr_heads) {
				while (elm != NULL) {
					for (; idx1 < nr_per_elem; idx1++) {
						if (elm->use_map & (1ul << idx1))
							return;
					}
					idx1 = 0;
					elm = elm->next;
				}
				idx2++;
				elm = &owner->heads[idx2];
			}
		}
		member *operator->() const {
			assert(!finished());
			assert(elm);
			return &elm->content[idx1];
		}
		member &operator*() const {
			assert(!finished());
			assert(elm);
			return elm->content[idx1];
		}
		member &operator*() {
			assert(!finished());
			assert(elm);
			return elm->content[idx1];
		}
		void erase() {
			elm->use_map &= ~(1ul << idx1);
			owner->sz--;
			advance();
		}
	};
	class const_iterator {
		const HashTable *owner;
		const elem *elm;
		int idx1;
		int idx2;
	public:
		const_iterator(const HashTable *_owner)
			: owner(_owner)
		{
			elm = NULL;
			idx1 = nr_per_elem;
			idx2 = -1;
			advance();
		}
		bool finished() const {
			return idx2 == nr_heads;
		}
		bool started() const {
			return idx2 != -1;
		}
		void advance() {
			idx1 = (idx1 + 1) % nr_per_elem;
			if (idx1 == 0) {
				if (elm) {
					elm = elm->next;
				} else {
					assert(idx2 < nr_heads);
					idx2++;
					elm = &owner->heads[idx2];
				}
			}
			while (idx2 < nr_heads) {
				while (elm != NULL) {
					for (; idx1 < nr_per_elem; idx1++) {
						if (elm->use_map & (1ul << idx1))
							return;
					}
					idx1 = 0;
					elm = elm->next;
				}
				idx2++;
				elm = &owner->heads[idx2];
			}
		}
		member *operator->() const {
			assert(!finished());
			assert(elm);
			return &elm->content[idx1];
		}
		const member &operator*() const {
			assert(!finished());
			assert(elm);
			return elm->content[idx1];
		}
	};
};

template <typename member, int nr_heads = 2053, int nr_per_elem = 4> class HashedSet {
	typedef HashTable<member, nr_heads, nr_per_elem> contentT;
	contentT content;
public:
	HashedSet() {}
	bool contains(const member &v) const {
		const typename contentT::elem *c = content.getHead(v.hash());
		while (c) {
			for (int i = 0; i < contentT::nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) &&
				     c->content[i] == v )
					return true;
			}
			c = c->next;
		}
		return false;
	}
	/* Returns true if the thing was already present or false
	 * otherwise. */
	bool insert(const member &v) {
		typename contentT::elem *c = content.getHead(v.hash());
		typename contentT::elem **last = (typename contentT::elem **)0xf001;
		member *slot = NULL;
		unsigned long *slot_use = (unsigned long *)0xf001; /* shut compiler up */
		unsigned long slot_use_mask = 0xdeadbeefcafebabeul;
		while (c) {
			for (int i = 0; i < contentT::nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) ) {
					if (c->content[i] == v )
						return true;
				} else if (!slot) {
					slot = &c->content[i];
					slot_use = &c->use_map;
					slot_use_mask = 1ul << i;
				}
			}
			last = &c->next;
			c = c->next;
		}
		content.sz++;
		if (slot) {
			*slot = v;
			*slot_use |= slot_use_mask;
			return false;
		}
		c = new typename contentT::elem();
		c->use_map = 1;
		c->content[0] = v;
		*last = c;
		return false;
	}
	bool erase(const member &v) {
		typename contentT::elem *c = content.getHead(v.hash());
		while (c) {
			for (int i = 0; i < contentT::nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) &&
				     c->content[i] == v ) {
					c->use_map &= ~(1ul << i);
					content.sz--;
					return true;
				}
			}
			c = c->next;
		}
		return false;
	}
	void clear() {
		content.clear();
	}
	/* Extend @this by adding in the contents of @o.  Returns true
	 * if we do anything or false if it's a no-op. */
	template <int _nr_heads, int _elem_per_head> bool extend(const HashedSet<member, _nr_heads, _elem_per_head> &o) {
		bool res = false;
		for (auto it = o.begin(); !it.finished(); it.advance())
			res |= !insert(*it);
		return res;
	}

	size_t size() const { return content.size(); }
	bool empty() const { return content.empty(); }

	typedef typename contentT::iterator iterator;
	iterator begin() { return iterator(&content); }
	typedef typename contentT::const_iterator const_iterator;
	const_iterator begin() const { return const_iterator(&content); }
};

template <typename key, typename value, int nr_heads = 2053, int nr_per_elem = 4> class HashedMap {
	typedef HashTable<std::pair<key, value>, nr_heads, nr_per_elem> contentT;
	contentT content;
public:
	Maybe<value> get(const key &k) const {
		const typename contentT::elem *c = content.getHead(k.hash());
		while (c) {
			for (int i = 0; i < contentT::nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) &&
				     c->content[i].first == k )
					return Maybe<value>::just(c->content[i].second);
			}
			c = c->next;
		}
		return Maybe<value>::nothing();
	}
	void set(const key &k, value &v) {
		typename contentT::elem *c = content.getHead(k.hash());
		typename contentT::elem **last;
		std::pair<key, value> *slot = NULL;
		unsigned long *slot_use;
		unsigned long slot_use_mask;
		while (c) {
			for (int i = 0; i < contentT::nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) ) {
					if (c->content[i].first == k ) {
						c->content[i].second = v;
						return;
					}
				} else if (!slot) {
					slot = &c->content[i];
					slot_use = &c->use_map;
					slot_use_mask = 1ul << i;
				}
			}
			last = &c->next;
			c = c->next;
		}
		content.sz++;
		if (slot) {
			*slot = std::pair<key, value>(k, v);
			*slot_use |= slot_use_mask;
			return;
		}
		c = new typename contentT::elem();
		c->use_map = 1;
		c->content[0].first = k;
		c->content[0].second = v;
		*last = c;
	}
};

template <typename ptr> class HashedPtr {
	ptr *content;
public:
	operator ptr*() const { return content; }
	ptr &operator*() { return *content; }
	ptr *operator->() { return content; }
	const ptr &operator*() const { return *content; }
	ptr *operator->() const { return content; }
	HashedPtr(ptr *_content)
		: content(_content)
	{}
	unsigned long hash() const {
		return (unsigned long)content;
	}
	HashedPtr() {}
};

#endif /* !HASH_TABLE_HPP */
