#ifndef HASH_TABLE_HPP__
#define HASH_TABLE_HPP__

#include "maybe.hpp"

template <typename member, int _nr_heads = 2053, int _nr_per_elem = 4> class HashTable {
	/* Duplicating an entire hash table is expensive.  Discourage
	   people from doing so by making this private and
	   not-implemented. */
	HashTable(const HashTable &o);
public:
	HashTable() {}

	static const int nr_heads = _nr_heads;
	static const int nr_per_elem = _nr_per_elem;

	struct elem {
		struct elem *next;
		unsigned long use_map;
		member content[nr_per_elem];
		elem()
			: next(NULL), use_map(0)
		{}
	};
	struct elem heads[nr_heads];
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
			idx1 = -1;
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
		const member *operator->() const {
			assert(!finished());
			assert(elm);
			return &elm->content[idx1];
		}
		const member &operator*() const {
			assert(!finished());
			assert(elm);
			return elm->content[idx1];
		}
		void erase() {
			assert(elm->use_map & (1ul << idx1));
			elm->use_map &= ~(1ul << idx1);
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
			idx1 = -1;
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
		const member *operator->() const {
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
					return true;
				}
			}
			c = c->next;
		}
		return false;
	}

	/* Extend @this by adding in the contents of @o.  Returns true
	 * if we do anything or false if it's a no-op. */
	template <int _nr_heads, int _elem_per_head> bool extend(const HashedSet<member, _nr_heads, _elem_per_head> &o) {
		bool res = false;
		for (auto it = o.begin(); !it.finished(); it.advance())
			res |= !insert(*it);
		return res;
	}

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
	HashedPtr(ptr *_content)
		: content(_content)
	{}
	unsigned long hash() const {
		return (unsigned long)content;
	}
	HashedPtr() {}
};

#endif /* !HASH_TABLE_HPP */
