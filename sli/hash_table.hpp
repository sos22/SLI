/* Hash-based, rather than red-black tree-based, implementations of
   map and set ADTs.  The interface is a bit different from std::map
   and std::set.

   HashedSet
   ---------

   bool contains(const member &v) const;
   -> check whether the set contains @v, returns true if it does or
      false otherwise.  Essentially the same as std::set::count.
   
   bool _insert(const member &v);
   -> insert @v in the set, or no-op if it's already present.  Returns
      true if it actually inserted it or false otherwise.  Any
      outstanding iterators remain valid, but it's undefined whether
      they will ever return the item just inserted.

   void insert(const member &v);
   -> like _insert, but returns void.  Exists mostly because I'm
      forever getting the sense of the return value of _insert wrong,
      and having a function which doesn't return anything makes it
      obvious which ones need auditing.
      
   bool erase(const member &v);
   -> erase @v from the set, or no-op if it isn't present.  Returns
      true if anything erase or false otherwise.  Invalidates any
      current iterators.

   void clear();
   -> remove everything from the set.  Invalidates all iterators.

   size_t size();
   -> count of number of elements in set.

   bool empty();
   -> equivalent to size() == 0.

   iterator begin();
   const_iterator begin() const;
   -> create a new iterator.  These are not standard iterators.  They
      have these methods:

      bool started() const;
      -> returns true if advance() has ever been called.
      
      bool finished() const;
      -> returns true if the iterator has reached the end of the set,
         so that dereferencing it is no longer safe.

      void advance();
      -> move on to the next element of the set.  Unsafe if the
         iterator is finished.

      member *operator->() const;
      member &operator* const;
      -> Get various flavours of reference to the current item.

      void erase();
      -> erase the current item from the set.  Implicitly advances to
         the next item.  Invalidates any other outstanding iterators
         on this set.  Not in const iterators.
*/
#ifndef HASH_TABLE_HPP__
#define HASH_TABLE_HPP__

#include "maybe.hpp"
#include "either.hpp"

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
	/* For some reason, gdb can't see the debug symbols for
	   operator=, which makes debugging a pain.  I don't know
	   whether the problem is gcc or gdb, but just making
	   operator= a proxy for assign() avoids the issue, so do
	   that. */
	void operator=(const HashTable &o) { assign(o); }
private:
	void assign(const HashTable &o) {
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
public:

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
		void erase() {
			assert(elm->use_map & (1ul << idx1));
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
	/* returns true if we did anything or false present */
	bool _insert(const member &v) {
		typename contentT::elem *c = content.getHead(v.hash());
		typename contentT::elem **last = (typename contentT::elem **)0xf001;
		member *slot = NULL;
		unsigned long *slot_use = (unsigned long *)0xf001; /* shut compiler up */
		unsigned long slot_use_mask = 0xdeadbeefcafebabeul;
		while (c) {
			for (int i = 0; i < contentT::nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) ) {
					if (c->content[i] == v )
						return false;
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
			return true;
		}
		c = new typename contentT::elem();
		c->use_map = 1;
		c->content[0] = v;
		*last = c;
		assert(contains(v));
		return true;
	}
	void insert(const member &v) {
		_insert(v);
	}
	bool erase(const member &v) {
		typename contentT::elem *c = content.getHead(v.hash());
		while (c) {
			for (int i = 0; i < contentT::nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) &&
				     c->content[i] == v ) {
					assert(contains(v));
					c->use_map &= ~(1ul << i);
					content.sz--;
					assert(!contains(v));
					return true;
				}
			}
			c = c->next;
		}
		assert(!contains(v));
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
			res |= _insert(*it);
		return res;
	}

	size_t size() const { return content.size(); }
	bool empty() const { return content.empty(); }

	typedef typename contentT::iterator iterator;
	iterator begin() { return iterator(&content); }
	typedef typename contentT::const_iterator const_iterator;
	const_iterator begin() const { return const_iterator(&content); }
};

template <typename _key, typename _value, int nr_heads = 2053, int nr_per_elem = 4> class HashedMap {
	typedef HashTable<std::pair<_key, _value>, nr_heads, nr_per_elem> contentT;
	contentT content;
public:
	bool hasKey(const _key &k) const {
		const typename contentT::elem *c = content.getHead(k.hash());
		while (c) {
			for (int i = 0; i < contentT::nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) &&
				     c->content[i].first == k ) {
					return true;
				}
			}
			c = c->next;
		}
		return false;
	}
	Maybe<_value> get(const _key &k) const {
		const typename contentT::elem *c = content.getHead(k.hash());
		while (c) {
			for (int i = 0; i < contentT::nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) &&
				     c->content[i].first == k )
					return Maybe<_value>::just(c->content[i].second);
			}
			c = c->next;
		}
		return Maybe<_value>::nothing();
	}
	_value *getSlot(const _key &k, const _value &defaultV) {
		typename contentT::elem *c = content.getHead(k.hash());
		typename contentT::elem **last;
		std::pair<_key, _value> *slot = NULL;
		unsigned long *slot_use;
		unsigned long slot_use_mask;

		/* Shut compiler up */
		slot_use = (unsigned long *)0xf001;
		slot_use_mask = 0xaaaabbbb;
		last = (typename contentT::elem **)0xdead;

		while (c) {
			for (int i = 0; i < contentT::nr_per_elem; i++) {
				if ( (c->use_map & (1ul << i)) ) {
					if (c->content[i].first == k )
						return &c->content[i].second;
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
			*slot = std::pair<_key, _value>(k, defaultV);
			*slot_use |= slot_use_mask;
			return &slot->second;
		}
		c = new typename contentT::elem();
		c->use_map = 1;
		c->content[0].first = k;
		c->content[0].second = defaultV;
		*last = c;
		return &c->content[0].second;
	}
	void set(const _key &k, const _value &v) {
		*getSlot(k, v) = v;
	}
	size_t size() const {
		return content.size();
	}

	class iterator {
		typename contentT::iterator it;
	public:
		iterator(contentT *content)
			: it(content)
		{
		}
		bool finished() const { return it.finished(); }
		bool started() const { return it.started(); }
		void advance() { it.advance(); }
		const _key &key() const { return it->first; }
		const _value &value() const { return it->second; }
	};
	iterator begin() { return iterator(&content); }

	class const_iterator {
		typename contentT::const_iterator it;
	public:
		const_iterator(const contentT *content)
			: it(content)
		{
		}
		bool finished() const { return it.finished(); }
		bool started() const { return it.started(); }
		void advance() { it.advance(); }
		const _key &key() const { return it->first; }
		const _value &value() const { return it->second; }
	};
	const_iterator begin() const { return const_iterator(&content); }
};

/* Like a HashedMap, except that it has a special case for very small
   tables, making it fast to set up when you don't have very many
   items while only being slightly slower for larger tables. */
template <typename _key, typename _value, int nr_small = 4,
	  int nr_heads = 64, int nr_per_elem = 4> class HashedMapSmall {
	typedef HashedMap<_key, _value, nr_heads, nr_per_elem> largeT;
	largeT *large;
	int nr_small_used;
	std::pair<_key, _value> small[nr_small];
	void operator=(const HashedMapSmall &o); /* Not implemented */
public:
	/* Turn @o into a copy of *this and simultaneously clear
	 * *this. */
	void move(HashedMapSmall &o) {
		new (&o) HashedMapSmall();
		if (large) {
			o.large = large;
			large = NULL;
		} else {
			o.nr_small_used = nr_small_used;
			for (int i = 0; i < o.nr_small_used; i++) {
				new (&o.small[i]) std::pair<_key, _value>(small[i]);
				typedef std::pair<_key, _value> foo;
				small[i].~foo();
			}
			nr_small_used = 0;
		}
	}
	HashedMapSmall()
		: large(NULL),
		  nr_small_used(0)
	{}
	~HashedMapSmall()
	{
		if (large)
			delete large;
	}
	HashedMapSmall(const HashedMapSmall &o)
		: large(NULL), nr_small_used(0)
	{
		if (o.large) {
			large = new largeT(*o.large);
		} else {
			nr_small_used = o.nr_small_used;
			for (int i = 0; i < o.nr_small_used; i++)
				new (&small[i]) std::pair<_key, _value>(o.small[i]);
		}
	}
	bool hasKey(const _key &k) const {
		if (large)
			return large->hasKey(k);
		for (int i = 0; i < nr_small_used; i++) {
			if (small[i].first == k) {
				return true;
			}
		}
		return false;
	}
	size_t size() const {
		if (large)
			return large->size();
		else
			return nr_small_used;
	}
	_value *getSlot(const _key &k, const _value &defaultV) {
		if (large)
			return large->getSlot(k, defaultV);
		for (int i = 0; i < nr_small_used; i++) {
			if (small[i].first == k)
				return &small[i].second;
		}
		if (nr_small_used == nr_small) {
			large = new largeT();
			for (int i = 0; i < nr_small_used; i++)
				large->set(small[i].first, small[i].second);
			nr_small_used = 0;
			return large->getSlot(k, defaultV);
		}
		small[nr_small_used].first = k;
		small[nr_small_used].second = defaultV;
		nr_small_used++;
		return &small[nr_small_used-1].second;
	}
	void set(const _key &k, const _value &v) {
		*getSlot(k, v) = v;
	}

	class const_iterator {
		typedef either<typename largeT::const_iterator,
			       typename std::pair<const HashedMapSmall *,
						  int> > contentT;
		contentT content;
	public:
		const_iterator(const HashedMapSmall *owner)
			: content(owner->large ?
				  contentT::Left(((const largeT *)owner->large)->begin()) :
				  contentT::Right(std::pair<const HashedMapSmall *, int>
						  (owner, 0)))
		{
		}
		bool finished() const {
			if (content.isLeft)
				return content.left().finished();
			else
				return content.right().second ==
					content.right().first->nr_small_used;
		}
		bool started() const {
			if (content.isLeft)
				return content.left().started();
			else
				return content.right().second != 0;
		}
		void advance() {
			if (content.isLeft)
				content.left().advance();
			else
				content.right().second++;
		}
		const _key &key() const {
			if (content.isLeft) {
				return content.left().key();
			} else {
				assert(content.right().second < content.right().first->nr_small_used);
				return content.right().first->small[content.right().second].first;
			}
		}
		const _value &value() const {
			if (content.isLeft) {
				return content.left().value();
			} else {
				assert(content.right().second < content.right().first->nr_small_used);
				return content.right().first->small[content.right().second].second;
			}
		}
	};
	const_iterator begin() const { return const_iterator(this); }
};

template <typename ptr> class HashedPtr {
	ptr *content;
public:
	operator ptr*() const { return content; }
	ptr *get() const { return content; }
	ptr &operator*() { return *content; }
	ptr *operator->() { return content; }
	const ptr &operator*() const { return *content; }
	ptr *operator->() const { return content; }
	HashedPtr(ptr *_content)
		: content(_content)
	{}
	unsigned long hash() const {
		if (content)
			return content->hash();
		else
			return 0;
	}
	HashedPtr() {}
};

#endif /* !HASH_TABLE_HPP */
