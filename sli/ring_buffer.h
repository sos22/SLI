#ifndef RING_BUFFER_H__
#define RING_BUFFER_H__

#include <vector>
#include <iterator>

template <typename t, int size>
class ring_buffer {
	std::vector<t> content;
	int producer;
	int consumer;
public:
	typedef t value_type;
	class iterator {
		friend class ring_buffer<t, size>;
		int idx;
		ring_buffer<t, size> *owner;
	public:
		iterator(int i, ring_buffer<t, size> &o) : idx(i), owner(&o) {}
		void operator++() { idx++; }
		void operator++(int) { idx++; }
		void operator--() { idx--; }
		void operator--(int) { idx--; }
		bool operator==(const iterator &o) { return idx == o.idx; }
		bool operator!=(const iterator &o) { return idx != o.idx; }
		t & operator*() { return owner->content[idx%size]; }
		t *operator->() { return &owner->content[idx % size]; }

		iterator operator+(int offset) { return iterator(idx + offset, *owner); }
	};
	class const_iterator {
		int idx;
		const ring_buffer<t, size> &owner;
	public:
		typedef t value_type;
		const_iterator(int i, const ring_buffer<t, size> &o) : idx(i), owner(o) {}
		const t & operator*() const { return owner.content[idx%size]; }
		void operator++() { idx++; }
		void operator++(int) { idx++; }
		bool operator==(const const_iterator &o) const { return idx == o.idx; }
		bool operator!=(const const_iterator &o) const { return idx != o.idx; }
		const t *operator->() const { return &owner.content[idx % size]; }
	};
	class reverse_iterator {
		int idx;
		ring_buffer<t, size> &owner;
	public:
		typedef t value_type;
		reverse_iterator(int i, ring_buffer<t, size> &o) : idx(i), owner(o) {}
		t & operator*() { return owner.content[(idx-1) % size]; }
		void operator++() { idx--; }
		void operator++(int) { idx--; }
		bool operator==(const reverse_iterator &o) { return idx == o.idx; }
		bool operator!=(const reverse_iterator &o) { return idx != o.idx; }
		t *operator->() { return &owner.content[idx%size]; }
	};

	ring_buffer() : producer(0), consumer(0) { content.resize(size); }

	void push(t x) {
		content[producer % size] = x;
		if (consumer == producer - size)
			consumer++;
		producer++;
	}
	void push_back(t x) { push(x); }
	t pop() {
		assert(consumer < producer);
		consumer++;
		return content[(consumer - 1) % size];
	}
	t pop_back() {
		assert(consumer < producer);
		producer--;
		return content[producer % size];
	}
	bool empty() const {
		return consumer == producer;
	}

	iterator begin() {
		return iterator(consumer, *this);
	}
	iterator end() {
		return iterator(producer, *this);
	}
	const_iterator begin() const {
		return const_iterator(consumer, *this);
	}
	const_iterator end() const {
		return const_iterator(producer, *this);
	}
	reverse_iterator rbegin() {
		return reverse_iterator(producer, *this);
	}
	reverse_iterator rend() {
		return reverse_iterator(consumer, *this);
	}

	iterator erase(iterator it) {
		assert(it.idx >= consumer && it.idx < producer);
		assert(it.owner == this);
		for (int x = it.idx + 1; x != producer; x++)
			content[(x - 1) % size] = content[x % size];
		producer--;
		return it;
	}
};

#endif /* !RING_BUFFER_H__ */
