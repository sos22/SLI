#ifndef WEAK_MAP_HPP__
#define WEAK_MAP_HPP__

template <typename key, typename value, typename extension, Heap *heap> class weak_map
	: public sane_map<key, value>, GcCallback<heap> {
	void runGc(HeapVisitor &hv) {
		sane_map<key, value> n;
		extension *ths = static_cast<extension *>(this);
		for (auto it = this->begin(); it != this->end(); it++) {
			key k(it->first);
			value v(it->second);
			if (ths->visitKey(hv, k) &&
			    ths->visitValue(hv, v)) {
				n.insert(k, v);
			}
		}
		this->clear();
		for (auto it = n.begin(); it != n.end(); it++) {
			this->insert(it->first, it->second);
		}
	}
public:
	weak_map()
		: GcCallback<heap>(true)
	{}

	/* These should be overridden in derived classes */
	bool visitKey(HeapVisitor &hv, key &what) {
		what = hv.visited(what);
		return what != NULL;
	}
	bool visitValue(HeapVisitor &hv, value &what) {
		what = hv.visited(what);
		return what != NULL;
	}
};

#endif /* !WEAK_MAP_HPP__ */
