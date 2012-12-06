#ifndef QUERY_CACHE_H__
#define QUERY_CACHE_H__

template <typename a_type,
	  typename b_type,
	  typename result_type,
	  unsigned NR_ENTRIES = 255,
	  unsigned ASSOCIATIVITY = 128>
class QueryCache : GcCallback<&ir_heap> {
public:
	struct p {
		a_type *a;
		b_type *b;
		result_type res;
		p(a_type *_a, b_type *_b, bool _res)
			: a(_a),
			  b(_b),
			  res(_res)
		{}
		p()
			: a(NULL), b(NULL)
		{}
	};

	struct cache_entry {
		unsigned nr_entries;
		unsigned prod_idx;
		struct p p[ASSOCIATIVITY];
	};
	unsigned nr_queries;
	unsigned nr_hits;
	unsigned nr_assoc_discards;
	const char *name;
	struct cache_entry cache[NR_ENTRIES];

	QueryCache(const char *_name)
		: GcCallback<&ir_heap>(true), nr_queries(0),
		  nr_hits(0), nr_assoc_discards(0), name(_name)
	{
		memset(cache, 0, sizeof(cache));
	}
		  
	~QueryCache()
	{
		if (nr_queries != 0)
			printf("%s cache: %d queries, %d hits, rate %e; %d associativity discards\n",
			       name,
			       nr_queries, nr_hits, (double)nr_hits / nr_queries, nr_assoc_discards);
	}

	void runGc(HeapVisitor &hv) {
		printf("%s cache: %d queries, %d hits, rate %e; %d associativity discards\n",
		       name, nr_queries, nr_hits, (double)nr_hits / nr_queries,
		       nr_assoc_discards);
		for (unsigned i = 0; i < NR_ENTRIES; i++) {
			struct cache_entry *e = &cache[i];
			unsigned in_idx = 0;
			unsigned out_idx = 0;
			while (in_idx < e->nr_entries) {
				e->p[in_idx].a = hv.visited(e->p[in_idx].a);
				if (e->p[in_idx].a) {
					e->p[in_idx].b = hv.visited(e->p[in_idx].b);
					if (e->p[in_idx].b) {
						e->p[out_idx] = e->p[in_idx];
						out_idx++;
					}
				}
				in_idx++;
			}
			e->nr_entries = out_idx;
			e->prod_idx = out_idx;
		}
	}

	static int hash(a_type *a, b_type *b) {
		unsigned long acc = (unsigned long)a / 32;
		while (acc >= NR_ENTRIES)
			acc = (acc / NR_ENTRIES) + (acc % NR_ENTRIES);
		acc += (unsigned long)b / 32;
		while (acc >= NR_ENTRIES)
			acc = (acc / NR_ENTRIES) + (acc % NR_ENTRIES);
		return acc;
	}

	bool query(a_type *a, b_type *b, int idx, result_type *res) {
		struct cache_entry *e = &cache[idx];
		nr_queries++;
		for (unsigned x = 0; x < e->nr_entries; x++) {
			if (e->p[x].b == b &&
			    e->p[x].a == a) {
				*res = e->p[x].res;
				nr_hits++;
				return true;
			}
		}
		return false;
	}

	void set(a_type *a, b_type *b, int idx, result_type res) {
		struct cache_entry *e = &cache[idx];
		if (e->nr_entries != ASSOCIATIVITY) {
			e->nr_entries++;
		} else {
			nr_assoc_discards++;
		}
		e->p[e->prod_idx] = p(a, b, res);
		e->prod_idx = (e->prod_idx + 1) % ASSOCIATIVITY;
	}
};

#endif /* !QUERY_CACHE_H__ */
