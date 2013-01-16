#ifndef ALLOC_MAI_HPP__
#define ALLOC_MAI_HPP__

#include "cfgnode.hpp"

class MaiMap : public GarbageCollected<MaiMap, &ir_heap> {
	int nextId;
	std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> > *maiCorrespondence;
	MaiMap()
		: nextId(1), maiCorrespondence(new std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> >())
	{}
	MaiMap(int _nextId, const std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> > *_corr)
		: nextId(_nextId),
		  maiCorrespondence(new std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> >(*_corr))
	{}
	void operator = (const MaiMap &o); /* DNI */
	MaiMap(const MaiMap &o); /* DNI */
public:
	~MaiMap()
	{
		delete maiCorrespondence;
	}
	static MaiMap *empty() { return new MaiMap(); }
	MaiMap *dupe() const
	{
		return new MaiMap(nextId, maiCorrespondence);
	}

	MemoryAccessIdentifier operator()(unsigned tid, const CFGNode *node);
	IRExpr *freeVariable(IRType ty, unsigned tid, const CFGNode *node, bool isUnique);
	static MaiMap *parse(const std::map<CfgLabel, const CFGNode *> &, const char *, const char **);
	static MaiMap *fromFile(const StateMachine *sm, const char *fname);
	static MaiMap *fromFile(const StateMachine *sm1, const StateMachine *sm2, const char *fname);
	void print(FILE *f) const;

	class const_iterator {
		std::vector<const CFGNode *>::const_iterator it;
		std::vector<const CFGNode *>::const_iterator endIt;
	public:
		const_iterator(const std::vector<const CFGNode *> &m)
			: it(m.begin()), endIt(m.end())
		{}
		bool finished() const { return it == endIt; }
		void advance() { it++; }
		const CFGNode *node() const { return *it; }
		const CfgLabel &label() const  { return (*it)->label; }
		DynAnalysisRip dr() const { return DynAnalysisRip(node()->rip); }
	};
	const_iterator begin(const MemoryAccessIdentifier &mai) const {
		auto it = maiCorrespondence->find(mai);
		assert(it != maiCorrespondence->end());
		return const_iterator(it->second);
	}
	class iterator {
		std::vector<const CFGNode *>::iterator it;
		std::vector<const CFGNode *> &vect;
	public:
		iterator(std::vector<const CFGNode *> &m)
			: it(m.begin()), vect(m)
		{}
		bool finished() const { return it == vect.end(); }
		void advance() { it++; }
		void erase() { it = vect.erase(it); }
		const CFGNode *node() const { return *it; }
		const CfgLabel &label() const  { return (*it)->label; }
		DynAnalysisRip dr() const { return DynAnalysisRip(node()->rip); }
	};
	iterator begin(const MemoryAccessIdentifier &mai) {
		auto it = maiCorrespondence->find(mai);
		assert(it != maiCorrespondence->end());
		return iterator(it->second);
	}

	class key_iterator {
		std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> >::iterator it;
		std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> > &map;
	public:
		key_iterator(std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> > &c)
			: it(c.begin()), map(c)
		{}
		bool finished() const { return it == map.end(); }
		void advance() { it++; }
		void erase() { map.erase(it++); }
		const MemoryAccessIdentifier &mai() const { return it->first; }
		bool empty() const { return it->second.empty(); }
		iterator begin() { return iterator(it->second); }
	};
	key_iterator begin() {
		return key_iterator(*maiCorrespondence);
	}

	MemoryAccessIdentifier merge(int tid, const std::set<MemoryAccessIdentifier> &mais) {
		MemoryAccessIdentifier res(nextId, tid);
		nextId++;
		std::vector<const CFGNode *> &entry1( (*maiCorrespondence)[res] );
		for (auto it = mais.begin(); it != mais.end(); it++) {
			assert(*it != res);
			assert(maiCorrespondence->count(*it));
			const std::vector<const CFGNode *> &entry2( (*maiCorrespondence)[*it] );
			for (auto it2 = entry2.begin(); it2 != entry2.end(); it2++) {
				bool alreadyPresent = false;
				for (auto it3 = entry1.begin(); !alreadyPresent && it3 != entry1.end(); it3++) {
					if (*it2 == *it3)
						alreadyPresent = true;
				}
				if (!alreadyPresent)
					entry1.push_back(*it2);
			}
		}
		return res;
	}

	void restrict(const std::set<const CFGNode *> &cfgNodes,
		      const std::set<MemoryAccessIdentifier> &mais);

	void visit(HeapVisitor &hv) {
		for (auto it = maiCorrespondence->begin();
		     it != maiCorrespondence->end();
		     it++)
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++)
				hv(*it2);
	}
	NAMED_CLASS
};

#endif /* !ALLOC_MAI_HPP__ */
