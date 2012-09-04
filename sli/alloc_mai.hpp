#ifndef ALLOC_MAI_HPP__
#define ALLOC_MAI_HPP__

class MaiMap : public GarbageCollected<MaiMap, &ir_heap> {
	int nextId;
	std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> > *maiCorrespondence;
	MaiMap()
		: nextId(1), maiCorrespondence(new std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> >())
	{}
	MaiMap(int _nextId, std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> > *_corr)
		: nextId(_nextId),
		  maiCorrespondence(_corr)
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
		return new MaiMap(
			nextId,
			new std::map<MemoryAccessIdentifier, std::vector<const CFGNode *> >(*maiCorrespondence));
	}

	MemoryAccessIdentifier operator()(unsigned tid, const CFGNode *node);
	IRExpr *freeVariable(IRType ty, unsigned tid, const CFGNode *node, bool isUnique);
	static MaiMap *parse(const std::map<CfgLabel, const CFGNode *> &, const char *, const char **);
	static MaiMap *fromFile(const StateMachine *sm, const char *fname);
	static MaiMap *fromFile(const StateMachine *sm1, const StateMachine *sm2, const char *fname);
	void print(FILE *f) const;

	class iterator {
		std::vector<const CFGNode *>::const_iterator it;
		std::vector<const CFGNode *>::const_iterator endIt;
	public:
		iterator(const std::vector<const CFGNode *> &m)
			: it(m.begin()), endIt(m.end())
		{}
		bool finished() const { return it == endIt; }
		void advance() { it++; }
		const CFGNode *node() const { return *it; }
		DynAnalysisRip dr() const { return DynAnalysisRip(node()->rip); }
	};

	iterator begin(const MemoryAccessIdentifier &mai) const {
		auto it = maiCorrespondence->find(mai);
		assert(it != maiCorrespondence->end());
		return iterator(it->second);
	}

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
