#ifndef ALLOC_MAI_HPP__
#define ALLOC_MAI_HPP__

class MemoryAccessIdentifierAllocator {
	std::map<std::pair<int, CfgLabel>, unsigned> ids;
public:
	MemoryAccessIdentifier operator()(const CfgLabel &, int);
	IRExpr *freeVariable(IRType ty, int tid, const CfgLabel &node, bool isUnique);
};

#endif /* !ALLOC_MAI_HPP__ */
