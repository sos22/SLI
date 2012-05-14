#ifndef ALLOC_MAI_HPP__
#define ALLOC_MAI_HPP__

class MemoryAccessIdentifierAllocator {
	std::map<ThreadRip, unsigned> ids;
public:
	MemoryAccessIdentifier operator()(const ThreadRip &rip);
	IRExpr *freeVariable(IRType ty, const ThreadRip &rip);
};

#endif /* !ALLOC_MAI_HPP__ */
