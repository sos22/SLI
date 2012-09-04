#ifndef CFGNODE_HPP__
#define CFGNODE_HPP__

#include "typesdb.hpp"
#include "library.hpp"
#include "hash_table.hpp"

class Oracle;

enum CfgSuccessorType {succ_default, succ_branch, succ_call, succ_unroll};
template <typename succ_t>
class CfgSuccessorT {
	CfgSuccessorT(CfgSuccessorType _type,
		      const succ_t &_instr,
		      LibraryFunctionType _calledFunction)
		: type(_type), instr(_instr), calledFunction(_calledFunction)
	{}
public:
	CfgSuccessorT(const succ_t &s)
		: type((CfgSuccessorType)-1),
		  instr(s),
		  calledFunction(LibraryFunctionTemplate::none)
	{}
	template <typename ot> CfgSuccessorT(const CfgSuccessorT<ot> &o,
					     const succ_t targ)
		: type(o.type), instr(targ), calledFunction(o.calledFunction)
	{}
	CfgSuccessorType type;
	succ_t instr;
	LibraryFunctionType calledFunction;

	bool operator==(const CfgSuccessorT<succ_t> &o) const {
		return instr == o.instr && type == o.type &&
			calledFunction == o.calledFunction;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "%s:", instr ? instr->label.name() : "<null>");
		switch (type) {
		case succ_default:
			fprintf(f, "default");
		case succ_branch:
			fprintf(f, "branch");
		case succ_call:
			fprintf(f, "call");
		case succ_unroll:
			fprintf(f, "unroll");
		}
		if (calledFunction != LibraryFunctionTemplate::none)
			LibraryFunctionTemplate::pp(calledFunction, f);
	}

	static CfgSuccessorT<succ_t> call(const succ_t & _rip)
	{
		return CfgSuccessorT<succ_t>(succ_call, _rip, LibraryFunctionTemplate::none);
	}
	static CfgSuccessorT<succ_t> branch(const succ_t & _rip)
	{
		return CfgSuccessorT<succ_t>(succ_branch, _rip, LibraryFunctionTemplate::none);
	}
	static CfgSuccessorT<succ_t> dflt(const succ_t & _rip, LibraryFunctionType _calledFunction = LibraryFunctionTemplate::none)
	{
		return CfgSuccessorT<succ_t>(succ_default, _rip, _calledFunction);
	}
	static CfgSuccessorT<succ_t> unroll(const succ_t &_rip)
	{
		return CfgSuccessorT<succ_t>(succ_unroll, _rip, LibraryFunctionTemplate::none);
	}

	void visit(HeapVisitor &hv) {
		hv(instr);
	}
};

template <typename ripType>
class _CFGNode : public GarbageCollected<_CFGNode<ripType>, &ir_heap> {
public:
	typedef CfgSuccessorT<_CFGNode<ripType> *> successor_t;

	ripType rip;
	CfgLabel label;
	std::vector<successor_t> successors;
	_CFGNode(const ripType &_rip, const CfgLabel &_label)
		: rip(_rip), label(_label)
	{}
	_CFGNode(_CFGNode *base, const CfgLabel &_label)
		: rip(base->rip), label(_label), successors(base->successors)
	{}

	bool operator==(const _CFGNode<ripType> &o) const {
		return rip == o.rip && label == o.label && successors == o.successors;
	}

	successor_t *getDefault() {
		successor_t *res = NULL;
		for (auto it = successors.begin(); it != successors.end(); it++) {
			if (it->type == succ_default) {
				assert(!res);
				res = &*it;
			}
		}
		return res;
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "instr(%s, %s, succ = {", label.name(), rip.name());
		for (auto it = successors.begin(); it != successors.end(); it++) {
			if (it != successors.begin())
				fprintf(f, ", ");
			it->prettyPrint(f);
		}
		fprintf(f, "}\n");
	}
	void visit(HeapVisitor &hv) {
		for (auto it = successors.begin(); it != successors.end(); it++)
			it->visit(hv);
	};
	NAMED_CLASS
};

typedef _CFGNode<VexRip> CFGNode;

void getStoreCFGs(CfgLabelAllocator &allocLabel,
		  const std::set<DynAnalysisRip> &, Oracle *,
		  CFGNode ***, int *);
bool getProbeCFGs(CfgLabelAllocator &allocLabel,
		  Oracle *oracle, const DynAnalysisRip &vr,
		  HashedSet<HashedPtr<CFGNode> > &out,
		  HashedSet<HashedPtr<const CFGNode> > &targetNodes);

void trimUninterestingCFGNodes(std::map<VexRip, CFGNode *> &m,
			       const std::set<DynAnalysisRip> &roots);
void trimUninterestingCFGNodes(std::map<VexRip, CFGNode *> &m,
			       const DynAnalysisRip &target);

class StateMachine;
class MaiMap;
class StateMachineState;
StateMachine *storeCFGToMachine(Oracle *oracle,
				unsigned tid,
				CFGNode *root,
				MaiMap &mai);
void probeCFGsToMachine(Oracle *oracle,
			unsigned tid,
			HashedSet<HashedPtr<CFGNode> > &roots,
			HashedSet<HashedPtr<const CFGNode> > &proximalNodes,
			MaiMap &mai,
			std::set<StateMachine *> &out);
void dumpCFGToDot(const HashedSet<HashedPtr<CFGNode> > &allNodes, const char *fname);

#endif /* !CFGNODE_HPP__ */
