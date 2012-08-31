#ifndef CFGNODE_HPP__
#define CFGNODE_HPP__

#include "typesdb.hpp"
#include "library.hpp"
#include "hash_table.hpp"

class Oracle;

template <typename ripType>
class _CFGNode : public GarbageCollected<_CFGNode<ripType>, &ir_heap> {
public:
	class successor_t {
	public:
		enum succ_type {succ_default, succ_branch, succ_call, succ_unroll};
	private:
		successor_t(succ_type _type,
			    const ripType &_rip,
			    _CFGNode *_instr,
			    LibraryFunctionType _calledFunction)
			: type(_type), rip(_rip), instr(_instr),
			  calledFunction(_calledFunction)
		{}
	public:
		succ_type type;
		ripType rip;
		_CFGNode<ripType> *instr;
		LibraryFunctionType calledFunction;

		bool operator==(const successor_t &o) const {
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

		static successor_t call(const ripType _rip)
		{
			return successor_t(succ_call, _rip,
					   NULL, LibraryFunctionTemplate::none);
		}
		static successor_t call(_CFGNode *i)
		{
			return successor_t(succ_call, ripType(), i, LibraryFunctionTemplate::none);
		}
		static successor_t branch(const ripType _rip)
		{
			return successor_t(succ_branch, _rip, NULL,
					   LibraryFunctionTemplate::none);
		}
		static successor_t branch(_CFGNode *i)
		{
			return successor_t(succ_branch, ripType(), i,
					   LibraryFunctionTemplate::none);
		}
		static successor_t dflt(const ripType _rip, LibraryFunctionType _calledFunction = LibraryFunctionTemplate::none)
		{
			return successor_t(succ_default, _rip, NULL,
					   _calledFunction);
		}
		static successor_t dflt(_CFGNode *i)
		{
			return successor_t(succ_default, ripType(), i,
					   LibraryFunctionTemplate::none);
		}
		static successor_t unroll(_CFGNode *i)
		{
			return successor_t(succ_unroll, ripType(), i,
					   LibraryFunctionTemplate::none);
		}
		static successor_t unroll(const ripType &_rip)
		{
			return successor_t(succ_unroll, _rip, NULL,
					   LibraryFunctionTemplate::none);
		}

		void visit(HeapVisitor &hv) {
			hv(instr);
		}
	};

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
			if (it->type == successor_t::succ_default) {
				assert(!res);
				res = &*it;
			}
		}
		return res;
	}
	void addBranch(const ripType &r) {
		successors.push_back(successor_t::branch(r));
	}
	void addCall(const ripType &r) {
		successors.push_back(successor_t::call(r));
	}
	void addDefault(const ripType &r, LibraryFunctionType t = LibraryFunctionTemplate::none) {
		assert(!getDefault());
		successors.push_back(successor_t::dflt(r, t));
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
class MemoryAccessIdentifierAllocator;
class StateMachineState;
StateMachine *storeCFGToMachine(Oracle *oracle,
				unsigned tid,
				CFGNode *root,
				MemoryAccessIdentifierAllocator &mai);
void probeCFGsToMachine(Oracle *oracle,
			unsigned tid,
			HashedSet<HashedPtr<CFGNode> > &roots,
			HashedSet<HashedPtr<const CFGNode> > &proximalNodes,
			MemoryAccessIdentifierAllocator &mai,
			std::set<StateMachine *> &out);
void dumpCFGToDot(const HashedSet<HashedPtr<CFGNode> > &allNodes, const char *fname);

#endif /* !CFGNODE_HPP__ */
