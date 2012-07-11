#ifndef CFGNODE_HPP__
#define CFGNODE_HPP__

#include "typesdb.hpp"
#include "library.hpp"

class Oracle;

template <typename key_type = VexRip>
class _CFGNode : public GarbageCollected<_CFGNode<key_type>, &ir_heap>, public PrettyPrintable {
public:
	struct successor_t : public std::pair<key_type, _CFGNode<key_type> *> {
		void prettyPrint(FILE *f) const {
			fprintf(f, "%s(%p)", this->first.name(), this->second);
		}
		successor_t(const key_type &vr, _CFGNode<key_type> *cfg)
			: std::pair<key_type, _CFGNode<key_type> *> (vr, cfg)
		{}
		successor_t()
			: std::pair<key_type, _CFGNode<key_type> *> ()
		{}
	};
	successor_t fallThrough;
	std::vector<successor_t> branches;

	LibraryFunctionType libraryFunction;
	key_type my_rip;

	_CFGNode(const key_type &rip,
		 LibraryFunctionType _libraryFunction)
		: libraryFunction(_libraryFunction),
		  my_rip(rip)
	{}

	_CFGNode *dupe() {
		_CFGNode *r = new _CFGNode(my_rip,
					   libraryFunction);
		r->fallThrough = fallThrough;
		r->branches = branches;
		return r;
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%s: ", my_rip.name());
		fallThrough.prettyPrint(f);
		if (branches.size() != 0) {
			fprintf(f, " {");
			for (auto it = branches.begin(); it != branches.end(); it++) {
				if (it != branches.begin())
					fprintf(f, ", ");
				it->prettyPrint(f);
			}
			fprintf(f, "}");
		}
		if (libraryFunction != LibraryFunctionTemplate::none) {
			fprintf(f, " (");
			LibraryFunctionTemplate::pp(libraryFunction, f);
			fprintf(f, ")");
		}
		fprintf(f, "\n");
	}
	void visit(HeapVisitor &hv) {
		hv(fallThrough.second);
		for (auto it = branches.begin(); it != branches.end(); it++)
			hv(it->second);
	}

	static _CFGNode *forRip(Oracle *oracle, const VexRip &vr);

	NAMED_CLASS
};

enum cfgflavour_t { cfg_flavour_true, cfg_flavour_dupe, cfg_flavour_ordinary };

typedef _CFGNode<VexRip> CFGNode;

void getStoreCFGs(const std::set<DynAnalysisRip> &, Oracle *,
		  CFGNode ***, int *);
bool getProbeCFGs(Oracle *oracle, const DynAnalysisRip &vr,
		  std::set<CFGNode *> &out);

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
void probeCFGsToMachine(Oracle *oracle, unsigned tid, std::set<CFGNode *> &roots,
			const DynAnalysisRip &proximalRip,
			MemoryAccessIdentifierAllocator &mai,
			std::set<StateMachine *> &out);

#endif /* !CFGNODE_HPP__ */
