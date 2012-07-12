#ifndef CFGNODE_HPP__
#define CFGNODE_HPP__

#include "typesdb.hpp"
#include "library.hpp"
#include "genfix.hpp"

class Oracle;

typedef Instruction<VexRip> CFGNode;

void getStoreCFGs(CfgLabelAllocator &allocLabel,
		  const std::set<DynAnalysisRip> &, Oracle *,
		  CFGNode ***, int *);
bool getProbeCFGs(CfgLabelAllocator &allocLabel,
		  Oracle *oracle, const DynAnalysisRip &vr,
		  std::set<CFGNode *> &out,
		  std::set<const CFGNode *> &targetNodes);

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
			std::set<CFGNode *> &roots,
			std::set<const CFGNode *> &proximalNodes,
			MemoryAccessIdentifierAllocator &mai,
			std::set<StateMachine *> &out);
void dumpCFGToDot(const std::set<CFGNode *> &allNodes, const char *fname);

#endif /* !CFGNODE_HPP__ */
