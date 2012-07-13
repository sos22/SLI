#include "sli.h"
#include "enforce_crash.hpp"

Instruction<ThreadCfgLabel> *
ThreadCfgDecode::addCfg(int tid, const CFGNode *node)
{
	ThreadCfgLabel l(tid, node->label);
	auto it_did_insert = content.insert(std::pair<ThreadCfgLabel, Instruction<ThreadCfgLabel> *>(l, (Instruction<ThreadCfgLabel> *)0xf001ul));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;
	Instruction<ThreadCfgLabel> *work = new Instruction<ThreadCfgLabel>(-1, node->label);
	work->rip = ThreadCfgLabel(tid, node->label);
	work->successors.reserve(node->successors.size());
	for (auto it = node->successors.begin(); it != node->successors.end(); it++) {
		if (!it->instr)
			continue;
		switch (it->type) {
		case Instruction<ThreadCfgLabel>::successor_t::succ_default:
			work->addDefault(addCfg(tid, it->instr));
			break;
		case Instruction<ThreadCfgLabel>::successor_t::succ_branch:
			work->addBranch(addCfg(tid, it->instr));
			break;
		case Instruction<ThreadCfgLabel>::successor_t::succ_call:
			work->addCall(addCfg(tid, it->instr));
			break;
		case Instruction<ThreadCfgLabel>::successor_t::succ_unroll:
			work->successors.push_back(
				Instruction<ThreadCfgLabel>::successor_t::unroll(
					addCfg(tid, it->instr)));
			break;
		}
	}
	it->second = work;
	return work;
}

void
ThreadCfgDecode::addMachine(StateMachine *sm)
{
	assert(sm->origin.size() == 1);
	assert(sm->cfg_roots.size() == 1);
	addCfg(sm->origin[0].first, sm->cfg_roots[0]);
}
