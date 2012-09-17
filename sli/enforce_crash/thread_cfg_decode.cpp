#include "sli.h"
#include "enforce_crash.hpp"

Instruction<ThreadCfgLabel> *
ThreadCfgDecode::addCfg(const AbstractThread &tid, const CFGNode *node)
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
		case succ_default:
			work->addDefault(addCfg(tid, it->instr));
			break;
		case succ_branch:
			work->addBranch(addCfg(tid, it->instr));
			break;
		case succ_call:
			work->addCall(addCfg(tid, it->instr));
			break;
		case succ_unroll:
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
ThreadCfgDecode::addMachine(StateMachine *sm, ThreadAbstracter &abs)
{
	for (auto it = sm->cfg_roots.begin(); it != sm->cfg_roots.end(); it++)
		addCfg(abs.newThread(it->first), it->second);
}

void
CrashCfg::prettyPrint(FILE *f, bool verbose)
{
	fprintf(f, "\tCFG:\n");
	for (auto it = content.begin(); it != content.end(); it++) {
		auto *instr = it->second;
		fprintf(f, "\t\t%s: %s {", it->first.name(), instr->rip.name());
		bool done_one = false;
		for (auto it2 = instr->successors.begin();
		     it2 != instr->successors.end();
		     it2++) {
			if (!it2->instr)
				continue;
			if (done_one)
				fprintf(f, ", ");
			fprintf(f, "%s", it2->instr->label.name());
			done_one = true;
		}
		fprintf(f, "}");
		if (verbose) {
			fprintf(f, " [");
			for (unsigned x = 0; x < instr->len; x++) {
				if (x != 0)
					fprintf(f, " ");
				fprintf(f, "%02x", instr->content[x]);
			}
			fprintf(f, "]");
			if (instr->relocs.size() != 0) {
				fprintf(f, " relocs = [");
				for (auto it = instr->relocs.begin();
				     it != instr->relocs.end();
				     it++) {
					if (it != instr->relocs.begin())
						fprintf(f, ", ");
					if (auto rrr = dynamic_cast<RipRelativeRelocation<VexRip> *>(*it)) {
						fprintf(f, "rrr(at=%d, size=%d, target=%s, nr_imm=%d)",
							rrr->offset,
							rrr->size,
							rrr->target.name(),
							rrr->nrImmediateBytes);
					} else if (auto rrbr = dynamic_cast<RipRelativeBranchRelocation<VexRip> *>(*it)) {
						fprintf(f, "rrbr(at=%d, size=%d, target=%s)",
							rrbr->offset,
							rrbr->size,
							rrbr->target.name());
					} else {
						fprintf(f, "<bad reloc>");
					}
				}
				fprintf(f, "]");
			}
			if (instr->lateRelocs.size() != 0) {
				fprintf(f, " lateRelocs = [");
				for (auto it = instr->lateRelocs.begin();
				     it != instr->lateRelocs.end();
				     it++) {
					if (it != instr->lateRelocs.begin())
						fprintf(f, ", ");
					fprintf(f, "r(at=%d, size=%d, target=%s, nrImmediate=%d, %s)",
						(*it)->offset,
						(*it)->size,
						(*it)->target,
						(*it)->nrImmediateBytes,
						(*it)->relative ? "relative" : "absolute");
				}
				fprintf(f, "]");
			}
				
		}
		fprintf(f, "\n");
	}
}

bool
CrashCfg::parse(AddressSpace *as, const char *str, const char **suffix)
{
	if (!parseThisString("CFG:\n", str, &str))
		return false;
	const char *cursor = str;
	std::map<ThreadCfgLabel, std::pair<VexRip, std::vector<CfgLabel> > > content;
	while (1) {
		ThreadCfgLabel label;
		std::pair<VexRip, std::vector<CfgLabel> > value;
		if (!label.parse(cursor, &cursor) ||
		    !parseThisString(": ", cursor, &cursor) ||
		    !parseVexRip(&value.first, cursor, &cursor) ||
		    !parseThisString(" {", cursor, &cursor))
			break;
		while (1) {
			CfgLabel target(CfgLabel::uninitialised());
			if (!target.parse(cursor, &cursor))
				break;
			parseThisString(", ", cursor, &cursor);
			value.second.push_back(target);
		}
		if (!parseThisString("}\n", cursor, &cursor))
			break;
		content[label] = value;
	}
	for (auto it = content.begin(); it != content.end(); it++) {
		this->content[it->first] = Instruction<VexRip>::decode(
			it->first.label,
			as,
			it->second.first,
			NULL,
			expandJcc);
	}
	for (auto it = content.begin(); it != content.end(); it++) {
		auto it2 = this->content.find(it->first);
		assert(it2 != this->content.end());
		/* Now we need to match the successors we just
		   decoded up with the successors which are
		   provided by the parsed CFG. */
		Instruction<VexRip> *instr = it2->second;
		const AbstractThread &thread(it->first.thread);
		assert(instr != NULL);
		std::vector<CfgLabel> desiredSuccessors(it->second.second);
		std::vector<Instruction<VexRip>::successor_t> actualSuccessors(instr->successors);
		std::vector<bool> actualSuccessorsUsed;
		actualSuccessorsUsed.resize(actualSuccessors.size(), false);
		std::vector<Instruction<VexRip>::successor_t> resSuccessors;
		for (auto it = desiredSuccessors.begin();
		     it != desiredSuccessors.end();
		     it++) {
			auto it3 = this->content.find(ThreadCfgLabel(thread, *it));
			if (it3 == this->content.end())
				return false;
			Instruction<VexRip> *desiredTarget = it3->second;
			assert(desiredTarget != NULL);
			unsigned x;
			for (x = 0; x < actualSuccessors.size(); x++) {
				if (actualSuccessors[x].rip == desiredTarget->rip) {
					/* Let's use this one. */
					actualSuccessorsUsed[x] = true;
					switch (actualSuccessors[x].type) {
					case succ_default:
						resSuccessors.push_back(
							Instruction<VexRip>::successor_t::dflt(desiredTarget));
						break;
					case succ_branch:
						resSuccessors.push_back(
						Instruction<VexRip>::successor_t::branch(desiredTarget));
						break;
					case succ_call:
						resSuccessors.push_back(
							Instruction<VexRip>::successor_t::call(desiredTarget));
						break;
					case succ_unroll:
					/* Shouldn't be generated by the decoder */
						abort();
					}
					break;
				}
			}
			assert(x != actualSuccessors.size());
		}
		/* So now all of the desired successors have been
		   matched to actual successors, so they've been
		   classified as branch or default or call successors.
		   Now find any actual edges which haven't been used,
		   so that we can record that we need to kill them. */
		for (unsigned x = 0; x < actualSuccessors.size(); x++) {
			if (!actualSuccessorsUsed[x]) {
				assert(!actualSuccessors[x].instr);
				resSuccessors.push_back(actualSuccessors[x]);
			}
		}

		instr->successors = resSuccessors;
	}
	*suffix = cursor;
	return true;
}

void
CrashCfg::removeAllBut(const std::set<Instruction<VexRip> *> &retain)
{
	for (auto it = content.begin(); it != content.end(); ) {
		if (!retain.count(it->second))
			content.erase(it++);
		else
			it++;
	}
}

