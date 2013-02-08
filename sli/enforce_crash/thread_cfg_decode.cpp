#include "sli.h"
#include "enforce_crash.hpp"

Instruction<ThreadCfgLabel> *
ThreadAbstracter::instr_iterator::get() const
{
	return cfg.findInstr(underlying.get());
}

predecessorMapT::predecessorMapT(CrashCfg &cfg)
{
	for (auto it = cfg.begin(); !it.finished(); it.advance()) {
		auto v = it.instr();
		if (!count(v))
			(*this)[v];
		for (auto it2 = v->successors.begin(); it2 != v->successors.end(); it2++)
			if (it2->instr)
				(*this)[it2->instr].insert(v);
	}
}

void
happensBeforeEdge::prettyPrint(FILE *f) const
{
	fprintf(f, "\t\thb%d: %s <-< %s {", msg_id, before->rip.name(),
		after->rip.name());
	for (auto it = content.begin(); !it.finished(); it.advance()) {
		if (it.started()) {
			fprintf(f, ", ");
		}
		fprintf(f, "%s", it.get().name());
	}
	fprintf(f, "}\n");
	if (sideCondition) {
		fprintf(f, "\t\tSide condition =\n");
		sideCondition->prettyPrint(f);
	} else {
		fprintf(f, "\t\tNo side condition\n");
	}
}

happensBeforeEdge *
happensBeforeEdge::parse(bbdd::scope *scope, CrashCfg &cfg, const char *str, const char **suffix)
{
	unsigned msgId;
	ThreadCfgLabel before;
	ThreadCfgLabel after;
	if (!parseThisString("hb", str, &str) ||
	    !parseDecimalUInt(&msgId, str, &str) ||
	    !parseThisString(": ", str, &str) ||
	    !before.parse(str, &str) ||
	    !parseThisString(" <-< ", str, &str) ||
	    !after.parse(str, &str) ||
	    !parseThisString(" {", str, &str)) {
		return NULL;
	}
	sane_vector<input_expression> content;
	if (!parseThisChar('}', str, &str)) {
		while (1) {
			std::pair<input_expression, bool> a(input_expression::parse(str, &str));
			if (!a.second) {
				return NULL;
			}
			content.push_back(a.first);
			if (parseThisChar('}', str, &str)) {
				break;
			}
			if (!parseThisString(", ", str, &str)) {
				return NULL;
			}
		}
	}

	bbdd *cond;
	if (parseThisString("\nSide condition =\n", str, &str)) {
		if (!bbdd::parse(scope, &cond, str, &str)) {
			return NULL;
		}
	} else if (parseThisString("\nNo side condition\n", str, &str)) {
		cond = NULL;
	} else {
		return NULL;
	}
	*suffix = str;
	return new happensBeforeEdge(cfg.findInstr(before),
				     cfg.findInstr(after),
				     cond,
				     content,
				     msgId);
}
	    
void
happensBeforeMapT::prettyPrint(FILE *f) const
{
	std::set<happensBeforeEdge *> allEdges;
	for (auto it = begin(); it != end(); it++) {
		allEdges |= it->second;
	}
	fprintf(f, "\thappensBeforeMap:\n");
	for (auto it = allEdges.begin();
	     it != allEdges.end();
	     it++) {
		(*it)->prettyPrint(f);
	}
}

bool
happensBeforeMapT::parse(bbdd::scope *scope, CrashCfg &cfg, const char *str, const char **suffix)
{
	if (!parseThisString("happensBeforeMap:\n", str, &str)) {
		return false;
	}

	while (1) {
		auto hbe = happensBeforeEdge::parse(scope, cfg, str, &str);
		if (!hbe) {
			break;
		}
		(*this)[hbe->before->rip].insert(hbe);
		(*this)[hbe->after->rip].insert(hbe);
	}
	*suffix = str;
	return true;
}
