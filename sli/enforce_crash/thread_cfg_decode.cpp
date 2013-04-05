#include "sli.h"
#include "enforce_crash.hpp"

Instruction<ThreadCfgLabel> *
ThreadAbstracter::instr_iterator::get() const
{
	return cfg.findInstr(underlying.get());
}

void
happensBeforeEdge::prettyPrint(FILE *f) const
{
	fprintf(f, "\t\thb%d: %s <-< %s\n", msg_id, before->rip.name(),
		after->rip.name());
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
	    !parseThisString("\n", str, &str)) {
		return NULL;
	}
	bbdd *cond;
	if (parseThisString("Side condition =\n", str, &str)) {
		if (!bbdd::parse(scope, &cond, str, &str)) {
			return NULL;
		}
	} else if (parseThisString("No side condition\n", str, &str)) {
		cond = NULL;
	} else {
		return NULL;
	}
	*suffix = str;
	return new happensBeforeEdge(cfg.findInstr(before),
				     cfg.findInstr(after),
				     cond,
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
		if (hbe->before && hbe->after) {
			(*this)[hbe->before->rip].insert(hbe);
			(*this)[hbe->after->rip].insert(hbe);
		}
	}
	*suffix = str;
	return true;
}
