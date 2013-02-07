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

happensBeforeEdge *
happensBeforeEdge::parse(CrashCfg &cfg, const char *str, const char **suffix)
{
	ThreadCfgLabel before;
	ThreadCfgLabel after;
	unsigned msg_id;
	if (!parseDecimalUInt(&msg_id, str, &str) ||
	    !parseThisString(": ", str, &str) ||
	    !before.parse(str, &str) ||
	    !parseThisString(" <-< ", str, &str) ||
	    !after.parse(str, &str) ||
	    !parseThisString(" {", str, &str))
		return NULL;
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
	*suffix = str;
	return new happensBeforeEdge(cfg.findInstr(before), cfg.findInstr(after), content, msg_id);
}
