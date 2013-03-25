#include "sli.h"
#include "enforce_crash.hpp"

char *
input_expression::mkName() const
{
	switch (tag) {
	case inp_entry_point:
		return my_asprintf("entry(%d, %s)", thread, label1.name());
	case inp_control_flow:
		return my_asprintf("control_flow(%d, %s, %s)",
				   thread,
				   label1.name(),
				   label2.name());
	case inp_register:
		return my_asprintf("register(%d, %d)",
				   thread,
				   vex_offset);
	}
	abort();
}

input_expression::input_expression(unsigned _thread, unsigned _vex_offset)
	: tag(inp_register),
	  thread(_thread),
	  vex_offset(_vex_offset),
	  label1(CfgLabel::uninitialised()),
	  label2(CfgLabel::uninitialised())
{}
input_expression::input_expression(unsigned _thread, const CfgLabel &_label1)
	: tag(inp_entry_point),
	  thread(_thread),
	  vex_offset(-1),
	  label1(_label1),
	  label2(CfgLabel::uninitialised())
{}
input_expression::input_expression(unsigned _thread, const CfgLabel &_label1, const CfgLabel &_label2)
	: tag(inp_control_flow),
	  thread(_thread),
	  vex_offset(-1),
	  label1(_label1),
	  label2(_label2)
{}

bool
input_expression::operator < (const input_expression &o) const
{
	if (tag < o.tag) {
		return true;
	} else if (tag > o.tag) {
		return false;
	} else if (thread < o.thread) {
		return true;
	} else if (thread > o.thread) {
		return false;
	}

	switch (tag) {
	case inp_entry_point:
		return label1 < o.label1;
	case inp_control_flow:
		if (label1 < o.label1) {
			return true;
		} else if (o.label1 < label1) {
			return false;
		} else {
			return label2 < o.label2;
		}
	case inp_register:
		return vex_offset < o.vex_offset;
	}
	abort();
}

bool
input_expression::operator ==(const input_expression &o) const
{
	if (tag != o.tag || thread != o.thread) {
		return false;
	}
	switch (tag) {
	case inp_entry_point:
		return label1 == o.label1;
	case inp_control_flow:
		return label1 == o.label1 && label2 == o.label2;
	case inp_register:
		return vex_offset == o.vex_offset;
	}
	abort();
}
bool
input_expression::operator !=(const input_expression &o) const
{
	return !(*this == o);
}

bool
input_expression::matches(const IRExpr *what) const
{
	switch (what->tag) {
	case Iex_Get:
		return *this == registr((const IRExprGet *)what);
	case Iex_ControlFlow:
		return *this == control_flow((const IRExprControlFlow *)what);
	case Iex_EntryPoint:
		return *this == entry_point((const IRExprEntryPoint *)what);
	default:
		return false;
	}
}

std::pair<input_expression, bool>
input_expression::parse(const char *str, const char **suffix)
{
	if (parseThisString("entry(", str, &str)) {
		unsigned thread;
		CfgLabel label(CfgLabel::uninitialised());
		if (!parseDecimalUInt(&thread, str, &str) ||
		    !parseThisString(", ", str, &str) ||
		    !label.parse(str, &str) ||
		    !parseThisChar(')', str, suffix)) {
			return std::pair<input_expression, bool>
				(input_expression(), false);
		}
		return std::pair<input_expression, bool>
			(input_expression(thread, label), true);
	} else if (parseThisString("control_flow(", str, &str)) {
		unsigned thread;
		CfgLabel label1(CfgLabel::uninitialised());
		CfgLabel label2(CfgLabel::uninitialised());
		if (!parseDecimalUInt(&thread, str, &str) ||
		    !parseThisString(", ", str, &str) ||
		    !label1.parse(str, &str) ||
		    !parseThisString(", ", str, &str) ||
		    !label2.parse(str, &str) ||
		    !parseThisChar(')', str, suffix)) {
			return std::pair<input_expression, bool>
				(input_expression(), false);
		}
		return std::pair<input_expression, bool>
			(input_expression(thread, label1, label2), true);
	} else if (parseThisString("register(", str, &str)) {
		unsigned thread;
		unsigned vex_offset;
		if (!parseDecimalUInt(&thread, str, &str) ||
		    !parseThisString(", ", str, &str) ||
		    !parseDecimalUInt(&vex_offset, str, &str) ||
		    !parseThisChar(')', str, suffix)) {
			return std::pair<input_expression, bool>
				(input_expression(), false);
		}
		return std::pair<input_expression, bool>
			(input_expression(thread, vex_offset), true);
	} else {
		return std::pair<input_expression, bool>
			(input_expression(), false);
	}
}

input_expression
input_expression::registr(const IRExprGet *ieg)
{
	assert(ieg->reg.isReg());
	return input_expression(ieg->reg.tid(),
				ieg->reg.asReg());
}

input_expression
input_expression::control_flow(const IRExprControlFlow *ieg)
{
	return input_expression(ieg->thread,
				ieg->cfg1,
				ieg->cfg2);
}

input_expression
input_expression::entry_point(const IRExprEntryPoint *ieg)
{
	return input_expression(ieg->thread, ieg->label);
}
