#include "sli.h"
#include "enforce_crash.hpp"

char *
input_expression::mkName() const
{
	return strdup(nameIRExpr(content));
}

input_expression::input_expression()
	: content(NULL)
{}

bool
input_expression::operator <(const input_expression &o) const
{
	return content < o.content;
}

bool
input_expression::operator==(const input_expression &o) const
{
	return content == o.content;
}

bool
input_expression::matches(const IRExpr *what) const
{
	return content == what;
}

const IRExpr *
input_expression::unwrap() const
{
	return content;
}

input_expression
input_expression::wrap(const IRExpr *what)
{
	input_expression e;
	e.content = what;
	return e;
}

std::pair<input_expression, bool>
input_expression::parse(const char *str, const char **suffix)
{
	IRExpr *res;
	if (parseIRExpr(&res, str, suffix)) {
		return std::pair<input_expression, bool>(
			input_expression::wrap(res), true);
	} else {
		return std::pair<input_expression, bool>(
			input_expression(), false);
	}
}

void
input_expression::visit(HeapVisitor &hv)
{
	hv(content);
}
