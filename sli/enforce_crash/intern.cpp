#include "sli.h"
#include "enforce_crash.hpp"

exprEvalPoint internmentState::intern(const exprEvalPoint &x) {
	return exprEvalPoint(x.invert, x.thread, intern(x.e));
}