#include "sli.h"
#include "enforce_crash.hpp"
#include "offline_analysis.hpp"

class EnumNeededExpressionsTransformer : public IRExprTransformer {
public:
	std::set<IRExpr *> &out;
	EnumNeededExpressionsTransformer(std::set<IRExpr *> &_out)
		: out(_out)
	{}
	IRExpr *transformIex(IRExprGet *) {
		out.insert(currentIRExpr());
		return NULL;
	}
	IRExpr *transformIex(IRExprHappensBefore *) {
		out.insert(currentIRExpr());
		return NULL;
	}
};
void
enumerateNeededExpressions(IRExpr *e, std::set<IRExpr *> &out)
{
	EnumNeededExpressionsTransformer trans(out);
	trans.doit(e);
}

