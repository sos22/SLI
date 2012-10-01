#include "sli.h"
#include "enforce_crash.hpp"
#include "offline_analysis.hpp"

class EnumNeededExpressionsTransformer : public IRExprTransformer {
public:
	std::set<IRExpr *> &out;
	EnumNeededExpressionsTransformer(std::set<IRExpr *> &_out)
		: out(_out)
	{}
	IRExpr *transformIex(IRExprGet *e) {
		out.insert(e);
		return NULL;
	}
	IRExpr *transformIex(IRExprHappensBefore *e) {
		out.insert(e);
		return NULL;
	}
	IRExpr *transformIex(IRExprEntryPoint *e) {
		out.insert(e);
		return NULL;
	}
};
void
enumerateNeededExpressions(IRExpr *e, std::set<IRExpr *> &out)
{
	EnumNeededExpressionsTransformer trans(out);
	trans.doit(e);
}

