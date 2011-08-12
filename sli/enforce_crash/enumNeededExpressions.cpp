#include "sli.h"
#include "enforce_crash.hpp"
#include "offline_analysis.hpp"

class EnumNeededExpressionsTransformer : public IRExprTransformer {
public:
	std::set<IRExpr *> &out;
	EnumNeededExpressionsTransformer(std::set<IRExpr *> &_out)
		: out(_out)
	{}
	IRExpr *transformIex(IRExpr::RdTmp *e) {
		abort(); /* Should all have been eliminated by now */
	}
	IRExpr *transformIex(IRExpr::Get *e) {
		out.insert(currentIRExpr());
		return NULL;
	}
	IRExpr *transformIex(IRExpr::Load *e) {
		out.insert(currentIRExpr());
		/* Note that we don't recurse into the address
		   calculation here.  We can always evaluate this
		   expression after seeing the load itself, regardless
		   of where the address came from. */
		return NULL;
	}
	IRExpr *transformIex(IRExpr::HappensBefore *e) {
		out.insert(currentIRExpr());
		/* Again, we don't recurse into the details of the
		   happens before expression, because we only need the
		   two instructions, and not details of their
		   side-effects. */
		return NULL;
	}
	IRExpr *transformIex(IRExpr::ClientCall *e) {
		out.insert(currentIRExpr());
		return NULL;
	}
};
void
enumerateNeededExpressions(IRExpr *e, std::set<IRExpr *> &out)
{
	EnumNeededExpressionsTransformer trans(out);
	trans.transformIRExpr(e);
}

