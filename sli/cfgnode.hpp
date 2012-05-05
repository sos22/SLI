#include "typesdb.hpp"

class Oracle;

class CFGNode : public GarbageCollected<CFGNode, &ir_heap>, public PrettyPrintable {
public:
	enum flavour_t { true_target_instr, dupe_target_instr, ordinary_instr } flavour;
	VexRip fallThroughRip;
	VexRip branchRip;
	CFGNode *fallThrough;
	CFGNode *branch;

	VexRip my_rip;

	CFGNode(const VexRip &rip,
		flavour_t _flavour)
		: flavour(_flavour),
		  my_rip(rip)
	{}

	CFGNode *dupe() {
		CFGNode *r = new CFGNode(my_rip,
					 flavour == true_target_instr ? dupe_target_instr : flavour);
		r->fallThroughRip = fallThroughRip;
		r->branchRip = branchRip;
		r->fallThrough = fallThrough;
		r->branch = branch;
		return r;
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%s: %s(%p), %s(%p)",
			my_rip.name(),
			fallThroughRip.name(),
			fallThrough,
			branchRip.name(),
			branch);
	}
	void visit(HeapVisitor &hv) {
		hv(fallThrough);
		hv(branch);
	}

	static CFGNode *forRip(Oracle *oracle, const VexRip &vr, flavour_t flavour);

	NAMED_CLASS
};

void printCFG(const CFGNode *cfg, const char *prefix, FILE *f);
void getStoreCFGs(const std::set<DynAnalysisRip> &, Oracle *,
		  CFGNode ***, int *);
