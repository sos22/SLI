#include "typesdb.hpp"

class Oracle;

class CFGNode : public GarbageCollected<CFGNode, &ir_heap>, public PrettyPrintable {
public:
	enum flavour_t { true_target_instr, dupe_target_instr, ordinary_instr } flavour;
	struct successor_t : public std::pair<VexRip, CFGNode *> {
		void prettyPrint(FILE *f) const {
			fprintf(f, "%s(%p)", first.name(), second);
		}
		successor_t(const VexRip &vr, CFGNode *cfg)
			: std::pair<VexRip, CFGNode *> (vr, cfg)
		{}
		successor_t()
			: std::pair<VexRip, CFGNode *> ()
		{}
	};
	successor_t fallThrough;
	std::vector<successor_t> branches;

	VexRip my_rip;

	CFGNode(const VexRip &rip,
		flavour_t _flavour)
		: flavour(_flavour),
		  my_rip(rip)
	{}

	CFGNode *dupe() {
		CFGNode *r = new CFGNode(my_rip,
					 flavour == true_target_instr ? dupe_target_instr : flavour);
		r->fallThrough = fallThrough;
		r->branches = branches;
		return r;
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%s: ", my_rip.name());
		fallThrough.prettyPrint(f);
		if (branches.size() != 0) {
			fprintf(f, " {");
			for (auto it = branches.begin(); it != branches.end(); it++) {
				if (it != branches.begin())
					fprintf(f, ", ");
				it->prettyPrint(f);
			}
			fprintf(f, "}");
		}
	}
	void visit(HeapVisitor &hv) {
		hv(fallThrough.second);
		for (auto it = branches.begin(); it != branches.end(); it++)
			hv(it->second);
	}

	static CFGNode *forRip(Oracle *oracle, const VexRip &vr, flavour_t flavour);

	NAMED_CLASS
};

void printCFG(const CFGNode *cfg, const char *prefix, FILE *f);
void getStoreCFGs(const std::set<DynAnalysisRip> &, Oracle *,
		  CFGNode ***, int *);
