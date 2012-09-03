#include <ctype.h>
#include <queue>

#include "sli.h"
#include "cfgnode.hpp"
#include "libvex_parse.h"
#include "oracle.hpp"

#include "getStoreCFGs.cpp"

class named_string : public std::string, public Named {
	char *mkName() const {
		return strdup(c_str());
	}
};

typedef _CFGNode<named_string> cfg_node;

static bool
parseCfgFlavour(_getStoreCFGs::cfgflavour_store_t *out, const char *buf, const char **suffix)
{
	if (parseThisString("true", buf, suffix)) {
		*out = _getStoreCFGs::cfgs_flavour_true;
		return true;
	}
	if (parseThisString("dupe", buf, suffix)) {
		*out = _getStoreCFGs::cfgs_flavour_dupe;
		return true;
	}
	if (parseThisString("ordinary", buf, suffix)) {
		*out = _getStoreCFGs::cfgs_flavour_ordinary;
		return true;
	}
	return false;
}

static bool
parseWord(named_string *out, const char *buf, const char **suffix)
{
	while (!isspace(buf[0])) {
		out->push_back(buf[0]);
		buf++;
	}
	if (out->length() == 0)
		return false;
	*suffix = buf;
	return true;
}

static bool
parseNodeDecl(std::map<named_string, cfg_node *> &nodes,
	      std::map<const cfg_node *, _getStoreCFGs::cfgflavour_store_t> &cfgFlavours,
	      const char *buf,
	      const char **suffix)
{
	named_string label;
	_getStoreCFGs::cfgflavour_store_t flavour;
	if (!parseWord(&label, buf, &buf) ||
	    !parseThisChar(' ', buf, &buf) ||
	    !parseCfgFlavour(&flavour, buf, &buf) ||
	    !parseThisChar('\n', buf, suffix))
		return false;
	if (nodes.count(label))
		return false;
	cfg_node *n = new cfg_node(label, CfgLabel::uninitialised());
	nodes[label] = n;
	cfgFlavours[n] = flavour;
	return true;
}

static bool
parseEdgeDecl(std::map<named_string, cfg_node *> &nodes,
	      const char *buf,
	      const char **suffix)
{
	while (1) {
		named_string start, end;
		const char *p;
		if (!parseWord(&start, buf, &p) ||
		    !parseThisString(" -> ", p, &p) ||
		    !parseWord(&end, p, &p) ||
		    !parseThisChar('\n', p, &buf))
			break;
		cfg_node *s = nodes[start];
		cfg_node *e = nodes[end];
		if (!s || !e)
			return false;
		s->successors.push_back(cfg_node::successor_t::branch(e));
	}
	*suffix = buf;
	return true;
}

static bool
parseCFG(HashedSet<HashedPtr<cfg_node> > &roots,
	 std::map<const cfg_node *, _getStoreCFGs::cfgflavour_store_t> &flavours,
	 const char *buf, const char **suffix)
{
	std::map<named_string, cfg_node *> nodes;
	while (1) {
		if (!parseNodeDecl(nodes, flavours, buf, &buf))
			break;
	}
	if (!parseEdgeDecl(nodes, buf, &buf))
		return false;
	if (!parseThisString("Roots:\n", buf, &buf))
		return false;
	while (!parseThisString("End of roots\n", buf, suffix)) {
		if (!*buf)
			return false;
		named_string key;
		if (!parseWord(&key, buf, &buf) ||
		    !parseThisChar('\n', buf, &buf))
			return false;
		if (!nodes.count(key))
			return false;
		roots.insert(nodes[key]);
	}
	return true;
}

static void
read_cfg_and_depth(HashedSet<HashedPtr<cfg_node> > &roots, std::map<const cfg_node *, _getStoreCFGs::cfgflavour_store_t> &flavours, int *maxDepth, int fd)
{
	char *buf = readfile(fd);
	const char *suffix;
	const char *p = buf;
	if (!parseThisString("depth = ", p, &p) ||
	    !parseDecimalInt(maxDepth, p, &p) ||
	    !parseThisChar('\n', p, &p) ||
	    !parseCFG(roots, flavours, p, &suffix))
		errx(1, "cannot parse %s as test specification", buf);
	if (*suffix)
		warnx("trailing garbage after cfg: %s", suffix);
	free(buf);
}

static void
uniqueify_labels(HashedSet<HashedPtr<cfg_node> > &roots)
{
	HashedSet<HashedPtr<cfg_node> > allNodes;
	for (auto it = roots.begin(); !it.finished(); it.advance())
		enumerateCFG(it->get(), allNodes);
	std::map<named_string, int> counters;
	for (auto it = allNodes.begin(); !it.finished(); it.advance()) {
		auto it2 = counters.insert(std::pair<named_string, int>( (*it)->rip, 0) ).first;
		it2->second++;
		if (it2->second != 1) {
			int c = 1;
			while (c <= it2->second)
				c *= 10;
			c /= 10;
			while (c != 0) {
				(*it)->rip.push_back( ((it2->second / c) % 10) + '0' );
				c /= 10;
			}
		}
	}
}

static void
printCFG(HashedSet<HashedPtr<cfg_node> > &roots, std::map<const cfg_node *, _getStoreCFGs::cfgflavour_store_t> &flavours, FILE *f)
{
	HashedSet<HashedPtr<cfg_node> > allNodes;
	for (auto it = roots.begin(); !it.finished(); it.advance())
		enumerateCFG(it->get(), allNodes);
	HashedSet<HashedPtr<cfg_node> > defined;
	for (auto it = allNodes.begin(); !it.finished(); it.advance()) {
		const char *fl = NULL;
		auto it_fl = flavours.find(*it);
		assert(it_fl != flavours.end());
		switch ( it_fl->second ) {
		case _getStoreCFGs::cfgs_flavour_true:
			fl = "true";
			break;
		case _getStoreCFGs::cfgs_flavour_dupe:
			fl = "dupe";
			break;
		case _getStoreCFGs::cfgs_flavour_ordinary:
			fl = "ordinary";
			break;
		}
		assert(fl != NULL);
		fprintf(f, "%s %s\n", (*it)->rip.c_str(), fl);
	}
	for (auto it = allNodes.begin(); !it.finished(); it.advance()) {
		cfg_node *n = *it;
		for (auto it = n->successors.begin(); it != n->successors.end(); it++) {
			if (it->instr)
				fprintf(f, "%s -> %s\n", n->rip.c_str(), it->instr->rip.c_str());
		}
	}
	fprintf(f, "Roots:\n");
	for (auto it = roots.begin(); !it.finished(); it.advance())
		fprintf(f, "%s\n", (*it)->rip.c_str());
	fprintf(f, "End of roots\n");
}

int
main()
{
	init_sli();

	HashedSet<HashedPtr<cfg_node> > roots;
	std::map<const cfg_node *, _getStoreCFGs::cfgflavour_store_t> flavours;
	int maxPathLength;
	CfgLabelAllocator allocLabel;
	read_cfg_and_depth(roots, flavours, &maxPathLength, 0);
	_getStoreCFGs::performUnrollAndCycleBreak(allocLabel, roots, flavours, maxPathLength);
	uniqueify_labels(roots);
	printCFG(roots, flavours, stdout);

	return 0;
}
