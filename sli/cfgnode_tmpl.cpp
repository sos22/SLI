#ifdef NDEBUG
#define debug_find_roots 0
#else
static int debug_find_roots = 0;
#endif

/* This ends up getting #include'd in various places so as to instantiate the
   templates.  Sigh. */
namespace cfgnode_tmpl {

template <typename t> static void
resolveReferences(const std::map<t, _CFGNode<t> *> &m, _CFGNode<t> *what)
{
	assert(what);

	struct {
		const std::map<t, CFGNode *> *m;
		CFGNode *operator()(const t &vr) {
			if (!vr.isValid())
				return NULL;
			auto it = m->find(vr);
			if (it != m->end())
				return it->second;
			else
				return NULL;
		}
	} resolveBranch = {&m};

	what->fallThrough.second = resolveBranch(what->fallThrough.first);
	for (auto it = what->branches.begin(); it != what->branches.end(); it++)
		it->second = resolveBranch(it->first);
}

template <typename t> static void
resolveReferences(std::map<t, _CFGNode<t> *> &m)
{
	if (TIMEOUT)
		return;
	for (auto it = m.begin(); it != m.end(); it++)
		cfgnode_tmpl::resolveReferences(m, it->second);
}

template <typename t> static void
enumerateCFG(_CFGNode<t> *start, std::set<_CFGNode<t> *> &out)
{
	std::vector<_CFGNode<t> *> pending;
	pending.push_back(start);
	while (!pending.empty()) {
		_CFGNode<t> *n = pending.back();
		pending.pop_back();
		if (!out.insert(n).second)
			continue;
		if (n->fallThrough.second)
			pending.push_back(n->fallThrough.second);
		for (auto it = n->branches.begin(); it != n->branches.end(); it++)
			if (it->second)
				pending.push_back(it->second);
	}
}

template <typename t> static void
trimUninterestingCFGNodes(std::set<_CFGNode<t> *> &roots,
			  const std::map<const _CFGNode<t> *, cfgflavour_t> &flavours)
{
	std::set<_CFGNode<t> *> interesting(roots);
	std::set<_CFGNode<t> *> allCFGNodes;
	for (auto it = roots.begin(); !TIMEOUT && it != roots.end(); it++)
		cfgnode_tmpl::enumerateCFG(*it, allCFGNodes);
	bool progress = true;
	while (!TIMEOUT && progress) {
		progress = false;
		for (auto it = allCFGNodes.rbegin(); it != allCFGNodes.rend(); it++) {
			_CFGNode<t> *n = *it;
			if (interesting.count(n))
				continue;
			bool isInteresting = false;
			auto fl_it = flavours.find(n);
			assert(fl_it != flavours.end());
			if ( fl_it->second == cfg_flavour_true ||
			     fl_it->second == cfg_flavour_dupe ||
			     (n->fallThrough.second && interesting.count(n->fallThrough.second)))
				isInteresting = true;
			for (auto it2 = n->branches.begin(); !isInteresting && it2 != n->branches.end(); it2++)
				if (it2->second && interesting.count(it2->second))
					isInteresting = true;
			if (isInteresting) {
				interesting.insert(n);
				progress = true;
			}
		}
	}
	for (auto it = allCFGNodes.begin(); !TIMEOUT && it != allCFGNodes.end(); it++) {
		_CFGNode<t> *n = *it;
		if (n->fallThrough.second && !interesting.count(n->fallThrough.second))
			n->fallThrough.second = NULL;
		for (auto it2 = n->branches.begin(); it2 != n->branches.end(); it2++)
			if (it2->second && !interesting.count(it2->second))
				it2->second = NULL;
	}
}

template <typename t> static void
removeReachable(std::set<_CFGNode<t> *> &out, const _CFGNode<t> *n)
{
	std::vector<const _CFGNode<t> *> pending;
	pending.push_back(n);
	while (!pending.empty()) {
		const _CFGNode<t> *n = pending.back();
		pending.pop_back();
		if (TIMEOUT)
			return;
		if (!out.erase(const_cast<CFGNode *>(n))) {
			/* Already not-present */
			continue;
		}
		if (n->fallThrough.second)
			pending.push_back(n->fallThrough.second);
		for (auto it = n->branches.begin(); it != n->branches.end(); it++)
			if (it->second)
				pending.push_back(it->second);
	}
}

template <typename t> static void
removeReachable(std::set<_CFGNode<t> *> &out, const std::set<_CFGNode<t> *> &roots)
{
	for (auto it = roots.begin(); it != roots.end(); it++)
		removeReachable(out, *it);
}

template <typename t> static int
distanceToTrueInstr(const _CFGNode<t> *n, const std::map<const _CFGNode<t> *, cfgflavour_t> &flavours)
{
	std::set<const _CFGNode<t> *> successors;
	std::queue<const _CFGNode<t> *> pendingAtCurrentDepth;
	int depth = 0;
	pendingAtCurrentDepth.push(n);
	while (1) {
		std::queue<const _CFGNode<t> *> pendingAtNextDepth;
		assert(pendingAtNextDepth.empty());
		while (!pendingAtCurrentDepth.empty()) {
			const _CFGNode<t> *n = pendingAtCurrentDepth.front();
			pendingAtCurrentDepth.pop();
			auto it = flavours.find(n);
			assert(it != flavours.end());
			if (it->second == cfg_flavour_true)
				return depth;
			if (!successors.insert(n).second)
				continue;
			for (auto it = n->branches.begin(); it != n->branches.end(); it++)
				if (it->second)
					pendingAtNextDepth.push(it->second);
			if (n->fallThrough.second)
				pendingAtNextDepth.push(n->fallThrough.second);
		}
		pendingAtCurrentDepth = pendingAtNextDepth;
		depth++;
	}
	/* Can't reach any true instructions -> shouldn't happen. */
	abort();
}

template <typename t> static void
operator|=(std::set<t> &a, const std::set<t> &b)
{
	for (auto it = b.begin(); it != b.end(); it++)
		a.insert(*it);
}

/* Populate @roots with nodes such that, for every node in @m, there
   is a path from something in @roots which reaches @m.  We try to
   make @roots as small as possible, but ony guarantee to produce a
   minimal result if @m is acyclic. */
template <typename t> static void
findRoots(const std::set<_CFGNode<t> *> &allNodes,
	  const std::map<const _CFGNode<t> *, cfgflavour_t> &cfgFlavours,
	  std::set<_CFGNode<t> *> &roots)
{
	std::set<_CFGNode<t> *> currentlyUnrooted(allNodes);

	if (debug_find_roots) {
		printf("findRoots():\n");
		for (auto it = allNodes.begin(); it != allNodes.end(); it++) {
			printf("\t%p -> ", *it);
			if ((*it)->fallThrough.second)
				printf("%p, ", (*it)->fallThrough.second);
			for (auto it2 = (*it)->branches.begin();
			     it2 != (*it)->branches.end();
			     it2++)
				printf("%p, ", it2->second);
			printf("\n");
		}
	}

	/* First rule: if something in @currentlyUnrooted cannot be
	   reached from any node in @currentlyUnrooted then that node
	   should definitely be a root. */
	std::set<_CFGNode<t> *> newRoots = currentlyUnrooted;
	for (auto it = allNodes.begin();
	     it != allNodes.end();
	     it++) {
		_CFGNode<t> *n = *it;
		if (n->fallThrough.second) {
			newRoots.erase(n->fallThrough.second);
			if (debug_find_roots)
				printf("%p is not a root because of %p\n", n->fallThrough.second,
				       n);
		}
		for (auto it2 = n->branches.begin(); it2 != n->branches.end(); it2++)
			if (it2->second) {
				if (debug_find_roots)
					printf("%p is not a root because of %p\n",
					       it2->second, n);
				newRoots.erase(it2->second);
			}
	}

	if (debug_find_roots) {
		printf("Basic root set: ");
		for (auto it = newRoots.begin(); it != newRoots.end(); it++)
			printf("%p, ", *it);
		printf("\n");
	}

	removeReachable(currentlyUnrooted, newRoots);
	roots |= newRoots;
	while (!TIMEOUT && !currentlyUnrooted.empty()) {
		/* Nasty case: everything in @currentlyUnrooted is
		   part of a cycle in @currentlyUnrooted.  Try to grab
		   something which is as far as possible away from the
		   first true-flavoured instruction.  That tends to
		   give us the most useful information. */
		_CFGNode<t> *best_node;
		int best_distance;
		best_node = NULL;
		best_distance = -1;
		for (auto it = currentlyUnrooted.begin(); it != currentlyUnrooted.end(); it++) {
			int n = distanceToTrueInstr(*it, cfgFlavours);
			if (n > best_distance) {
				best_distance = n;
				best_node = *it;
			}
		}

		if (debug_find_roots)
			printf("Selected cycle-breaking root %p (%d)\n",
			       best_node, best_distance);
		assert(best_node != NULL);
		roots.insert(best_node);
		removeReachable(currentlyUnrooted, best_node);
	}
}

template <typename t> static void
findRoots(const std::map<t, _CFGNode<t> *> &m, std::set<_CFGNode<t> *> &roots)
{
	std::set<_CFGNode<t> *> allNodes;
	for (auto it = m.begin(); it != m.end(); it++)
		allNodes.insert(it->second);
	cfgnode_tmpl::findRoots(allNodes, roots);
}

template <typename t> static void
dumpCFGToDot(const std::set<_CFGNode<t> *> &roots, FILE *f)
{
	std::set<_CFGNode<t> *> allNodes;
	for (auto it = roots.begin(); it != roots.end(); it++)
		cfgnode_tmpl::enumerateCFG(*it, allNodes);

	fprintf(f, "digraph {\n");
	for (auto it = allNodes.begin(); it != allNodes.end(); it++) {
		_CFGNode<t> *n = *it;
		fprintf(f, "n%p [label=\"%p\"", n, n);
		if (roots.count(n))
			fprintf(f, ", shape=box");
		fprintf(f, "]\n");
		if (n->fallThrough.second)
			fprintf(f, "n%p -> n%p [color=blue]\n", n, n->fallThrough.second);
		for (auto it = n->branches.begin();
		     it != n->branches.end();
		     it++)
			if (it->second)
				fprintf(f, "n%p -> n%p [color=red]\n", n, it->second);
	}
	fprintf(f, "}\n");
}

template <typename t> static void
dumpCFGToDot(const std::set<_CFGNode<t> *> &allNodes, const char *fname)
{
	FILE *f = fopen(fname, "w");
	if (!f) {
		printf("can't open %s\n", fname);
		return;
	}
	cfgnode_tmpl::dumpCFGToDot(allNodes, f);
	fclose(f);
}

template <typename t> static void
printCFG(const _CFGNode<t> *cfg, FILE *f)
{
	std::vector<const _CFGNode<t> *> pending;
	std::set<const _CFGNode<t> *> done;

	pending.push_back(cfg);
	while (!pending.empty()) {
		cfg = pending.back();
		pending.pop_back();
		if (done.count(cfg))
			continue;
		fprintf(f, "%p: ", cfg);
		cfg->prettyPrint(f);
		if (cfg->fallThrough.second)
			pending.push_back(cfg->fallThrough.second);
		for (auto it = cfg->branches.begin();
		     it != cfg->branches.end();
		     it++)
			if (it->second)
				pending.push_back(it->second);
		done.insert(cfg);
	}
}

/* End of namespace cfgnode_tmpl */
}

template <typename t> _CFGNode<t> *
_CFGNode<t>::forRip(Oracle *oracle, const VexRip &vr)
{
	IRSB *irsb = oracle->getIRSBForRip(vr);
	if (!irsb)
		return NULL;
	_CFGNode *work = new _CFGNode(vr, LibraryFunctionTemplate::none);
	int x;
	for (x = 1; x < irsb->stmts_used && irsb->stmts[x]->tag != Ist_IMark; x++) {
		if (irsb->stmts[x]->tag == Ist_Exit)
			work->branches.push_back(
				_CFGNode::successor_t(((IRStmtExit *)irsb->stmts[x])->dst.rip,
						     NULL));
	}
	if (x == irsb->stmts_used) {
		if (irsb->jumpkind == Ijk_Ret) {
			work->fallThrough.first = vr;
			work->fallThrough.first.rtrn();
		} else if (irsb->jumpkind == Ijk_Call) {
			if (irsb->next_is_const) {
				if (oracle->isPltCall(irsb->next_const.rip)) {
					work->libraryFunction = oracle->identifyLibraryCall(irsb->next_const.rip);
					work->fallThrough.first = extract_call_follower(irsb);
				} else {
					work->branches.push_back(
						_CFGNode::successor_t(irsb->next_const.rip,
								     NULL));
				}
			} else {
				std::vector<VexRip> b;
				oracle->getInstrCallees(vr, b);
				for (auto it = b.begin(); it != b.end(); it++)
					work->branches.push_back(
						_CFGNode::successor_t(*it, NULL));
			}
		} else if (irsb->next_is_const) {
			work->fallThrough.first = irsb->next_const.rip;
		} else {
			/* Note that the oracle has a slightly
			   different idea of fall-throughs to
			   us: it considers the targets of a
			   dynamic branch to be fall-through
			   targets, whereas we consider them
			   to be branch targets. */
			std::vector<VexRip> b;
			oracle->getInstrFallThroughs(vr, b);
			for (auto it = b.begin(); it != b.end(); it++)
				work->branches.push_back(
					_CFGNode::successor_t(*it, NULL));
		}
	} else {
		assert(irsb->stmts[x]->tag == Ist_IMark);
		work->fallThrough.first = ((IRStmtIMark *)irsb->stmts[x])->addr.rip;
	}
	return work;
}

template <typename t> void
findRoots(const std::map<t, _CFGNode<t> *> &m, std::set<_CFGNode<t> *> &roots)
{
	cfgnode_tmpl::findRoots(m, roots);
}

template <typename t> void
findRoots(const std::set<_CFGNode<t> *> &allNodes, const std::map<const _CFGNode<t> *, cfgflavour_t> &cfgFlavours, std::set<_CFGNode<t> *> &roots)
{
	cfgnode_tmpl::findRoots(allNodes, cfgFlavours, roots);
}

template <typename t> void
resolveReferences(const std::map<t, _CFGNode<t> *> &m, _CFGNode<t> *what)
{
	cfgnode_tmpl::resolveReferences(m, what);
}

template <typename t> void
resolveReferences(std::map<t, _CFGNode<t> *> &m)
{
	cfgnode_tmpl::resolveReferences(m);
}

template <typename t> void
trimUninterestingCFGNodes(std::set<_CFGNode<t> *> &roots,
			  const std::map<const _CFGNode<t> *, cfgflavour_t> &flavours)
{
	cfgnode_tmpl::trimUninterestingCFGNodes(roots, flavours);
}

template <typename t> void
printCFG(const _CFGNode<t> *cfg, FILE *f)
{
	cfgnode_tmpl::printCFG(cfg, f);
}

template <typename t> void
dumpCFGToDot(const std::set<_CFGNode<t> *> &allNodes, const char *fname)
{
	cfgnode_tmpl::dumpCFGToDot(allNodes, fname);
}

template <typename t> void
dumpCFGToDot(const std::set<_CFGNode<t> *> &allNodes, FILE *f)
{
	cfgnode_tmpl::dumpCFGToDot(allNodes, f);
}

template <typename t> void
enumerateCFG(_CFGNode<t> *start, std::set<_CFGNode<t> *> &out)
{
	return cfgnode_tmpl::enumerateCFG(start, out);
}

