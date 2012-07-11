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
printCFG(const _CFGNode<t> *cfg, FILE *f)
{
	cfgnode_tmpl::printCFG(cfg, f);
}

template <typename t> void
enumerateCFG(_CFGNode<t> *start, std::set<_CFGNode<t> *> &out)
{
	return cfgnode_tmpl::enumerateCFG(start, out);
}

