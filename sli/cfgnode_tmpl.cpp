/* This ends up getting #include'd in various places so as to instantiate the
   templates.  Sigh. */
namespace cfgnode_tmpl {

template <typename t> static void
resolveReferences(const std::map<t, _CFGNode<t> *> &m, _CFGNode<t> *what)
{
	assert(what);

	struct {
		const std::map<t, CFGNode *> *m;
		_CFGNode<t> *operator()(const t &vr) {
			if (!vr.isValid())
				return NULL;
			auto it = m->find(vr);
			if (it != m->end())
				return it->second;
			else
				return NULL;
		}
	} resolveBranch = {&m};

	for (auto it = what->successors.begin(); it != what->successors.end(); it++)
		it->instr = resolveBranch(it->rip);
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
enumerateCFG(_CFGNode<t> *start, HashedSet<HashedPtr<_CFGNode<t> > > &out)
{
	std::vector<_CFGNode<t> *> pending;
	pending.push_back(start);
	while (!pending.empty()) {
		_CFGNode<t> *n = pending.back();
		pending.pop_back();
		if (!out._insert(n))
			continue;
		for (auto it = n->successors.begin(); it != n->successors.end(); it++)
			if (it->instr)
				pending.push_back(it->instr);
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
		for (auto it = cfg->successors.begin();
		     it != cfg->successors.end();
		     it++)
			if (it->instr)
				pending.push_back(it->instr);
		done.insert(cfg);
	}
}

/* End of namespace cfgnode_tmpl */
}

template <typename t> _CFGNode<t> *
CfgNodeForRip(const CfgLabel &label, Oracle *oracle, const VexRip &vr)
{
	IRSB *irsb = oracle->getIRSBForRip(vr);
	if (!irsb)
		return NULL;
	_CFGNode<t> *work = new _CFGNode<t>(vr, label);
	int x;
	for (x = 1; x < irsb->stmts_used && irsb->stmts[x]->tag != Ist_IMark; x++) {
		if (irsb->stmts[x]->tag == Ist_Exit)
			work->addBranch(((IRStmtExit *)irsb->stmts[x])->dst.rip);
	}
	if (x == irsb->stmts_used) {
		if (irsb->jumpkind == Ijk_Ret) {
			VexRip r(vr);
			r.rtrn();
			work->addDefault(r);
		} else if (irsb->jumpkind == Ijk_Call) {
			if (irsb->next_is_const) {
				if (oracle->isPltCall(irsb->next_const.rip)) {
					LibraryFunctionType tmpl = oracle->identifyLibraryCall(irsb->next_const.rip);
					work->addDefault(extract_call_follower(irsb), tmpl);
				} else {
					work->addCall(irsb->next_const.rip);
				}
			} else {
				std::vector<VexRip> b;
				oracle->getInstrCallees(vr, b);
				for (auto it = b.begin(); it != b.end(); it++)
					work->addCall(*it);
			}
		} else if (irsb->next_is_const) {
			work->addDefault(irsb->next_const.rip);
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
				work->addBranch(*it);
		}
	} else {
		assert(irsb->stmts[x]->tag == Ist_IMark);
		work->addDefault(((IRStmtIMark *)irsb->stmts[x])->addr.rip);
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
enumerateCFG(_CFGNode<t> *start, HashedSet<HashedPtr<_CFGNode<t> > > &out)
{
	return cfgnode_tmpl::enumerateCFG(start, out);
}

