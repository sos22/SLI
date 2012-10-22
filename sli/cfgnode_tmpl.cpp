/* This ends up getting #include'd in various places so as to instantiate the
   templates.  Sigh. */
template <typename from, typename to>
class CfgSuccMap : public std::map<_CFGNode<from> *, std::vector<CfgSuccessorT<to> > > {
	
};

namespace cfgnode_tmpl {

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
CfgNodeForRip(const CfgLabel &label,
	      Oracle *oracle,
	      const VexRip &vr,
	      const t &rip,
	      CfgSuccMap<t, t> &succMap,
	      std::map<_CFGNode<t> *, unsigned> *sizeMap = NULL)
{
	IRSB *irsb = oracle->getIRSBForRip(vr, true);
	if (!irsb)
		return NULL;
	_CFGNode<t> *work = new _CFGNode<t>(rip, label);
	std::vector<CfgSuccessorT<t> > &relocs(succMap[work]);
	int x;
	assert(irsb->stmts[0]->tag == Ist_IMark);
	if (sizeMap)
		(*sizeMap)[work] = ((IRStmtIMark *)irsb->stmts[0])->len;
	for (x = 1; x < irsb->stmts_used && irsb->stmts[x]->tag != Ist_IMark; x++) {
		if (irsb->stmts[x]->tag == Ist_Exit)
			relocs.push_back(CfgSuccessorT<t>::branch(t(((IRStmtExit *)irsb->stmts[x])->dst.rip)));
	}
	if (x == irsb->stmts_used) {
		if (irsb->jumpkind == Ijk_Ret) {
			VexRip r(vr);
			r.rtrn();
			relocs.push_back(CfgSuccessorT<t>::dflt(t(r)));
		} else if (irsb->jumpkind == Ijk_Call) {
			if (irsb->next_is_const) {
				if (oracle->isPltCall(irsb->next_const.rip)) {
					if (!oracle->functionNeverReturns(StaticRip(irsb->next_const.rip))) {
						LibraryFunctionType tmpl = oracle->identifyLibraryCall(irsb->next_const.rip);
						relocs.push_back(CfgSuccessorT<t>::dflt(t(extract_call_follower(irsb)), tmpl));
					}
				} else {
					relocs.push_back(CfgSuccessorT<t>::call(t(irsb->next_const.rip)));
				}
			} else {
				std::vector<VexRip> b;
				oracle->getInstrCallees(vr, b);
				for (auto it = b.begin(); it != b.end(); it++)
					relocs.push_back(CfgSuccessorT<t>::call(t(*it)));
			}
		} else if (irsb->next_is_const) {
			relocs.push_back(CfgSuccessorT<t>::dflt(t(irsb->next_const.rip)));
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
				relocs.push_back(CfgSuccessorT<t>::branch(t(*it)));
		}
	} else {
		assert(irsb->stmts[x]->tag == Ist_IMark);
		relocs.push_back(CfgSuccessorT<t>::dflt(t(((IRStmtIMark *)irsb->stmts[x])->addr.rip)));
	}
	return work;
}

template <typename from, typename to> void
resolveReferences(CfgSuccMap<to, from> &succMap, const std::map<to, _CFGNode<from> *> &lookup)
{
	for (auto it = succMap.begin(); it != succMap.end(); it++) {
		_CFGNode<from> *a = it->first;
		const std::vector<CfgSuccessorT<from> > &desired(it->second);
		assert(a->successors.size() == 0);
		a->successors.reserve(desired.size());
		for (auto it = desired.begin(); it != desired.end(); it++) {
			auto it2 = lookup.find(it->instr);
			if (it2 != lookup.end())
				a->successors.push_back(
					typename _CFGNode<to>::successor_t(
						*it,
						it2->second));
		}
	}
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

