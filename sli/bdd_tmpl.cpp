/* The various templates used to build the BDD library.  This gets
   #include'd into a bunch of other files. */




template <typename constT, typename subtreeT> template <typename scopeT, typename zipInternalT>
subtreeT *
_bdd<constT, subtreeT>::zip(scopeT *scope,
			    const zipInternalT &where,
			    std::map<zipInternalT, subtreeT *> &memo)
{
	if (TIMEOUT)
		return NULL;

	if (where.isLeaf())
		return where.leafzip();

	auto it_did_insert = memo.insert(
		std::pair<zipInternalT, subtreeT *>(where, (subtreeT *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;

	IRExpr *bestCond;
	const bdd_rank &bestRank(where.bestCond(&bestCond));
	subtreeT *trueSucc = zip(scope, where.trueSucc(scope->ordering, bestRank), memo);
	subtreeT *falseSucc = zip(scope, where.falseSucc(scope->ordering, bestRank), memo);
	it->second = where.mkNode(scope, bestCond, trueSucc, falseSucc);
	return it->second;
}

template <typename subtreeT> class assume_zip_internal {
public:
	subtreeT *thing;
	bbdd *assumption;
	assume_zip_internal(subtreeT *_thing, bbdd *_assumption)
		: thing(_thing), assumption(_assumption)
	{}
	const bdd_rank &bestCond(IRExpr **cond) const {
		assert(!(thing->isLeaf() && assumption->isLeaf()));
		if (thing->isLeaf()) {
			*cond = assumption->internal().condition;
			return assumption->internal().rank;
		} else if (assumption->isLeaf()) {
			*cond = thing->internal().condition;
			return thing->internal().rank;
		} else if (thing->internal().rank < assumption->internal().rank) {
			*cond = thing->internal().condition;
			return thing->internal().rank;
		} else {
			*cond = assumption->internal().condition;
			return assumption->internal().rank;
		}
	}
	assume_zip_internal trueSucc(bdd_ordering *ordering, const bdd_rank &cond) const {
		return assume_zip_internal(
			ordering->trueBranch(thing, cond),
			ordering->trueBranch(assumption, cond));
	}
	assume_zip_internal falseSucc(bdd_ordering *ordering, const bdd_rank &cond) const {
		return assume_zip_internal(
			ordering->falseBranch(thing, cond),
			ordering->falseBranch(assumption, cond));
	}
	bool isLeaf() const {
		return assumption->isLeaf() || thing->isLeaf();
	}
	subtreeT *leafzip() const {
		if (assumption->isLeaf()) {
			if (assumption->leaf())
				return thing;
			else
				return NULL;
		} else {
			assert(thing->isLeaf());
			return thing;
		}
	}
	subtreeT *mkNode(bdd_scope<subtreeT> *scope, IRExpr *cond, subtreeT *t, subtreeT *f) const
	{
		if (!t)
			return f;
		if (!f)
			return t;
		return scope->makeInternal(cond, t, f);
	}
	bool operator<(const assume_zip_internal &o) const {
		if (thing < o.thing)
			return true;
		if (thing > o.thing)
			return false;
		return assumption < o.assumption;
	}
};
template <typename constT, typename subtreeT> template <typename scopeT> subtreeT *
_bdd<constT, subtreeT>::assume(scopeT *scope, subtreeT *thing, bbdd *assumption)
{
	return zip(scope, assume_zip_internal<subtreeT>(thing, assumption));
}

#define INTBDD_DONT_CARE ((subtreeT *)0x1)
template <typename subtreeT, typename scopeT>
class from_enabling_internal {
public:
	bool failed;
	typename subtreeT::enablingTableT table;
	from_enabling_internal(const typename subtreeT::enablingTableT &_table)
		: failed(false)
	{
		for (auto it = _table.begin(); !it.finished(); it.advance())
			if (!it.key()->isLeaf() ||
			    it.key()->leaf())
				table.set(it.key(), it.value());
	}
	from_enabling_internal(bool _failed)
		: failed(_failed)
	{}
	bool isLeaf() const {
		return failed || table.size() <= 1;
	}
	subtreeT *leafzip() const {
		if (failed)
			return NULL;
		else if (table.size() == 0)
			return INTBDD_DONT_CARE;
		else
			return table.begin().value();
	}
	const bdd_rank &bestCond(IRExpr **cond) const {
		IRExpr *c = NULL;
		const bdd_rank *bestCond = NULL;
		for (auto it = table.begin(); !it.finished(); it.advance()) {
			if (!it.key()->isLeaf() &&
			    (!bestCond || it.key()->internal().rank < *bestCond)) {
				c = it.key()->internal().condition;
				bestCond = &it.key()->internal().rank;
			}
			if (!it.value()->isLeaf() &&
			    (!bestCond || it.value()->internal().rank < *bestCond)) {
				c = it.value()->internal().condition;
				bestCond = &it.value()->internal().rank;
			}
		}
		assert(c);
		assert(bestCond != NULL);
		*cond = c;
		return *bestCond;
	}
	from_enabling_internal trueSucc(bdd_ordering *ordering, const bdd_rank &cond) const
	{
		from_enabling_internal res(false);
		for (auto it = table.begin(); !it.finished(); it.advance()) {
			bbdd *newGuard = ordering->trueBranch(it.key().get(), cond);
			if (newGuard->isLeaf() && !newGuard->leaf())
				continue;
			subtreeT *newRes = ordering->trueBranch(it.value(), cond);
			subtreeT **newSlot = res.table.getSlot(newGuard, newRes);
			if (*newSlot != newRes)
				return from_enabling_internal(true);
		}
		return res;
	}
	from_enabling_internal falseSucc(bdd_ordering *ordering, const bdd_rank &cond) const
	{
		from_enabling_internal res(false);
		for (auto it = table.begin(); !it.finished(); it.advance()) {
			bbdd *newGuard = ordering->falseBranch(it.key().get(), cond);
			if (newGuard->isLeaf() && !newGuard->leaf())
				continue;
			subtreeT *newRes = ordering->falseBranch(it.value(), cond);
			subtreeT **newSlot = res.table.getSlot(newGuard, newRes);
			if (*newSlot != newRes)
				return from_enabling_internal(true);
		}
		return res;
	}
	subtreeT *mkNode(scopeT *scope, IRExpr *a, subtreeT *t, subtreeT *f) const
	{
		if (t == NULL || f == NULL)
			return NULL;
		if (t == INTBDD_DONT_CARE)
			return f;
		if (f == INTBDD_DONT_CARE)
			return t;
		return scope->makeInternal(a, t, f);
	}
	bool operator<(const from_enabling_internal &o) const {
		auto it1 = table.begin();
		auto it2 = o.table.begin();
		while (!it1.finished() && !it2.finished()) {
			if (it1.key() < it2.key())
				return true;
			if (it1.key() > it2.key())
				return false;
			if (it1.value() < it2.value())
				return true;
			if (it1.value() > it2.value())
				return false;
			it1.advance();
			it2.advance();
		}
		if (it1.finished() && !it2.finished())
			return true;
		return false;
	}
};

template <typename constT, typename subtreeT> template <typename scopeT>
subtreeT *
_bdd<constT, subtreeT>::from_enabling(scopeT *scope, const enablingTableT &inp, subtreeT *defaultValue)
{
	subtreeT *res = zip(scope, from_enabling_internal<subtreeT, scopeT>(inp));
	if (res == INTBDD_DONT_CARE)
		return defaultValue;
	else
		return res;
}
#undef INTBDD_DONT_CARE

template <typename leafT, typename subtreeT> void
_bdd<leafT, subtreeT>::prettyPrint(FILE *f)
{
	int nextLabel = 0;
	std::map<_bdd *, int> labels;

	/* First, assign labels to anything which occurs multiple
	 * times. */
	{
		std::set<_bdd *> seen;
		std::vector<_bdd *> pending;
		pending.push_back(this);
		while (!pending.empty()) {
			auto l = pending.back();
			assert(l);
			pending.pop_back();
			if (labels.count(l))
				continue;
			if (seen.count(l)) {
				/* Need a label */
				labels[l] = nextLabel;
				nextLabel++;
			}
			seen.insert(l);
			if (!l->isLeaf()) {
				assert(l->internal().trueBranch);
				assert(l->internal().falseBranch);
				pending.push_back(l->internal().trueBranch);
				pending.push_back(l->internal().falseBranch);
			}
		}
	}

	int lsize = 1;
	int c = 1;
	while (c <= nextLabel) {
		c *= 10;
		lsize++;
	}

	/* Now print it */
	std::set<_bdd *> printed;
	std::vector<std::pair<int, _bdd *> > pending;
	pending.push_back(std::pair<int, _bdd *>(0, this));
	while (!pending.empty()) {
		int depth = pending.back().first;
		auto what = pending.back().second;
		pending.pop_back();

		if (labels.count(what) && !printed.count(what))
			fprintf(f, "[%*d]", lsize, labels[what]);
		else
			fprintf(f, "%*s", lsize + 2, "");
		fprintf(f, "%*s", depth, "");
		if (printed.count(what)) {
			assert(labels.count(what));
			fprintf(f, "[->%d]", labels[what]);
		} else {
			printed.insert(what);
			if (what->isLeaf()) {
				fprintf(f, "Leaf: ");
				what->_prettyPrint(f, what->leaf());
			} else {
				fprintf(f, "Mux: ");
				ppIRExpr(what->internal().condition, f);
				pending.push_back(std::pair<int, _bdd *>(depth + 1, what->internal().falseBranch));
				pending.push_back(std::pair<int, _bdd *>(depth + 1, what->internal().trueBranch));
			}
		}
		fprintf(f, "\n");
	}
}

template <typename leafT, typename subtreeT> template <typename scopeT,
						       subtreeT *(*parseLeaf)(scopeT *, const char *, const char **)> subtreeT *
_bdd<leafT, subtreeT>::_parse(scopeT *scope,
			      const char *str,
			      const char **suffix,
			      std::map<int, subtreeT *> &labels)
{
	int label = -1;
	/* Discard whitespace */
	parseThisChar(' ', str, &str);

	/* Deal with references to elsewhere in the tree. */
	if (parseThisString("[->", str, &str)) {
		if (!parseDecimalInt(&label, str, &str) ||
		    !parseThisString("]\n", str, suffix) ||
		    !labels.count(label))
			return NULL;
		return labels[label];
	}

	/* Does it have a label? */
	if (parseThisChar('[', str, &str)) {
		/* Yes */
		parseThisChar(' ', str, &str);
		if (!parseDecimalInt(&label, str, &str) ||
		    !parseThisChar(']', str, &str) ||
		    labels.count(label))
			return NULL;
		parseThisChar(' ', str, &str);
	}
	subtreeT *res;
	if (parseThisString("Leaf: ", str, &str)) {
		res = parseLeaf(scope, str, &str);
		if (!res || !parseThisChar('\n', str, suffix))
			return NULL;
	} else if (parseThisString("Mux: ", str, &str)) {
		IRExpr *a;
		if (!parseIRExpr(&a, str, &str))
			return NULL;
		subtreeT *t = _parse<scopeT, parseLeaf>(scope, str, &str, labels);
		if (!t)
			return NULL;
		subtreeT *f = _parse<scopeT, parseLeaf>(scope, str, suffix, labels);
		if (!f)
			return NULL;
		res = scope->makeInternal(a, t, f);
	} else {
		return NULL;
	}
	if (label != -1)
		labels[label] = res;
	return res;
}

template <typename leafT, typename subtreeT> template <typename scopeT,
						       subtreeT *(*parseLeaf)(scopeT *scope, const char *, const char **)> bool
_bdd<leafT, subtreeT>::_parse(scopeT *scope, subtreeT **root, const char *str, const char **suffix)
{
	std::map<int, subtreeT *> labels;
	subtreeT *res = _parse<scopeT, parseLeaf>(scope, str, suffix, labels);
	if (res) {
		*root = res;
		return true;
	} else {
		return false;
	}
}

template <typename t> t *
bdd_scope<t>::makeInternal(IRExpr *cond, t *a, t *b)
{
	assert(a);
	assert(b);
	assert(a->isLeaf() == true || a->isLeaf() == false);
	assert(a->isLeaf() || ordering->before(cond, a));
	assert(b->isLeaf() || ordering->before(cond, b));
	if (a == b)
		return a;
	if (cond->tag == Iex_Const) {
		if ( ((IRExprConst *)cond)->Ico.U1 )
			return a;
		else
			return b;
	}

	if (cond->tag == Iex_ControlFlow &&
	    !a->isLeaf() &&
	    a->internal().condition->tag == Iex_ControlFlow &&
	    ((IRExprControlFlow *)a->internal().condition)->thread == ((IRExprControlFlow *)cond)->thread &&
	    ((IRExprControlFlow *)a->internal().condition)->cfg1 == ((IRExprControlFlow *)cond)->cfg1)  {
		assert(((IRExprControlFlow *)a->internal().condition)->cfg2 != ((IRExprControlFlow *)cond)->cfg2);
		a = a->internal().falseBranch;
	}

	if (cond->tag == Iex_Binop &&
	    ((IRExprBinop *)cond)->op >= Iop_CmpEQ8 &&
	    ((IRExprBinop *)cond)->op <= Iop_CmpEQ64 &&
	    !a->isLeaf() &&
	    a->internal().condition->tag == Iex_Binop &&
	    ((IRExprBinop *)a->internal().condition)->op >= Iop_CmpEQ8 &&
	    ((IRExprBinop *)a->internal().condition)->op <= Iop_CmpEQ64 &&
	    ((IRExprBinop *)a->internal().condition)->arg2 ==
		((IRExprBinop *)cond)->arg2 &&
	    ((IRExprBinop *)cond)->arg1->tag == Iex_Const &&
	    ((IRExprBinop *)a->internal().condition)->arg1->tag == Iex_Const &&
	    !eqIRExprConst( (IRExprConst *)((IRExprBinop *)a->internal().condition)->arg1,
			    (IRExprConst *)((IRExprBinop *)cond)->arg1) ) {
		assert(((IRExprBinop *)a->internal().condition)->arg1 !=
		       ((IRExprBinop *)cond)->arg1);
		a = a->internal().falseBranch;
	}

	if (cond->tag == Iex_HappensBefore &&
	    !a->isLeaf() &&
	    a->internal().condition->tag == Iex_HappensBefore) {
		const IRExprHappensBefore *condhb =
			(const IRExprHappensBefore *)cond;
		const IRExprHappensBefore *ahb =
			(const IRExprHappensBefore *)a->internal().condition;
		if (condhb->before.tid == ahb->before.tid &&
		    condhb->after.tid == ahb->after.tid &&
		    condhb->before.id >= ahb->before.id &&
		    condhb->after.id <= ahb->after.id) {
			/* @cond is (tA:idA <-< tB:idB) and @a's first
			   condition is (tA:idC <-< tB:idD).  We
			   further have that idA >= idC and idB <=
			   idD.  Because of the way we assign MAIs to
			   memory accesses (see setMais in
			   probeCFGstoMachine.cpp) idC <= idA implies
			   tA:idC <-< tA:idA, and likewise
			   idB <= idD implies tB:idB <-< tB:idD.
			   Combining these with cond gives us
			   
			   tA:idC <-< tA:idA <-< tB:idB <-< tB:idD

			   i.e.

			   tA:idC <-< tB:idD and we can replace @a
			   with @a->trueBranch. */
			a = a->internal().trueBranch;
		}
	}
	    
	if (a == b)
		return a;

	bdd_rank r(ordering->rankVariable(cond));
	auto it_did_insert = intern.insert(
		std::pair<entry, t *>(
			entry(r, a, b),
			(t *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = new t(r, cond, a, b);
	return it->second;
}

template <typename t> t *
bdd_scope<t>::makeInternal(IRExpr *cond, const bdd_rank &r, t *a, t *b)
{
	assert(a);
	assert(b);
	assert(a->isLeaf() || ordering->before(cond, a));
	assert(b->isLeaf() || ordering->before(cond, b));
	if (a == b)
		return a;
	if (cond->tag == Iex_Const) {
		if ( ((IRExprConst *)cond)->Ico.U1 )
			return a;
		else
			return b;
	}

	if (cond->tag == Iex_ControlFlow &&
	    !a->isLeaf() &&
	    a->internal().condition->tag == Iex_ControlFlow &&
	    ((IRExprControlFlow *)a->internal().condition)->thread == ((IRExprControlFlow *)cond)->thread &&
	    ((IRExprControlFlow *)a->internal().condition)->cfg1 == ((IRExprControlFlow *)cond)->cfg1)  {
		assert(((IRExprControlFlow *)a->internal().condition)->cfg2 != ((IRExprControlFlow *)cond)->cfg2);
		a = a->internal().falseBranch;
	}

	if (cond->tag == Iex_Binop &&
	    ((IRExprBinop *)cond)->op >= Iop_CmpEQ8 &&
	    ((IRExprBinop *)cond)->op <= Iop_CmpEQ64 &&
	    !a->isLeaf() &&
	    a->internal().condition->tag == Iex_Binop &&
	    ((IRExprBinop *)a->internal().condition)->op >= Iop_CmpEQ8 &&
	    ((IRExprBinop *)a->internal().condition)->op <= Iop_CmpEQ64 &&
	    ((IRExprBinop *)a->internal().condition)->arg2 ==
		((IRExprBinop *)cond)->arg2 &&
	    ((IRExprBinop *)cond)->arg1->tag == Iex_Const &&
	    ((IRExprBinop *)a->internal().condition)->arg1->tag == Iex_Const &&
	    !eqIRExprConst( (IRExprConst *)((IRExprBinop *)a->internal().condition)->arg1,
			    (IRExprConst *)((IRExprBinop *)cond)->arg1) ) {
		assert(((IRExprBinop *)a->internal().condition)->arg1 !=
		       ((IRExprBinop *)cond)->arg1);
		a = a->internal().falseBranch;
	}

	if (cond->tag == Iex_HappensBefore &&
	    !a->isLeaf() &&
	    a->internal().condition->tag == Iex_HappensBefore) {
		const IRExprHappensBefore *condhb =
			(const IRExprHappensBefore *)cond;
		const IRExprHappensBefore *ahb =
			(const IRExprHappensBefore *)a->internal().condition;
		if (condhb->before.tid == ahb->before.tid &&
		    condhb->after.tid == ahb->after.tid &&
		    condhb->before.id >= ahb->before.id &&
		    condhb->after.id <= ahb->after.id) {
			/* @cond is (tA:idA <-< tB:idB) and @a's first
			   condition is (tA:idC <-< tB:idD).  We
			   further have that idA >= idC and idB <=
			   idD.  Because of the way we assign MAIs to
			   memory accesses (see setMais in
			   probeCFGstoMachine.cpp) idC <= idA implies
			   tA:idC <-< tA:idA, and likewise
			   idB <= idD implies tB:idB <-< tB:idD.
			   Combining these with cond gives us
			   
			   tA:idC <-< tA:idA <-< tB:idB <-< tB:idD

			   i.e.

			   tA:idC <-< tB:idD and we can replace @a
			   with @a->trueBranch. */
			a = a->internal().trueBranch;
		}
	}

	auto it_did_insert = intern.insert(
		std::pair<entry, t *>(
			entry(r, a, b),
			(t *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert)
		it->second = new t(r, cond, a, b);
	return it->second;
}

template <typename constT, typename subtreeT> template <IRExpr *mkConst(constT)> IRExpr *
const_bdd<constT, subtreeT>::to_irexpr(subtreeT *what, std::map<subtreeT *, IRExpr *> &memo)
{
	auto it_did_insert = memo.insert(std::pair<subtreeT *, IRExpr *>(what, (IRExpr *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (what->isLeaf()) {
			it->second = mkConst(what->leaf());
		} else {
			it->second = IRExpr_Mux0X(
				what->internal().condition,
				to_irexpr<mkConst>(what->internal().falseBranch, memo),
				to_irexpr<mkConst>(what->internal().trueBranch, memo));
		}
	} else {
		assert(it->second != NULL);
	}
	return it->second;
}

template <typename constT, typename subtreeT> template <IRExpr *mkConst(constT)> IRExpr *
const_bdd<constT, subtreeT>::to_irexpr(subtreeT *what)
{
	std::map<subtreeT *, IRExpr *> memo;
	return to_irexpr<mkConst>(what, memo);
}

template <typename constT, typename subtreeT> template <typename scopeT> const std::map<constT, bbdd *> &
_bdd<constT, subtreeT>::to_selectors(scopeT *scope,
				     subtreeT *what,
				     std::map<subtreeT *, std::map<constT, bbdd *> > &memo)
{
	auto it_did_insert = memo.insert(std::pair<subtreeT *, std::map<constT, bbdd *> >(what, std::map<constT, bbdd *>()));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		std::map<constT, bbdd *> &res(it->second);
		assert(res.empty());
		if (what->isLeaf()) {
			res[what->leaf()] = scope->cnst(true);
		} else {
			const std::map<constT, bbdd *> &trueB(to_selectors(scope, what->internal().trueBranch, memo));
			const std::map<constT, bbdd *> &falseB(to_selectors(scope, what->internal().falseBranch, memo));
			auto true_it = trueB.begin();
			auto false_it = falseB.begin();
			bbdd *const_false = scope->cnst(false);
			while (true_it != trueB.end() || false_it != falseB.end()) {
				if (true_it != trueB.end() &&
				    (false_it == falseB.end() || true_it->first < false_it->first)) {
					res[true_it->first] =
						scope->makeInternal(what->internal().condition,
								    true_it->second,
								    const_false);
					true_it++;
				} else if (false_it != falseB.end() &&
					   (true_it == trueB.end() || false_it->first < true_it->first)) {
					res[false_it->first] =
						scope->makeInternal(what->internal().condition,
								    const_false,
								    false_it->second);
					false_it++;
				} else {
					/* (true_it != trueB.end() || false_it != falseB.end()) &&
					   !(true_it != trueB.end() &&
					    (false_it == falseB.end() || true_it->first < false_it->first)) &&
					   !(false_it != falseB.end() &&
					    (true_it == trueB.end() || false_it->first < true_it->first))
					   =>
					   (true_it != trueB.end() || false_it != falseB.end()) &&
					   (true_it == trueB.end() ||
					    (false_it != falseB.end() && !(true_it->first < false_it->first))) &&
					   (false_it == falseB.end() ||
					    (true_it != trueB.end() && !(false_it->first < true_it->first)))
					   =>
					   (!finished(t) || !finished(f)) &&
					   (finished(t) || (!finished(f) && t >= f)) &&
					   (finished(f) || (!finished(t) && f >= t))
					   =>
					   (!finished(t) &&
					     (finished(t) || (!finished(f) && t >= f)) &&
					     (finished(f) || (!finished(t) && f >= t))) ||
					   (!finished(f) &&
					     (finished(t) || (!finished(f) && t >= f)) &&
					     (finished(f) || (!finished(t) && f >= t)))
					   =>
					   (!finished(t) &&
					     (!finished(f) && t >= f) &&
					     (finished(f) || f >= t)) ||
					   (!finished(f) &&
					     (finished(t) || t >= f) &&
					     (!finished(t) && f >= t))
					   =>
					   (!finished(t) &&
					    !finished(f) &&
					    t >= f &&
					    f >= t) ||
					   (!finished(f) &&
					    t >= f &&
					    !finished(t) &&
					    f >= t)
					   => !finished(t) && !finished(f) && t == f
					*/
					res[false_it->first] =
						scope->makeInternal(what->internal().condition,
								    true_it->second,
								    false_it->second);
					true_it++;
					false_it++;
				}
			}
		}
	}
	return it->second;
}

template <typename constT, typename subtreeT> template <typename scopeT> std::map<constT, bbdd *>
_bdd<constT, subtreeT>::to_selectors(scopeT *scope, subtreeT *what)
{
	std::map<subtreeT *, std::map<constT, bbdd *> > memo;
	return to_selectors(scope, what, memo);
}

template <typename subtreeT, typename scopeT> class ifelse_zip_internal {
	bbdd *cond;
	subtreeT *ifTrue;
	subtreeT *ifFalse;
public:
	ifelse_zip_internal(bbdd *_cond, subtreeT *_ifTrue, subtreeT *_ifFalse)
		: cond(_cond), ifTrue(_ifTrue), ifFalse(_ifFalse)
	{}
	bool isLeaf() const {
		return cond->isLeaf() || (ifTrue == ifFalse);
	}
	subtreeT *leafzip() const {
		if (cond->isLeaf()) {
			if (cond->leaf())
				return ifTrue;
			else
				return ifFalse;
		}
		if (ifTrue == ifFalse)
			return ifTrue;
		abort();
	}
	const bdd_rank &bestCond(IRExpr **c) const {
		assert(!cond->isLeaf());
		const bdd_rank *best = &cond->internal().rank;
		*c = cond->internal().condition;
		if (!ifTrue->isLeaf() && ifTrue->internal().rank < *best) {
			best = &ifTrue->internal().rank;
			*c = ifTrue->internal().condition;
		}
		if (!ifFalse->isLeaf() && ifFalse->internal().rank < *best) {
			best = &ifFalse->internal().rank;
			*c = ifFalse->internal().condition;
		}
		return *best;
	}
	ifelse_zip_internal trueSucc(bdd_ordering *ordering, const bdd_rank &on) const {
		return ifelse_zip_internal(
			ordering->trueBranch(cond, on),
			ordering->trueBranch(ifTrue, on),
			ordering->trueBranch(ifFalse, on));
	}
	ifelse_zip_internal falseSucc(bdd_ordering *ordering, const bdd_rank &on) const {
		return ifelse_zip_internal(
			ordering->falseBranch(cond, on),
			ordering->falseBranch(ifTrue, on),
			ordering->falseBranch(ifFalse, on));
	}
	subtreeT *mkNode(scopeT *scope, IRExpr *cond, subtreeT *trueB, subtreeT *falseB) const {
		if (!trueB || !falseB)
			return NULL;
		return scope->makeInternal(cond, trueB, falseB);
	}
	bool operator<(const ifelse_zip_internal &o) const {
		if (cond < o.cond)
			return true;
		if (cond > o.cond)
			return false;
		if (ifTrue < o.ifTrue)
			return true;
		if (ifTrue > o.ifTrue)
			return false;
		return ifFalse < o.ifFalse;
	}
};

template <typename constT, typename subtreeT> template <typename scopeT> subtreeT *
_bdd<constT, subtreeT>::ifelse(scopeT *scope,
			       bbdd *cond,
			       subtreeT *ifTrue,
			       subtreeT *ifFalse)
{
	return zip(scope, ifelse_zip_internal<subtreeT, scopeT>(cond, ifTrue, ifFalse));
}

template <typename constT, typename subtreeT> subtreeT *
const_bdd<constT, subtreeT>::replaceTerminal(scope *scp,
					     constT from,
					     constT to,
					     subtreeT *in,
					     std::map<subtreeT *, subtreeT *> &memo)
{
	if (in->isLeaf()) {
		if (in->leaf() == from)
			return scp->cnst(to);
		else
			return in;
	}
	auto it_did_insert = memo.insert(std::pair<subtreeT *, subtreeT *>(in, (subtreeT *)NULL));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		subtreeT *t = replaceTerminal(scp, from, to, in->internal().trueBranch, memo);
		subtreeT *f = replaceTerminal(scp, from, to, in->internal().falseBranch, memo);
		if (t != in->internal().trueBranch ||
		    f != in->internal().falseBranch)
			it->second = scp->makeInternal(in->internal().condition, t, f);
		else
			it->second = in;
	}
	return it->second;
}

template <typename constT, typename subtreeT> subtreeT *
const_bdd<constT, subtreeT>::replaceTerminal(scope *scp,
					     constT from,
					     constT to,
					     subtreeT *in)
{
	std::map<subtreeT *, subtreeT *> memo;
	return replaceTerminal(scp, from, to, in, memo);
}

template <typename t> void
bdd_scope<t>::runGc(HeapVisitor &hv)
{
	std::map<entry, t *> newIntern;
	for (auto it = intern.begin();
	     it != intern.end();
	     it++) {
		t *value = hv.visited(it->second);
		if (!value)
			continue;
		entry e(it->first);
		e.trueB = hv.visited(e.trueB);
		e.falseB = hv.visited(e.falseB);
		assert(e.trueB && e.falseB);
		newIntern.insert(std::pair<entry, t *>(e, value));
	}
	intern = newIntern;
}
