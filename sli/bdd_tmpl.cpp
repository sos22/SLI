/* The various templates used to build the BDD library.  This gets
   #include'd into a bunch of other files. */


/* Methods for a zipInternalT:

   const bdd_rank &bestCond(IRExpr **cond) const;

   Figure out what variable needs to be tested next.  Return its rank
   and set @cond to the actual IRExpr.


   bool isLeaf() const

   Return true if calling ::leafzip() is safe.


   subtreeT *leafzip() const;

   Return a BDD representing this point in the zip.  Only called if
   ::isLeaf() returns true.


   zipInternalT trueSucc(const bdd_rank &cond) const;

   Generate a new zipInternalT assuming that @cond is true.  @cond
   will be the result of ::bestCond().  Only called when ::isLeaf()
   returns false.


   zipInternalT falseSucc(const bdd_rank &cond) const;

   Like trueSucc, but assuming that @cond is false.


   bool operator<(const zipInternalT &o) const;

   Standard ordering operator, used to build std::map<> over the
   zipInternalT.  There are no semantic requirements on the order,
   beyond those needed for std::map to work.


   static subtreeT *fixup(subtreeT *what);

   Called for each node in the BDD once we've fixed its contents.  It
   can replace the node with another one (but probably shouldn't
   allocate any new stuff).  @what is potentially unreduced, but its
   true and false branches will be fully reduced.  This is used to
   e.g. remove _|_ nodes in assume operations.

   static bool badPtr(subtreeT *what);

   Return true if @what is a bad pointer and should not be
   dereferenced by the zip machinery.  Such pointers should be removed
   by ::fixup() later on.

*/

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
	assume_zip_internal trueSucc(const bdd_rank &cond) const {
		return assume_zip_internal(
			thing->trueBranch(cond),
			assumption->trueBranch(cond));
	}
	assume_zip_internal falseSucc(const bdd_rank &cond) const {
		return assume_zip_internal(
			thing->falseBranch(cond),
			assumption->falseBranch(cond));
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
	bool operator<(const assume_zip_internal &o) const {
		if (thing < o.thing)
			return true;
		if (thing > o.thing)
			return false;
		return assumption < o.assumption;
	}
	static subtreeT *fixup(subtreeT *what) {
		if (what->isLeaf())
			return what;
		if (what->internal().trueBranch == NULL)
			return what->internal().falseBranch;
		if (what->internal().falseBranch == NULL)
			return what->internal().trueBranch;
		return what;
	}
	static bool badPtr(subtreeT *what) {
		return what == NULL;
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
		if (failed || table.size() == 0)
			return true;
		bool allValuesSame = true;
		auto it = table.begin();
		subtreeT *v = it.value();
		for (it.advance(); allValuesSame && !it.finished(); it.advance())
			allValuesSame &= it.value() == v;
		return allValuesSame;
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
	from_enabling_internal trueSucc(const bdd_rank &cond) const
	{
		from_enabling_internal res(false);
		for (auto it = table.begin(); !it.finished(); it.advance()) {
			bbdd *newGuard = it.key().get()->trueBranch(cond);
			if (newGuard->isLeaf() && !newGuard->leaf())
				continue;
			subtreeT *newRes = it.value()->trueBranch(cond);
			subtreeT **newSlot = res.table.getSlot(newGuard, newRes);
			if (*newSlot != newRes)
				return from_enabling_internal(true);
		}
		return res;
	}
	from_enabling_internal falseSucc(const bdd_rank &cond) const
	{
		from_enabling_internal res(false);
		for (auto it = table.begin(); !it.finished(); it.advance()) {
			bbdd *newGuard = it.key().get()->falseBranch(cond);
			if (newGuard->isLeaf() && !newGuard->leaf())
				continue;
			subtreeT *newRes = it.value()->falseBranch(cond);
			subtreeT **newSlot = res.table.getSlot(newGuard, newRes);
			if (*newSlot != newRes)
				return from_enabling_internal(true);
		}
		return res;
	}
	static subtreeT *fixup(subtreeT *what) {
		if (what->internal().trueBranch == NULL ||
		    what->internal().falseBranch == NULL)
			return NULL;
		if (what->internal().trueBranch == INTBDD_DONT_CARE)
			return what->internal().falseBranch;
		if (what->internal().falseBranch == INTBDD_DONT_CARE)
			return what->internal().trueBranch;
		return what;
	}
	static bool badPtr(subtreeT *what) {
		return what == NULL || what == INTBDD_DONT_CARE;
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
			pending.pop_back();
			if (!l || labels.count(l))
				continue;
			if (seen.count(l)) {
				/* Need a label */
				labels[l] = nextLabel;
				nextLabel++;
				continue;
			}
			seen.insert(l);
			if (!l->isLeaf()) {
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

		if (what && labels.count(what) && !printed.count(what))
			fprintf(f, "[%*d]", lsize, labels[what]);
		else
			fprintf(f, "%*s", lsize + 2, "");
		fprintf(f, "%*s", depth, "");
		if (!what) {
			fprintf(f, "!!!NULL!!!");
		} else if (printed.count(what)) {
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

template <typename t> void
bdd_scope<t>::normalise(IRExpr *cond, t *&a, t *&b)
{
	assert(a);
	assert(b);
	assert(a->isLeaf() == true || a->isLeaf() == false);
	assert(a->isLeaf() || ordering->before(cond, a));
	assert(b->isLeaf() || ordering->before(cond, b));

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
}

template <typename t> t *
bdd_scope<t>::makeInternal(IRExpr *cond, const bdd_rank &r, t *a, t *b)
{
	if (a == b)
		return a;
	assert(cond->tag != Iex_Const);
	normalise(cond, a, b);
	if (a == b)
		return a;

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
bdd_scope<t>::makeInternal(IRExpr *cond, t *a, t *b)
{
	if (a == b)
		return a;
	if (cond->tag == Iex_Const) {
		if ( ((IRExprConst *)cond)->Ico.U1 )
			return a;
		else
			return b;
	}
	normalise(cond, a, b);
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
bdd_scope<t>::internBdd(t *what)
{
	assert(what);
	assert(!what->isLeaf());
	if (what->internal().trueBranch == what->internal().falseBranch)
		return what->internal().trueBranch;
	normalise(what->internal().condition,
		  what->unsafe_internal().trueBranch,
		  what->unsafe_internal().falseBranch);
	if (what->internal().trueBranch == what->internal().falseBranch)
		return what->internal().trueBranch;
	auto it_did_insert = intern.insert(
		std::pair<entry, t *>(
			entry(what->internal().rank,
			      what->internal().trueBranch,
			      what->internal().falseBranch),
			what));
	return it_did_insert.first->second;
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
	ifelse_zip_internal trueSucc(const bdd_rank &on) const {
		return ifelse_zip_internal(
			cond->trueBranch(on),
			ifTrue->trueBranch(on),
			ifFalse->trueBranch(on));
	}
	ifelse_zip_internal falseSucc(const bdd_rank &on) const {
		return ifelse_zip_internal(
			cond->falseBranch(on),
			ifTrue->falseBranch(on),
			ifFalse->falseBranch(on));
	}
	static subtreeT *fixup(subtreeT *what) {
		return what;
	}
	static bool badPtr(subtreeT *) {
		return false;
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

template <typename constT, typename subtreeT> template <typename scopeT, typename zipInternalT>
subtreeT *
_bdd<constT, subtreeT>::reduceBdd(scopeT *scope, std::map<subtreeT *, subtreeT *> &reduced, subtreeT *start)
{
	if (zipInternalT::badPtr(start))
		return start;
	if (start->isLeaf())
		return start;
	auto it_did_insert = reduced.insert(std::pair<subtreeT *, subtreeT *>(start, start));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (!did_insert)
		return it->second;
	start->unsafe_internal().trueBranch = reduceBdd<scopeT, zipInternalT>(scope, reduced, start->internal().trueBranch);
	start->unsafe_internal().falseBranch = reduceBdd<scopeT, zipInternalT>(scope, reduced, start->internal().falseBranch);
	subtreeT *fixed = zipInternalT::fixup(start);
	if (fixed != start) {
		if (!zipInternalT::badPtr(fixed) && !fixed->isLeaf())
			it->second = scope->internBdd(fixed);
		else
			it->second = fixed;
	} else {
		assert(!fixed->isLeaf());
		it->second = scope->internBdd(start);
	}
	return it->second;
}

template <typename constT, typename subtreeT> template <typename scopeT, typename zipInternalT>
subtreeT *
_bdd<constT, subtreeT>::zip(scopeT *scope, const zipInternalT &rootZip)
{
	if (TIMEOUT)
		return NULL;

	if (rootZip.isLeaf())
		return rootZip.leafzip();

	subtreeT *newRoot;
	typedef std::pair<subtreeT **, zipInternalT> relocT;
	typedef std::pair<const bdd_rank &, IRExpr *> relocKeyT;
	std::map<relocKeyT, std::vector<relocT> > relocs;

	/* Set up root relocation */
	{
		IRExpr *rootCond;
		const bdd_rank &rootRank(rootZip.bestCond(&rootCond));
		relocs[relocKeyT(rootRank, rootCond)].push_back(relocT(&newRoot, rootZip));
	}

	/* Resolve relocs.  This is a little bit cunning.  The idea is
	   to construct the new nodes in ascending order of the BDD
	   rank, so that we never need to build up a memo table for
	   the entire zip operation.  That's helpful because such a
	   memo table could easily be far larger than the final
	   BDD. */
	/* You can kind of think of this as doing the build
	   breadth-first, if that helps at all: we start at a root,
	   then do all of the depth-1 nodes, then all of the depth-2
	   nodes, and so on.  It's a little bit more complicated than
	   that, though, because some edges cross multiple levels; in
	   that case, we compute edges in ascending order of the
	   *destination* depth. */
	/* Another way of thinking about this is to say that we have a
	   kind of implicit operator node, which is a bit like an
	   instance of the zipInternalT type.  The relocs show how to
	   tie these operators back into the BDD we're building.  It's
	   a little more complicated than that, though, again, because
	   our operator nodes are n-ary, and the BDDs are always
	   binary. */

	/* This is guaranteed to produce a ``locally'' reduced BDD, so
	   that there are no non-interned duplicates in the result,
	   but it's not globally reduced, so there might be duplicates
	   elsewhere in the scope.  You have to intern the results in
	   order to produce a fully reduced BDD. */

	/* Leaves are special, because they don't test any
	   expressions.  Process them last. */
	std::vector<relocT> leafRelocs;

	while (!relocs.empty()) {
		if (TIMEOUT)
			return NULL;

		auto it = relocs.begin();
		const relocKeyT key(it->first);
		const std::vector<relocT> &rq(it->second);

		/* Construct all nodes which test key.first. */
		assert(key.first == scope->ordering->rankVariable(key.second));

		std::map<zipInternalT, subtreeT *> memo;
		for (auto it2 = rq.begin(); it2 != rq.end(); it2++) {
			subtreeT **relocPtr = it2->first;
			const zipInternalT &relocWhere(it2->second);
			assert(!relocWhere.isLeaf());
#ifndef NDEBUG
			{
				IRExpr *relocExpr;
				const bdd_rank relocRank(relocWhere.bestCond(&relocExpr));
				assert(relocRank == key.first);
				assert(physicallyEqual(relocExpr, key.second));
			}
#endif
			auto it3_did_insert = memo.insert(std::pair<zipInternalT, subtreeT *>(relocWhere, (subtreeT *)NULL));
			auto it3 = it3_did_insert.first;
			auto did_insert = it3_did_insert.second;
			if (did_insert) {
				/* Not encounted this zip point
				 * before, figure out what we're doing
				 * next. */
				zipInternalT trueSucc(relocWhere.trueSucc(key.first));
				zipInternalT falseSucc(relocWhere.falseSucc(key.first));
				assert(trueSucc < falseSucc || falseSucc < trueSucc);

				/* Construct a new node */
				subtreeT *newNode = new subtreeT(key.first, key.second,
								 NULL, NULL);
				/* Set up relocations for the true and
				 * false branches */
				if (trueSucc.isLeaf()) {
					leafRelocs.push_back(relocT(&newNode->unsafe_internal().trueBranch, trueSucc));
				} else {
					IRExpr *cond;
					const bdd_rank &rank(trueSucc.bestCond(&cond));
					assert(key.first < rank);
					relocs[relocKeyT(rank, cond)].push_back(relocT(&newNode->unsafe_internal().trueBranch, trueSucc));
				}
				if (falseSucc.isLeaf()) {
					leafRelocs.push_back(relocT(&newNode->unsafe_internal().falseBranch, falseSucc));
				} else {
					IRExpr *cond;
					const bdd_rank &rank(falseSucc.bestCond(&cond));
					assert(key.first < rank);
					relocs[relocKeyT(rank, cond)].push_back(relocT(&newNode->unsafe_internal().falseBranch, falseSucc));
				}

				it3->second = newNode;
			} else {
				/* Already have a node for this zip point, so just
				   reuse it. */
			}
			assert(it3->second);
			*relocPtr = it3->second;
		}

		relocs.erase(it);
	}

	std::map<subtreeT *, subtreeT *> reduced;

	/* Now process leaf relocations */
	std::map<zipInternalT, subtreeT *> leafMemo;

	for (auto it = leafRelocs.begin(); it != leafRelocs.end(); it++) {
		if (TIMEOUT)
			return NULL;

		subtreeT **relocPtr = it->first;
		const zipInternalT &relocWhere(it->second);
		assert(relocWhere.isLeaf());
		auto it2_did_insert = leafMemo.insert(std::pair<zipInternalT, subtreeT *>(relocWhere, (subtreeT *)NULL));
		auto it2 = it2_did_insert.first;
		auto did_insert = it2_did_insert.second;
		if (did_insert) {
			it2->second = relocWhere.leafzip();
			/* We rely on the zip type returning fully
			 * reduced leaves. */
			reduced[it2->second] = it2->second;
		}
		*relocPtr = it2->second;
	}

	/* Now use the scope to fully reduce it. */
	newRoot = reduceBdd<scopeT, zipInternalT>(scope, reduced, newRoot);

	return newRoot;
}
