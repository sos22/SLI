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


   void move(zipInternalT &o);

   Set o to be a copy of *this, with the hint that this will never be
   referenced again except to run its destructor.


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
	void move(assume_zip_internal &o) const {
		o = *this;
	}
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
	assume_zip_internal<subtreeT> f(thing, assumption);
	return zip(scope, f);
}

#define INTBDD_DONT_CARE ((subtreeT *)0x1)
template <typename subtreeT, typename scopeT>
class from_enabling_internal {
public:
	bool failed;
	typename subtreeT::enablingTableT table;
	void move(from_enabling_internal &o) {
		o.failed = failed;
		table.move(o.table);
	}
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
	from_enabling_internal<subtreeT, scopeT> f(inp);
	subtreeT *res = zip(scope, f);
	if (res == INTBDD_DONT_CARE)
		return defaultValue;
	else
		return res;
}
#undef INTBDD_DONT_CARE

template <typename leafT, typename subtreeT> void
_bdd<leafT, subtreeT>::labelledPrint(FILE *f, std::map<subtreeT *, int> &labels)
{
	int nextLabel = 1;
	std::vector<std::pair<int, subtreeT *> > pending;
	pending.push_back(std::pair<int, subtreeT *>(0, (subtreeT *)this));
	while (!pending.empty()) {
		int depth = pending.back().first;
		subtreeT *what = pending.back().second;
		pending.pop_back();
		if (labels.count(what)) {
			fprintf(f, "        %*s[->%d]", depth * 3, "", labels[what]);
		} else {
			fprintf(f, "[%5d] %*s", nextLabel, depth * 3, "");
			labels[what] = nextLabel;
			nextLabel++;
			if (what->isLeaf()) {
				fprintf(f, "Leaf: ");
				what->_prettyPrint(f, what->leaf());
			} else {
				fprintf(f, "Mux:");
				ppIRExpr(what->internal().condition, f);
				pending.push_back(std::pair<int, subtreeT *>(depth + 1, what->internal().falseBranch));
				pending.push_back(std::pair<int, subtreeT *>(depth + 1, what->internal().trueBranch));
			}
		}
		fprintf(f, "\n");
	}
}

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
				pending.push_back(l->internal().falseBranch);
				pending.push_back(l->internal().trueBranch);
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
		res = scope->node(a, scope->ordering->rankVariable(a, bdd_ordering::rank_hint::Never()), t, f);
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

/* Both IRExpr arguments are really const, but I only mark one so as
   to make it a bit easier to be sure I haven't mixed them up later
   on. */
static bool
_dereferences(IRExpr *expr, const IRExpr *addr, std::set<IRExpr *> &memo)
{
	if (!memo.insert(expr).second) {
		return false;
	}
	switch (expr->tag) {
	case Iex_Get:
	case Iex_GetI:
	case Iex_Const:
	case Iex_HappensBefore:
	case Iex_FreeVariable:
	case Iex_EntryPoint:
	case Iex_ControlFlow:
		return false;
	case Iex_Mux0X:
		abort();
	case Iex_Qop:
		return _dereferences(((IRExprQop *)expr)->arg1, addr, memo) ||
			_dereferences(((IRExprQop *)expr)->arg2, addr, memo) ||
			_dereferences(((IRExprQop *)expr)->arg3, addr, memo) ||
			_dereferences(((IRExprQop *)expr)->arg4, addr, memo);
	case Iex_Triop:
		return _dereferences(((IRExprTriop *)expr)->arg1, addr, memo) ||
			_dereferences(((IRExprTriop *)expr)->arg2, addr, memo) ||
			_dereferences(((IRExprTriop *)expr)->arg3, addr, memo);
	case Iex_Binop:
		return _dereferences(((IRExprBinop *)expr)->arg1, addr, memo) ||
			_dereferences(((IRExprBinop *)expr)->arg2, addr, memo);
	case Iex_Unop:
		return _dereferences(((IRExprUnop *)expr)->arg, addr, memo);
	case Iex_Load: {
		IRExprLoad *l = (IRExprLoad *)expr;
		if ( l->addr == addr ) {
			return true;
		}
		if ( l->addr->tag == Iex_Associative &&
		     ((IRExprAssociative *)l->addr)->op == Iop_Add64 &&
		     ((IRExprAssociative *)l->addr)->nr_arguments == 2 &&
		     ((IRExprAssociative *)l->addr)->contents[0]->tag == Iex_Const &&
		     ((IRExprConst *)((IRExprAssociative *)l->addr)->contents[0])->Ico.content.U64 <= (1 << 10) &&
		     ((IRExprAssociative *)l->addr)->contents[1] == addr ) {
			return true;
		}
		return _dereferences(l->addr, addr, memo);
	}
	case Iex_CCall: {
		IRExprCCall *e = (IRExprCCall *)expr;
		for (int i = 0; e->args[i]; i++) {
			if (_dereferences(e->args[i], addr, memo)) {
				return true;
			}
		}
		return false;
	}
	case Iex_Associative: {
		IRExprAssociative *e = (IRExprAssociative *)expr;
		for (int i = 0; i < e->nr_arguments; i++) {
			if (_dereferences(e->contents[i], addr, memo)) {
				return true;
			}
		}
		return false;
	}
	}
	abort();
}

static bool
dereferences(IRExpr *expr, const IRExpr *addr)
{
	if (!bdd_use_dereferences) {
		return false;
	}
	std::set<IRExpr *> memo;
	return _dereferences(expr, addr, memo);
}

template <typename t> void
bdd_scope<t>::checkInternSize() const
{
	if (intern.size() >= 1000000) {
		LibVEX_request_GC();
	}
}

template <typename t> void
bdd_scope<t>::normalise(IRExpr *cond, t *&a, t *&b)
{
	assert(a);
	assert(b);
	assert(a->isLeaf() == true || a->isLeaf() == false);

	bool progress = true;
	while (progress) {
		progress = false;
		if (!b->isLeaf() &&
		    b->internal().condition->tag == Iex_Unop &&
		    ((IRExprUnop *)b->internal().condition)->op == Iop_BadPtr &&
		    !a->isLeaf() &&
		    a->internal().condition->tag == Iex_Unop &&
		    ((IRExprUnop *)a->internal().condition)->op == Iop_BadPtr &&
		    ((IRExprUnop *)a->internal().condition)->arg ==
			((IRExprUnop *)b->internal().condition)->arg &&
		    dereferences(cond, ((IRExprUnop *)a->internal().condition)->arg)) {
			/* @cond dereferences X, and both a and b are
			   BadPtr tests of x.  That implies that A ==
			   C in this context, so see if we can do any
			   simplifications based on that. */
			t *A = a->internal().trueBranch;
			t *B = a->internal().falseBranch;
			t *C = b->internal().trueBranch;
			t *D = b->internal().falseBranch;
			if (B == C) {
				/* A == B -> true branch becomes trivial */
				a = A;
				progress = true;
			}
			if (A == D) {
				/* C == D -> false branch becomes trivial */
				b = C;
				progress = true;
			}
		}
	}

redo_b:
	progress = true;
	while (progress) {
		progress = false;
		if (!b->isLeaf() && cond == b->internal().condition) {
			b = b->internal().falseBranch;
			progress = true;
		}

		/* ifelse(cond, A, ifelse(BadPtr(X), B, C)) ->
		   ifelse(cond, A, C) if cond depends on LD(X). */
		if (!b->isLeaf() &&
		    b->internal().condition->tag == Iex_Unop &&
		    ((IRExprUnop *)b->internal().condition)->op == Iop_BadPtr &&
		    dereferences(cond,
				 ((IRExprUnop *)b->internal().condition)->arg)) {
			b = b->internal().falseBranch;
			progress = true;
		}
		if (!b->isLeaf() &&
		    b->internal().condition->tag == Iex_Binop &&
		    ((IRExprBinop *)b->internal().condition)->op == Iop_CmpEQ64 &&
		    ((IRExprBinop *)b->internal().condition)->arg1->tag == Iex_Const &&
		    ((IRExprConst *)((IRExprBinop *)b->internal().condition)->arg1)->Ico.content.U64 <= (1 << 10) &&
		    dereferences(cond,
				 ((IRExprBinop *)b->internal().condition)->arg2)) {
			b = b->internal().falseBranch;
			progress = true;
		}

		/* ifelse(k1<x,A,ifelse(k2 == X, B, C)) -> ifelse(k1<x,A,C) if k2 > k1 */
		/* ifelse(k1<x,A,ifelse(k2<x,B,C)) -> ifelse(k1<x,A,C) if k2 > k1 */
		if (!b->isLeaf() &&
		    cond->tag == Iex_Binop &&
		    ((IRExprBinop *)cond)->op >= Iop_CmpLT8U &&
		    ((IRExprBinop *)cond)->op <= Iop_CmpLT64U &&
		    ((IRExprBinop *)cond)->arg1->tag == Iex_Const &&
		    b->internal().condition->tag == Iex_Binop &&
		    ((((IRExprBinop *)b->internal().condition)->op >= Iop_CmpEQ8 &&
		      ((IRExprBinop *)b->internal().condition)->op <= Iop_CmpEQ64) ||
		     (((IRExprBinop *)b->internal().condition)->op >= Iop_CmpLT8U &&
		      ((IRExprBinop *)b->internal().condition)->op <= Iop_CmpLT64U)) &&
		    ((IRExprBinop *)b->internal().condition)->arg1->tag == Iex_Const &&
		    ((IRExprBinop *)b->internal().condition)->arg2 ==
		            ((IRExprBinop *)cond)->arg2) {
			IRExprConst *k1 = (IRExprConst *)((IRExprBinop *)cond)->arg1;
			IRExprConst *k2 = (IRExprConst *)((IRExprBinop *)b->internal().condition)->arg1;
			bool doit;
			switch (((IRExprBinop *)cond)->op) {
			case Iop_CmpLT8U:
				doit = k2->Ico.content.U8 > k1->Ico.content.U8;
				break;
			case Iop_CmpLT16U:
				doit = k2->Ico.content.U16 > k1->Ico.content.U16;
				break;
			case Iop_CmpLT32U:
				doit = k2->Ico.content.U32 > k1->Ico.content.U32;
				break;
			case Iop_CmpLT64U:
				doit = k2->Ico.content.U64 > k1->Ico.content.U64;
				break;
			default:
				abort();
			}
			if (doit) {
				b = b->internal().falseBranch;
				progress = true;
			}
		}

		if (!b->isLeaf() &&
		    b->internal().condition->tag == Iex_Unop &&
		    ((IRExprUnop *)b->internal().condition)->op == Iop_BadPtr &&
		    dereferences(cond, ((IRExprUnop *)b->internal().condition)->arg)) {
			/* We know that a == b->true, so try to simplify a bit based on that. */
			if (a == b->internal().falseBranch) {
				b = b->internal().falseBranch;
				progress = true;
			} else {
				a = b->internal().trueBranch;
				/* Don't set progress: we're updating
				 * @a, not @b. */
			}
		}
	}

	progress = true;
	while (progress) {
		progress = false;
		if (!a->isLeaf() &&
		    cond == a->internal().condition) {
			a = a->internal().trueBranch;
			progress = true;
		}

		if (!a->isLeaf() &&
		    cond->tag == Iex_EntryPoint &&
		    a->internal().condition->tag == Iex_EntryPoint &&
		    ((IRExprEntryPoint *)a->internal().condition)->thread == ((IRExprEntryPoint *)cond)->thread) {
			assert(((IRExprEntryPoint *)a->internal().condition)->label != ((IRExprEntryPoint *)cond)->label);
			a = a->internal().falseBranch;
			progress = true;
		}

		if (!a->isLeaf() &&
		    cond->tag == Iex_ControlFlow &&
		    a->internal().condition->tag == Iex_ControlFlow &&
		    ((IRExprControlFlow *)a->internal().condition)->thread == ((IRExprControlFlow *)cond)->thread &&
		    ((IRExprControlFlow *)a->internal().condition)->cfg1 == ((IRExprControlFlow *)cond)->cfg1)  {
			assert(((IRExprControlFlow *)a->internal().condition)->cfg2 != ((IRExprControlFlow *)cond)->cfg2);
			a = a->internal().falseBranch;
			progress = true;
		}

		if (!a->isLeaf() &&
		    cond->tag == Iex_Binop &&
		    ((IRExprBinop *)cond)->op >= Iop_CmpEQ8 &&
		    ((IRExprBinop *)cond)->op <= Iop_CmpEQ64 &&
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
			progress = true;
		}

		if (!a->isLeaf() &&
		    cond->tag == Iex_HappensBefore &&
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
				progress = true;
			}
		}

		/* We have ifelse(cond1, ifelse(BadPtr(X), A, B), C).
		   If cond1 dereferences BadPtr then we can simplify
		   that down to ifelse(cond1, B, C). */
		if (!a->isLeaf() &&
		    a->internal().condition->tag == Iex_Unop &&
		    ((IRExprUnop *)a->internal().condition)->op == Iop_BadPtr &&
		    dereferences(cond,
				 ((IRExprUnop *)a->internal().condition)->arg)) {
			a = a->internal().falseBranch;
			progress = true;
		}
		/* Likewise, if we just dereferenced X then we know
		   that X can't be a small constant. */
		if (!a->isLeaf() &&
		    a->internal().condition->tag == Iex_Binop &&
		    ((IRExprBinop *)a->internal().condition)->op == Iop_CmpEQ64 &&
		    ((IRExprBinop *)a->internal().condition)->arg1->tag == Iex_Const &&
		    ((IRExprConst *)((IRExprBinop *)a->internal().condition)->arg1)->Ico.content.U64 <= (1 << 10) &&
		    dereferences(cond,
				 ((IRExprBinop *)a->internal().condition)->arg2)) {
			progress = true;
			a = a->internal().falseBranch;
		}

		if (!a->isLeaf() &&
		    a->internal().condition->tag == Iex_Unop &&
		    ((IRExprUnop *)a->internal().condition)->op == Iop_BadPtr &&
		    dereferences(cond, ((IRExprUnop *)a->internal().condition)->arg)) {
			/* We know that a->true == b, so try to simplify a bit based on that. */
			if (b == a->internal().falseBranch) {
				a = a->internal().falseBranch;
			} else {
				b = a->internal().trueBranch;
				goto redo_b;
			}
		}
	}
}

template <typename t> t *
bdd_scope<t>::mkInternal(IRExpr *cond, const bdd_rank &r, t *a, t *b)
{
	assert(a != b);
	assert(cond->tag != Iex_Const);
	assert(a->isLeaf() || r < a->internal().rank);
	assert(b->isLeaf() || r < b->internal().rank);

	auto it_did_insert = intern.insert(
		std::pair<entry, t *>(
			entry(r, a, b),
			(t *)0xdead));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		it->second = new t(r, cond, a, b);
		nr_ever++;
		checkInternSize();
	}
	return it->second;
}

/* Note that this is unmemoised, deliberately.  It used to be
   memoised, but the memo table didn't hit often enough to be
   worthwhile.  The mkInternal() memo table is sufficient to achieve
   correctness, so just use that one. */
template <typename t> t *
bdd_scope<t>::node(IRExpr *cond, const bdd_rank &r, t *a, t *b)
{
	if (cond->tag == Iex_Const) {
		if ( ((IRExprConst *)cond)->Ico.content.U1 ) {
			return a;
		} else {
			return b;
		}
	}
	if (a == b) {
		return a;
	}
	normalise(cond, a, b);
	if (a == b) {
		return a;
	}
	if (cond->tag == Iex_HappensBefore &&
	    !b->isLeaf() &&
	    b->internal().condition->tag == Iex_HappensBefore &&
	    a == b->internal().trueBranch) {
		auto *condhb = (IRExprHappensBefore *)cond;
		auto *bhb = (IRExprHappensBefore *)b->internal().condition;
		if (condhb->before.tid == bhb->before.tid &&
		    condhb->after.tid == bhb->after.tid &&
		    condhb->before.id >= bhb->before.id &&
		    condhb->after.id <= bhb->after.id) {
			/* The idea here is to consider rewriting
			   ifelse(cond, X, ifelse(b->cond, X, Y)) to
			   ifelse(b->cond, X, ifelse(cond, X, Y)).
			   Normally, that would violate the ordering
			   constraints, except that the HB edges give
			   us enough structure to fix it up.  @cond is
			   (tA:idA <-< tB:idB) and @b's condition is
			   (tA:idC <-< tB:idD).  We also have idC <=
			   idA and idB <= idD.  The way we assign MAIs
			   ensures that idA >= idC implies tA:idA >=> tA:idB,
			   so we have tB:idB <=< tB:idD and
			   tA:idC <=< tA:idA.  If @b's condition is
			   false then we also have tB:idD <-< tA:idC.
			   Combining them all gives
			   tB:idB <=< tB:idB <-< tA:idC <=< tA:idA
			   which implies tB:idB <-< tA:idA.
			   i.e. if @b's condition is false then
			   so is @cond.  We can therefore rewrite
			   to ifelse(b->cond, X, Y) = b. */
			return b;
		}
	}

	assert(a->isLeaf() || r < a->internal().rank || a->internal().rank < r);
	assert(b->isLeaf() || r < b->internal().rank || b->internal().rank < r);
	if (a->isLeaf() || r < a->internal().rank) {
		/* True branch is fine */
		if (b->isLeaf() || r < b->internal().rank) {
			/* False branch is also fine */
			return mkInternal(cond, r, a, b);
		} else {
			/* Need to re-order on false branch */
			return node(
				b->internal().condition,
				b->internal().rank,
				node(cond, r, a, b->internal().trueBranch),
				node(cond, r, a, b->internal().falseBranch));
		}
	} else {
		/* True branch must be reordered */
		if (b->isLeaf() || r < b->internal().rank) {
			/* Only need to re-order on true branch */
			return node(
				a->internal().condition,
				a->internal().rank,
				node(cond, r, a->internal().trueBranch, b),
				node(cond, r, a->internal().falseBranch, b));
		} else {
			/* Tricky case.  Need to re-order on both branches */
			if (a->internal().rank < b->internal().rank) {
				return node(
					a->internal().condition,
					a->internal().rank,
					node(b->internal().condition,
					     b->internal().rank,
					     node(cond, r, a->internal().trueBranch,  b->internal().trueBranch),
					     node(cond, r, a->internal().trueBranch,  b->internal().falseBranch)),
					node(b->internal().condition,
					     b->internal().rank,
					     node(cond, r, a->internal().falseBranch, b->internal().trueBranch),
					     node(cond, r, a->internal().falseBranch, b->internal().falseBranch)));
			} else if (a->internal().rank == b->internal().rank) {
				return node(
					a->internal().condition,
					a->internal().rank,
					node(cond, r, a->internal().trueBranch,  b->internal().trueBranch),
					node(cond, r, a->internal().falseBranch, b->internal().falseBranch));
			} else {
				return node(
					b->internal().condition,
					b->internal().rank,
					node(a->internal().condition,
					     a->internal().rank,
					     node(cond, r, a->internal().trueBranch,  b->internal().trueBranch),
					     node(cond, r, a->internal().falseBranch, b->internal().trueBranch)),
					node(a->internal().condition,
					     a->internal().rank,
					     node(cond, r, a->internal().trueBranch,  b->internal().falseBranch),
					     node(cond, r, a->internal().falseBranch, b->internal().falseBranch)));
			}
		}
	}
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

	auto cond = what->internal().condition;
	auto b = what->internal().falseBranch;
	auto a = what->internal().trueBranch;
	if (cond->tag == Iex_HappensBefore &&
	    !b->isLeaf() &&
	    b->internal().condition->tag == Iex_HappensBefore &&
	    a == b->internal().trueBranch) {
		auto *condhb = (IRExprHappensBefore *)cond;
		auto *bhb = (IRExprHappensBefore *)b->internal().condition;
		if (condhb->before.tid == bhb->before.tid &&
		    condhb->after.tid == bhb->after.tid &&
		    condhb->before.id >= bhb->before.id &&
		    condhb->after.id <= bhb->after.id) {
			return b;
		}
	}

	auto it_did_insert = intern.insert(
		std::pair<entry, t *>(
			entry(what->internal().rank,
			      what->internal().trueBranch,
			      what->internal().falseBranch),
			what));
	if (it_did_insert.second) {
		checkInternSize();
	}
	return it_did_insert.first->second;
}

template <typename constT, typename subtreeT> template <IRExpr *mkConst(constT)> IRExpr *
const_bdd<constT, subtreeT>::to_irexpr(subtreeT *what, std::map<subtreeT *, IRExpr *> &memo)
{
	auto it_did_insert = memo.insert(std::pair<subtreeT *, IRExpr *>(what, (IRExpr *)0xdead));
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
	stackedCdf::startBDD();
	auto res = to_irexpr<mkConst>(what, memo);
	stackedCdf::stopBDD();
	return res;
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
						scope->node(what->internal().condition,
							    what->internal().rank,
							    true_it->second,
							    const_false);
					true_it++;
				} else if (false_it != falseB.end() &&
					   (true_it == trueB.end() || false_it->first < true_it->first)) {
					res[false_it->first] =
						scope->node(what->internal().condition,
							    what->internal().rank,
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
						scope->node(what->internal().condition,
							    what->internal().rank,
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
	stackedCdf::startBDD();
	auto res = to_selectors(scope, what, memo);
	stackedCdf::stopBDD();
	return res;
}

template <typename subtreeT, typename scopeT> class ifelse_zip_internal {
	bbdd *cond;
	subtreeT *ifTrue;
	subtreeT *ifFalse;
public:
	void move(ifelse_zip_internal &o) const {
		o = *this;
	}
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
	ifelse_zip_internal<subtreeT, scopeT> f(cond, ifTrue, ifFalse);
	return zip(scope, f);
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
	auto it_did_insert = memo.insert(std::pair<subtreeT *, subtreeT *>(in, (subtreeT *)0xdead));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		subtreeT *t = replaceTerminal(scp, from, to, in->internal().trueBranch, memo);
		subtreeT *f = replaceTerminal(scp, from, to, in->internal().falseBranch, memo);
		if (t != in->internal().trueBranch ||
		    f != in->internal().falseBranch)
			it->second = scp->node(in->internal().condition, in->internal().rank, t, f);
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
	stackedCdf::startBDD();
	auto res = replaceTerminal(scp, from, to, in, memo);
	stackedCdf::stopBDD();
	return res;
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

template <typename zipInternalT> class _relocKeyT {
	void operator=(const _relocKeyT &o); /* NI */
public:
	const bdd_rank &rank;
	IRExpr *const expr;
	unsigned char __target[sizeof(zipInternalT)];
	const zipInternalT &target() const {
		return *(const zipInternalT *)__target;
	}
	_relocKeyT(const _relocKeyT &o)
		: rank(o.rank), expr(o.expr)
	{
		new ((zipInternalT *)&target()) zipInternalT(o.target());
	}
	_relocKeyT(const bdd_rank &_rank,
		   IRExpr *_expr,
		   zipInternalT &_target)
		: rank(_rank), expr(_expr)
	{
		_target.move(*(zipInternalT *)&target());
	}
	~_relocKeyT()
	{
		target().~zipInternalT();
	}
	bool operator<(const _relocKeyT &o) const {
		switch (rank.compare(o.rank)) {
		case bdd_rank::lt:
			return true;
		case bdd_rank::gt:
			return false;
		case bdd_rank::eq:
			return target() < o.target();
		}
		abort();
	}
};

template <typename constT, typename subtreeT> template <typename scopeT, typename zipInternalT>
subtreeT *
_bdd<constT, subtreeT>::zip(scopeT *scope, zipInternalT &rootZip)
{
	if (rootZip.isLeaf())
		return rootZip.leafzip();

	stackedCdf::startBDD();
	subtreeT *newRoot;
	typedef _relocKeyT<zipInternalT> relocKeyT;
	std::map<relocKeyT, std::vector<subtreeT **> > relocs;

	/* Set up root relocation */
	{
		IRExpr *rootCond;
		const bdd_rank &rootRank(rootZip.bestCond(&rootCond));
		relocs[relocKeyT(rootRank, rootCond, rootZip)].push_back(&newRoot);
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
	std::map<zipInternalT, std::vector<subtreeT **> > leafRelocs;

	while (!relocs.empty()) {
		auto it = relocs.begin();
		const relocKeyT &key(it->first);
		const std::vector<subtreeT **> &dests(it->second);
		const zipInternalT &relocWhere(key.target());

		assert(key.rank == scope->ordering->rankVariable(key.expr, bdd_ordering::rank_hint::Never()));
		assert(!relocWhere.isLeaf());

#ifndef NDEBUG
		IRExpr *relocExpr;
		const bdd_rank relocRank(relocWhere.bestCond(&relocExpr));
		assert(relocRank == key.rank);
		assert(relocExpr == key.expr);
#endif

		zipInternalT trueSucc(relocWhere.trueSucc(key.rank));
		zipInternalT falseSucc(relocWhere.falseSucc(key.rank));
		
		subtreeT *newNode = new subtreeT(key.rank, key.expr, (subtreeT *)0xb00b, (subtreeT *)0xd00d);

		/* Patch it into the BDD we've built up so far. */
		for (auto it2 = dests.begin(); it2 != dests.end(); it2++)
			**it2 = newNode;

		relocs.erase(it);

		/* Set up relocations for the true and
		 * false branches */
		if (trueSucc.isLeaf()) {
			leafRelocs[trueSucc].push_back(&newNode->unsafe_internal().trueBranch);
		} else {
			IRExpr *cond;
			const bdd_rank &rank(trueSucc.bestCond(&cond));
#ifndef NDEBUG
			assert(relocRank < rank);
#endif
			relocs[relocKeyT(rank, cond, trueSucc)].push_back(&newNode->unsafe_internal().trueBranch);
		}
		if (falseSucc.isLeaf()) {
			leafRelocs[falseSucc].push_back(&newNode->unsafe_internal().falseBranch);
		} else {
			IRExpr *cond;
			const bdd_rank &rank(falseSucc.bestCond(&cond));
#ifndef NDEBUG
			assert(relocRank < rank);
#endif
			relocs[relocKeyT(rank, cond, falseSucc)].push_back(&newNode->unsafe_internal().falseBranch);
		}
	}

	std::map<subtreeT *, subtreeT *> reduced;

	while (!leafRelocs.empty()) {
		auto it = leafRelocs.begin();
		const zipInternalT &leafNode(it->first);
		const std::vector<subtreeT **> &relocs(it->second);
		assert(leafNode.isLeaf());
		subtreeT *l = leafNode.leafzip();
		reduced[l] = l;
		for (auto it2 = relocs.begin(); it2 != relocs.end(); it2++)
			**it2 = l;
		leafRelocs.erase(it);
	}

	/* Now use the scope to fully reduce it. */
	newRoot = reduceBdd<scopeT, zipInternalT>(scope, reduced, newRoot);

	stackedCdf::stopBDD();

	return newRoot;
}

/* ``Restructuring'' zips are used for things which are a bit more
   involved than ordinary zips, so that we can't do the breadth-first
   trick.  The canonical example is transforming the leaves of an
   exprbdd, which can end up getting to the leaves and then
   discovering that there was something involved we should have done
   much earlier on. */
template <typename leafT, typename subtreeT> template <typename scopeT, typename bscopeT, typename zipT> subtreeT *
_bdd<leafT, subtreeT>::restructure_zip(scopeT *scope, bscopeT *bscope, const zipT &what, std::map<zipT, subtreeT *> &memo)
{
	auto it_did_insert = memo.insert(std::pair<zipT, subtreeT *>(what, (subtreeT *)0xbeef));
	auto it = it_did_insert.first;
	auto did_insert = it_did_insert.second;
	if (did_insert) {
		if (what.isLeaf()) {
			it->second = what.leaf(scope, bscope);
		} else {
			IRExpr *condition;
			bdd_rank rank(what.rank(&condition));
			subtreeT *t = restructure_zip(scope, bscope, what.trueBranch(rank), memo);
			if (t) {
				subtreeT *f = restructure_zip(scope, bscope, what.falseBranch(rank), memo);
				if (f)
					it->second = scope->node(condition, rank, t, f);
			}
		}
	}
	return it->second;
}
template <typename leafT, typename subtreeT> template <typename scopeT, typename bscopeT, typename zipT> subtreeT *
_bdd<leafT, subtreeT>::restructure_zip(scopeT *scope, bscopeT *bscope, const zipT &root)
{
	std::map<zipT, subtreeT *> memo;
	return restructure_zip(scope, bscope, root, memo);
}

template <typename leafT, typename subtreeT> void
_bdd<leafT, subtreeT>::dotPrintNodes(FILE *f, std::set<const _bdd *> &memo) const
{
	if (!memo.insert(this).second) {
		return;
	}
	fprintf(f, "\tnode%p [label=\"", this);
	if (isLeaf()) {
		_prettyPrint(f, leaf());
		fprintf(f, "\", shape=oval];\n");
	} else {
		internal().rank.prettyPrint(f);
		fprintf(f, "\", shape=box];\n");
		internal().trueBranch->dotPrintNodes(f, memo);
		internal().falseBranch->dotPrintNodes(f, memo);
	}
}

template <typename leafT, typename subtreeT> void
_bdd<leafT, subtreeT>::dotPrintEdges(FILE *f, std::set<const _bdd *> &memo) const
{
	if (isLeaf()) {
		return;
	}
	if (!memo.insert(this).second) {
		return;
	}
	fprintf(f, "\tnode%p -> node%p;\n", this, internal().trueBranch);
	fprintf(f, "\tnode%p -> node%p [style=dotted];\n", this, internal().falseBranch);
	internal().trueBranch->dotPrintEdges(f, memo);
	internal().falseBranch->dotPrintEdges(f, memo);
}

/* Print the BDD in DOT format, because that makes it a bit easier to
 * read its structure. */
template <typename leafT, typename subtreeT> void
_bdd<leafT, subtreeT>::dotPrint(FILE *f) const
{
	fprintf(f, "digraph {\n");
	std::set<const _bdd *> memo;
	dotPrintNodes(f, memo);
	memo.clear();
	dotPrintEdges(f, memo);
	fprintf(f, "}\n");
}
