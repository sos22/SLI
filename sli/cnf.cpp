/* Various bits for manipulating expressions in explicit CNF form. */
#include <map>

#include "sli.h"
#include "cnf.hpp"
#include "offline_analysis.hpp"

#include "libvex_prof.hpp"

static IRExpr *internIRExpr(IRExpr *x);


class CnfExpression : public GarbageCollected<CnfExpression>, public Named {
public:
	virtual CnfExpression *CNF(void) = 0;
	virtual CnfExpression *invert() = 0;
	virtual IRExpr *asIRExpr(std::map<int, IRExpr *> &,
				 IRExprTransformer &) = 0;
	virtual int complexity() = 0;
	NAMED_CLASS
};

class CnfVariable : public CnfExpression {
	static int nextId;
protected:
	char *mkName() const {
		if (inverted)
			return my_asprintf("~(v%d)", id);
		else
			return my_asprintf("v%d", id);
	}
public:
	CnfExpression *CNF() { return this; }
	CnfVariable() : id(nextId++) {}
	CnfVariable(int _id, bool _inverted) : id(_id), inverted(_inverted) {}
	void visit(HeapVisitor &hv) {}
	CnfExpression *invert() { return new CnfVariable(id, !inverted); }
	int getId() { return id; }
	IRExpr *asIRExpr(std::map<int, IRExpr *> &m,
			 IRExprTransformer &t)
	{
		IRExpr *e = t.transformIRExpr(m[id]);
		if (inverted)
			e = IRExpr_Unop(Iop_Not1, e);
		return e;
	}
	int complexity() { return 0; }
	int id;
	bool inverted;
};

class CnfGrouping : public CnfExpression {
protected:
	char *mkName(char op) const {
		char *acc = NULL;
		char *acc2;
		if (args.size() == 0)
			return my_asprintf("(%c)", op);
		for (unsigned x = 0; x < args.size(); x++) {
			if (x == 0)
				acc2 = my_asprintf("(%s", args[x]->name());
			else
				acc2 = my_asprintf("%s %c %s", acc, op, args[x]->name());
			free(acc);
			acc = acc2;
		}
		acc2 = my_asprintf("%s)", acc);
		free(acc);
		return acc2;
	}
public:
	void visit(HeapVisitor &hv) {
		for (unsigned x = 0; x < args.size(); x++)
			hv(args[x]);
	}
	void addChild(CnfExpression *e) { args.push_back(e); }
	int complexity() {
		if (args.size() == 0)
			return 0;
		int acc = 1;
		for (unsigned x = 0; x < args.size(); x++)
			acc += args[x]->complexity();
		return acc;
	}
	std::vector<CnfExpression *> args;
};

class CnfOr : public CnfGrouping {
protected:
	char *mkName() const { return CnfGrouping::mkName('|'); }
public:
	CnfExpression *CNF();
	CnfExpression *invert();
	void sort();
	bool optimise(void);
	CnfVariable *getArg(unsigned x) {
		assert(x < args.size());
		CnfVariable *r = dynamic_cast<CnfVariable *>(args[x]);
		assert(r);
		return r;
	}
	IRExpr *asIRExpr(std::map<int, IRExpr *> &m, IRExprTransformer &t) {
		if (args.size() == 0) {
			return IRExpr_Const(IRConst_U1(0));
		} else if (args.size() == 1) {
			return args[0]->asIRExpr(m, t);
		} else {
			IRExpr *work = IRExpr_Associative(Iop_Or1, NULL);
			for (unsigned x = 0; x < args.size(); x++)
				addArgumentToAssoc(work, args[x]->asIRExpr(m, t));
			return work;
		}
	}
};

class CnfAnd : public CnfGrouping {
	class myTransformer : public IRExprTransformer {
	public:
		std::map<IRExpr *, IRExpr *> cnstTable;
		IRExprTransformer &underlying;
		IRExpr *transformIRExpr(IRExpr *e, bool *done_something) {
			if (cnstTable.count(e)) {
				*done_something = true;
				e = cnstTable[e];
			}
			e = IRExprTransformer::transformIRExpr(e, done_something);
			e = underlying.transformIRExpr(e, done_something);
			return e;
		}
		myTransformer(IRExprTransformer &_underlying)
			: underlying(_underlying)
		{}
	};
protected:
	char *mkName() const { return CnfGrouping::mkName('&'); }
public:
	CnfExpression *CNF();
	CnfExpression *invert();
	void sort();
	CnfOr *getArg(unsigned x) {
		assert(x < args.size());
		CnfOr *r = dynamic_cast<CnfOr *>(args[x]);
		assert(r);
		return r;
	}
	void optimise();
	IRExpr *asIRExpr(std::map<int, IRExpr *> &m, IRExprTransformer &t) {
		if (args.size() == 0) {
			return IRExpr_Const(IRConst_U1(1));
		} else {
			IRExpr *work = IRExpr_Associative(Iop_And1, NULL);
			myTransformer trans(t);
			for (unsigned x = 0; x < args.size(); x++) {
				IRExpr *exp = args[x]->asIRExpr(m, trans);
				addArgumentToAssoc(work, exp);
				if (exp->tag == Iex_Binop &&
				    exp->Iex.Binop.op == Iop_CmpEQ64 &&
				    exp->Iex.Binop.arg1->tag == Iex_Const)
					trans.cnstTable[exp->Iex.Binop.arg2] = exp->Iex.Binop.arg1;
			}
			return work;
		}
	}
};
int CnfVariable::nextId = 450;

static bool
__comparator1(CnfExpression *_a, CnfExpression *_b)
{
	CnfVariable *a = dynamic_cast<CnfVariable *>(_a);
	CnfVariable *b = dynamic_cast<CnfVariable *>(_b);
	assert(a && b);
	if (a->getId() < b->getId())
		return true;
	else if (a->getId() == b->getId())
		return a->inverted < b->inverted;
	else
		return false;
}

void
CnfOr::sort()
{
	std::sort(args.begin(), args.end(), __comparator1);
}

static bool
__comparator2(CnfExpression *_a, CnfExpression *_b)
{
	CnfOr *a = dynamic_cast<CnfOr *>(_a);
	CnfOr *b = dynamic_cast<CnfOr *>(_b);
	assert(a && b);
	for (unsigned x = 0;
	     x < a->args.size() && x < b->args.size();
	     x++) {
		if (a->getArg(x)->getId() <
		    b->getArg(x)->getId())
			return true;
		if (a->getArg(x)->getId() >
		    b->getArg(x)->getId())
			return false;
	}
	if (a->args.size() < b->args.size())
		return true;
	return false;
}

void
CnfAnd::sort()
{
	for (unsigned x = 0; x < args.size(); x++)
		getArg(x)->sort();
	std::sort(args.begin(), args.end(), __comparator2);
}

/* Or expressions are allowed to have variables or negations of
   variables as arguments, but not other or expressions or and
   expressions. */
CnfExpression *
CnfOr::CNF()
{
	for (unsigned x = 0; x < args.size(); x++)
		args[x] = args[x]->CNF();
	for (unsigned x = 0; x < args.size(); x++) {
		if (dynamic_cast<CnfVariable *>(args[x]))
			continue;
		if (CnfOr *cor = dynamic_cast<CnfOr *>(args[x])) {
			/* Flatten nested ORs. */
			for (unsigned y = 0; y < cor->args.size(); y++) {
				args.push_back(cor->args[y]);
			}
			args.erase(args.begin() + x);
			x--;
		} else {
			/* Deal with these in a second pass */
			assert(dynamic_cast<CnfAnd *>(args[x]));
		}
	}

	for (unsigned x = 0; x < args.size(); x++) {
		CnfAnd *cad = dynamic_cast<CnfAnd *>(args[x]);
		if (!cad)
			continue;
		if (args.size() == 1)
			return args[0];
		if (cad->args.size() == 1) {
			args[x] = cad->args[0];
			continue;
		}
		/* Okay, we have something of the form
		   a | b | c | (1 & 2 & 3 & ...) ... .
		   Convert it to
		   (a | b | c | 1) & (a | b | c | 2) & (a | b | c | 3) & ...

		*/
		CnfAnd *newRoot = new CnfAnd();
		std::vector<CnfExpression *> newArgs = args;
		newArgs.erase(newArgs.begin() + x);
		newRoot->args.resize(cad->args.size());
		for (unsigned y = 0; y < cad->args.size(); y++) {
			CnfGrouping *cg = new CnfOr();
			cg->args = newArgs;
			cg->addChild(cad->args[y]);
			newRoot->args[y] = cg;
		}
		return newRoot->CNF();
	}
	return this;
}

/* And expressions are only allowed to have or expressions as
 * children. */
CnfExpression *
CnfAnd::CNF()
{
	for (unsigned x = 0; x < args.size(); x++)
		args[x] = args[x]->CNF();
	for (unsigned x = 0; x < args.size(); x++) {
		if (dynamic_cast<CnfVariable *>(args[x])) {
			CnfGrouping *n = new CnfOr();
			n->addChild(args[x]);
			args[x] = n;
			continue;
		}
		if (CnfAnd *car = dynamic_cast<CnfAnd *>(args[x])) {
			args.erase(args.begin() + x);
			args.insert(args.end(), car->args.begin(), car->args.end());
			x--;
		}
	}
	return this;
}

CnfExpression *
CnfOr::invert()
{
	CnfAnd *a = new CnfAnd();
	a->args.resize(args.size());
	for (unsigned x = 0; x < args.size(); x++)
		a->args[x] = args[x]->invert();
	return a;
}

bool
CnfOr::optimise()
{
	for (unsigned i = 0; i + 1 < args.size(); i++) {
		/* Eliminate any duplicates, and if we have x | ~x
		   eliminate the whole clause. */
		/* This relies on the arguments having been sorted
		   already so that any duplicates will be next to each
		   other. */
		while (i + 1 < args.size() && getArg(i)->getId() == getArg(i+1)->getId()) {
			if (getArg(i)->inverted == getArg(i + 1)->inverted) {
				args.erase(args.begin() + i + 1);
			} else {
				return true;
			}
		}
	}
	return false;
}

CnfExpression *
CnfAnd::invert()
{
	CnfOr *a = new CnfOr();
	a->args.resize(args.size());
	for (unsigned x = 0; x < args.size(); x++)
		a->args[x] = args[x]->invert();
	return a;
}

void
CnfAnd::optimise()
{
	bool progress;
	do {
		progress = false;

		if (TIMEOUT)
			return;

		for (unsigned i = 0; i < args.size(); ) {
			if (getArg(i)->optimise()) {
				args.erase(args.begin() + i);
			} else {
				i++;
			}
		}

		/* First rule: (A | b) & (A | ~b) -> just A. */
		for (unsigned i = 0; !TIMEOUT && i < args.size(); i++) {
			for (unsigned j = i + 1; !TIMEOUT && j < args.size(); j++) {
				/* If two terms differ in a single
				   atom, and that difference is just
				   whether the atom is negatated, they
				   can be merged. */
				bool haveDifference;
				bool haveDisallowedDifference;
				CnfOr *argi = getArg(i);
				CnfOr *argj = getArg(j);
				if (argi->args.size() !=
				    argj->args.size())
					continue;
				haveDifference = false;
				haveDisallowedDifference = false;
				for (unsigned k = 0;
				     !TIMEOUT && k < argi->args.size();
				     k++) {
					if (argi->getArg(k)->getId() !=
					    argj->getArg(k)->getId())
						haveDisallowedDifference = true;
					if (argi->getArg(k)->inverted != argj->getArg(k)->inverted) {
						if (haveDifference)
							haveDisallowedDifference = true;
						else
							haveDifference = true;
					}
				}
				if (TIMEOUT || haveDisallowedDifference)
					continue;
				if (!haveDifference) {
					/* i and j are identical ->
					 * just kill of j */
				} else {
					/* Yay.  We're going to
					   eliminate a single atom
					   from argi, and eliminate
					   argj completely. */
					for (unsigned k = 0;
					     !TIMEOUT;
					     k++) {
						assert(k < argi->args.size());
						assert(argi->getArg(k)->getId() ==
						       argj->getArg(k)->getId());
						if (argi->getArg(k)->inverted != argj->getArg(k)->inverted) {
							/* This is the one */
							argi->args.erase(argi->args.begin() + k);
							argi->clearName();
							break;
						}
					}
				}
				args.erase(args.begin() + j);
				clearName();
				progress = true;
				j--;
			}
		}

		/* Second rule: A & (A | B) -> A */
		for (unsigned i = 0; !TIMEOUT && i < args.size(); i++) {
			for (unsigned j = 0; !TIMEOUT && j < args.size(); j++) {
				if (i == j)
					continue;
				CnfOr *argi = getArg(i);
				CnfOr *argj = getArg(j);
				bool iSubsetJ = true;
				for (unsigned k = 0; !TIMEOUT && iSubsetJ && k < argi->args.size(); k++) {
					bool present = false;
					for (unsigned m = 0; !present && m < argj->args.size(); m++) {
						if (argi->getArg(k)->getId() == argj->getArg(m)->getId() &&
						    argi->getArg(k)->inverted == argj->getArg(m)->inverted)
							present = true;
					}
					if (!present)
						iSubsetJ = false;
				}
				if (iSubsetJ) {
					/* argi is a subset of argj,
					 * so argj can be safely
					 * eliminated. */
					progress = true;
					args.erase(args.begin() + j);
					clearName();
					/* Start again from the
					 * beginning. */
					i = j = 0;
				}
			}
		}

		/* Third rule: a & (B | ~a) -> a & B. */
		for (unsigned i = 0; !TIMEOUT && i < args.size(); i++) {
			CnfOr *argi = getArg(i);
			if (argi->args.size() != 1)
				continue;
			CnfVariable *argiA = argi->getArg(0);
			for (unsigned j = 0; !TIMEOUT && j < args.size(); j++) {
				if (j == i)
					continue;
				CnfOr *argj = getArg(j);
				for (unsigned k = 0; k < argj->args.size(); k++) {
					CnfVariable *argjA = argj->getArg(k);
					if (argjA->getId() != argiA->getId())
						continue;
					/* Normally, the second rule
					   would have already
					   eliminated argj if this
					   were true, but that isn't
					   always the case if we've
					   modified the structure so
					   that rule 2 now fires where
					   it wouldn't before.  Just
					   leave it until the next
					   iteration. */
					if (argjA->inverted == argiA->inverted) {
						continue;
					}
					progress = true;
					argj->args.erase(argj->args.begin() + k);
					argj->clearName();
					k--;
				}
			}
		}
	} while (progress);
}

static void
buildVarMap(IRExpr *inp, std::map<IRExpr *, CnfExpression *> &toVars,
	    std::map<int, IRExpr *> &toExprs)
{
	if (toVars.count(inp))
		return;
	if (inp->tag == Iex_Associative &&
	    (inp->Iex.Associative.op == Iop_And1 ||
	     inp->Iex.Associative.op == Iop_Or1)) {
		for (int x = 0; x < inp->Iex.Associative.nr_arguments; x++)
			buildVarMap(inp->Iex.Associative.contents[x],
				    toVars,
				    toExprs);
	} else if (inp->tag == Iex_Unop &&
		   inp->Iex.Unop.op == Iop_Not1) {
		buildVarMap(inp->Iex.Unop.arg, toVars, toExprs);
	} else {
		CnfVariable *v = new CnfVariable();
		toExprs[v->id] = inp;
		toVars[inp] = v;
	}
}

static CnfExpression *
convertIRExprToCNF(IRExpr *inp, std::map<IRExpr *, CnfExpression *> &m)
{
	CnfExpression *r;
	if (m.count(inp))
		return m[inp];
	if (inp->tag == Iex_Unop) {
		assert(inp->Iex.Unop.op == Iop_Not1);
		r = convertIRExprToCNF(inp->Iex.Unop.arg, m)->invert();
	} else {
		CnfGrouping *r2;
		assert(inp->tag == Iex_Associative);
		if (inp->Iex.Associative.op == Iop_And1) {
			r2 = new CnfAnd();
		} else {
			assert(inp->Iex.Associative.op == Iop_Or1);
			r2 = new CnfOr();
		}
		for (int x = 0; x < inp->Iex.Associative.nr_arguments; x++)
			r2->addChild(convertIRExprToCNF(inp->Iex.Associative.contents[x], m));
		r = r2;
	}
	m[inp] = r;
	return r;
}

static CnfAnd *
IRExprToCnf(IRExpr *inp, CnfExpression **_root, std::map<int, IRExpr *> &varsToExprs)
{
	__set_profiling(IRExprToCnf);
	std::map<IRExpr *, CnfExpression *> exprsToVars;
	CnfExpression *root;
	CnfAnd *a;

	{
		__set_profiling(buildVarMap);
		buildVarMap(inp, exprsToVars, varsToExprs);
	}
	{
		__set_profiling(convertIRExprToCNF);
		root = convertIRExprToCNF(inp, exprsToVars);
	}
	root = root->CNF();
	a = dynamic_cast<CnfAnd *>(root);
	if (!a) {
		CnfOr *o = dynamic_cast<CnfOr *>(root);
		if (!o) {
			assert(dynamic_cast<CnfVariable *>(root));
			o = new CnfOr();
			o->addChild(root);
		}
		a = new CnfAnd();
		a->addChild(o);
	}
	{
		__set_profiling(sort_cnf);
		a->sort();
	}
	{
		__set_profiling(optimise_cnf);
		a->optimise();
	}

	if (_root)
		*_root = root;
	return a;
}

/* A different kind of simplification: assume that @inp is a boolean
   expression, and consists of some tree of And1, Or1, and Not1
   expressions with other stuff at the leaves.  Treat all of the other
   stuff as opaque boolean variables, and then convert to CNF.  Try to
   simplify it there.  If we make any reasonable progress, convert
   back to the standard IRExpr form and return the result.  Otherwise,
   just return @inp. */
IRExpr *
simplifyIRExprAsBoolean(IRExpr *inp, bool *done_something)
{
	__set_profiling(simplifyIRExprAsBoolean);
	
	if (!((inp->tag == Iex_Unop &&
	       inp->Iex.Unop.op == Iop_Not1) ||
	      (inp->tag == Iex_Associative &&
	       (inp->Iex.Associative.op == Iop_Or1 ||
		inp->Iex.Associative.op == Iop_And1))))
		return inp;

	inp = internIRExpr(inp);

	std::map<int, IRExpr *> varsToExprs;
	CnfExpression *root;
	IRExprToCnf(inp, &root, varsToExprs);
	IRExprTransformer t;
	IRExpr *r;
	{
		__set_profiling(cnf_as_irexpr);
		r = root->asIRExpr(varsToExprs, t);
	}
	if (exprComplexity(r) < exprComplexity(inp)) {
		*done_something = true;
		return r;
	} else
		return inp;
}


/* internIRExpr doesn't really belong here, but it doesn't really
   belong anywhere else, either, and since we're the only callers this
   seemed like as good a place as any to stash it. */
struct internIRExprTable {
	static const int nr_entries = 17;
	std::map<IRExpr *, IRExpr *> lookups[nr_entries];
};

static unsigned
shallow_hash(const IRExpr *e)
{
	switch (e->tag) {
	case Iex_Const:
		return 100242167;
	case Iex_Binder:
		return e->Iex.Binder.binder * 100000393 + 100005469;
	case Iex_Get:
		return e->Iex.Get.offset * 100001029 + 100011943;
	case Iex_GetI:
		return 100013213;
	case Iex_RdTmp:
		return e->Iex.RdTmp.tmp * 100017493 + 100025479;
	case Iex_Qop:
		return e->Iex.Qop.op * 100034159 + 100043347;
	case Iex_Triop:
		return e->Iex.Triop.op * 100046753 + 100050683;
	case Iex_Binop:
		return e->Iex.Binop.op * 100057339 + 100067581;
	case Iex_Unop:
		return e->Iex.Unop.op * 100080689 + 100102913;
	case Iex_Load:
		return 100110343;
	case Iex_CCall:
		return 100125853;
	case Iex_Mux0X:
		return 100146091;
	case Iex_Associative:
		return e->Iex.Associative.op * 100161727 + e->Iex.Associative.nr_arguments * 100268423 + 100176877;
	case Iex_FreeVariable:
		return e->Iex.FreeVariable.key.val * 100190957;
	case Iex_ClientCallFailed:
		return 100213697;
	case Iex_ClientCall:
		return 100256371;
	case Iex_HappensBefore:
		return 100234427;
	}
	abort();
}

static IRExpr *
internIRExpr(IRExpr *e, internIRExprTable &lookupTable)
{
	unsigned h = shallow_hash(e) % internIRExprTable::nr_entries;
	if (lookupTable.lookups[h].count(e))
		return lookupTable.lookups[h][e];
	switch (e->tag) {
	case Iex_Binder:
	case Iex_Get:
	case Iex_RdTmp:
	case Iex_Const:
	case Iex_FreeVariable:
	case Iex_HappensBefore:
		break;
	case Iex_GetI:
		e->Iex.GetI.ix = internIRExpr(e->Iex.GetI.ix, lookupTable);
		break;
	case Iex_Qop:
		e->Iex.Qop.arg4 = internIRExpr(e->Iex.Qop.arg4, lookupTable);
	case Iex_Triop:
		e->Iex.Qop.arg3 = internIRExpr(e->Iex.Qop.arg3, lookupTable);
	case Iex_Binop:
		e->Iex.Qop.arg2 = internIRExpr(e->Iex.Qop.arg2, lookupTable);
	case Iex_Unop:
		e->Iex.Qop.arg1 = internIRExpr(e->Iex.Qop.arg1, lookupTable);
		break;
	case Iex_Load:
		e->Iex.Load.addr = internIRExpr(e->Iex.Load.addr, lookupTable);
		break;
	case Iex_CCall:
		for (int x = 0; e->Iex.CCall.args[x]; x++)
			e->Iex.CCall.args[x] =
				internIRExpr(e->Iex.CCall.args[x], lookupTable);
		break;
	case Iex_Mux0X:
		e->Iex.Mux0X.cond = internIRExpr(e->Iex.Mux0X.cond, lookupTable);
		e->Iex.Mux0X.expr0 = internIRExpr(e->Iex.Mux0X.expr0, lookupTable);
		e->Iex.Mux0X.exprX = internIRExpr(e->Iex.Mux0X.exprX, lookupTable);
		break;
	case Iex_Associative:
		for (int x = 0; x < e->Iex.Associative.nr_arguments; x++)
			e->Iex.Associative.contents[x] =
				internIRExpr(e->Iex.Associative.contents[x], lookupTable);
		break;
	case Iex_ClientCall:
		for (int x = 0; e->Iex.ClientCall.args[x]; x++)
			e->Iex.ClientCall.args[x] =
				internIRExpr(e->Iex.ClientCall.args[x], lookupTable);
		break;
	case Iex_ClientCallFailed:
		e->Iex.ClientCallFailed.target =
			internIRExpr(e->Iex.ClientCallFailed.target, lookupTable);
		break;
	}
	for (std::map<IRExpr *, IRExpr *>::iterator it = lookupTable.lookups[h].begin();
	     it != lookupTable.lookups[h].end();
	     it++) {
		IRExpr *other = it->first;
		if (other->tag != e->tag)
			continue;
		switch (e->tag) {
			/* For some structures, equality can be
			   checked by bitwise comparison. */
#define do_case(n)							\
			case Iex_ ## n:					\
				if (memcmp(&other->Iex. n,		\
					   &e->Iex. n,			\
					   sizeof(e->Iex. n)))		\
					continue;			\
			break
			do_case(Binder);
			do_case(Get);
			do_case(GetI);
			do_case(RdTmp);
			do_case(Qop);
			do_case(Triop);
			do_case(Binop);
			do_case(Unop);
			do_case(Load);
			do_case(Mux0X);
			do_case(FreeVariable);
			do_case(ClientCallFailed);
#undef do_case
			/* Others are harder. */
		case Iex_CCall: {
			bool bad;
			if (other->Iex.CCall.retty != e->Iex.CCall.retty)
				continue;
			bad = false;
			for (int x = 0; !bad && e->Iex.CCall.args[x]; x++) {
				if (e->Iex.CCall.args[x] !=
				    other->Iex.CCall.args[x])
					bad = true;
			}
			if (bad)
				continue;
			break;
		}

		case Iex_Associative: {
			if (other->Iex.Associative.op != e->Iex.Associative.op ||
			    other->Iex.Associative.nr_arguments != e->Iex.Associative.nr_arguments)
				continue;
			bool bad = false;
			for (int x = 0; !bad && x < e->Iex.Associative.nr_arguments; x++)
				if (e->Iex.Associative.contents[x] !=
				    other->Iex.Associative.contents[x])
					bad = true;
			if (bad)
				continue;
			break;
		}

		case Iex_Const:
			if (!physicallyEqual(e->Iex.Const.con,
					     other->Iex.Const.con))
				continue;
			break;

		case Iex_ClientCall: {
			bool bad;
			if (other->Iex.ClientCall.calledRip != e->Iex.ClientCall.calledRip)
				continue;
			bad = false;
			for (int x = 0; !bad; x++) {
				if (e->Iex.ClientCall.args[x] != other->Iex.ClientCall.args[x])
					bad = true;
				if (e->Iex.ClientCall.args[x] == NULL)
					break;
			}
			if (bad)
				continue;
			break;
		}

		case Iex_HappensBefore:
			if (e->Iex.HappensBefore.before->rip != other->Iex.HappensBefore.before->rip ||
			    e->Iex.HappensBefore.after->rip != other->Iex.HappensBefore.after->rip)
				continue;
			break;
		}

		/* If we get here, they match and we're done. */

		/* If the expressions are equal, then any optimisation
		   which has been applied to one can be assumed to
		   have been applied to the other. */
		e->optimisationsApplied |= it->second->optimisationsApplied;
		it->second->optimisationsApplied |= e->optimisationsApplied;

		lookupTable.lookups[h][e] = it->second;
		return it->second;
	}
	/* No duplicates of this IRExpr found so far */
	lookupTable.lookups[h][e] = e;
	return e;
}

static IRExpr *
internIRExpr(IRExpr *x)
{
	__set_profiling(internIRExpr);
	internIRExprTable t;
	return internIRExpr(x, t);
}

