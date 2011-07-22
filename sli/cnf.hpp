#ifndef CNF_HPP__
#define CNF_HPP__

#include "simplify_irexpr.hpp"
#include "offline_analysis.hpp"

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

IRExpr *simplifyIRExprAsBoolean(IRExpr *inp, bool *done_something);

#endif /* !CNF_HPP */
