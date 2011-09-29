#ifndef DNF_HPP__
#define DNF_HPP__

/* bool is whether to invert it or not. */
typedef std::pair<bool, IRExpr *> NF_Atom;
typedef std::vector<NF_Atom> NF_Conjunction;
typedef std::vector<NF_Conjunction> NF_Disjunction;

#define NF_MAX_DISJUNCTION 1000000

bool nf(IRExpr *e, NF_Disjunction &out);
void printNf(NF_Disjunction &dnf, FILE *f);

#endif /* !DNF_HPP__ */
