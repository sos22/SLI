#ifndef DNF_HPP__
#define DNF_HPP__

/* bool is whether to invert it or not. */
typedef std::pair<bool, IRExpr *> DNF_Atom;
typedef std::vector<DNF_Atom> DNF_Conjunction;
typedef std::vector<DNF_Conjunction> DNF_Disjunction;

#define DNF_MAX_DISJUNCTION 1000000

bool dnf(IRExpr *e, DNF_Disjunction &out);
void printDnf(DNF_Disjunction &dnf, FILE *f);

#endif /* !DNF_HPP__ */
