#ifndef DNF_HPP__
#define DNF_HPP__

#include "../nf.hpp"

#define NF_MAX_EXPRESSION 1000000

bool nf(IRExpr *e, NF_Expression &out);
void printNf(NF_Expression &dnf, FILE *f);

#endif /* !DNF_HPP__ */
