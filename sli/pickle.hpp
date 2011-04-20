#ifndef PICKLE_HPP__
#define PICKLE_HPP__

void pickleIRExpr(IRExpr *e, FILE *f);
IRExpr * unpickleIRExpr(FILE *f);

#endif /* !PICKLE_HPP__ */
