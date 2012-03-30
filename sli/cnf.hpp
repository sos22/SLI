#ifndef CNF_HPP__
#define CNF_HPP__

IRExpr *simplifyIRExprAsBoolean(IRExpr *inp, bool *done_something);
IRExpr *internIRExpr(IRExpr *x);

#endif /* !CNF_HPP */
