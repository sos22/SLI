#ifndef INTERN_HPP__
#define INTERN_HPP__

class StateMachine;

IRExpr *internIRExpr(IRExpr *x);
StateMachine *internStateMachine(StateMachine *sm);

#endif /* !INTERN_HPP__ */

