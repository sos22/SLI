#ifndef PICKLE_HPP__
#define PICKLE_HPP__

class StateMachine;

void pickleIRExpr(IRExpr *e, FILE *f);
IRExpr * unpickleIRExpr(FILE *f);
void pickleStateMachine(StateMachine *sm, FILE *f);
StateMachine *unpickleStateMachine(FILE *f);

#endif /* !PICKLE_HPP__ */
