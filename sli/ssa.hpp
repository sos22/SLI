#ifndef SSA_HPP__
#define SSA_HPP__

class StateMachine;

StateMachine *convertToSSA(StateMachine *);
StateMachine *deSSA(StateMachine *);
StateMachine *optimiseSSA(StateMachine *inp, bool *done_something);

#endif /* !SSA_HPP__ */
