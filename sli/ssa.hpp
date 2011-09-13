#ifndef SSA_HPP__
#define SSA_HPP__

class StateMachine;

StateMachine *convertToSSA(StateMachine *);
StateMachine *deSSA(StateMachine *);

#endif /* !SSA_HPP__ */
