#ifndef SSA_HPP__
#define SSA_HPP__

class StateMachine;
struct SMScopes;

StateMachine *convertToSSA(SMScopes *, StateMachine *, std::map<threadAndRegister, threadAndRegister> &);

#endif /* !SSA_HPP__ */
