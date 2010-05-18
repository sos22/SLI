#include "thread.cpp"
#include "machinestate.cpp"
#include "interpreter.cpp"
#include "syscalls.cpp"

MK_MACHINE_STATE(unsigned long);
MK_INTERPRETER(unsigned long);
MK_THREAD(unsigned long);
