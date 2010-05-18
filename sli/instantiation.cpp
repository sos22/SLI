#include "thread.cpp"
#include "machinestate.cpp"
#include "interpreter.cpp"
#include "syscalls.cpp"

#define MK_INTERP(t)				\
	MK_MACHINE_STATE(t);			\
	MK_INTERPRETER(t);			\
	MK_THREAD(t)

MK_INTERP(unsigned long);
