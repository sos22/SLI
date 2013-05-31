#include <stdbool.h>

volatile int read_cntr;
volatile int write_cntr;

#define STOP_ANALYSIS()					\
	asm volatile (".fill 100,1,0x90\n")

static volatile bool force_quit;

