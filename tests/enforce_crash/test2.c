#include "test_common.h"

static void
stall(void)
{
	unsigned x;
	for (x = 0; x < 10000; x++)
		asm volatile( "" );
}

static void
read_section()
{
	stall();
	if (the_ptr != NULL) {
		(*the_ptr)++;
		(*the_ptr) *= 3;
	}
}

static void
write_section(double delay)
{
	usleep(delay * 1e6);
	the_ptr = NULL;
	usleep(delay * 1e6);
	the_ptr = &my_int;
}
