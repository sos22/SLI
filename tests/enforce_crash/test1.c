#include "test_common.h"

static void
read_section()
{
	if (the_ptr != NULL)
		(*the_ptr)++;
}

static void
write_section(double delay)
{
	usleep(delay * 1e6);
	the_ptr = NULL;
	usleep(delay * 1e6);
	the_ptr = &my_int;
}
