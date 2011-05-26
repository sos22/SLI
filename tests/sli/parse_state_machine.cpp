#include <err.h>
#include <stdio.h>
#include <unistd.h>

#include "sli.h"
#include "state_machine.hpp"

static char *
readfile(int fd)
{
	size_t buf_allocated = 8192;
	char *buf = (char *)malloc(buf_allocated + 1);
	unsigned buf_used = 0;
	int r;

	while (1) {
		r = read(fd, buf + buf_used, buf_allocated - buf_used);
		if (r == 0)
			break;
		if (r < 0)
			err(1, "read(%d)", fd);
		buf_used += r;
		if (buf_used == buf_allocated) {
			buf_allocated += 8192;
			buf = (char *)realloc(buf, buf_allocated + 1);
		}
	}
	buf[buf_used] = 0;
	return buf;
}

int
main()
{
	char *buf;
	StateMachine *sm;

	init_sli();
	buf = readfile(0);
	if (!parseStateMachine(&sm, buf, (const char **)&buf))
		errx(1, "cannot parse input");
	printf("Suffix %s\n", buf);
	printStateMachine(sm, stdout);

	return 0;
}
