/* Simple thing to make it easy to run a program repeatedly and time
   how long it takes */
#include <sys/time.h>
#include <err.h>
#include <errno.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <wait.h>

static bool
sane_strtol(const char *what, long *res)
{
	char *suffix;
	long r;
	int old_errno;

	*res = -1;
	old_errno = errno;
	errno = 0;
	r = strtol(what, &suffix, 0);
	if (errno == ERANGE || *suffix) {
		errno = old_errno;
		return false;
	}
	errno = old_errno;
	*res = r;
	return true;
}

int
main(int argc, char *argv[])
{
	const char *outfname;
	long nr_iters;
	int i;
	FILE *outfile;

	if (argc < 4)
		errx(1, "need at least nr_iters, timing file, and command to run");
	if (!sane_strtol(argv[1], &nr_iters) || nr_iters < 1)
		errx(1, "nr_iters should be positive integer");
	outfname = argv[2];
	argv += 3;
	argc -= 3;

	outfile = fopen(outfname, "w");
	if (!outfile)
		err(1, "opening %s", outfname);

	for (i = 0; i < nr_iters; i++) {
		struct timeval start;
		struct timeval end;
		pid_t child;

		printf("Start iter %d/%ld\n", i, nr_iters);
		gettimeofday(&start, NULL);
		child = fork();
		if (child == -1)
			err(1, "fork()");
		if (child == 0) {
			close(1);
			execv(argv[0], argv);
			err(1, "execv(%s) failed", argv[0]);
		}
		if (waitpid(child, NULL, 0) != child)
			err(1, "waiting for child");
		gettimeofday(&end, NULL);

		end.tv_sec -= start.tv_sec;
		end.tv_usec -= start.tv_usec;
		if (end.tv_usec < 0) {
			end.tv_sec--;
			end.tv_usec += 1000000;
		}
		fprintf(outfile, "%ld.%06ld\n", end.tv_sec, end.tv_usec);
		fflush(outfile);
	}
	return 0;
}
