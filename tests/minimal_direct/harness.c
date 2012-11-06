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
	const char *enforcer;
	bool randomise = false;
	bool no_sideconditions = false;
	long nr_iters = 0;
	int i;

	argv++;
	argc--;
	while (argv[0]) {
		if (!strcmp(argv[0], "-r")) {
			randomise = true;
			argv++;
			argc--;
		} else if (!strcmp(argv[0], "-s")) {
			no_sideconditions = true;
			argv++;
			argc--;
		} else if (!strcmp(argv[0], "-n")) {
			argv++;
			argc--;
			if (!sane_strtol(argv[0], &nr_iters))
				errx(1, "expected argument to -n to be an integer");
			argv++;
			argc--;
		} else {
			break;
		}
	}

	if (nr_iters <= 0)
		errx(1, "nr_iters must be > 0");

	enforcer = argv[0];
	argv++;
	argc--;

	if (access(argv[0], X_OK))
		errx(1, "%s is not executable?", argv[0]);

	if (!strcmp(enforcer, "<none>")) {
		unsetenv("LD_PRELOAD");
	} else {
		if (access(enforcer, R_OK))
			errx(1, "%s must be readable", enforcer);
		setenv("LD_PRELOAD", enforcer, 1);
	}
	if (randomise)
		setenv("SOS22_ENFORCER_RANDOMISE", "1", 1);
	else
		unsetenv("SOS22_ENFORCER_RANDOMISE");
	if (no_sideconditions)
		setenv("SOS22_DISABLE_SIDECONDITIONS", "1", 1);
	else
		unsetenv("SOS22_DISABLE_SIDECONDITIONS");

	for (i = 0; i < nr_iters; i++) {
		struct timeval start;
		struct timeval end;
		pid_t child;

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
		printf("%ld.%06ld\n", end.tv_sec, end.tv_usec);
		fflush(stdout);
	}
	return 0;
}
