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
	bool usedc = false;
	long nr_iters = 0;
	int i;
	FILE *logfile;

	logfile = stdout;

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
		} else if (!strcmp(argv[0], "-l")) {
			argv++;
			argc--;
			logfile = fopen(argv[0], "w");
			if (!logfile) {
				err(1, "opening %s", argv[0]);
			}
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
	} else if (!strcmp(enforcer, "<dc>")) {
		usedc = true;
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
		pid_t timeout;
		pid_t exited;

		timeout = fork();
		if (timeout == -1)
			err(1, "fork() timeout");
		if (timeout == 0) {
			sleep(180);
			_exit(0);
		}

		gettimeofday(&start, NULL);
		child = fork();
		if (child == -1)
			err(1, "fork()");
		if (child == 0) {
			setpgid(0, 0);
			close(1);
			if (usedc) {
				char **args;
				args = calloc(sizeof(char *), argc + 2);
				args[0] = "/local/scratch/sos22/notdc/ndc";
				memcpy(args + 1, argv, sizeof(char *) * argc);
				execv(args[0], args);
			} else {
				execv(argv[0], argv);
			}
			err(1, "execv(%s) failed", argv[0]);
		}
		exited = wait(NULL);
		gettimeofday(&end, NULL);

		end.tv_sec -= start.tv_sec;
		end.tv_usec -= start.tv_usec;
		if (end.tv_usec < 0) {
			end.tv_sec--;
			end.tv_usec += 1000000;
		}
		if (exited == timeout)
			fprintf(logfile, "%ld.%06ld T\n", end.tv_sec, end.tv_usec);
		else
			fprintf(logfile, "%ld.%06ld\n", end.tv_sec, end.tv_usec);
		fflush(logfile);

		if (exited == timeout)
			kill(-child, 9);
		else
			kill(timeout, 9);
		wait(NULL);
	}
	return 0;
}
