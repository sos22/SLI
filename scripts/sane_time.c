#include <sys/time.h>
#include <sys/wait.h>
#include <err.h>
#include <stdio.h>
#include <unistd.h>

int
main(int argc, char *argv[])
{
	char *outfile = argv[1];
	struct timeval starttime;
	struct timeval endtime;
	int status;
	FILE *f;
	pid_t child;

	/* Check we can write to it */
	f = fopen(outfile, "w");
	if (!f) {
		err(1, "opening %s", outfile);
	}
	fclose(f);

	gettimeofday(&starttime, NULL);
	child = fork();
	if (child == -1) {
		err(1, "fork");
	}
	if (child == 0) {
		execvp(argv[2], argv + 2);
		err(1, "exec %s", argv[2]);
	}
	if (waitpid(child, &status, 0) != child) {
		err(1, "waitpid");
	}
	gettimeofday(&endtime, NULL);

	endtime.tv_usec -= starttime.tv_usec;
	endtime.tv_sec -= starttime.tv_sec;
	if (endtime.tv_usec < 0) {
		endtime.tv_usec += 1000000;
		endtime.tv_sec--;
	}

	f = fopen(outfile, "w");
	if (!f) {
		err(1, "re-opening %s", outfile);
	}
	fprintf(f, "%ld.%06ld\n", endtime.tv_sec, endtime.tv_usec);
	fclose(f);

	if (WIFEXITED(status)) {
		return WEXITSTATUS(status);
	} else if (WIFSIGNALED(status)) {
		fprintf(stderr, "child exited with signal %d\n", WTERMSIG(status));
		return 1;
	} else {
		fprintf(stderr, "child exited with unknown status 0x%x\n", status);
		return 1;
	}
}
