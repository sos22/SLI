#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

static int *volatile global_ptr1;
static int *volatile global_ptr2;

static int read_events[2];
static int write_events;
static volatile bool force_quit;
static int mode;

#define BAD_PTR ((void *)0x57ul)
#define STOP_ANALYSIS()					\
	asm (".fill 100,1,0x90\n")

static void
bug1(void)
{
	int *p = global_ptr1;
	if (p != BAD_PTR) {
		p = global_ptr1;
		*p = 5;
	}
}

static void
bug2(void)
{
	static int q;
	global_ptr2 = &q;
	*global_ptr2 = 6;
}

static void *
thr_main(void *ign)
{
	int r;
	while (!force_quit) {
		if (mode == 0)
			r = random() % 2;
		else if (mode == 1)
			r = 0;
		else
			r = 1;
		STOP_ANALYSIS();
		if (r) {
			bug1();
		} else {
			bug2();
		}
		STOP_ANALYSIS();
		read_events[r]++;
	}
	return NULL;
}

int
main(int argc, char *argv[])
{
	pthread_t thr;
	static int t;
	int cntr;
	int forever = !!getenv("SOS22_RUN_FOREVER");

	if (argc == 1) {
		mode = 0;
	} else if (argc == 2 && !strcmp(argv[1], "1")) {
		mode = 1;
	} else if (argc == 2 && !strcmp(argv[1], "2")) {
		mode = 2;
	} else {
		errx(1, "need at most one argument which should be 1 or 2 to select a mode");
	}

	global_ptr1 = &t;

	pthread_create(&thr, NULL, thr_main, NULL);

	usleep(100000);
	time_t start_time = time(NULL);

	while (forever || time(NULL) < start_time + 10) {
		for (cntr = 0; cntr < 2000000; cntr++) {
			STOP_ANALYSIS();
			global_ptr2 = BAD_PTR;
			STOP_ANALYSIS();
		}
		STOP_ANALYSIS();
		global_ptr1 = &t;
		STOP_ANALYSIS();
		global_ptr1 = BAD_PTR;
		STOP_ANALYSIS();
		write_events++;
		usleep(1);
	}

	printf("Survived, %d read events and %d write events\n", read_events[0] + read_events[1], write_events);
	printf("%d,%d read events, %d write\n", read_events[0], read_events[1], write_events);
	return 0;
}
