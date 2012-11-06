#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

static int *volatile global_ptr;

static int read_events;
static int write_events;

static volatile bool force_quit;

#define STOP_ANALYSIS()					\
	asm (".fill 100,1,0x90\n")

static int
f(void)
{
	STOP_ANALYSIS();
	if (global_ptr)
		return 1;
	else
		return 0;
}

static void *
thr_main(void *ign)
{
	while (!force_quit) {
		STOP_ANALYSIS();
		if (f())
			*global_ptr = 5;
		STOP_ANALYSIS();
		read_events++;
	}
	return NULL;
}

int
main()
{
	pthread_t thr;
	int t;
	int forever = !!getenv("SOS22_RUN_FOREVER");
	pthread_create(&thr, NULL, thr_main, NULL);

	time_t start_time = time(NULL);

	while (forever ||time(NULL) < start_time + 10) {
		STOP_ANALYSIS();
		global_ptr = &t;
		STOP_ANALYSIS();
		usleep(1000000);
		STOP_ANALYSIS();
		global_ptr = NULL;
		STOP_ANALYSIS();
		write_events++;
	}

	printf("%d read events, %d write\n", read_events, write_events);
	return 0;
}
